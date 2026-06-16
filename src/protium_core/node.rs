use crate::{
    can::{
        CanId, Frame, ProtiumFrameError, WireBits, WireLayout, IDENTIFIER_EXTENSION_BIT_IDX,
        MAX_STUFFED_EXTENDED_FRAME_SIZE_BITS, MAX_UNSTUFFED_EXTENDED_FRAME_SIZE_BITS, SRR_BIT_IDX,
    },
    printerr,
};
use bitvec::{field::BitField, order::Msb0, vec::BitVec};
use std::{cmp::Ordering, ops::Deref};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum ProtiumNodeError {
    // Implementation errors
    #[error("node lost transmission due to bus priority")]
    NodeLostTransmission,
    #[error("implementation error in rx/tx bit stream: frame layout/length desync. attempt to access out of bounds index in stream.")]
    BitStreamOutOfBounds,

    // CAN errors
    #[error("recessive bit read on wire after transmitting a dominant bit")]
    BitError,
    #[error("fixed-field format contains illegal bits. the field this error occured in was the '{0}' field")]
    FormError(&'static str),
    #[error("calculated crc != received crc. the receiver calculated crc is '{0}' while the received crc field is '{1}'")]
    CRCError(u16, u16),
    #[error("no dominant ack slot bit detected after sending recessive ack slot bit")]
    AckError,
}

#[derive(Debug)]
pub enum TransmitResult {
    Continue,
    LostArbitration,
    Completed,
}

/// Represents the current Node error state.
///
/// Error states happen on different conditions based on the value
/// of the nodes transmission and receiving error counters.
/// See the following fields in the [`Node`] struct:
/// - [`crate::node::Node::transmit_error_counter`]
/// - [`crate::node::Node::receive_error_counter`]
///
/// (let TEC = the nodes transmission error counter, let REC = the nodes receive error counter)
///
/// Each error state occurs when the following conditions are met:
/// None - The node is not in a state of error
/// Active - TEC < 128 and REC < 128
/// Passive - TEC >= 128 and REC >= 128
/// BusOff - TEC > 255
///
/// When the node is in the `BusOff` error state, the node will not
/// receive or transmit to or from the bus unless it is reset or
/// a consecutive sequence of recessive bits is sent.
#[derive(Debug, Default, PartialEq, Eq, Clone, Copy)]
pub enum NodeErrorState {
    #[default]
    None,
    Active,
    Passive,
    BusOff,
}

/// Represents the current state of the Node
///
/// Idle - The node is open to transmitting & receiving data from the bus
/// Sleeping - The node is not open to transmitting & receiving data from the bus
///            but is not in a state of error
/// Transmitting - The node is actively sending data via a CAN bus
/// Receiving - The node is actively receiving data from a CAN bus
/// Error - The node has experienced an error. Check the [`error_state`] field
///         and see [`crate::node::NodeErrorState`] for more detailed info on the error
#[derive(Debug, Default, PartialEq, Eq, Clone, Copy)]
pub enum NodeState {
    #[default]
    Idle,
    Sleeping,
    Transmitting,
    Receiving,
    Error,
}

/// A stream created when receiving a message from the bus
#[derive(Debug, Default, Clone)]
struct ReceiveStream {
    /// The stream of bits received. After every 5 identical consecutive bits, an opposite bit is inserted after.
    stuffed_bits: WireBits,
    /// Bits that are not stuffed. This stream can contain more than 5 identical consecutive bits.
    destuffed_bits: WireBits,
    /// Tracks the `stuffed_bits` bitstream. Contains the latest bit idx received in `stuffed_bits`
    wire_idx: usize,
    /// Tracks the `destuffed_bits` bitstream. Contains the latest bit idx received in `destuffed_bits`
    frame_idx: usize,
    /// Tracks the `stuffed_bits` bitstream to detect when a bit is a stuff-bit. Essential in the rolling
    /// destuffing logic.
    consecutive_identical_bits: usize,
    /// A flag set if the receiver wants to flip the ACK slot bit in a message.
    /// This is required per-protocol. When a receiver successfully receives a mesasge,
    /// there are no errors (e.g. calculated checksum doesn't equal received checksum),
    /// this flag will be set and the bus will know to push a dominant bit to all nodes for the ACK slot
    pending_ack: bool,

    // Data to gather about the frame
    // we're receiving. We piece together
    // this data as we are receiving the bits
    /// Whether or not the frame we're receiving is an extended frame.
    /// This is true if the Identifier Extension Bit at index
    /// [`crate::can::IDENTIFIER_EXTENSION_BIT`] in `bits` is 1 (true)
    is_extended_frame: bool,
    /// Contains the bits of "data length code" field apart of a CAN frame.
    /// Is always 4 bits long and represents the length of the `data` field in a
    /// CAN frame in bytes.
    frame_dlc_bits: WireBits,
    /// Represents the size of the data field in the receiving CAN frame in bytes
    ///
    /// When `frame_dlc_bits` is full (4 bits long) containing the full data length code,
    /// it is converted to a u16 and this option will contain that value. Otherwise, it will
    /// be None.
    frame_data_length: Option<u16>,
    /// The interpreted wirebits layout of the frame we're receiving
    /// The layout is created after we know two things:
    ///     1. if the frame is extended or not
    ///     2. the size of the data field in bits
    /// Because the start and end index of almost every field relies on
    /// how big the data field is and if the frame is extended.
    frame_layout: Option<WireLayout>,
}

/// A struct created when transmitting a frame to nodes via a bus
///
/// The frame is encoded and stored in `bits` using [`crate::can::Frame::encode`],
/// and `ts_frame_layout` is generated using [`crate::can::WireLayout`] along with the known
/// information about the frame before it is encoded (data length size and if its extended)
#[derive(Debug, Default)]
struct TransmitStream {
    bits: WireBits,
    ts_idx: usize,
    ack_slot_stuffed_idx: usize,
    ts_frame_layout: WireLayout,
    pending_retransmit: bool,
}

/// Represents a node (e.g. ECU) that can send and receive messages on a CAN bus
#[derive(Debug)]
pub struct Node {
    /// The CAN ID of the node. Every Node must have a CAN ID
    /// The more dominant (0) bits a CAN ID has, the higher priority it's messages
    /// it sends have over other Nodes
    can_id: CanId,
    /// Only process frames from other nodes with the following `CanId`'s
    filtered_can_ids: Vec<CanId>,
    pub(crate) state: NodeState,
    error_state: NodeErrorState,
    receive_error_counter: u16,
    transmit_error_counter: u16,
    transmit_stream: Option<TransmitStream>,
    receive_stream: Option<ReceiveStream>,
    on_complete_receive_callback: Option<fn(node_id: CanId, received_bits: &WireBits)>,
    on_complete_transmit_callback: Option<fn(node_id: CanId)>,
}

impl PartialEq for Node {
    fn eq(&self, other: &Self) -> bool {
        self.can_id == other.can_id
    }
}

impl Node {
    /// Create a new Node with CAN ID `can_id` in an `Idle` state, and `None` error state.
    pub fn new(can_id: CanId) -> Self {
        Self {
            can_id,
            filtered_can_ids: Vec::new(),
            state: NodeState::Idle,
            error_state: NodeErrorState::None,
            receive_error_counter: 0,
            transmit_error_counter: 0,

            transmit_stream: None,
            receive_stream: None,

            on_complete_receive_callback: None,
            on_complete_transmit_callback: None,
        }
    }

    /// Check if the current node is active and can
    /// transmit or receive message.
    ///
    /// An node is inactive if it is in the `BusOff`` `ErrorState` or
    /// the node is in the `Sleeping` state
    pub fn is_active(&self) -> bool {
        if self.state() == NodeState::Error && self.error_state() == NodeErrorState::BusOff
            || self.state() == NodeState::Sleeping
        {
            // Node is not active
            false
        } else {
            true
        }
    }

    /// Set the Node to sleep mode
    /// The node will not receive or transmit data in this mode unless
    /// [`Node::idle`] or [`Node::prepare_transmission`] is called
    pub fn sleep(&mut self) {
        self.state = NodeState::Sleeping;
    }

    /// Set the Node to idle mode
    /// The node is not receiving or transmitting but can whenever
    /// e.g. if this node is idle and another node sends a message, this node will receive
    pub fn idle(&mut self) {
        self.state = NodeState::Idle;
    }

    /// Get the current stae of the node
    pub fn state(&self) -> NodeState {
        self.state
    }

    /// Get the current state of error the node is in
    pub fn error_state(&self) -> NodeErrorState {
        self.error_state
    }

    /// Get the CAN ID of the node
    pub fn id(&self) -> CanId {
        self.can_id
    }

    /// Get a list of CAN IDs, this node has filtered
    ///
    /// The node will only process received messages from the
    /// nodes with the following CAN IDs
    pub fn filtered_can_ids(&self) -> &Vec<CanId> {
        &self.filtered_can_ids
    }

    pub(crate) fn set_idle(&mut self) {
        if self.state == NodeState::Transmitting {
            if let Some(transmitted_callback) = self.on_complete_transmit_callback.as_ref() {
                transmitted_callback(self.can_id);
            }
        }

        if let Some(received_bits) = self.receive_stream.as_ref().map(|rs| &rs.destuffed_bits) {
            if !received_bits.is_empty() {
                if let Some(received_callback) = self.on_complete_receive_callback.as_ref() {
                    received_callback(self.can_id, received_bits);
                }
            }
        }

        self.state = NodeState::Idle;
    }

    pub(crate) fn set_transmitting(&mut self) {
        if self.state == NodeState::Receiving {
            if let Some(received_bits) = self.receive_stream.as_ref().map(|rs| &rs.stuffed_bits) {
                if let Some(received_callback) = self.on_complete_receive_callback.as_ref() {
                    received_callback(self.can_id, received_bits);
                }
            }
        }

        self.transmit_stream = None;
        self.state = NodeState::Transmitting;
    }

    pub(crate) fn set_receiving(&mut self) {
        self.transmit_stream = None;
        self.receive_stream = None;
        self.state = NodeState::Receiving;
    }

    /// Encode and prepare the transmission of `frame` via CAN bus to allow the node
    /// to be queried by the bus when checking for transmitting nodes.
    ///
    /// When a frame is prepared for transmission, `Node.state` will be `Transmitting` and available
    /// to be queried by the bus when the bus asks this node what bit to drive. The node will push
    /// the encoded frame bits, bit by bit on every bus bit tick unless the node lost tranmission
    /// due to priority.
    pub fn queue_transmission(&mut self, frame: &Frame) -> Result<(), ProtiumFrameError> {
        let stuffed = frame.encode_stuffed().inspect_err(|_| {
            self.error(true);
        })?;

        let encoded = frame.encode().inspect_err(|_| {
            self.error(true);
        })?;

        let unstuffed_layout =
            WireLayout::generate_layout(frame.data_length_bits(), frame.is_extended());
        let ack_unstuffed = unstuffed_layout.acknowledgement_field.start;

        // Walk stuffed bits, skip stuff bits, count until we've seen ack_unstuffed real bits
        let mut real_count = 0;
        let mut consecutive = 0usize;
        let mut prev: Option<bool> = None;
        let mut ack_stuffed_idx = 0;

        for (i, bit) in stuffed.iter().enumerate() {
            let b = *bit;
            if let Some(p) = prev {
                if b != p {
                    if consecutive == 5 {
                        // this was a stuff bit, don't count it
                        consecutive = 0;
                        prev = Some(b);
                        continue;
                    }
                    consecutive = 1;
                } else {
                    consecutive += 1;
                }
            } else {
                consecutive = 1;
            }
            prev = Some(b);
            real_count += 1;
            if real_count == ack_unstuffed + 1 {
                ack_stuffed_idx = i;
                break;
            }
        }

        self.transmit_stream = Some(TransmitStream {
            bits: stuffed,
            ts_idx: 0,
            ack_slot_stuffed_idx: ack_stuffed_idx,
            ts_frame_layout: unstuffed_layout,
            pending_retransmit: false,
        });

        self.state = NodeState::Transmitting;
        Ok(())
    }

    pub fn pending_retransmission(&self) -> bool {
        if let Some(ts) = &self.transmit_stream {
            ts.pending_retransmit
        } else {
            false
        }
    }

    /// Tells the node to run a function, `callback` everytime a receive operation is fully completed.
    pub fn set_on_complete_receive_callback(&mut self, callback: fn(CanId, &WireBits)) {
        self.on_complete_receive_callback = Some(callback)
    }

    /// Tells the node to run a function, `callback` everytime a transmission operation is fully completed.
    pub fn set_on_complete_tranmission_callback(&mut self, callback: fn(CanId)) {
        self.on_complete_transmit_callback = Some(callback)
    }

    pub(crate) fn queue_retransmission(&mut self, queue: bool) {
        if let Some(ts) = self.transmit_stream.as_mut() {
            ts.pending_retransmit = queue;
            if queue {
                // reset transmit bit idx if we're queuing to retransmit the whole stream
                ts.ts_idx = 0;
            }
        }
    }

    /// Determine what bit to send based on a couple factors.
    ///
    /// - If the node is currently transmitting, send the next bit in the transmission bitstream
    ///   and increment the transmission bit index by 1
    /// - If the node is receiving, we do not send any bits, except if we must
    ///   send the dominant (0) ACK slot bit to let the transmitting nodes know that
    ///   a node received their message on the wire.
    pub(crate) fn drive_bit(&mut self) -> Option<bool> {
        match self.state {
            NodeState::Transmitting => {
                // get next bit to send in ts_stream.bits
                let ts_stream = self.transmit_stream.as_mut()?;
                ts_stream.bits.get(ts_stream.ts_idx).map(|b| {
                    ts_stream.ts_idx += 1;
                    *b
                })
            }
            NodeState::Receiving => {
                // check if we need to set the ack slot of the current
                // data we're receiving to 0 per protocol
                let rs_stream = self.receive_stream.as_mut()?;
                if rs_stream.pending_ack {
                    rs_stream.pending_ack = false;
                    return Some(false);
                }

                None
            }
            _ => None,
        }
    }

    pub fn store_bit(&mut self, bit: bool) {
        let rc_stream = self.receive_stream.get_or_insert(ReceiveStream {
            stuffed_bits: WireBits::with_capacity(MAX_STUFFED_EXTENDED_FRAME_SIZE_BITS),
            destuffed_bits: WireBits::with_capacity(MAX_UNSTUFFED_EXTENDED_FRAME_SIZE_BITS),
            wire_idx: 0,
            frame_idx: 0,
            consecutive_identical_bits: 0,
            pending_ack: false,
            is_extended_frame: false,
            frame_dlc_bits: WireBits::with_capacity(4),
            frame_data_length: None,
            frame_layout: None,
        });

        if rc_stream.stuffed_bits.is_empty() && bit {
            return;
        }

        let prev_bit = rc_stream.stuffed_bits.last().map(|b| *b);
        rc_stream.stuffed_bits.push(bit);
        rc_stream.wire_idx += 1;

        if Some(bit) == prev_bit {
            rc_stream.consecutive_identical_bits += 1;
        } else {
            if rc_stream.consecutive_identical_bits == 5 {
                rc_stream.consecutive_identical_bits = 0;
                return;
            }
            rc_stream.consecutive_identical_bits = 1;
        }

        rc_stream.destuffed_bits.push(bit);
        rc_stream.frame_idx += 1;
    }

    pub(crate) fn process_receive(&mut self) -> Result<(), ProtiumNodeError> {
        let Some(rc_stream) = &mut self.receive_stream else {
            return Ok(());
        };
        let rc_idx = rc_stream.frame_idx.saturating_sub(1);
        let Some(bit) = rc_stream.destuffed_bits.last().map(|b| *b) else {
            return Ok(());
        };

        // goal: check if this is an ack slot to set the bit to 0
        // construct a wire layout based on the bits we receive
        // 1. determine if the frame is extended or not
        if rc_idx == IDENTIFIER_EXTENSION_BIT_IDX {
            rc_stream.is_extended_frame = bit;
        } else {
            let dlc_field_start_idx = if rc_stream.is_extended_frame { 35 } else { 15 };

            if rc_idx >= dlc_field_start_idx && rc_stream.frame_data_length.is_none() {
                // 2. determine length of data
                match rc_stream.frame_dlc_bits.len().cmp(&4) {
                    Ordering::Less => rc_stream.frame_dlc_bits.push(bit),
                    Ordering::Equal => {
                        let frame_data_size_bits = rc_stream.frame_dlc_bits.load_be::<u16>() * 8;
                        rc_stream.frame_data_length = Some(frame_data_size_bits);
                        rc_stream.frame_layout = Some(WireLayout::generate_layout(
                            frame_data_size_bits as usize,
                            rc_stream.is_extended_frame,
                        ));
                    }
                    _ => (),
                }
            }
        }

        // a wire layout has been built for the frame. we now
        // know the start, end and length of all CAN frame fields
        // and can use this information to our advantange.
        if let Some(layout) = rc_stream.frame_layout {
            // after we build a frame layout we want to determine
            // when we need to flip the ack bit to let transmitters know
            // we received their message
            if rc_idx + 1 == layout.acknowledgement_field.start
                && self.state == NodeState::Receiving
            {
                let received_checksum: u16 = match rc_stream
                    .destuffed_bits
                    .get(layout.data_field.end()..layout.crc_field.end() - 1)
                {
                    Some(checksum) => checksum.load_be(),
                    None => {
                        printerr!("failed to construct received checksum from bitslice - diagnostic information: \n`layout`: {:#?}", layout);
                        return Err(ProtiumNodeError::BitStreamOutOfBounds);
                    }
                };

                let mut checksum_input = match rc_stream
                    .destuffed_bits
                    .get(0..layout.data_field.end())
                {
                    Some(input) => input.to_bitvec(),
                    None => {
                        printerr!("failed to construct checksum INPUT to calculate checksum from bitslice: `0..layout.data_field.end()` - `layout`: {:#?}", layout);
                        return Err(ProtiumNodeError::BitStreamOutOfBounds);
                    }
                };

                checksum_input.append(&mut BitVec::<u8, Msb0>::repeat(false, 15));

                let calculated_checksum = Frame::checksum_with_input(&checksum_input);
                if calculated_checksum != received_checksum {
                    return Err(ProtiumNodeError::CRCError(
                        calculated_checksum,
                        received_checksum,
                    ));
                }

                rc_stream.pending_ack = calculated_checksum == received_checksum;
            }

            // verify all forms depending on rc_idx
            let verify_bit_at_index_is =
                |bit: bool, idx: usize, form: &'static str| -> Result<(), ProtiumNodeError> {
                    if rc_stream
                        .deref()
                        .destuffed_bits
                        .get(idx)
                        .map(|b| *b)
                        .ok_or(ProtiumNodeError::BitStreamOutOfBounds)?
                        != bit
                    {
                        Err(ProtiumNodeError::FormError(form))
                    } else {
                        Ok(())
                    }
                };

            if rc_stream.is_extended_frame {
                // verify SRR bit is 1
                if rc_idx >= SRR_BIT_IDX {
                    verify_bit_at_index_is(true, SRR_BIT_IDX, "SRR bit")?;
                }

                // verify ctrl field r0 bit is 0
                if rc_idx >= layout.control_field.start {
                    verify_bit_at_index_is(false, layout.control_field.start, "Control Field R0")?;
                }
            }

            // verify ctrl field r1 bit is dominant
            if rc_idx > layout.control_field.start {
                verify_bit_at_index_is(false, layout.control_field.start + 1, "Control Field R1")?;
            }

            // verify crc delimeter is recessive
            if rc_idx >= layout.crc_field.end() - 1 {
                verify_bit_at_index_is(true, layout.crc_field.end() - 1, "CRC Delimeter")?;
            }

            // verify ack delimeter
            if rc_idx > layout.acknowledgement_field.start {
                verify_bit_at_index_is(
                    true,
                    layout.acknowledgement_field.start + 1,
                    "ACK Delimeter",
                )?;
            }

            // verify end of frame field is all recessive bits
            if rc_idx >= layout.end_of_frame_field.end() {
                let eof_bit_rng = layout.end_of_frame_field.start..layout.end_of_frame_field.end();
                if eof_bit_rng.len() != 7 {
                    return Err(ProtiumNodeError::BitStreamOutOfBounds);
                }

                if !rc_stream
                    .stuffed_bits
                    .get(eof_bit_rng)
                    .ok_or(ProtiumNodeError::BitStreamOutOfBounds)?
                    .all()
                {
                    return Err(ProtiumNodeError::FormError("EOF Field"));
                }
            }
        }

        Ok(())
    }

    pub(crate) fn process_transmit(&mut self, wire: bool) -> Result<(), ProtiumNodeError> {
        let Some(ts_stream) = &mut self.transmit_stream else {
            return Ok(());
        };

        // the current bit idx of what bit to transmit next
        let ts_idx = ts_stream.ts_idx;
        let last_ts_idx = ts_idx.saturating_sub(1);
        let Some(last_sent) = ts_stream.bits.get(last_ts_idx).map(|b| *b) else {
            return Ok(());
        };

        // a bit on the wire has changed and is not the same as the bit we sent
        // we sent a 0 (dominant bit) but the wire has a 1 (recessive bit) which is very wrong
        if !last_sent && wire {
            return Err(ProtiumNodeError::BitError);
        }

        if wire != last_sent {
            // check if we lost transmission to another node
            // we only need to check if we are in CAN IDS, RTR, or IDE
            let arbitration_loss_possible_range_idx =
                0..ts_stream.ts_frame_layout.arbitration_field.end();

            if arbitration_loss_possible_range_idx.contains(&last_ts_idx) {
                return Err(ProtiumNodeError::NodeLostTransmission);
            }
        } else {
            // a bit on the wire has not changed. this is acceptable only if
            // we didn't just send the ack slot which is supposed to be flipped by a receiver
            if last_ts_idx == ts_stream.ack_slot_stuffed_idx {
                return Err(ProtiumNodeError::AckError);
            }
        }

        Ok(())
    }

    pub(crate) fn error(&mut self, transmit_error: bool) {
        if transmit_error {
            self.transmit_error_counter += 1
        } else {
            self.receive_error_counter += 1
        };

        if self.transmit_error_counter < 128 && self.receive_error_counter < 128 {
            self.error_state = NodeErrorState::Active;
            // todo: send error frame
        } else if self.transmit_error_counter >= 128 && self.receive_error_counter >= 128 {
            self.error_state = NodeErrorState::Passive;
            // todo: send error frame
        } else if self.transmit_error_counter > 255 {
            self.error_state = NodeErrorState::BusOff;
        }

        self.state = NodeState::Error;
    }
}
