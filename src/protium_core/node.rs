use crate::can::{
    CanId, Frame, ProtiumFrameError, WireBits, WireLayout, IDENTIFIER_EXTENSION_BIT_IDX,
};
use bitvec::{field::BitField, order::Msb0, vec::BitVec};
use std::cmp::Ordering;
use thiserror::Error;

#[derive(Debug, Error)]
pub enum ProtiumNodeError {
    #[error("node transmit stream invalid/unexpected value")]
    InvalidTransmissionStream,
    #[error("no dominant ack slot bit detected after sending recessive ack slot bit")]
    FrameNotAcknowledged,
    #[error("node lost transmission due to bus priority")]
    NodeLostTransmission,
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
#[derive(Debug, Default)]
struct ReceiveStream {
    /// The stream of bits received
    bits: WireBits,
    /// The index of the most recent bit received
    rc_idx: usize,
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
    /// The current state of the node
    state: NodeState,
    /// The current error state of the node
    error_state: NodeErrorState,
    /// The amount of errors encountered on receive
    receive_error_counter: u16,
    /// The amount of errors encountered on transmission
    transmit_error_counter: u16,
    /// A stream created when transmitting a CAN frame on a CAN bus
    transmit_stream: Option<TransmitStream>,
    /// A stream created when receiving data on a CAN bus
    receive_stream: Option<ReceiveStream>,
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

    /// Get a reference to a Node's most recently received bits
    pub fn received_bits(&self) -> Option<&WireBits> {
        self.receive_stream.as_ref().map(|rs| &rs.bits)
    }

    /// Encode and prepare the transmission of `frame` via CAN bus to allow the node
    /// to be queried by the bus when checking for transmitting nodes.
    ///
    /// When a frame is prepared for transmission, `Node.state` will be `Transmitting` and available
    /// to be queried by the bus when the bus asks this node what bit to drive. The node will push
    /// the encoded frame bits, bit by bit on every bus bit tick unless the node lost tranmission
    /// due to priority.
    pub fn queue_transmission(&mut self, frame: &Frame) -> Result<(), ProtiumFrameError> {
        let encoded = frame.encode().inspect_err(|_| {
            self.error(true);
        })?;

        self.transmit_stream = Some(TransmitStream {
            bits: encoded,
            ts_idx: 0,
            ts_frame_layout: WireLayout::generate_layout(
                frame.data_length_bits(),
                frame.is_extended(),
            ),
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

    pub(crate) fn queue_retransmission(&mut self, queue: bool) {
        if let Some(ts) = self.transmit_stream.as_mut() {
            ts.pending_retransmit = queue;
            if queue {
                // reset transmit bit idx if we're queuing to retransmit the whole stream
                ts.ts_idx = 0;
            }
        }
    }

    /// Sets the current state of the node
    pub(crate) fn set_state(&mut self, state: NodeState) {
        if state == NodeState::Receiving || state == NodeState::Transmitting {
            // switching to receiving/transmitting so clear/prepare receive_stream
            self.receive_stream = None;
        }

        self.state = state
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

    /// Take a relayed bit `wire` received from a node via a working CAN bus,
    /// andreceive the bit and transmit a bit only if
    /// `Node.state` is Transmitting and a frame has had
    /// transmission prepared with [`crate::node::Node::prepare_transmission`]
    pub(crate) fn read_wire(&mut self, wire: bool) -> Result<(), ProtiumNodeError> {
        Node::receive_bit(
            self.receive_stream.get_or_insert_default(),
            wire,
            self.state,
        );

        if self.state == NodeState::Transmitting {
            return match Node::transmit_bit(
                self.transmit_stream
                    .as_mut()
                    .ok_or(ProtiumNodeError::InvalidTransmissionStream)?,
                wire,
            ) {
                Err(ProtiumNodeError::NodeLostTransmission) => {
                    self.state = NodeState::Receiving;
                    if !self.pending_retransmission() {
                        self.queue_retransmission(true);
                    }

                    // self.set_state(NodeState::Receiving);
                    Ok(())
                }

                Err(e) => Err(e),
                _ => {
                    if self.pending_retransmission() {
                        self.queue_retransmission(false);
                    }

                    Ok(())
                }
            };
        }

        Ok(())
    }

    fn receive_bit(rc_stream: &mut ReceiveStream, bit: bool, node_state: NodeState) {
        let rc_idx = rc_stream.rc_idx;

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

        if let Some(layout) = rc_stream.frame_layout {
            if rc_idx + 1 == layout.acknowledgement_field.start
                && node_state == NodeState::Receiving
            {
                // verify crc checksum
                let received_checksum = rc_stream
                    .bits
                    .get(layout.data_field.end()..layout.crc_field.end() - 1)
                    .expect("Node received checksum is not valid")
                    .load_be();

                let mut checksum_input = rc_stream
                    .bits
                    .get(0..layout.data_field.end())
                    .expect("cannot get checksum input bits for some reason")
                    .to_bitvec();
                checksum_input.append(&mut BitVec::<u8, Msb0>::repeat(false, 15));

                let calculated_checksum = Frame::checksum_with_input(&checksum_input).unwrap();
                rc_stream.pending_ack = calculated_checksum == received_checksum;
            }
        }

        rc_stream.bits.push(bit);
        rc_stream.rc_idx += 1;
    }

    fn transmit_bit(ts_stream: &mut TransmitStream, wire: bool) -> Result<(), ProtiumNodeError> {
        // the current bit idx of what bit to transmit next
        // therefore, last bit idx is ts_idx - 1
        let ts_idx = ts_stream.ts_idx;
        let last_ts_idx = ts_idx.saturating_sub(1);
        let Some(last_sent) = ts_stream.bits.get(last_ts_idx) else {
            // the only time we wont have a reference to the last sent bit is if we are sending the first bit.
            // in this case its fine to return since we do not need to compute anything else
            return Ok(());
        };

        // a bit on the wire has changed and is not the same as the bit we sent
        if wire != last_sent {
            // check if we lost transmission to another node
            // we only need to check if we are in CAN IDS, RTR, or IDE
            let arbitration_loss_possible_range_idx =
                0..ts_stream.ts_frame_layout.arbitration_field.end();

            if arbitration_loss_possible_range_idx.contains(&ts_idx) {
                return Err(ProtiumNodeError::NodeLostTransmission);
            }
        } else {
            // a bit on the wire has not changed. this is acceptable only if
            // we didn't just send the ack slot which is supposed to be flipped by a receiver
            if last_ts_idx == ts_stream.ts_frame_layout.acknowledgement_field.start {
                // we send a recessive ack slot bit and it hasn't changed, meaning no node
                // flipped it to tell us a node received our bits
                return Err(ProtiumNodeError::FrameNotAcknowledged);
            }
        }

        Ok(())
    }

    fn error(&mut self, while_transmitting: bool) {
        if while_transmitting {
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
