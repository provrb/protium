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

#[derive(Debug, Default, PartialEq, Eq, Clone, Copy)]
pub enum ErrorState {
    #[default]
    None,
    Active,
    Passive,
    BusOff,
}

#[derive(Debug, Default, PartialEq, Eq, Clone, Copy)]
pub enum NodeState {
    #[default]
    Idle,
    Sleeping,
    Transmitting,
    Receiving,
    Error,
}

#[derive(Debug, Default)]
struct ReceiveStream {
    bits: WireBits,
    rc_idx: usize,
    pending_ack: bool, // acknowledge the receiving bits

    // Data to gather about the frame
    // we're receiving. We piece together
    // this data as we are receiving the bits
    is_extended_frame: bool,
    frame_data_length: Option<u16>,
    frame_dlc_bits: WireBits,
    frame_layout: Option<WireLayout>,
}

#[derive(Debug, Default)]
struct TransmitStream {
    bits: WireBits,
    ts_idx: usize,
    ts_frame_layout: WireLayout,
}

#[derive(Debug)]
pub struct Node {
    can_id: CanId,

    /// Only process frames from other nodes
    /// with the following `CanId`'s
    filtered_can_ids: Vec<CanId>,
    state: NodeState,
    error_state: ErrorState,
    receive_error_counter: u16,
    transmit_error_counter: u16,

    transmit_stream: Option<TransmitStream>,
    receive_stream: Option<ReceiveStream>,
}

impl PartialEq for Node {
    fn eq(&self, other: &Self) -> bool {
        self.can_id == other.can_id
    }
}

impl Node {
    pub fn new(can_id: CanId) -> Self {
        Self {
            can_id,
            filtered_can_ids: Vec::new(),
            state: NodeState::Idle,
            error_state: ErrorState::None,
            receive_error_counter: 0,
            transmit_error_counter: 0,

            transmit_stream: None,
            receive_stream: None,
        }
    }

    pub fn is_active(&self) -> bool {
        if self.state() == NodeState::Error && self.error_state() == ErrorState::BusOff
            || self.state() == NodeState::Sleeping
        {
            // Node is not active
            false
        } else {
            true
        }
    }

    pub fn sleep(&mut self) {
        self.state = NodeState::Sleeping;
    }

    pub fn idle(&mut self) {
        self.state = NodeState::Idle;
    }

    pub fn state(&self) -> NodeState {
        self.state
    }

    pub fn error_state(&self) -> ErrorState {
        self.error_state
    }

    pub fn id(&self) -> CanId {
        self.can_id
    }

    pub fn filtered_can_ids(&self) -> &Vec<CanId> {
        &self.filtered_can_ids
    }

    pub fn received_bits(&self) -> Option<&WireBits> {
        if let Some(rs) = self.receive_stream.as_ref() {
            Some(&rs.bits)
        } else {
            None
        }
    }

    pub fn prepare_transmission(&mut self, frame: &Frame) -> Result<(), ProtiumFrameError> {
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
        });

        self.state = NodeState::Transmitting;
        Ok(())
    }

    pub(crate) fn set_state(&mut self, state: NodeState) {
        self.state = state
    }

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
                    self.transmit_stream = None;
                    Ok(())
                }

                Err(e) => Err(e),
                _ => Ok(()),
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
            self.error_state = ErrorState::Active;
            // todo: send error frame
        } else if self.transmit_error_counter >= 128 && self.receive_error_counter >= 128 {
            self.error_state = ErrorState::Passive;
            // todo: send error frame
        } else if self.transmit_error_counter > 255 {
            self.error_state = ErrorState::BusOff;
        }

        self.state = NodeState::Error;
    }
}
