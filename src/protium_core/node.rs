use bitvec::{field::BitField, order::Msb0, vec::BitVec};

use crate::can::{
    self, CanId, Frame, IDE_BIT_IDX, MAX_EXTENDED_FRAME_SIZE_BITS, MAX_STANDARD_FRAME_SIZE_BITS, ProtiumFrameError, WireBits, WireLayout, push_byte, push_n_bits
};

#[derive(Debug, Default)]
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
    Transmitting,
    Receiving,
    Error,
}

#[derive(Debug)]
struct BitStream {
    bits: WireBits,
    curr_bit_idx: usize,
}

#[derive(Debug)]
struct ReceiveStream {
    bits: WireBits,
    curr_bit_idx: usize,
    is_extended_frame: bool,
    frame_data_length: Option<u16>,
    frame_dlc_bits: WireBits,
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

    current_transmitting_frame: Option<Frame>,
    transmit_stream: Option<BitStream>,
    receive_stream: Option<ReceiveStream>,
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

            current_transmitting_frame: None,
            transmit_stream: None,
            receive_stream: None,
        }
    }

    pub fn id(&self) -> CanId {
        self.can_id
    }

    pub fn filtered_can_ids(&self) -> &Vec<CanId> {
        &self.filtered_can_ids
    }

    pub fn encode(frame: &Frame) -> Result<WireBits, ProtiumFrameError> {
        let capacity = if frame.is_extended() {
            MAX_EXTENDED_FRAME_SIZE_BITS
        } else {
            MAX_STANDARD_FRAME_SIZE_BITS
        };

        let mut bitstream = WireBits::with_capacity(capacity);
        bitstream.push(false); // SOF bit

        // Aarbitration Field
        // For extended frames contains:
        // 1. 11 Bit CAN ID
        // 2. Substitute remote request (SRR) bit
        // 3. Identifier extension (IDE) bit
        // 4. 18 Bit CAN ID
        // 5. Remote transmission request (RTR) bit
        //
        // For standard frames contains:
        // 1. 11 Bit CAN ID
        // 2. Remote transmission request (RTR) bit
        if frame.is_extended() {
            let split_id = frame.id().split_extended_id()?;

            push_n_bits(&mut bitstream, split_id.base_11_id as u32, 11); // 1. 11 bit CAN ID
            bitstream.push(true); // 2. SRR bit - always 1
            bitstream.push(true); // 3. IDE bit - 1 because this is an extended frame

            push_n_bits(&mut bitstream, split_id.ext_18_id, 18); // 4. 18 bit CAN ID
        } else {
            push_n_bits(&mut bitstream, frame.id().as_u32(), 11); // 1. 11 bit CAN ID
        }
        bitstream.push(frame.is_remote_request()); // RTR bit

        // Control Field
        //
        // 1. IDE bit for non-extended frames (which is always 0)
        //    or r0 bit (which is also always 0) for extended frames
        // 2. r1 bit (always 0)
        // 3. Data length code (DLC), 4 bits long. Tells the size of the payload in bytes.
        bitstream.push(false); // 1. IDE/r0 bit (always 0)
        bitstream.push(false); // 2. r1 bit (always 0)
        push_n_bits(&mut bitstream, frame.data_length() as u32, 4); // 3. DLC

        // Data Field
        // Push all bytes of data into the bitstream as bits
        for byte in frame.data() {
            push_byte(&mut bitstream, *byte);
        }

        // CRC Field
        // Contains:
        // 1. 15 bit long CRC-15 CAN checksum
        // 2. CRC delimeter bit (always 1)
        push_n_bits(&mut bitstream, frame.checksum()? as u32, 15); // 1. checksum
        bitstream.push(true); // 2. CRC delimeter - comes after checksum bits

        // Acknowledgement (ACK) Field
        // Contains:
        // 1. ACK slot bit. Transmitters set this bit to 1 and
        //    receivers set this bit to 0.
        bitstream.push(true); // 1. ack slot. transmitter sets to 1
        bitstream.push(true); // 2. ack delimeter - always 1

        // End of Frame (EOF) field.
        // Contains 7 recessive bits at the end of the frame
        bitstream.extend([true].repeat(7));
        Ok(bitstream)
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

    /// Sets the nodes current state and clears the error state, if any.
    pub(crate) fn set_state(&mut self, state: NodeState) {
        if state == self.state {
            return;
        }

        println!(
            "[Node:{}] Switched state from `{:?}` to `{:?}`",
            self.can_id, self.state, state
        );
        self.state = state;
        self.error_state = ErrorState::None;

        self.reset_transmit_stream();
    }

    pub fn get_state(&self) -> NodeState {
        self.state
    }

    pub fn transmit(&mut self, frame: Frame) -> Result<(), ProtiumFrameError> {
        let encoded = Node::encode(&frame).inspect_err(|_| {
            self.error(true);
        })?;

        self.current_transmitting_frame = Some(frame);
        self.transmit_stream = Some(BitStream {
            bits: encoded,
            curr_bit_idx: 0,
        });

        self.state = NodeState::Transmitting;
        Ok(())
    }

    fn reset_transmit_stream(&mut self) {
        self.transmit_stream = None;
    }

    pub(crate) fn transmit_bit(&mut self) -> Option<bool> {
        match &mut self.transmit_stream {
            Some(stream) => {
                if stream.curr_bit_idx + 1 > stream.bits.len() {
                    return None;
                }

                let old_idx = stream.curr_bit_idx;
                stream.curr_bit_idx += 1;
                stream.bits.get(old_idx).map(|bit| *bit)
            }
            _ => None,
        }
    }

    /// During transmission, the bus will tell us the bit we
    /// sent and the bit that won.
    /// If `used` != `sent` and the bit is apart of the CAN ID, RTR, or IDE bit's
    /// we lost the wire and must stop transmission.
    ///
    /// If `sent` is true and `used` is false and we sent the ACK slot (which is always 1)
    /// that means that a node received our message. If this does not happen, no node has received
    /// our message and we must retransmit.
    pub fn resultant_bus_bit(&mut self, sent: bool, used: bool) {
        // println!("[Node:{}] Sent bit: `{}` - bit on bus: `{}`", self.id(), sent, used);
        let Some(frame) = &self.current_transmitting_frame else {
            return;
        };

        let Some(stream) = &self.transmit_stream else {
            return;
        };

        let base_layout = WireLayout::generate_layout(frame.data_length(), frame.is_extended());
        if sent == true && used == false {
            // check if we lost transmission
            // we lose transmission if this bit is apart of CAN ID, RTR, or IDE
            // and sent != used
            let arb = base_layout.arbitration_field;

            if (arb.start..arb.end()).contains(&stream.curr_bit_idx) {
                // we lost transmission. start receiving the messages now
                self.set_state(NodeState::Receiving);
            }
        } else if sent == true && used == true {
            if stream.curr_bit_idx == base_layout.acknowledgement_field.start {
                // ack slot not updated by a receiver node
                panic!(
                    "[Node:{}] ACK slot bit: `{}` - bit on bus: `{}` - ACK bit not set to 0.",
                    self.id(),
                    sent,
                    used
                );
            }
        }
    }

    pub(crate) fn receive_bit(&mut self, bit: bool) {
        let receive_stream = self.receive_stream.get_or_insert(ReceiveStream {
            bits: WireBits::new(),
            curr_bit_idx: 0,
            frame_data_length: None,
            is_extended_frame: false,
            frame_dlc_bits: WireBits::with_capacity(4),
        });

        if receive_stream.curr_bit_idx == IDE_BIT_IDX {
            receive_stream.is_extended_frame = bit;
        }

        let dlc_idx_range = if receive_stream.is_extended_frame {
            32..36
        } else {
            15..19
        };

        if dlc_idx_range.contains(&receive_stream.curr_bit_idx) {
            receive_stream.frame_dlc_bits.push(bit);
        }

        if receive_stream.frame_dlc_bits.len() == 4 && receive_stream.frame_data_length.is_none() {
            receive_stream.frame_data_length = Some(receive_stream.frame_dlc_bits.load_be());
        }

        if let Some(data_len) = receive_stream.frame_data_length {
            // check if this is ack bit
            let layout = WireLayout::generate_layout(data_len as usize, receive_stream.is_extended_frame);
            if receive_stream.curr_bit_idx == layout.acknowledgement_field.start && bit {
                
            }
        }

        println!("[Node:{}] Received bit `{}` from bus", self.can_id, bit);

        receive_stream.bits.push(bit);
        receive_stream.curr_bit_idx = receive_stream.bits.len() - 1;
    }
}
