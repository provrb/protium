use crate::can::{
    push_byte, push_n_bits, CanId, Frame, ProtiumFrameError, WireBits, WireLayout,
    EXTENDED_DLC_BIT_RANGE_IDX, IDENTIFIER_EXTENSION_BIT_IDX, MAX_EXTENDED_FRAME_SIZE_BITS,
    MAX_STANDARD_FRAME_SIZE_BITS, STANDARD_DLC_BIT_RANGE_IDX,
};
use bitvec::{bitvec, field::BitField, order::Msb0, vec::BitVec};

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

#[derive(Debug, Default)]
struct ReceiveStream {
    bits: WireBits,
    rc_idx: usize,

    // Data to gather about the frame
    // we're receiving. We piece together
    // this data as we are receiving the bits
    is_extended_frame: bool,
    frame_data_length: Option<u16>,
    frame_dlc_bits: WireBits,
}

#[derive(Debug)]
struct TransmitStream {
    bits: WireBits,
    ts_idx: usize,
    ts_frame: Frame,
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
        println!("bit stream b4: {}", bitstream);
        push_n_bits(&mut bitstream, frame.data_length() as u32, 4); // 3. DLC
        println!(
            "bitstream. data length: `{}` as bits: `{:b}`. last four bits are dlc: {}",
            frame.data_length() as u32,
            frame.data_length() as u32,
            bitstream
        );
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

    pub fn prepare_transmission(&mut self, frame: &Frame) -> Result<(), ProtiumFrameError> {
        let encoded = Node::encode(frame).inspect_err(|_| {
            self.error(true);
        })?;

        self.transmit_stream = Some(
            TransmitStream {
                bits: encoded,
                ts_idx: 0,
                ts_frame: frame.clone(),
                ts_frame_layout: WireLayout::generate_layout(frame.data_length(), frame.is_extended())
            }
        );

        self.state = NodeState::Transmitting;
        Ok(())
    }

    pub fn reset_transmission(&mut self) {
        self.transmit_stream = None;
    }

    pub fn drive_bit(&mut self, peek: bool) -> Option<bool> {
        todo!()
    }

    pub fn read_wire(&mut self, wire: bool) {
        if self.state == NodeState::Receiving {
            let rs_stream = self.receive_stream.get_or_insert_default();
            
            rs_stream.bits.push(wire);
            rs_stream.rc_idx += 1;
        }

        if self.state == NodeState::Transmitting {
            let Some(ts_stream) = self.transmit_stream.as_mut() else {
                // we have no data to send. set state to receiving and return
                self.state = NodeState::Receiving;
                return;
            };

            // the current bit idx of what bit to transmit next
            // therefore, last bit idx is ts_idx - 1
            let ts_idx = ts_stream.ts_idx;
            let last_ts_idx = ts_idx.saturating_sub(1);
            if let Some(last_sent) = ts_stream.bits.get(last_ts_idx) {
                // a bit on the wire has changed and is not the same as the bit we sent
                if wire != last_sent {
                    // this should ONLY happen if we reached the acknowledgement field.
                    // a receiver will change the bit of the ack slot to tell us a node received it
                    if last_ts_idx == ts_stream.ts_frame_layout.acknowledgement_field.start {
                        // this is fine, a receiver flipped the ack slot like theyre supposed to
                    } else {
                        // is it possible we lost trasmission to another node?
                        // check if we lost transmission
                        // we only need to check if we are in CAN IDS, RTR, or IDE
                        let arbitration_loss_possible_range_idx = 0..=ts_stream.ts_frame_layout.arbitration_field.end();
                        if arbitration_loss_possible_range_idx.contains(&ts_idx) {
                            // lost transmission. set state to receiving
                            self.state = NodeState::Receiving;
                            return;
                        }
                    }
                } else {
                    // a bit on the wire has not changed. this is acceptable only if
                    // we didn't just send the ack slot which is supposed to be flipped by a receiver
                    if last_ts_idx == ts_stream.ts_frame_layout.acknowledgement_field.start {
                        // we send a recessive ack slot bit and it hasn't changed, meaning no node
                        // flipped it to tell us a node received our bits
                        panic!("No receiver flipped ack slot bit.");
                    }

                    // no problems when trasmitting so keep transmitting
                }
            }

            // at this point all possible things that could go wrong when transmitting
            // have been addressed (lost transmission, invalid ack slot bit)
            // so increment the idx of the bit to trasnmit

            ts_stream.ts_idx += 1;
        }        
    }


    // pub fn resultant_bus_bit(&mut self, sent: Option<bool>, used: bool) {
    //     // println!("[Node:{}] Sent bit: `{:?}` - bit on bus: `{}`", self.id(), sent, used);

    //     // receive bit
    //     let rs = self.receive_stream.get_or_insert(ReceiveStream {
    //         bits: WireBits::new(),
    //         curr_bit_idx: 0,
    //         frame_data_length: None,
    //         is_extended_frame: false,
    //         frame_dlc_bits: WireBits::with_capacity(4),
    //     });

    //     let rs_idx = rs.curr_bit_idx;

    //     // try and generate layout
    //     if rs_idx == IDENTIFIER_EXTENSION_BIT_IDX {
    //         rs.is_extended_frame = used;
    //     } else if rs_idx > IDENTIFIER_EXTENSION_BIT_IDX {
    //         let dlc_idx = if rs.is_extended_frame {
    //             EXTENDED_DLC_BIT_RANGE_IDX
    //         } else {
    //             STANDARD_DLC_BIT_RANGE_IDX
    //         }; 
    //         if dlc_idx.contains(&rs_idx) {
    //             // parse dlc
    //             rs.frame_dlc_bits.push(used);
    //         }
    //     }

    //     // all dlc bits have been pushed
    //     // now we can save the data length
    //     if rs.frame_data_length.is_none() && rs.frame_dlc_bits.len() == 4 {
    //         rs.frame_data_length = Some(rs.frame_dlc_bits.load_be());
    //     }

    //     let layout = match rs.frame_data_length {
    //         Some(data_size) => Some(WireLayout::generate_layout(
    //             data_size as usize,
    //             rs.is_extended_frame,
    //         )),
    //         None => None,
    //     };

    //     if let Some(layout) = layout {
    //         if rs_idx + 1 == layout.acknowledgement_field.start {
    //             println!("Node is pending acknowledge bit set");
    //             self.pending_ack = true;
    //         }
    //     };

    //     println!("push bit: {used} @ idx {rs_idx}, ack slot idx: {}", layout.unwrap_or_default().acknowledgement_field.start);
    //     rs.bits.push(used);
    //     rs.curr_bit_idx += 1;

    //     let Some(sent) = sent else {
    //         return;
    //     };

    //     let Some(layout) = layout else {
    //         return;
    //     };

    //     let Some(ts) = self.transmit_stream.as_mut() else {
    //         println!("[Node:{}] No transmitting stream", self.can_id);
    //         return;
    //     };
    //     let ts_idx = ts.curr_bit_idx.saturating_sub(1);
    //     if self.state == NodeState::Transmitting {
    //         if sent && !used {
    //             // check if we lost transmission
    //             // we lose transmission if this bit is apart of CAN ID, RTR, or IDE
    //             // and sent != used
    //             let arb = layout.arbitration_field;

    //             if (arb.start..arb.end()).contains(&ts_idx) {
    //                 // we lost transmission. start receiving the messages now
    //                 println!(
    //                     "[Node:{}] Lost transmission. Switching to receiving.",
    //                     self.can_id
    //                 );
    //                 self.state = NodeState::Receiving;
    //             }
    //         }

    //         if (sent && used) && ts_idx == layout.acknowledgement_field.start {
    //             // ack slot not updated by a receiver node
    //             panic!(
    //                 "[Node:{}] ACK slot bit: `{}` - bit on bus: `{}` - ACK bit not set to 0.",
    //                 self.id(),
    //                 sent,
    //                 used
    //             );
    //         }
    //     }
    // }
}
