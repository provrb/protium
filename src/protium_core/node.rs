use crate::can::{
    push_byte, push_n_bits, Frame, ProtiumFrameError, WireBits, MAX_EXTENDED_FRAME_SIZE_BITS,
    MAX_STANDARD_FRAME_SIZE_BITS,
};

#[repr(u8)]
#[derive(Debug, Default)]
pub enum ErrorState {
    #[default]
    None,

    Active,
    Passive,
    BusOff,
}

#[derive(Debug, Default)]
pub struct Node {
    pub error_state: ErrorState,
    pub receive_error_counter: u16,
    pub transmit_error_counter: u16,
}

impl Node {
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

    #[allow(unused_variables)]
    pub fn transmit(&self, frame: &Frame) -> Result<(), ProtiumFrameError> {
        todo!()
    }

    #[allow(unused_variables)]
    pub fn receive(&self, bits: WireBits) -> Result<Frame, ProtiumFrameError> {
        todo!()
    }
}
