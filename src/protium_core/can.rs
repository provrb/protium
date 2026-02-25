use bitvec::prelude::*;

/// The generator polynomial constant used for CRC-15 (used by CAN) checksum
/// as the divisor to generate a checksum for the provided input data.
///
/// All checksum logic must use this in their checksum process.
const CRC_15_GENERATOR_POLYNOMIAL: u16 = 0b0100010110011001;

#[repr(u32)]
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum CanId {
    /// 11-bit standard CAN ID.
    Standard(u16),
    /// 29-bit extended CAN ID.
    /// consists of 11-bit base id combined with an 18-bit extended id
    Extended(u32),
}

/// Contains the 11-bit and 18-bit IDs used
/// to create a 29-bit extended CAN ID
pub(crate) struct ExtendedIdSplit {
    base_11_id: u16,
    ext_18_id: u32,
}

impl CanId {
    /// Validates a CAN ID and ensures it cannot be greater than
    /// the maximum conceptual size.
    ///
    /// Specifically; ensures an 11-bit CAN ID cannot be greater than 0x7FF and
    /// an 18-bit CAN ID cannot be greater than 0x1FFFFFFF.
    pub fn validate(&self) -> Result<(), ProtiumFrameError> {
        match *self {
            CanId::Standard(std_id) => {
                if std_id > 0x7FF {
                    return Err(ProtiumFrameError::InvalidCANId);
                }
            }
            CanId::Extended(ext_id) => {
                if ext_id > 0x1FFFFFFF {
                    return Err(ProtiumFrameError::InvalidCANId);
                }
            }
        }

        Ok(())
    }

    /// Splits an extended, 29-bit CAN ID into its components:
    /// 11-bit CAN ID and an 18-bit CAN ID
    ///
    /// Throws a `FrameError::InvalidCANId` error if the CanId the method is ran on
    /// is not an extended CAN ID.
    pub(crate) fn split_extended_id(&self) -> Result<ExtendedIdSplit, ProtiumFrameError> {
        match *self {
            Self::Extended(id) => {
                let base_11: u16 = ((id >> 18) & 0x7FF) as u16; // bits 28..18
                let ext_18: u32 = id & 0x3FFFF; // bits 17..0

                Ok(ExtendedIdSplit {
                    base_11_id: base_11,
                    ext_18_id: ext_18,
                })
            }
            _ => Err(ProtiumFrameError::InvalidCANId),
        }
    }
}

#[derive(Debug)]
pub struct FieldSpan {
    pub start: usize,
    pub len: usize,
}

/// Represents an Encoded CAN frame. (Unstuffed)
///
/// This struct is compatible with both 11-bit CAN ID frames and
/// 29-bit extended CAN ID frames.
///
/// The encoded message is stored as a bit vector. The frame includes field spans
/// that detail where a component of the message starts and it's size. For example,
/// the data field. `data_field` contains the index in `bits` where it starts at, and the size of
/// the field.
#[derive(Debug)]
pub struct EncodedFrame {
    pub bits: BitVec<u8, Msb0>, // bits[0] = 0 for start of frame (SOF) bit
    /// For standard CAN frames:
    /// 11-bit CAN ID | RTR bit
    ///
    /// For extended 29-bit CAN frames:
    /// 11-bit CAN ID | SRR bit | IDE bit | 18-bit CAN ID | RTR bit
    pub arbitration_field: FieldSpan,
    /// For standard CAN frames:
    /// IDE bit | Reserved R0 bit | Data Length Code (DLC)
    ///
    /// For extended 29-bit CAN frames:
    /// Reserved bit (r1) | Reserved bit (r0) | Data Length Code (DLC)
    pub control_field: FieldSpan,
    pub data_field: FieldSpan,
    /// Cyclic Redundancy Check field:
    /// Checksum (size varies based on CAN version) | CRC delimeter bit (always 1)
    pub crc_field: FieldSpan,
    pub acknowledgement_field: FieldSpan, // ACK slot bit | ACK delimeter
    pub end_of_frame_field: FieldSpan,    // 7 recessive (1) bits at the end of the frame
}

/// Represents a human friendly CAN frame.
///
/// Rather than just being bits, this struct seperates parts of a CAN
/// frame into accessible fields. Recessive and dominant bits like the ACK slot,
/// SOF delimeter, and unnecessary things like the IDE are not included in this struct
/// and are only present in `EncodedFrame`'s.
#[derive(Debug)]
pub struct Frame {
    can_id: CanId,
    payload: Vec<u8>,
    is_remote_request: bool,
}

/// An API error that is not to be confused with any technical error
/// regarding the wire.
///
/// Used in Results to determine the outcome of a `Frame` API call, like
/// `Frame::calculate_checksum()``
#[derive(Debug)]
pub enum ProtiumFrameError {
    InvalidChecksum,
    InvalidCANId,
}

impl Frame {
    /// Create a new frame with payload data `payload`
    ///
    /// Automatically calculates the checksum for the CAN frame and saves it.
    pub fn new(
        can_id: CanId,
        payload: Vec<u8>,
        is_remote_request: bool,
    ) -> Result<Self, ProtiumFrameError> {
        can_id.validate()?;

        let frame = Frame {
            can_id,
            payload,
            is_remote_request,
        };

        Ok(frame)
    }

    pub fn calculate_checksum(&self) -> Result<u16, ProtiumFrameError> {
        // checksum = input data (as a binary stream) % generator constant
        let input_data = self.create_checksum_input_stream()?;
        let mut crc = 0;
        for bit in &input_data {
            let feedback = ((crc >> 14) & 1) ^ (*bit as u16);

            crc <<= 1;
            crc &= 0x7fff;

            if feedback != 0 {
                crc ^= CRC_15_GENERATOR_POLYNOMIAL;
            }
        }

        let checksum = crc;
        Ok(checksum)
    }

    pub fn encode(&self) -> Result<EncodedFrame, ProtiumFrameError> {
        todo!()
    }

    /// Create a binary stream of input data for the checksum to compute with.
    ///
    /// The checksum binary input data consists of:
    /// SOF bit (always 0) | Arbitration field | Control field | Data field
    fn create_checksum_input_stream(&self) -> Result<BitVec<u8, Msb0>, ProtiumFrameError> {
        fn push_n_bits(dst: &mut BitVec<u8, Msb0>, value: u32, nbits: usize) {
            debug_assert!(nbits <= 32);
            for i in (0..nbits).rev() {
                dst.push(((value >> i) & 1) != 0);
            }
        }

        fn push_byte(dst: &mut BitVec<u8, Msb0>, byte: u8) {
            push_n_bits(dst, byte as u32, 8);
        }

        // input data = [1 | xxxx xxxx xxxx xxxx xxxx xxxx xxxx xxxx (32 bits) | xxxx xx (6 bits) | (up to 64 bits)]
        // convert input data into binary stream
        let mut input_data = BitVec::<u8, Msb0>::new();
        input_data.push(false); // SOF bit (always 0)

        // Arbitration field
        match self.can_id {
            CanId::Standard(base_11_id) => {
                push_n_bits(&mut input_data, base_11_id as u32, 11);
                input_data.push(self.is_remote_request); // Remote transmission request RTR bit
            }
            CanId::Extended(_) => {
                let extended_id_split = self.can_id.split_extended_id()?;

                push_n_bits(&mut input_data, extended_id_split.base_11_id as u32, 11);
                input_data.push(true); // SRR bit, always 1
                input_data.push(true); // Idetifier extension bit (IDE), always 1 for ext frame
                push_n_bits(&mut input_data, extended_id_split.ext_18_id, 18);
                input_data.push(self.is_remote_request); // Remote transmission request RTR bit
            }
        }

        // Control field
        input_data.push(false); // IDE bit OR r1 bit that is always 0
        input_data.push(false); // r0 bit
        push_n_bits(&mut input_data, self.payload.len() as u32, 4); // Data length code

        // Data field
        for byte in &self.payload {
            push_byte(&mut input_data, *byte);
        }

        Ok(input_data)
    }
}
