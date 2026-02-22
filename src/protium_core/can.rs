use bitvec::prelude::*;

/// The generator polynomial constant used for CRC checksum 
/// as the divisor to generate a checksum for the provided input data.
/// 
/// All checksum logic must use this in their checksum process.
pub const CRC_15_GENERATOR_POLYNOMIAL: u16 = 0b0100010110011001;

/// Represents a CAN ID
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum CanId {
    /// 11-bit standard CAN ID
    Standard(u16),
    /// 29-bit extended CAN ID
    /// consists of 11-bit base id combined with an 18-bit extended id
    Extended(u32),
    /// Contains the 11-bit and 18-bit IDs used
    /// to create a 29-bit extended CAN ID
    ExtendedSplit(u16, u32)
}

impl CanId {
    pub fn split_extended_id(&self) -> Result<CanId, ()> {
        match *self {
            Self::Extended(id) => {
                let base_11: u16 = ((id >> 18) & 0x7FF) as u16; // bits 28..18
                let ext_18: u32 = id & 0x3FFFF;                 // bits 17..0

                Ok(Self::ExtendedSplit(base_11, ext_18))
            },
            _ => Err(())
        }
    }
}

impl Default for CanId {
    fn default() -> Self {
        CanId::Standard(0)
    }
}

#[derive(Debug)]
pub struct FieldSpan {
    pub start: usize,
    pub len: usize,
}

impl FieldSpan {
    pub fn end(&self) -> usize {
        self.start + self.len
    }
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
    pub end_of_frame_field: FieldSpan, // 7 recessive (1) bits at the end of the frame
}

/// Represents a human friendly CAN frame.
/// 
/// Rather than just being bits, this struct seperates parts of a CAN
/// frame into accessible fields. Recessive and dominant bits like the ACK slot,
/// SOF delimeter, and unnecessary things like the IDE are not included in this struct
/// and are only present in EncodedFrame's.
#[derive(Debug)]
pub struct Frame {
    pub can_id: CanId,
    pub arbitration_field: ArbitrationField,
    pub payload: Vec<u8>,
    /// Classical CAN only
    pub checksum: u16, 
}

#[derive(Debug, Default)]
pub struct ArbitrationField {
    standard_can_id: CanId,
    rtr_bit: bool,

    srr_bit: Option<bool>,
    extended_can_id: Option<CanId>,
    ide_bit: Option<bool>,
}

#[derive(Debug)]
pub enum FrameError {
    InvalidChecksum,
    InvalidCANId,
}

impl Frame {
    pub fn new(
        can_id: CanId,
        is_remote_request: bool,
        payload: Vec<u8>,
    ) -> Result<Self, FrameError> {
        let mut frame = Frame {
            can_id: can_id,
            arbitration_field: ArbitrationField::default(),
            payload: payload,
            checksum: 0
        };

        match can_id {
            CanId::Standard(_) => {
                frame.arbitration_field = ArbitrationField { 
                    standard_can_id: can_id, 
                    rtr_bit: is_remote_request,
                    srr_bit: None, 
                    extended_can_id: None, 
                    ide_bit: None
                }
            },
            CanId::Extended(_) => {
                let CanId::ExtendedSplit(
                    base_11_id, 
                    ext_18_id
                ) = can_id.split_extended_id().map_err(|_| FrameError::InvalidCANId)? else {
                    unreachable!()
                };
                
                frame.arbitration_field = ArbitrationField { 
                    standard_can_id: CanId::Standard(base_11_id), 
                    rtr_bit: is_remote_request,
                    srr_bit: Some(true), 
                    extended_can_id: Some(CanId::Extended(ext_18_id)), 
                    ide_bit: Some(true)
                }
            },
            _ => return Err(FrameError::InvalidCANId)
        };

        Ok(frame)
    }

    pub fn get_arbitration_field(&self) {
        todo!()
    }

    pub fn generate_checksum(&mut self) {
        // checksum = input data (as a binary stream) % generator constant
        // input data = SOF | Arbitration field | Control field | Data field

        let input_data = BitVec::<u8, Msb0>::from_slice(
           &self.payload
        );

        // append 15 zero bits

    }

    pub fn encode(&self) -> Option<EncodedFrame> {
        None
    }
}

impl EncodedFrame {
    pub fn from_bits(bits: &BitVec<u8, Msb0>) -> Option<Self> {
        None
    }
}
