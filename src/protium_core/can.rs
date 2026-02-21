use bitvec::prelude::*;

/// Represents a CAN ID
#[derive(Debug, PartialEq, Eq)]
pub enum CanId {
    /// 11-bit standard CAN ID
    Standard(u16),
    /// 29-bit extended CAN ID
    Extended(u32)
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
    pub is_remote_request: bool,
    pub payload: Vec<u8>,
    /// Classical CAN only
    pub checksum: u16, 
}

impl Frame {
    pub fn encode(&self) -> Option<EncodedFrame> {
        None
    }
}

impl EncodedFrame {
    pub fn from_bits(bits: &BitVec<u8, Msb0>) -> Option<Self> {
        None
    }
}
