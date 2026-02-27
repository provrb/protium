use bitvec::prelude::*;
use std::ops::RangeInclusive;
use thiserror::Error;

/// The generator polynomial constant used for CRC-15 (used by CAN) checksum
/// as the divisor to generate a checksum for the provided input data.
///
/// All checksum logic must use this in their checksum process.
const CRC_15_GENERATOR_POLYNOMIAL: u16 = 0b0100010110011001;

/// The position/index of the bit in an encoded CAN Frame bitsream that determines
/// if the CAN Frame is a 29-bit CAN ID frame or 11-bit CAN ID Frame
///
/// The bit index for the IDE  is the same for both 29-bit and 11-bit CAN frames
const IDENTIFIER_EXTENSION_BIT_IDX: usize = 13;

/// Minimum valid size of an unstuffed 11-bit CAN ID frame in bits
/// 44 bits (0 byte data field)
pub const MIN_STANDARD_FRAME_SIZE_BITS: usize = 44;
/// Maximum valid size of an unstuffed 11-bit CAN ID frame in bits
/// 108 bits (8 byte (max for classical CAN) data field)
pub const MAX_STANDARD_FRAME_SIZE_BITS: usize = 108;
/// Range of the valid size an 11-bit standard unstuffed CAN frame can be in bits.
pub const VALID_STANDARD_FRAME_SIZE_BITS: RangeInclusive<usize> =
    MIN_STANDARD_FRAME_SIZE_BITS..=MAX_STANDARD_FRAME_SIZE_BITS;

/// Minimum valid size of an unstuffed extended 29-bit CAN ID frame in bits
/// 64 bits (0 byte data field)
pub const MIN_EXTENDED_FRAME_SIZE_BITS: usize = 64;
/// Maximum valid size of an unstuffed extended 29-bit CAN ID frame in bits
/// 128 bits (8 byte (max for classical CAN) data field
pub const MAX_EXTENDED_FRAME_SIZE_BITS: usize = 128;
/// Range of the valid size a 29-bit extended unstuffed CAN frame can be in bits.
pub const VALID_EXTENDED_FRAME_SIZE_BITS: RangeInclusive<usize> =
    MIN_EXTENDED_FRAME_SIZE_BITS..=MAX_EXTENDED_FRAME_SIZE_BITS;

/// The bits in an 11-bit CAN ID that contain the int that represents the length of the data
const STANDARD_DLC_BIT_RANGE_IDX: RangeInclusive<usize> = 15..=18;
/// The bits in a 29-bit CAN ID that contain the int that represents the length of the data
const EXTENDED_DLC_BIT_RANGE_IDX: RangeInclusive<usize> = 35..=38;

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

impl ExtendedIdSplit {
    pub fn to_bits(&self) -> (BitVec<u16, Msb0>, BitVec<u32, Msb0>) {
        (
            BitVec::<u16, Msb0>::from_element(self.base_11_id).split_off(16 - 11), // trim to fit 11 bit CAN id
            BitVec::<u32, Msb0>::from_element(self.ext_18_id).split_off(32 - 18)
        )
    }
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
                    return Err(ProtiumFrameError::InvalidCANId { provided: *self });
                }
            }
            CanId::Extended(ext_id) => {
                if ext_id > 0x1FFFFFFF {
                    return Err(ProtiumFrameError::InvalidCANId { provided: *self });
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
            _ => Err(ProtiumFrameError::InvalidCANId { provided: *self }),
        }
    }

    pub fn to_bits(&self) -> BitVec<u32, Msb0> {
        const SIZE_OF_U32_BITS: usize = size_of::<u32>() * 8;

        match *self {
            Self::Standard(std_id) => {
                let mut v = BitVec::<u32, Msb0>::from_element(std_id as u32);
                v.split_off(SIZE_OF_U32_BITS - 11) // trim to fit 11 bit CAN id
            }
            Self::Extended(ext_id) => {
                let mut v = BitVec::<u32, Msb0>::from_element(ext_id);
                v.split_off(SIZE_OF_U32_BITS - 29) // trim to fit 29 bit CAN id
            }
        }
    }
}

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct FieldSpan {
    pub start: usize,
    pub len: usize,
}

impl FieldSpan {
    pub fn end(&self) -> usize {
        self.start + self.len
    }
}

/// The CAN data bits that are sent over the wire between nodes.
///
/// This is the most accurate representation of CAN frames
/// sent over the wire compared to the other abstraction types like
/// `AnnotatedFrame` & `Frame`
///
/// The first element (index 0) will always be 0 (dominant bit) for the start of frame (SOF) bit.
pub type WireBits = BitVec<u8, Msb0>;

/// Contains `FieldSpan`'s of each technical field/part of a CAN frame encoded in bits
/// to denote the start and size of each field
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct WireLayout {
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

impl WireLayout {
    ///
    pub fn generate_layout(data_size_bits: usize, extended: bool) -> Self {
        let arbitration_field_size_bits = if extended { 32 } else { 12 };
        let mut layout = WireLayout::default();
        layout.arbitration_field = FieldSpan {
            start: 1,
            len: arbitration_field_size_bits,
        };
        layout.control_field = FieldSpan {
            start: layout.arbitration_field.end(),
            len: 6,
        };
        layout.data_field = FieldSpan {
            start: layout.control_field.end(),
            len: data_size_bits,
        };
        layout.crc_field = FieldSpan {
            start: layout.data_field.end(),
            len: 16,
        };
        layout.acknowledgement_field = FieldSpan {
            start: layout.crc_field.end(),
            len: 2,
        };
        layout.end_of_frame_field = FieldSpan {
            start: layout.acknowledgement_field.end(),
            len: 7,
        };

        let range_to_check = if extended {
            VALID_EXTENDED_FRAME_SIZE_BITS
        } else {
            VALID_STANDARD_FRAME_SIZE_BITS
        };

        debug_assert!(
            range_to_check
                .contains(&(layout.end_of_frame_field.start + layout.end_of_frame_field.len)),
            "eof_start + eof_len is not in valid frame size range. got: {}",
            layout.end_of_frame_field.start + layout.end_of_frame_field.len
        );

        layout
    }
}

/// Represents an Encoded CAN frame. (Unstuffed)
///
/// This struct is compatible with both 11-bit CAN ID frames and
/// 29-bit extended CAN ID frames.
///
/// The encoded message is stored as a bit vector.
/// The frame includes a layout including field spans that detail where a
/// component of the message starts and it's size. For example,
/// the data field. `data_field` contains the index in `bits` where it starts at, and the size of
/// the field.
#[derive(Debug)]
pub struct AnnotatedFrame {
    /// The fields in bits follow the order the same as they're defined in `WireLayout`:
    /// 
    /// 1. Arbitration field 
    /// 2. Control Field 
    /// 3. Data Field 
    /// 4. CRC 
    /// 5. ACK field 
    /// 6. EOF
    bits: WireBits,
    layout: WireLayout,
}

impl AnnotatedFrame {
    pub fn new(bits: WireBits) -> Result<Self, ProtiumFrameError> {
        // unstuffed | for 11 bit can id frame length:
        // SOF bit. | 11 BIT ID. | RTR BIT. | IDE BIT. | R0 BIT. | DLC (4 BITS). |
        // DATA FIELD (0-8 BYTES). | CRC (16 BITS). | ACK FIELD (2 BITS). | EOF FIELD (7 BITS).
        // 44 bits (when data field is 0 bytes)
        // 44 bits + 8 bytes = 44 bits + 64 bits = 108 bits (when data field is 8 bytes)
        // therefore a valid 11 bit CAN ID Frame would be between 44-108 bits

        // unstuffed | for 29 bit can id frame length:
        // SOF BIT | 11 BIT ID | SRR BIT | IDE BIT | 18 BIT ID | RTR BIT | R1 BIT |
        // R0 BIT | DLC (4 BITS) | DATA FIELD (0-8 BYTES) | CRC (16 BITS) | ACK FIELD (2 BITS) | EOF FIELD (7 BITS)
        // 64 bits (when data field is 0 bytes)
        // 64 bits + 8 bytes = 64 bits + 64 bits = 128 bits (when data field is 8 bytes)
        // therefore, a 29 bit can id frame has a min length of 64 bits and a max length of 128

        let bit_len = bits.len();
        let mut frame = Self {
            bits,
            layout: WireLayout::default(),
        };

        // validate size of frame
        if frame.is_extended() {
            if !VALID_EXTENDED_FRAME_SIZE_BITS.contains(&bit_len) {
                return Err(ProtiumFrameError::InvalidFrameLength {
                    provided: bit_len,
                    expected: VALID_EXTENDED_FRAME_SIZE_BITS,
                });
            }
        } else if !VALID_STANDARD_FRAME_SIZE_BITS.contains(&bit_len) {
            return Err(ProtiumFrameError::InvalidFrameLength {
                provided: bit_len,
                expected: VALID_STANDARD_FRAME_SIZE_BITS,
            });
        }

        // check if sof bit is 0 (false)
        // bits[0] is the SOF bit which must always be 0 (false)
        if let Some(sof_bit) = frame.bits.get(0) {
            if sof_bit != false {
                // we could set it here instead of throwing an error but
                // if its not already set its safe to assume that there
                // is a flaw in the logic that encoded these bits, so return an error
                return Err(ProtiumFrameError::InvalidStartOfFrameBit);
            }
        }

        frame.layout =
            WireLayout::generate_layout(frame.data_length() as usize, frame.is_extended());

        // expected frame bit length != calculated frame bit length
        if bit_len != frame.layout.end_of_frame_field.end() {
            return Err(ProtiumFrameError::InvalidFrameLength {
                provided: bit_len,
                expected: frame.layout.end_of_frame_field.end()
                    ..=frame.layout.end_of_frame_field.end(),
            });
        }

        Ok(frame)
    }

    /// Check if the current frame is an extended 29-bit CAN ID frame
    ///
    /// Checks if the Identifier Extension Bit is set to 1
    pub fn is_extended(&self) -> bool {
        match self.bits.get(IDENTIFIER_EXTENSION_BIT_IDX) {
            Some(ide_bit) => ide_bit == true,
            None => false,
        }
    }

    /// Get the length of the data field in bits
    ///
    /// Read the 4-bit long Data Length Code (DLC) in the CAN frame bits
    /// and convert it to a u16 to get the length of the data in bytes,
    /// finally, convert the read value into bits.
    pub fn data_length(&self) -> u16 {
        let dlc_bit_range = if self.is_extended() {
            EXTENDED_DLC_BIT_RANGE_IDX
        } else {
            STANDARD_DLC_BIT_RANGE_IDX
        };

        match self.bits.get(dlc_bit_range) {
            Some(dlc_bits) => dlc_bits.load_be::<u16>() * 8, // (convert bytes to bits)
            None => 0,
        }
    }

    pub fn wire_bits(&self) -> &WireBits {
        &self.bits
    }

    pub fn bit_layout(&self) -> &WireLayout {
        &self.layout
    }

    pub fn get_bit_field(&self, field_data: &FieldSpan) -> &BitSlice<u8, Msb0> {
        let start_idx = field_data.start;
        let end_idx = field_data.end();

        match self.wire_bits().get(start_idx..end_idx) {
            Some(bits) => bits,
            None => BitSlice::empty()
        }
    }
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
#[derive(Debug, Error)]
pub enum ProtiumFrameError {
    #[error("CAN id is invalid. got `{provided:?}`")]
    InvalidCANId { provided: CanId },
    /// The first element in all `WireBits` must be 0
    /// to indicate the start of the frame
    #[error("start of frame bit is invalid. SOF bit must always be '0' (false)")]
    InvalidStartOfFrameBit,
    #[error("frame length is invalid. got `{provided}` bits but expected range `{expected:?}`")]
    InvalidFrameLength {
        provided: usize,
        expected: RangeInclusive<usize>,
    },
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

    pub fn is_extended(&self) -> bool {
        match self.can_id {
            CanId::Standard(_) => false,
            CanId::Extended(_) => true,
        }
    }

    pub fn annotate(&self) -> Result<AnnotatedFrame, ProtiumFrameError> {
        let capacity = if self.is_extended() {
            MAX_EXTENDED_FRAME_SIZE_BITS
        } else {
            MAX_STANDARD_FRAME_SIZE_BITS
        };

        let mut bitstream = BitVec::<u8, Msb0>::with_capacity(capacity);
        bitstream.push(false); // SOF bit

        // arbitration field
        if self.is_extended() {
            // 11 BIT ID. SRR. IDE. 18 BIT ID. RTR
            let can_id = self.can_id.split_extended_id()?;
            let (std_can_id_bits, ext_can_id_bits) = can_id.to_bits();
            
            // 11 bit CAN id
            for bit in std_can_id_bits {
                bitstream.push(bit);
            }

            bitstream.push(true); // SRR bit - always 1
            bitstream.push(true); // IDE bit - 1 because this is an extended frame
            
            // 18 bit CAN ID
            for bit in ext_can_id_bits {
                bitstream.push(bit);
            }
            bitstream.push(self.is_remote_request); // RTR bit
        } else {
            // 11 BIT ID. RTR
            let std_can_id_bits = self.can_id.to_bits();
            for bit in std_can_id_bits {
                bitstream.push(bit);
            }

            bitstream.push(self.is_remote_request); // RTR bit
        }
        
        // control field
        // IDE bit for non-extended frames (which is always false) or r0 bit (which is also always false) for extended frames
        bitstream.push(false);
        bitstream.push(false); // r1 bit (always 0)
        // data length code
        let dlc: BitVec<usize, Msb0> = BitVec::from_element(self.payload.len()).split_off(
            (size_of::<usize>() * 8) - 4
        );
        for bit in dlc.clone() {
            bitstream.push(bit);
        }

        // data field
        let bit_payload = BitVec::<u8, Msb0>::from_vec(self.payload.clone());
        for bit in bit_payload {
            bitstream.push(bit);
        }

        // dbg!("{:?}", size_of::<usize>());
        // dbg!("dlc: {:?}", dlc);

        // CRC field
        let checksum = self.checksum()?;
        // dbg!("checksum: {#02b}", checksum);
        let checksum_bits: BitVec<u16, Msb0> = BitVec::from_element(checksum).split_off(16 - 15);
        for bit in checksum_bits {
            bitstream.push(bit);
        }
        bitstream.push(true); // CRC delimeter - comes after checksum bits

        // ACK field
        bitstream.push(true); // ack slot. transmitter sets to 1
        bitstream.push(true); // ack delimeter - always 1

        // end of frame field. add 7 recessive bits at the end of the frame
        for _ in 0..7 {
            bitstream.push(true);
        }

        // println!("[Frame::annotate()] bit stream is {:?}", bitstream);
        AnnotatedFrame::new(bitstream)
    }

    pub fn checksum(&self) -> Result<u16, ProtiumFrameError> {
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

        push_n_bits(&mut input_data, 0, 15);

        // println!("[checksum] input stream: {}", input_data);

        Ok(input_data)
    }
}
