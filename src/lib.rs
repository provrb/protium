/// Modules
mod protium_core;

/// Imports
pub use protium_core::*;

/// Unit tests
#[cfg(test)]
mod tests {
    use super::protium_core::can::*;
    use bitvec::{bitvec, order::Msb0, vec::BitVec};

    #[test]
    fn checksum() -> Result<(), String> {
        const EXPECTED_CHECKSUM_RESULT: u16 = 0x7bf1;

        let inp = BitVec::from_vec("hello".as_bytes().to_vec());
        let calculated_checksum = Frame::checksum_with_input(&inp).unwrap();
        if calculated_checksum != EXPECTED_CHECKSUM_RESULT {
            Err(format!(
                "wrong checksum result for frame - expected: `{:#02x}` received: `{:#02x}`",
                EXPECTED_CHECKSUM_RESULT, calculated_checksum
            ))
        } else {
            Ok(())
        }
    }

    #[test]
    fn annotated_frame_length() {
        assert!(
            AnnotatedFrame::new(bitvec![u8, Msb0; 1, 0, 1, 0]).is_err(),
            "annotated frame length is invalid but was not detected as such"
        );
    }

    #[test]
    fn annotated_frame_extended() {
        let mut bv = bitvec![u8, Msb0;];
        bv.extend([false; 44].iter());
    }

    #[test]
    fn annotated_frame_std_empty() -> Result<(), ProtiumFrameError> {
        // standard frames are 44 bits with no data
        // this should pass
        let mut bv = bitvec![u8, Msb0;];
        bv.extend([false; 44].iter());

        AnnotatedFrame::new(bv).map(|_| {})
    }

    #[test]
    fn annotated_frame_std_too_big() {
        // standard frames are 44 bits with no data
        // this should pass
        let mut bv = bitvec![u8, Msb0;];
        bv.extend([false; 110].iter());

        assert!(
            AnnotatedFrame::new(bv).is_err(),
            "annotated frame length is too big but was not detected as such"
        );
    }

    #[test]
    fn annotated_frame_std_dynamic_size() {
        let mut bv = bitvec![u8, Msb0;];
        bv.extend([false; 108].iter());

        // 1000 - 8 bytes
        bv.set(15, true);
        bv.set(16, false);
        bv.set(17, false);
        bv.set(18, false);

        assert!(
            AnnotatedFrame::new(bv).is_ok(),
            "gave dlc of 8 bytes (64 bits) and frame detected and sized itself incorrectly"
        );
    }
}
