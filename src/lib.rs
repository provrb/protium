/// Modules
mod protium_core;

/// Imports
pub use protium_core::*;

/// Unit tests
#[cfg(test)]
mod tests {
    use super::protium_core::can::*;

    #[test]
    fn checksum() -> Result<(), String> {
        const EXPECTED_CHECKSUM_RESULT: u16 = 0x342f;

        let can_id = CanId::Standard(0x7EF);
        let payload = vec![0x6c, 0x6c, 0x6f];
        let Ok(frame) = Frame::new(can_id, payload.clone(), false) else {
            panic!(
                "failed to create frame - can_id: `{can_id:?}` | payload: `{:?}`",
                &payload
            )
        };

        let calculated_checksum = frame.calculate_checksum().unwrap_or(0);
        if calculated_checksum != EXPECTED_CHECKSUM_RESULT {
            Err(format!(
                "wrong checksum result for frame - expected: `{:#02x}` received: `{:#02x}`",
                EXPECTED_CHECKSUM_RESULT, calculated_checksum
            ))
        } else {
            Ok(())
        }
    }
}
