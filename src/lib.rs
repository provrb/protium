/// Modules
mod protium_core;

/// Imports
pub use protium_core::*;

/// Unit tests
#[cfg(test)]
mod tests {
    use crate::{bus::Bus, node::Node};

    use super::protium_core::can::*;
    use bitvec::{bitarr, bits, bitvec, order::Msb0, slice::BitSlice, vec::BitVec};

    // CRC-15 CAN checksum computation test
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

    // Encoded frame logic tests

    #[test]
    fn encoded_frame_length() {
        assert!(
            EncodedFrame::new(bitvec![u8, Msb0; 1, 0, 1, 0]).is_err(),
            "annotated frame length is invalid but was not detected as such"
        );
    }

    #[test]
    fn encoded_frame_extended() {
        let mut bv = bitvec![u8, Msb0;];
        bv.extend([false; 44].iter());
    }

    #[test]
    fn encoded_frame_std_empty() -> Result<(), ProtiumFrameError> {
        // standard frames are 44 bits with no data
        // this should pass
        let mut bv = bitvec![u8, Msb0;];
        bv.extend([false; 44].iter());

        EncodedFrame::new(bv).map(|_| {})
    }

    #[test]
    fn encoded_frame_std_too_big() {
        // standard frames are 44 bits with no data
        // this should pass
        let mut bv = bitvec![u8, Msb0;];
        bv.extend([false; 110].iter());

        assert!(
            EncodedFrame::new(bv).is_err(),
            "annotated frame length is too big but was not detected as such"
        );
    }

    #[test]
    fn encoded_frame_std_dynamic_size() {
        let mut bv = bitvec![u8, Msb0;];
        bv.extend([false; 108].iter());

        // 1000 - 8 bytes
        bv.set(15, true);
        bv.set(16, false);
        bv.set(17, false);
        bv.set(18, false);

        assert!(
            EncodedFrame::new(bv).is_ok(),
            "gave dlc of 8 bytes (64 bits) and frame detected and sized itself incorrectly"
        );
    }

    // Node transmission and receiving tests on a bus

    #[test]
    /// One node transmits and another receives.
    /// Both nodes should have the transitted data in their received bitstream.
    /// If they dont then something is wrong. The process of sending and receiving
    /// also should not throw any errors.
    fn nodes_send_and_receive() {
        let mut bus = Bus::new(10);

        // ids
        let ecm_id = CanId::Standard(0x7E8);
        let tcm_id = CanId::Standard(0x7EA);

        let mut ecm = Node::new(ecm_id);
        let tcm = Node::new(tcm_id);

        let engine_oil_temperature = vec![0x22];
        let engine_oil_frame = Frame::new(ecm.id(), engine_oil_temperature, false)
            .expect("failed to create example engine oil frame");

        // prepare nodes to transmit their data when the bus is active
        ecm.queue_transmission(&engine_oil_frame)
            .expect("failed to prepare transmission frame for ECM");

        // register nodes on bus to send/receive
        bus.register_node(ecm);
        bus.register_node(tcm);

        // bus ticks
        loop {
            bus.tick().unwrap();

            if !bus.is_active() {
                break;
            }
        }

        // check if both modules have received the message sent by tcm
        let expected_received_bits = engine_oil_frame.encode().unwrap();
        assert_eq!(
            bus.get_node(ecm_id)
                .unwrap()
                .last_received_bits()
                .unwrap()
                .len(),
            expected_received_bits.len(),
        );

        assert_eq!(
            bus.get_node(tcm_id)
                .unwrap()
                .last_received_bits()
                .unwrap()
                .len(),
            expected_received_bits.len(),
        );
    }

    #[test]
    fn nodes_priority_transmission() {
        let mut bus = Bus::new(10);

        // ids
        let ecm_id = CanId::Standard(0x7E8);
        let tcm_id = CanId::Standard(0x7EA);

        // modules
        let mut ecm = Node::new(ecm_id);
        let mut tcm = Node::new(tcm_id);

        // frames
        let ecm_frame =
            Frame::new(ecm.id(), vec![0x22], false).expect("failed to create example ecm frame");
        let tcm_frame =
            Frame::new(tcm_id, vec![0x82], false).expect("failed to create example tcm frame");

        // queue both nodes for transmission
        // because ecm has the more amount of dominant bits in its CAN id (0x7E8 | 0b11111101000)
        // it should be the node transmitting the data.
        // then tcm should queue the lost frame for retransmission.
        ecm.queue_transmission(&ecm_frame)
            .expect("failed to prepare transmission frame for ECM");
        tcm.queue_transmission(&tcm_frame)
            .expect("failed to prepare transmission frame for TCM");

        // register nodes on bus to send/receive
        bus.register_node(ecm);
        bus.register_node(tcm);

        // bus ticks
        let mut successfully_queued_retransmission = false;
        loop {
            bus.tick().unwrap();

            if bus.get_node(tcm_id).unwrap().pending_retransmission() {
                successfully_queued_retransmission = true;
                break;
            }

            if !bus.is_active() {
                break;
            }
        }

        assert!(
            successfully_queued_retransmission,
            "node did not queue transmission for frame after it lost arbitration"
        );
    }

    #[test]
    fn bit_stuffing() {
        assert_eq!(
            bit_stuff(&bitvec![u8, Msb0; 1,1,1,1,1]),
            bitvec![u32, Msb0; 1,1,1,1,1,0]
        );
        assert_eq!(
            bit_stuff(&bitvec![u8, Msb0; 0,0,0,0,0,1]),
            bitvec![u32, Msb0; 0,0,0,0,0,1,1]
        );
        assert_eq!(
            bit_stuff(&bitvec![u8, Msb0; 1,1,1,1,1,1]),
            bitvec![u32, Msb0; 1,1,1,1,1,0,1]
        );
        assert_eq!(
            bit_stuff(&bitvec![u8, Msb0; 1,1,1,1,1,1,1]),
            bitvec![u32, Msb0; 1,1,1,1,1,0,1,1]
        );
        assert_eq!(
            bit_stuff(&bitvec![u8, Msb0; 1,1,1,1,1,0,0]),
            bitvec![u32, Msb0; 1,1,1,1,1,0,0,0]
        );
        assert_eq!(
            bit_stuff(&bitvec![u8, Msb0; 0,0,0,0,0,1,1]),
            bitvec![u32, Msb0; 0,0,0,0,0,1,1,1]
        );
        assert_eq!(
            bit_stuff(&bitvec![u8, Msb0; 1,0,1,1,1,1,1,0]),
            bitvec![u32, Msb0; 1,0,1,1,1,1,1,0,0]
        );
        assert_eq!(
            bit_stuff(&bitvec![u8, Msb0; 0,1,0,0,0,0,0,1]),
            bitvec![u32, Msb0; 0,1,0,0,0,0,0,1,1]
        );
        assert_eq!(
            bit_stuff(&bitvec![u8, Msb0; 1,1,1,1,1,0,1,1,1,1,1]),
            bitvec![u32, Msb0; 1,1,1,1,1,0,0,1,1,1,1,1,0]
        );
        assert_eq!(
            bit_stuff(&bitvec![u8, Msb0; 1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]),
            bitvec![u32, Msb0; 1,1,1,1,1,0,1,1,1,1,1,0,1,1,1,1,1,0,1,1,1,1,1,0]
        );
    }

    #[test]
    fn bit_destuffing() {
        assert_eq!(
            bit_destuff(&bitvec![u8, Msb0; 1,1,1,1,1,0]),
            bitvec![u32, Msb0; 1,1,1,1,1]
        );
        assert_eq!(
            bit_destuff(&bitvec![u8, Msb0; 0,0,0,0,0,1,1]),
            bitvec![u32, Msb0; 0,0,0,0,0,1]
        );
        assert_eq!(
            bit_destuff(&bitvec![u8, Msb0; 1,1,1,1,1,0,1,1]),
            bitvec![u32, Msb0; 1,1,1,1,1,1,1]
        );
        assert_eq!(
            bit_destuff(&bitvec![u8, Msb0; 1,1,1,1,1,0,1,1,1,1,1,0,1,1,1,1,1,0,1,1,1,1,1,0]),
            bitvec![u32, Msb0; 1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
        );
    }
}
