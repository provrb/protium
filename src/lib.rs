mod logging;
/// Modules
mod protium_core;

/// Imports
pub use protium_core::*;

/// Unit tests
#[cfg(test)]
mod tests {
    use crate::{bit_destuff, bit_stuff, bus::Bus, node::Node};

    use super::protium_core::can::*;
    use bitvec::{bitvec, order::Msb0, vec::BitVec};

    fn expected_bits(can_id: CanId, payload: Vec<u8>) -> BitVec<u8, Msb0> {
        let frame = Frame::new(can_id, payload, false).unwrap();
        let mut bits = frame.encode().unwrap();
        let layout = WireLayout::generate_layout(frame.data_length_bits(), frame.is_extended());
        bits.set(layout.acknowledgement_field.start, false);
        bits
    }

    // CRC-15 CAN checksum computation test
    #[test]
    fn checksum() -> Result<(), String> {
        const EXPECTED_CHECKSUM_RESULT: u16 = 0x7bf1;

        let inp = BitVec::from_vec("hello".as_bytes().to_vec());
        let calculated_checksum = Frame::checksum_with_input(&inp);
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
        let mut tcm = Node::new(tcm_id);

        let engine_oil_temperature = vec![0x22];
        let engine_oil_frame = Frame::new(ecm.id(), engine_oil_temperature, false)
            .expect("failed to create example engine oil frame");

        // prepare nodes to transmit their data when the bus is active
        ecm.queue_transmission(&engine_oil_frame)
            .expect("failed to prepare transmission frame for ECM");
        ecm.set_on_complete_receive_callback(|can_id, bits| {
            let engine_oil_temperature = vec![0x22];
            let engine_oil_frame = Frame::new(can_id, engine_oil_temperature, false)
                .expect("failed to create example engine oil frame");
            let expected_received_bits: BitVec<u8, Msb0> = engine_oil_frame.encode().unwrap();

            assert_eq!(bits.len(), expected_received_bits.len());
        });

        tcm.set_on_complete_receive_callback(|_, bits| {
            let engine_oil_temperature = vec![0x22];
            let engine_oil_frame =
                Frame::new(CanId::Standard(0x7E8), engine_oil_temperature, false)
                    .expect("failed to create example engine oil frame");
            let expected_received_bits: BitVec<u8, Msb0> = engine_oil_frame.encode().unwrap();

            assert_eq!(bits.len(), expected_received_bits.len());
        });

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

    #[test]
    fn nodes_send_and_receive_extended() {
        let mut bus = Bus::new(10);

        let ecm_id = CanId::Standard(0x7E8);
        let tcm_id = CanId::Extended(0x0CF00500);

        let mut ecm = Node::new(ecm_id);
        let mut tcm = Node::new(tcm_id);

        let frame =
            Frame::new(tcm.id(), vec![0x22], false).expect("failed to create extended frame");

        tcm.queue_transmission(&frame)
            .expect("failed to queue extended frame transmission");

        ecm.set_on_complete_receive_callback(|_, bits| {
            let expected = expected_bits(CanId::Extended(0x0CF00500), vec![0x22]);
            assert_eq!(
                bits.len(),
                expected.len(),
                "ecm received wrong number of bits from extended frame"
            );
            assert_eq!(
                *bits, expected,
                "ecm received bits do not match expected extended frame"
            );
        });

        tcm.set_on_complete_receive_callback(|_, bits| {
            let expected = expected_bits(CanId::Extended(0x0CF00500), vec![0x22]);
            assert_eq!(
                bits.len(),
                expected.len(),
                "tcm received wrong number of bits from extended frame"
            );
            assert_eq!(
                *bits, expected,
                "tcm received bits do not match expected extended frame"
            );
        });

        bus.register_node(ecm);
        bus.register_node(tcm);

        loop {
            bus.tick().unwrap();
            if !bus.is_active() {
                break;
            }
        }
    }

    #[test]
    fn nodes_send_and_receive_extended_max_payload() {
        let mut bus = Bus::new(10);

        let ecm_id = CanId::Standard(0x7E8);
        let tcm_id = CanId::Extended(0x0CF00500);

        let mut ecm = Node::new(ecm_id);
        let mut tcm = Node::new(tcm_id);

        let payload = vec![0xDE, 0xAD, 0xBE, 0xEF, 0x01, 0x02, 0x03, 0x04];
        let frame = Frame::new(tcm.id(), payload.clone(), false)
            .expect("failed to create extended frame with max payload");

        tcm.queue_transmission(&frame)
            .expect("failed to queue extended frame transmission");

        ecm.set_on_complete_receive_callback(|_, bits| {
            let expected = expected_bits(
                CanId::Extended(0x0CF00500),
                vec![0xDE, 0xAD, 0xBE, 0xEF, 0x01, 0x02, 0x03, 0x04],
            );

            assert_eq!(
                bits.len(),
                expected.len(),
                "received wrong bit count for max payload extended frame"
            );
            assert_eq!(
                *bits, expected,
                "received bits do not match expected max payload extended frame"
            );
        });

        bus.register_node(ecm);
        bus.register_node(tcm);

        loop {
            bus.tick().unwrap();
            if !bus.is_active() {
                break;
            }
        }
    }

    #[test]
    fn nodes_send_and_receive_extended_empty_payload() {
        let mut bus = Bus::new(10);

        let ecm_id = CanId::Standard(0x7E8);
        let tcm_id = CanId::Extended(0x0CF00500);

        let mut ecm = Node::new(ecm_id);
        let mut tcm = Node::new(tcm_id);

        let frame = Frame::new(tcm.id(), vec![], false)
            .expect("failed to create extended frame with empty payload");

        tcm.queue_transmission(&frame)
            .expect("failed to queue extended frame transmission");

        ecm.set_on_complete_receive_callback(|_, bits| {
            let expected = expected_bits(CanId::Extended(0x0CF00500), vec![]);

            assert_eq!(
                bits.len(),
                expected.len(),
                "received wrong bit count for empty payload extended frame"
            );
            assert_eq!(
                *bits, expected,
                "received bits do not match expected empty payload extended frame"
            );
        });

        bus.register_node(ecm);
        bus.register_node(tcm);

        loop {
            bus.tick().unwrap();
            if !bus.is_active() {
                break;
            }
        }
    }

    #[test]
    fn nodes_priority_transmission_extended_vs_standard() {
        let mut bus = Bus::new(10);

        // Standard 0x7E8 = 0b11111101000 — lots of recessive bits, lower priority
        // Extended 0x0CF00500 starts with 0b00001100 — more dominant bits, higher priority
        let ecm_id = CanId::Standard(0x7E8);
        let tcm_id = CanId::Extended(0x0CF00500);

        let mut ecm = Node::new(ecm_id);
        let mut tcm = Node::new(tcm_id);

        let ecm_frame = Frame::new(ecm.id(), vec![0x22], false).unwrap();
        let tcm_frame = Frame::new(tcm.id(), vec![0x22], false).unwrap();

        ecm.queue_transmission(&ecm_frame).unwrap();
        tcm.queue_transmission(&tcm_frame).unwrap();

        bus.register_node(ecm);
        bus.register_node(tcm);

        let mut ecm_queued_retransmit = false;
        loop {
            bus.tick().unwrap();

            if bus.get_node(ecm_id).unwrap().pending_retransmission() {
                ecm_queued_retransmit = true;
                break;
            }

            if !bus.is_active() {
                break;
            }
        }

        assert!(
        ecm_queued_retransmit,
        "ecm (standard) should have lost arbitration to tcm (extended) but did not queue retransmission"
    );
    }
}
