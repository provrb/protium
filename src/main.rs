use bitvec::vec::BitVec;
use protium::{
    can::{AnnotatedFrame, CanId, Frame},
    node::Node,
};

fn main() {
    let can_id = CanId::Standard(0x7EF);
    // 0111111011110001000110001000100001011111111
    // 01111110111100010000110001000100001011111111
    let payload: Vec<u8> = "hello".as_bytes().to_vec();
    if let Ok(frame) = Frame::new(can_id, payload, false) {
        //     // dbg!(frame);
        //     let x = frame.annotate().unwrap();
        // println!("{:#02x}", frame.checksum().unwrap());
        let inp = BitVec::from_vec("hello".as_bytes().to_vec());
        let checksum = Frame::checksum_with_input(&inp).unwrap();
        println!("checksum: {:#02x}", checksum);

        let wire_bits = Node::encode(&frame).unwrap();
        println!("{}", wire_bits);
        let annotated = AnnotatedFrame::new(wire_bits).unwrap();
        let layout = annotated.bit_layout();
        println!("annotated bit stream: `{}`", annotated.wire_bits());

        println!(
            "[annotated] arbitration field: `{}`",
            annotated.get_bit_field(&layout.arbitration_field)
        );
        println!(
            "[annotated] control field: `{}`",
            annotated.get_bit_field(&layout.control_field)
        );
        println!(
            "[annotated] data field: `{}`",
            annotated.get_bit_field(&layout.data_field)
        );
        println!(
            "[annotated] ACK field: `{}`",
            annotated.get_bit_field(&layout.acknowledgement_field)
        );
        println!(
            "[annotated] CRC field: `{}`",
            annotated.get_bit_field(&layout.crc_field)
        );
        println!(
            "[annotated] EOF field: `{}`",
            annotated.get_bit_field(&layout.end_of_frame_field)
        );
    }
}
