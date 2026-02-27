use protium::can::{CanId, Frame};

fn main() {
    let can_id = CanId::Standard(0x7EF);
    // 0111111011110001000110001000100001011111111
    // 01111110111100010000110001000100001011111111
    let payload: Vec<u8> = vec![0x3e, 0x4a, 0x42];
    if let Ok(frame) = Frame::new(can_id, payload, false) {
    //     // dbg!(frame);
    //     let x = frame.annotate().unwrap();
        println!("{:#02x}", frame.checksum().unwrap());
    }
}