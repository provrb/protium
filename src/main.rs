use protium::can::{CanId, Frame};

fn main() {
    let can_id = CanId::Standard(0x7EF);
    let payload = vec![0x65, 0x6c, 0x6c, 0x6f];
    if let Ok(frame) = Frame::new(can_id, payload, false) {
        dbg!(frame);
    }
}
