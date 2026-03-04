use std::{thread::sleep, time::Duration};

use protium::{
    bus::Bus,
    can::{CanId, Frame},
    node::Node,
};

const TCM_NODE_ID: CanId = CanId::Standard(0x7EF);
const ECU_NODE_ID: CanId = CanId::Standard(0x7E8);

fn main() {
    let mut bus = Bus::new(10);

    let mut tcm = Node::new(TCM_NODE_ID);
    let ecu = Node::new(ECU_NODE_ID);

    let frame = Frame::new(TCM_NODE_ID, r"TC".as_bytes().to_vec(), false).unwrap();

    println!(
        "TCM Node wants to send payload: {:#?} with len: {} - {}",
        &frame.data(),
        &frame.data_length(),
        frame.is_extended()
    );

    tcm.prepare_transmission(&frame).unwrap();
    dbg!(&tcm);
    

    bus.register_node(ecu);
    bus.register_node(tcm);

    let mut tick_count = 0;
    while tick_count < 200 {
        bus.tick();
        tick_count+=1;
        sleep(Duration::from_millis(10));
    }

    println!("{:?}", bus.get_node(ECU_NODE_ID).unwrap());
}
