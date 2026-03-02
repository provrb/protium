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

    let frame = Frame::new(
        TCM_NODE_ID,
        "Hello from the TCM!".as_bytes().to_vec(),
        false,
    )
    .unwrap();
    tcm.transmit(frame).unwrap();

    bus.register_node(ecu);
    bus.register_node(tcm);

    while bus.tick() {
        sleep(Duration::from_millis(10));
    }

    dbg!(bus.get_node(TCM_NODE_ID));
    dbg!(bus.get_node(ECU_NODE_ID));
}
