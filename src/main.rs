use protium::{
    bus::Bus,
    can::{CanId, Frame},
    node::Node,
};
use std::{thread::sleep, time::Duration};

fn main() {
    // global bus nodes will communicate on
    let mut bus = Bus::new(10);

    // example control Modules
    // ecm has highest priority, followed by tcm, then bcm - based on the CanIds alone
    let mut ecm = Node::new(CanId::Standard(0x7E8));
    let mut tcm = Node::new(CanId::Standard(0x7AF));
    let mut bcm = Node::new(CanId::Standard(0x7EF));
    bcm.sleep();

    // example frames to send from ecus
    let engine_oil_temperature = vec![0x22];
    let engine_oil_frame = Frame::new(ecm.id(), engine_oil_temperature, false)
        .expect("failed to create example engine oil frame");
    let trans_fluid_temperature = vec![0x1F];
    let trans_fluid_frame = Frame::new(tcm.id(), trans_fluid_temperature, false)
        .expect("failed to create example transmission oil frame");

    println!("Payload for ECU: {}", engine_oil_frame.encode().unwrap());
    println!("Payload for Trans: {}", trans_fluid_frame.encode().unwrap());

    // prepare nodes to transmit their data when the bus is active
    ecm.queue_transmission(&engine_oil_frame)
        .expect("failed to prepare transmission frame for ECM");
    tcm.queue_transmission(&trans_fluid_frame)
        .expect("failed to prepare transmission frame for TCM");

    // register nodes on bus to send/receive
    bus.register_node(ecm);
    bus.register_node(tcm);
    bus.register_node(bcm);

    // bus ticks
    loop {
        if let Err(e) = bus.tick() {
            println!("Error during bus tick: {e}");
            return;
        }

        if !bus.is_active() {
            break;
        }

        sleep(Duration::from_millis(10)); // example tick speed
    }

    for node in bus.get_nodes().iter() {
        println!(
            "[Node:{}] State: {:?} - Received bits: `{:?}`",
            node.id(),
            node.state(),
            node.received_bits()
        );
    }
}
