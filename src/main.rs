use std::{thread::sleep, time::Duration};

use bitvec::{bitvec, order::Msb0};
use protium::{bus::Bus, can::{CanId, Frame, bit_destuff, bit_stuff}, node::Node};

fn main() {
    let mut bus = Bus::new(10);
    let mut ecm = Node::new(CanId::Standard(0x7e8));
    let mut tcm = Node::new(CanId::Extended(0x0CF00500));

    let ecm_frame =
        Frame::new(ecm.id(), vec![0x22], false).expect("failed to create example ecm frame");

    println!("{:?}", &ecm_frame.encode());

    // prepare nodes to transmit their data when the bus is active
    ecm.queue_transmission(&ecm_frame)
        .expect("failed to prepare transmission frame for ECM");

    // tcm.set_on_complete_receive_callback(|node_id, received_bits| {
    //     println!("[Node:{}] Received bits: {:?}", node_id, received_bits)
    // });

    // register nodes on bus to send/receive
    bus.register_node(ecm);
    bus.register_node(tcm);

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

    // for node in bus.get_nodes().iter() {
    //     println!(
    //         "[Node:{}] State: {:?} - Received bits: `{:?}`",
    //         node.id(),
    //         node.state(),
    //         node.last_received_bits()
    //     );
    // }
}
