use std::{thread::sleep, time::Duration};
use protium::{bus::Bus, can::{CanId, Frame}, node::Node};

/// This example demonstrates a bus with two nodes registered
/// One node will transmit data over the bus to all nodes on the bus

fn main() {
    // Initialize Bus
    let mut bus = Bus::new(10);

    // Create two nodes
    let mut ecm = Node::new(CanId::Standard(0x7e8));
    let mut tcm = Node::new(CanId::Extended(0x0CF00500));

    // ECM will send this example data
    let ecm_frame =
        Frame::new(ecm.id(), vec![0x22], false).expect("failed to create example ecm frame");

    // Set the ECM node is an a transmitting state telling it what to send
    ecm.queue_transmission(&ecm_frame)
        .expect("failed to prepare transmission frame for ECM");

    // Example of using a node's received callback function
    // When the TCM fully receives a frame it will call this
    tcm.set_on_complete_receive_callback(|node_id, received_bits| {
        println!("[Node:{}] Received bits: {:?}", node_id, received_bits)
    });

    // Register all nodes on bus to send/receive
    bus.register_node(ecm);
    bus.register_node(tcm);

    // Bus tick
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

    // Print all received bits for all nodes
    for node in bus.get_nodes().iter() {
        println!(
            "[Node:{}] State: {:?} - Received bits: `{:?}`",
            node.id(),
            node.state(),
            node.last_received_bits()
        );
    }
}