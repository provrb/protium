use protium::{
    bus::Bus,
    can::{CanId, Frame},
    node::Node,
    printerr,
};
use std::{thread::sleep, time::Duration};

fn main() {
    let mut bus = Bus::new(10);
    let mut ecm = Node::new(CanId::Standard(0x7e8));
    let mut tcm = Node::new(CanId::Extended(0x0CF00500));

    let ecm_frame = Frame::new(ecm.id(), vec![0x1], false)
        .expect("failed to create example ecm frame");

    // prepare nodes to transmit their data when the bus is active
    ecm.queue_transmission(&ecm_frame)
        .expect("failed to prepare transmission frame for ECM");
    ecm.set_on_complete_tranmission_callback(|can_id| {
        println!(
            "[Node:{}/queue_transmission] Transmitted bits successfully",
            can_id
        );
    });

    ecm.set_on_complete_receive_callback(|node_id, received_bits| {
        println!("[Node:{}] Received bits: {}", node_id, received_bits)
    });
    tcm.set_on_complete_receive_callback(|node_id, received_bits| {
        println!("[Node:{}] Received bits: {}", node_id, received_bits);
        
        match Frame::from_encoded_bits(received_bits) {
            Ok(frame) => {
                if frame.payload_is_printable() {
                    println!(
                        "\t[1] Received payload: `{}`", 
                        String::from_utf8_lossy(frame.data())
                    );

                    println!(
                        "\t[2] Bits as Frame: `{:?}`", 
                        frame
                    );
                }
            }
            Err(e) => printerr!("Frame::from_encoded_bits failed with {e}")
        };
        
    });

    // register nodes on bus to send/receive
    bus.register_node(ecm);
    bus.register_node(tcm);

    // bus ticks
    let mut status_change = false;
    loop {
        if let Err(e) = bus.tick() {
            println!("Error during bus tick: {e}");
            return;
        }

        if bus.is_active() {
            status_change = true;
        }

        if status_change && !bus.is_active() {
            println!(
                "\n[Bus:State] Changing active from {} -> {}",
                !bus.is_active(),
                bus.is_active()
            );
            println!("[Bus:State] Current nodes on bus and their states:");

            for node in bus.get_nodes().iter() {
                println!("\t[Node:{}] State: {:?}", node.id(), node.state(),);
            }

            status_change = false;
        }

        sleep(Duration::from_millis(10)); // example tick speed
    }
}
