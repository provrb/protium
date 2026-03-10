use bitvec::{bitvec, order::Msb0};
use protium::can::bit_stuff;

fn main() {
    let input_data = bitvec![u32, Msb0; 1,1,1,1,1,1,1,1,1,1];
    let output_data = bit_stuff(&input_data);
    println!("input data: {:?}", input_data);
    println!("output data: {:?}", output_data);

    // let mut bus = Bus::new(10);
    // let mut ecm = Node::new(CanId::Extended(0x0CF00400));
    // let mut tcm = Node::new(CanId::Extended(0x0CF00500));

    // let ecm_frame =
    //     Frame::new(ecm.id(), vec![0x22], false).expect("failed to create example ecm frame");
    // let tcm_frame = Frame::new(
    //     tcm.id(),
    //     vec![0x80, 0x81, 0x81, 0x82, 0x83, 0x84, 0x85, 0x86],
    //     false,
    // )
    // .expect("failed to create example tcm frame");

    // // prepare nodes to transmit their data when the bus is active
    // ecm.queue_transmission(&ecm_frame)
    //     .expect("failed to prepare transmission frame for ECM");
    // tcm.queue_transmission(&tcm_frame)
    //     .expect("failed to prepare transmission frame for tcm");

    // ecm.set_on_complete_receive_callback(|node_id, received_bits| {
    //     println!("[Node:{}] Received bits: {:?}", node_id, received_bits)
    // });

    // // register nodes on bus to send/receive
    // bus.register_node(ecm);
    // bus.register_node(tcm);

    // // bus ticks
    // loop {
    //     if let Err(e) = bus.tick() {
    //         println!("Error during bus tick: {e}");
    //         return;
    //     }

    //     if !bus.is_active() {
    //         break;
    //     }

    //     sleep(Duration::from_millis(10)); // example tick speed
    // }

    // for node in bus.get_nodes().iter() {
    //     println!(
    //         "[Node:{}] State: {:?} - Received bits: `{:?}`",
    //         node.id(),
    //         node.state(),
    //         node.last_received_bits()
    //     );
    // }
}
