# Protium

A Rust library for simulating CAN (Controller Area Network) bus communication with multi-node support and complete ISO 11898-1 protocol implementation.

The goal of Protium is to provide a foundation and simulation framework to support the development of my other project, [OBDium](https://github.com/provrb/obdium). Rather than needing to physically connect to a vehicle, and/or manually create trouble codes on my vehicle to test features, it can all be simulated virtually with protocol accurate results, allowing for things like ECU, DTC and freeze frame simulation supporting all services and even Mode 22 PIDS, and even UDS. 

## What is Protium?

Protium is a CAN bus simulator that allows developers to model and test CAN network behavior in Rust. It provides:

- **Complete CAN Protocol Support**: Implementation of the physical and data link layers of the CAN protocol
- **Multi-Node Simulation**: Register multiple nodes on a virtual bus to simulate real-world CAN networks
- **Arbitration Handling**: Automatic CAN arbitration when multiple nodes attempt transmission simultaneously
- **Frame Encoding/Decoding**: Full support for both 11-bit (standard) and 29-bit (extended) CAN IDs
- **Bit-Level Operations**: Bit stuffing/destuffing and CRC-15 checksum calculation
- **Callback System**: Node-level callbacks for transmission completion and frame reception

## Why Use Protium?

- **Test CAN Network Logic**: Simulate multi-node CAN networks without hardware
- **Protocol Verification**: Verify correct CAN frame construction and transmission
- **Development & Debugging**: Develop and test CAN-based applications in pure Rust
- **Educational**: Learn how the CAN protocol works at the bit level
- **No External Dependencies**: Core CAN simulation with only essential dependencies

## Getting Started

### Installation

Add Protium to your `Cargo.toml`:

```toml
[dependencies]
protium = "0.1.0"
```

### Basic Usage

Here's a simple example of two nodes communicating over a CAN bus:

```rust
use protium::{
    bus::Bus,
    can::{CanId, Frame},
    node::Node,
};
use std::thread::sleep;
use std::time::Duration;

fn main() {
    // Create a bus with 10ms tick interval
    let mut bus = Bus::new(10);

    // Create two nodes with different CAN IDs
    let mut ecm = Node::new(CanId::Standard(0x7E8));  // Engine Control Module
    let mut tcm = Node::new(CanId::Standard(0x7EA));  // Transmission Control Module

    // Create a frame with data
    let frame = Frame::new(
        ecm.id(),
        vec![0x22],  // 1 byte of data
        false,       // not a remote frame
    ).expect("Failed to create frame");

    // Queue the frame for transmission
    ecm.queue_transmission(&frame)
        .expect("Failed to queue transmission");

    // Set up a callback to handle received frames on TCM
    tcm.set_on_complete_receive_callback(|node_id, bits| {
        println!("[Node:{}] Received {} bits", node_id, bits.len());
    });

    // Register nodes on the bus
    bus.register_node(ecm);
    bus.register_node(tcm);

    // Run the bus simulation
    loop {
        if let Err(e) = bus.tick() {
            eprintln!("Bus error: {}", e);
            break;
        }

        if !bus.is_active() {
            break;  // Simulation complete
        }

        sleep(Duration::from_millis(10));
    }
}
```

### Creating CAN Frames

Protium supports both standard (11-bit) and extended (29-bit) CAN IDs:

```rust
use protium::can::{CanId, Frame};

// Standard CAN ID (11-bit)
let standard_frame = Frame::new(
    CanId::Standard(0x123),
    vec![0x01, 0x02, 0x03],
    false,
)?;

// Extended CAN ID (29-bit)
let extended_frame = Frame::new(
    CanId::Extended(0x12345678),
    vec![0xFF],
    false,
)?;
```

### Multi-Node Communication

You can register multiple nodes on a bus. When multiple nodes attempt transmission simultaneously, CAN arbitration automatically resolves which node gets priority based on the CAN ID (dominant/recessive bits):

```rust
let mut bus = Bus::new(10);

// Create multiple nodes
let mut node1 = Node::new(CanId::Standard(0x100));
let mut node2 = Node::new(CanId::Standard(0x200));
let mut node3 = Node::new(CanId::Standard(0x300));

// Node with lower CAN ID (more dominant bits) wins arbitration
bus.register_node(node1);
bus.register_node(node2);
bus.register_node(node3);
```

### Node Callbacks

Use callbacks to handle events when frames are transmitted or received:

```rust
let mut node = Node::new(CanId::Standard(0x123));

// Callback when transmission completes
node.set_on_complete_tranmission_callback(|node_id| {
    println!("Node {} finished transmitting", node_id);
});

// Callback when a frame is fully received
node.set_on_complete_receive_callback(|node_id, bits| {
    println!("Node {} received {} bits", node_id, bits.len());
});
```

## Features

### Current Implementation

- ✅ **Physical Layer**: Bit-level bus operations, though bit stuffing/destuffing not fully included in tranmitting and receiving process
- ✅ **Data Link Layer**: Frame encoding/decoding, CRC-15 checksums, arbitration
- ✅ **Standard CAN Frames**: 11-bit CAN IDs with up to 8 bytes payload
- ✅ **Extended CAN Frames**: 29-bit CAN IDs with up to 8 bytes payload
- ✅ **Multi-Node Support**: Simulate networks with multiple nodes
- ✅ **CAN Arbitration**: Automatic priority resolution during collisions

### Planned Features

- Network/Transport Layer protocols (ISO-TP)
- Application layer support
- CAN FD (Flexible Data-rate) support
- Full ECU simulation
- Bit stuffing fully integrated into transmitting and receiving logic

## Architecture

Protium is organized into key modules:

- **`bus`**: Manages the virtual CAN bus and coordinates communication between nodes
- **`can`**: Core CAN protocol implementation (Frame, CanId, encoding/decoding)
- **`node`**: Represents CAN nodes with transmission/reception state machines
- **`bit_stuff` / `bit_destuff`**: Handles CAN bit stuffing protocol
- **`logging`**: Optional logging utilities for debugging

## Running Examples

The repository includes example programs demonstrating different use cases:

```bash
# Run the basic bus example
cargo run --example bus_with_nodes

# Run tests
cargo test
```

## API Reference

### Bus

```rust
pub fn new(tick_interval_ms: u32) -> Self
pub fn register_node(&mut self, node: Node)
pub fn tick(&mut self) -> Result<(), ProtiumError>
pub fn is_active(&self) -> bool
pub fn get_node(&self, id: CanId) -> Option<&Node>
pub fn get_nodes(&self) -> &[Node]
```

### Node

```rust
pub fn new(id: CanId) -> Self
pub fn id(&self) -> CanId
pub fn queue_transmission(&mut self, frame: &Frame) -> Result<()>
pub fn set_on_complete_tranmission_callback(&mut self, f: impl Fn(CanId))
pub fn set_on_complete_receive_callback(&mut self, f: impl Fn(CanId, BitVec<u8, Msb0>))
pub fn state(&self) -> NodeState
pub fn pending_retransmission(&self) -> bool
```

### Frame

```rust
pub fn new(can_id: CanId, payload: Vec<u8>, is_remote: bool) -> Result<Self>
pub fn encode(&self) -> Result<BitVec<u8, Msb0>>
pub fn checksum_with_input(input: &BitVec<u8, Msb0>) -> u16
```

## Testing

Run the full test suite:

```bash
cargo test
```

The test suite includes:
- Frame encoding/decoding validation
- CRC-15 checksum verification
- Multi-node transmission and reception
- CAN arbitration testing
- Bit stuffing/destuffing correctness

## Contributing

Contributions are welcome! Areas for contribution include:

- Additional protocol layer implementations (ISO-TP, UDS)
- Performance optimizations
- Extended test coverage
- Documentation improvements
- Example programs

## License

This project is licensed under the [MIT License](LICENSE.md).

## Support & Documentation

For issues, questions, or suggestions, please open an issue on the GitHub repository. The code includes extensive documentation and comments explaining the CAN protocol implementation.

## References

This project is created from hours of my own research and notes. A copy of my notes may be available in the far future. In the meantime, here are a couple useful references:

- [ISO 11898-1: CAN Protocol Specification](https://en.wikipedia.org/wiki/CAN_bus)
- [CAN Bus Technical Details](https://www.kvaser.com/about-can/)
- [CAN Bus Explained - A Simple Intro](https://www.csselectronics.com/pages/can-bus-simple-intro-tutorial)