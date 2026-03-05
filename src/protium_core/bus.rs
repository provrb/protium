use crate::{
    can::CanId,
    node::{Node, NodeState, ProtiumNodeError},
};

#[derive(Debug, Default, PartialEq, Eq)]
pub enum BusState {
    #[default]
    Idle,
    /// Bus is active/transmitting bits
    Transmitting,
}

#[derive(Debug, Default)]
pub struct Bus {
    nodes: Vec<Node>,
    state: BusState,

    #[allow(dead_code)]
    baud_rate: u16, // kbits/s
}

impl Bus {
    /// Create a new `Bus` instance in the `Idle` `BusState` with no registered nodes.
    pub const fn new(baud_rate: u16) -> Self {
        Self {
            nodes: Vec::new(),
            state: BusState::Idle,
            baud_rate,
        }
    }

    /// Check if the current Bus is Active/Transmitting bits to nodes on the wire
    pub fn is_active(&self) -> bool {
        self.state == BusState::Transmitting
    }

    /// Register a [`crate::node::Node`] on the current bus to be able to
    /// send and receive messages, to and from this Node.
    ///
    /// Registered nodes are able to send messages to other nodes
    /// on the bus, and receive messages from other nodes on the bus.
    ///
    /// Because [`Bus`] will own Node: use [`Bus::get_node`] to get a reference to the node.
    pub fn register_node(&mut self, node: Node) {
        if self.nodes.contains(&node) {
            return;
        }

        self.nodes.push(node);
    }

    /// Get a reference to a [`Node`] previously registered to this [`Bus`] with [`Bus::register_node`]
    /// from the Node's [`CanId`]
    pub fn get_node(&self, id: CanId) -> Option<&Node> {
        self.nodes.iter().find(|node| node.id() == id)
    }

    /// Get a vector of all currently registered nodes to this [`Bus`]
    pub fn get_nodes(&self) -> &Vec<Node> {
        &self.nodes
    }

    /// Simulate a bit-tick for the bus.
    ///
    /// 1. Get a vector of all bits every registered node wants to send to the wire.
    ///    - If there is none, set the `BusState` to `Idle` and set all registered nodes to
    ///      `Idle` `NodeState` if they are active. (see `Node::is_active()`)
    /// 2. Determine the bit that will occupy the wire. If there is a dominant bit, then a 0 bit
    ///    will be present on the wire over any recessive (1) bits.
    ///    If there are only recessive bits, then the bus will use a 1 bit.
    /// 3. Send the bit on the wire to all registered, active nodes for each
    ///    node to handle the bit depending on their state (i.e sending/receiving)
    ///
    /// See:
    ///     - [`crate::node::Node::is_active`]
    ///     - [`crate::node::Node::read_wire`]
    ///     - [`crate::bus::BusState`]
    ///     - [`crate::node::NodeState`]
    pub fn tick(&mut self) -> Result<(), ProtiumNodeError> {
        let bits_to_drive_this_tick: Vec<bool> = self
            .nodes
            .iter_mut()
            .filter_map(|n| n.drive_bit())
            .collect();

        // No work to do
        // Set all listening/previously transmitting Nodes to idle
        // Set bus state to idle
        if bits_to_drive_this_tick.is_empty() {
            for node in self.nodes.iter_mut() {
                if !node.is_active() {
                    continue;
                }

                node.set_state(NodeState::Idle);
            }

            self.state = BusState::Idle;
            return Ok(());
        }

        // update bus state
        if self.state != BusState::Transmitting {
            self.state = BusState::Transmitting;
        }

        // determine the winning bit
        // the winning bit will always be 0.
        // if there is a 0, winning bit is zero, otherwise its 1
        let winning_bit = !bits_to_drive_this_tick.iter().any(|b| !(*b));

        // iterate through all nodes and transmit winning bit
        for node in self.nodes.iter_mut() {
            if !node.is_active() {
                continue;
            }

            if node.state() == NodeState::Idle {
                node.set_state(NodeState::Receiving);
            }

            node.read_wire(winning_bit)?;
        }

        Ok(())
    }
}
