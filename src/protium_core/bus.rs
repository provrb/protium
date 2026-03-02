use std::collections::HashMap;

use crate::{
    can::CanId,
    node::{Node, NodeState},
};

#[derive(Debug, Default)]
pub struct Bus {
    nodes: Vec<Node>,
    state: bool,
    baud_rate: u16, // kbits/s
}

impl Bus {
    pub fn new(baud_rate: u16) -> Self {
        Self {
            // max amount of nodes usually allowed on a bus
            // depending on installed electronics.
            nodes: Vec::with_capacity(32),

            state: false,
            baud_rate,
        }
    }

    pub fn tick(&mut self) -> bool {
        // [node_can_id] = bit_sent_by_node
        let mut bit_sent_from_each = HashMap::with_capacity(self.nodes.len());
        for node in self.nodes.iter_mut() {
            if let Some(transmitted_bit) = node.transmit_bit() {
                bit_sent_from_each.insert(node.id().as_u32(), transmitted_bit);
            } else {
                node.set_state(NodeState::Receiving);
            }
        }

        // println!("[Bus] Bits sent from each node: {:?}", &bit_sent_from_each);

        // if any bit is dominant, dominant is 0
        let state = bit_sent_from_each.iter().any(|(_, b)| *b);

        // tell all nodes what bit was used
        // each node will determine if they won the transmission or not
        // winner is the person sending the most dominant bits in a row
        self.nodes.iter_mut().for_each(|n| {
            if let Some(bit_sent_by_node) = bit_sent_from_each.get(&n.id().as_u32()) {
                n.resultant_bus_bit(*bit_sent_by_node, state);
            }

            n.receive_bit(state);
        });

        // no bits sent from any node right now.
        // no node transmitting
        bit_sent_from_each.len() != 0
    }

    pub fn register_node(&mut self, node: Node) {
        self.nodes.push(node);
    }

    pub fn get_node(&self, id: CanId) -> Option<&Node> {
        self.nodes.iter().find(|node| node.id() == id)
    }

    pub fn post_bit(&mut self, bit: bool) {
        self.state = bit;
    }
}
