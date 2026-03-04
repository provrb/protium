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

    pub fn tick(&mut self)  {
        
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
