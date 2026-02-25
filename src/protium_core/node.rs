use crate::can::{AnnotatedFrame, WireBits, Frame, ProtiumFrameError};

#[repr(u8)]
#[derive(Debug, Default)]
pub enum ErrorState {
    #[default]
    None,

    Active,
    Passive,
    BusOff,
}

#[derive(Debug, Default)]
pub struct Node {
    pub error_state: ErrorState,
    pub receive_error_counter: u16,
    pub transmit_error_counter: u16,
}

impl Node {
    #[allow(unused_variables)]
    pub fn encode(&self, frame: &Frame) -> Result<AnnotatedFrame, ProtiumFrameError> {
        todo!()
    }

    #[allow(unused_variables)]
    pub fn transmit(&self, frame: &Frame) -> Result<(), ProtiumFrameError> {
        todo!()
    }
}
