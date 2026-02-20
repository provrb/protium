use bitvec::prelude::*;

#[derive(Debug)]
pub struct FieldSpan {
    pub start: usize,
    pub len: usize,
}

#[derive(Debug)]
pub struct Frame11 {
    pub bits: BitVec<u8, Msb0>,

    pub arbitration: FieldSpan,
    pub control: FieldSpan,
    pub data: FieldSpan,
    pub crc: FieldSpan,
    pub ack: FieldSpan,
    pub eof: FieldSpan,
}

impl Frame11 {
    pub fn new() -> Option<Self> {
        None
    }
}
