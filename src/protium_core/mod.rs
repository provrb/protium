use bitvec::{order::Msb0, vec::BitVec};

pub mod bus;
pub mod can;
pub mod node;

pub fn bit_stuff(bitstream: &BitVec<u8, Msb0>) -> BitVec<u8, Msb0> {
    // insert a 0 after five consecutive 1s, or a 1 after five consecutive 0
    let mut stuffed = BitVec::<u8, Msb0>::new();
    let mut count = 0;
    let mut last_bit: Option<bool> = None;
    for bit in bitstream.iter() {
        let curr_bit = *bit;
        if Some(curr_bit) == last_bit {
            count += 1;
        } else {
            count = 1;
        }

        stuffed.push(curr_bit);
        if count == 5 {
            stuffed.push(!last_bit.unwrap());
            count = 0;
        }

        last_bit = Some(curr_bit);
    }

    stuffed
}

pub fn bit_destuff(bitstream: &BitVec<u8, Msb0>) -> BitVec<u8, Msb0> {
    let mut count = 0;
    let mut last_bit: Option<bool> = None;
    let mut destuffed = BitVec::<u8, Msb0>::new();
    for bit in bitstream.iter() {
        let curr_bit = *bit;
        if count < 5 {
            destuffed.push(curr_bit);
        } else {
            count = 1;
        }

        if Some(curr_bit) == last_bit {
            count += 1;
        } else {
            count = 1;
        }

        last_bit = Some(curr_bit);
    }

    destuffed
}
