//! Intel PIT support.

use crate::asm::ports;

const CH0_ADDR: u16 = 0x40;
const COMMAND_ADDR: u16 = 0x43;

pub unsafe fn set_oneshot(count: u16) {
    ports::outb(COMMAND_ADDR, 0b00_11_000_0);
    ports::outb(CH0_ADDR, (count & 0xFF) as u8);
    ports::outb(CH0_ADDR, ((count >> 8) & 0xFF) as u8);
}
