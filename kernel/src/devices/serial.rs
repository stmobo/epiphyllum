use core::fmt;

use crate::lock::{LockedGlobal, NoIRQSpinlockGuard};

use x86_64::instructions::port::Port;

const DEFAULT_LCR_SETTINGS: u8 = 0x03; // 8N1
static DEFAULT_SERIAL: LockedGlobal<SerialPort> = LockedGlobal::new();

pub unsafe fn force_unlock() {
    DEFAULT_SERIAL.force_unlock();
}

pub fn get_default_serial() -> NoIRQSpinlockGuard<'static, SerialPort> {
    DEFAULT_SERIAL.init(|| SerialPort::new(0x3F8)).lock()
}

pub struct SerialPort {
    off0: Port<u8>,
    off1: Port<u8>,
    // interrupt_id: Port<u8>,
    line_control: Port<u8>,
    // line_status: Port<u8>,
}

impl SerialPort {
    pub fn new(io_base: u16) -> SerialPort {
        let mut ser = SerialPort::new_uninit(io_base);
        unsafe {
            ser.configure_interrupts(false, false);
            ser.set_divisor(3); // 38400 baud
        }

        ser
    }

    const fn new_uninit(io_base: u16) -> SerialPort {
        SerialPort {
            off0: Port::new(io_base),
            off1: Port::new(io_base + 1),
            // interrupt_id: Port::new(io_base + 2),
            line_control: Port::new(io_base + 3),
            // line_status: Port::new(io_base + 5)
        }
    }

    /// Configure the Line Control Register.
    ///
    /// Currently, only 8-N-1 operation is supported.
    pub unsafe fn configure_lcr(&mut self, dlab: bool) {
        if dlab {
            self.line_control.write(DEFAULT_LCR_SETTINGS | 0x80);
        } else {
            self.line_control.write(DEFAULT_LCR_SETTINGS);
        }
    }

    pub unsafe fn set_divisor(&mut self, divisor: u16) {
        let divisor_low: u8 = (divisor & 0xFF) as u8;
        let divisor_hi: u8 = ((divisor >> 8) & 0xFF) as u8;

        self.configure_lcr(true);
        self.off0.write(divisor_low);
        self.off1.write(divisor_hi);
        self.configure_lcr(false);
    }

    pub unsafe fn configure_interrupts(&mut self, tx: bool, rx: bool) {
        let mut cfg: u8 = 0;

        if tx {
            cfg |= 0x02;
        }

        if rx {
            cfg |= 0x01;
        }

        self.configure_lcr(false);
        self.off1.write(cfg);
    }

    pub fn write_byte(&mut self, tx: u8) {
        unsafe {
            self.off0.write(tx);
        }
    }

    pub fn write_str(&mut self, s: &str) {
        for c in s.bytes() {
            self.write_byte(c);
        }
    }
}

impl fmt::Write for SerialPort {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        SerialPort::write_str(self, s);
        Ok(())
    }
}

pub const unsafe fn get_panic_serial() -> SerialPort {
    SerialPort::new_uninit(0x3F8)
}
