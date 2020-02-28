use core::fmt;

use crate::vga;
use crate::serial;

#[macro_export]
macro_rules! print {
    ($($arg:tt)*) => ($crate::print::_do_blocking_print(format_args!($($arg)*)));
}

#[macro_export]
macro_rules! println {
    () => ($crate::print!("\n"));
    ($($arg:tt)*) => ($crate::print!("{}\n", format_args!($($arg)*)));
}

#[doc(hidden)]
pub fn _do_blocking_print(args: fmt::Arguments) {
    use fmt::Write;

    vga::DEFAULT_DISPLAY.lock().write_fmt(args).unwrap();
    serial::DEFAULT_SERIAL.lock().write_fmt(args).unwrap();
}

pub unsafe fn break_print_locks() {
    vga::force_unlock();
    serial::force_unlock();
}