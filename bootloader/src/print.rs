use core::fmt;

use crate::devices::serial;
use crate::devices::vga;

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

    serial::DEFAULT_SERIAL.lock().write_fmt(args).unwrap();

    #[cfg(not(test))]
    vga::DEFAULT_DISPLAY.lock().write_fmt(args).unwrap();
}

pub unsafe fn break_print_locks() {
    serial::force_unlock();

    #[cfg(not(test))]
    vga::force_unlock();
}
