use core::fmt;
use core::panic::PanicInfo;

use crate::devices::serial;
use crate::devices::vga;
use crate::stack_trace;

#[cfg(test)]
use crate::test;

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

    serial::get_default_serial().write_fmt(args).unwrap();

    #[cfg(not(test))]
    vga::get_default_vga().write_fmt(args).unwrap();
}

pub unsafe fn break_print_locks() {
    serial::force_unlock();

    #[cfg(not(test))]
    vga::force_unlock();
}

pub fn do_panic(info: &PanicInfo) -> ! {
    unsafe {
        break_print_locks();
    };

    print!("kernel panic: ");

    if let Some(msg) = info.message() {
        print!("{}", msg);
    } else if let Some(msg) = info.payload().downcast_ref::<&'static str>() {
        print!("{}", msg);
    } else {
        print!("(no message provided)");
    }

    if let Some(loc) = info.location() {
        print!(" at {}\n", loc);
    } else {
        print!(" - no location information available\n");
    }

    println!("Stack trace:");
    for frame in stack_trace::trace_stack() {
        println!("    {:#016x}", frame.frame_ip);
    }

    #[cfg(test)]
    test::test_panic();

    #[cfg(not(test))]
    loop {}
}
