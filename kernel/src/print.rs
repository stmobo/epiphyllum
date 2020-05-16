use core::fmt;
use core::panic::PanicInfo;

use crate::asm;
use crate::devices::serial;
use crate::devices::vga;
use crate::stack_trace;
use crate::task;

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

fn print_control_regs() {
    println!(
        "CR0: {:#018x}    CR2: {:#018x}",
        asm::get_cr0(),
        asm::get_cr2()
    );

    println!(
        "CR4: {:#018x}    CR3: {:#018x}",
        asm::get_cr4(),
        asm::get_cr3()
    );
}

pub fn do_panic(info: &PanicInfo) -> ! {
    unsafe {
        break_print_locks();
    };

    print!("\nkernel panic: ");

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

    println!("\n== [Current Stack Trace] ==");
    for frame in stack_trace::trace_stack() {
        println!("    {:#018x}", frame.frame_ip);
    }

    if let Some(ctx) = task::current_context() {
        println!("\n== [Task Context] ==\n{}", unsafe { &*ctx });
        print_control_regs();

        println!("\n== [Task Stack Trace] ==");
        for frame in unsafe { (*ctx).trace_stack() } {
            println!("    {:#018x}", frame.frame_ip);
        }
    } else {
        println!("\nUnable to identify task context.\n== [Control Registers] ==");
        print_control_regs();
    }

    #[cfg(test)]
    test::test_panic();

    #[cfg(not(test))]
    loop {}
}
