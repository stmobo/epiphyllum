use alloc_crate::string::String;
use core::fmt;
use core::panic::PanicInfo;
use core::sync::atomic::{AtomicBool, Ordering};

use crate::asm;
use crate::devices::serial;
use crate::interrupts;
use crate::lock::OnceCell;
use crate::stack_trace;
use crate::structures::{channel, Receiver, Sender};
use crate::task::Task;

#[cfg(not(test))]
use crate::devices::vga;

#[cfg(test)]
use crate::test;

static LOGGING_TASK_ENABLED: AtomicBool = AtomicBool::new(false);
static LOGGING_TASK: OnceCell<Task> = OnceCell::new();
static LOGGING_CHANNEL: OnceCell<Sender<String>> = OnceCell::new();

#[macro_export]
macro_rules! print {
    ($($arg:tt)*) => ($crate::print::_do_blocking_print(format_args!($($arg)*)));
}

#[macro_export]
macro_rules! println {
    () => ($crate::print!("\n"));
    ($($arg:tt)*) => ($crate::print!("{}\n", format_args!($($arg)*)));
}

#[macro_export]
macro_rules! direct_print {
    ($($arg:tt)*) => ($crate::print::_do_direct_print(format_args!($($arg)*)));
}

#[macro_export]
macro_rules! direct_println {
    () => ($crate::direct_print!("\n"));
    ($($arg:tt)*) => ($crate::direct_print!("{}\n", format_args!($($arg)*)));
}

#[doc(hidden)]
pub fn _do_blocking_print(args: fmt::Arguments) {
    if LOGGING_TASK_ENABLED.load(Ordering::SeqCst) {
        LOGGING_CHANNEL.get().unwrap().send(format!("{}", args));
    } else {
        _do_direct_print(args);
    }
}

#[doc(hidden)]
pub fn _do_direct_print(args: fmt::Arguments) {
    use fmt::Write;

    serial::get_default_serial().write_fmt(args).unwrap();

    #[cfg(not(test))]
    vga::get_default_vga().write_fmt(args).unwrap();
}

pub fn logging_task_enabled() -> bool {
    LOGGING_TASK_ENABLED.load(Ordering::SeqCst)
}

pub unsafe fn set_logging_task_mode(enabled: bool) {
    LOGGING_TASK_ENABLED.store(enabled, Ordering::SeqCst);
}

pub fn initialize() {
    let (sender, receiver) = channel();
    if LOGGING_CHANNEL.set(sender).is_err() {
        panic!("logging already initialized");
    }

    Task::from_closure(true, move || {
        logging_task(receiver);
        panic!("logging task died");
    })
    .expect("could not initialize logging task")
    .schedule();

    LOGGING_TASK_ENABLED.store(true, Ordering::SeqCst);
    println!("print: initialized logging task");
}

fn logging_task(log_recv: Receiver<String>) {
    for log_msg in log_recv.wait_iter() {
        serial::get_default_serial().write_str(&log_msg);

        #[cfg(not(test))]
        vga::get_default_vga().write_str(&log_msg);
    }
}

pub unsafe fn break_print_locks() {
    set_logging_task_mode(false);

    serial::force_unlock();

    #[cfg(not(test))]
    vga::force_unlock();
}

fn print_control_regs() {
    println!(
        "CR0: {:#018x}    CR2: {:#018x}",
        u64::from(asm::get_cr0()),
        asm::get_cr2()
    );

    println!(
        "CR4: {:#018x}    CR3: {:#018x}",
        u64::from(asm::get_cr4()),
        asm::get_cr3()
    );
}

pub fn do_panic(info: &PanicInfo) -> ! {
    unsafe {
        asm::interrupts::set_if(false);
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

    let int_ctx = interrupts::get_interrupt_context();
    if !int_ctx.is_null() {
        println!("\n== [Interrupt Context] ==\n{}", unsafe { &*int_ctx });

        println!("\n== [Interrupt Stack Trace] ==");
        for frame in unsafe { (*int_ctx).trace_stack() } {
            println!("    {:#018x}", frame.frame_ip);
        }
    }

    println!("\n== [Control Registers] ==");
    print_control_regs();

    #[cfg(test)]
    test::test_panic();

    #[cfg(not(test))]
    loop {}
}
