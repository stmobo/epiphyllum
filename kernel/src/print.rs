use alloc_crate::string::String;
use core::fmt;
use core::panic::PanicInfo;
use core::sync::atomic::{AtomicBool, Ordering};
use core::cell::UnsafeCell;
use spin::Once;

use crate::asm;
use crate::devices::serial;
use crate::interrupts;
use crate::lock::OnceCell;
use crate::stack_trace;
use crate::structures::{channel, Receiver, Sender};
use crate::task::Task;
use crate::devices::vga;

#[cfg(test)]
use crate::test;

static LOGGING_TASK_ENABLED: AtomicBool = AtomicBool::new(false);
static LOGGING_TASK: OnceCell<Task> = OnceCell::new();
static LOGGING_CHANNEL: OnceCell<Sender<String>> = OnceCell::new();
static PANIC_SINKS: Once<PanicOutputSinks> = Once::new();

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
    ($($arg:tt)*) => ($crate::print::_do_direct_print(false, format_args!($($arg)*)));
}

#[macro_export]
macro_rules! direct_println {
    () => ($crate::direct_print!("\n"));
    ($($arg:tt)*) => ($crate::direct_print!("{}\n", format_args!($($arg)*)));
}

#[macro_export]
macro_rules! panic_print {
    ($($arg:tt)*) => ($crate::print::_do_direct_print(true, format_args!($($arg)*)));
}

#[macro_export]
macro_rules! panic_println {
    () => ($crate::panic_print!("\n"));
    ($($arg:tt)*) => ($crate::panic_print!("{}\n", format_args!($($arg)*)));
}

struct PanicOutputSinks {
    serial: UnsafeCell<serial::SerialPort>,
    vga: UnsafeCell<vga::VGATextMode>
}

impl PanicOutputSinks {
    fn get() -> &'static PanicOutputSinks {
        PANIC_SINKS.call_once(|| {
            unsafe {
                let r = PanicOutputSinks {
                    serial: UnsafeCell::new(serial::get_panic_serial()),
                    vga: UnsafeCell::new(vga::get_panic_vga()),
                };

                #[cfg(not(test))]
                (*r.vga.get()).clear();

                r
            }
        })
    }

    unsafe fn write_fmt(&self, args: fmt::Arguments) -> fmt::Result {
        use fmt::Write;

        (*self.serial.get()).write_fmt(args)?;

        #[cfg(not(test))]
        (*self.vga.get()).write_fmt(args)
    }
}

unsafe impl Send for PanicOutputSinks {}
unsafe impl Sync for PanicOutputSinks {}

#[doc(hidden)]
pub fn _do_blocking_print(args: fmt::Arguments) {
    if LOGGING_TASK_ENABLED.load(Ordering::SeqCst) {
        LOGGING_CHANNEL.get().unwrap().send(format!("{}", args));
    } else {
        _do_direct_print(false, args);
    }
}

#[doc(hidden)]
pub fn _do_direct_print(in_panic: bool, args: fmt::Arguments) {
    use fmt::Write;

    if in_panic {
        unsafe {
            PanicOutputSinks::get().write_fmt(args).unwrap();
        }
    } else {
        serial::get_default_serial().write_fmt(args).unwrap();

        #[cfg(not(test))]
        vga::get_default_vga().write_fmt(args).unwrap();
    }
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

pub fn do_panic(info: &PanicInfo) -> ! {
    unsafe {
        asm::interrupts::set_if(false);
        set_logging_task_mode(false);
    };
    
    panic_print!("\nkernel panic: ");

    if let Some(msg) = info.message() {
        panic_print!("{}", msg);
    } else if let Some(msg) = info.payload().downcast_ref::<&'static str>() {
        panic_print!("{}", msg);
    } else {
        panic_print!("(no message provided)");
    }

    if let Some(loc) = info.location() {
        panic_print!(" at {}\n", loc);
    } else {
        panic_print!(" - no location information available\n");
    }

    panic_println!("\n== [Current Stack Trace] ==");
    for frame in stack_trace::trace_stack() {
        panic_println!("    {:#018x}", frame.frame_ip);
    }

    let int_ctx = interrupts::get_interrupt_context();
    if !int_ctx.is_null() {
        panic_println!("\n== [Interrupt Context] ==\n{}", unsafe { &*int_ctx });

        panic_println!("\n== [Interrupt Stack Trace] ==");
        for frame in unsafe { (*int_ctx).trace_stack() } {
            panic_println!("    {:#018x}", frame.frame_ip);
        }
    }

    panic_println!("\n== [Control Registers] ==");
    panic_println!(
        "CR0: {:#018x}    CR2: {:#018x}",
        u64::from(asm::get_cr0()),
        asm::get_cr2()
    );

    panic_println!(
        "CR4: {:#018x}    CR3: {:#018x}",
        u64::from(asm::get_cr4()),
        asm::get_cr3()
    );

    #[cfg(test)]
    test::test_panic();

    #[cfg(not(test))]
    loop {}
}
