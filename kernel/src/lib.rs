#![no_std]
#![feature(panic_info_message)]
#![feature(rustc_private)]
#![feature(custom_test_frameworks)]
#![test_runner(crate::test_runner::test_runner)]
#![reexport_test_harness_main = "test_main"]

extern crate compiler_builtins;

#[macro_use]
pub mod print;
pub mod devices;

#[cfg(test)]
pub mod test_runner;

use core::panic::PanicInfo;
use core::mem;

#[panic_handler]
#[allow(unused_must_use)]
fn panic(info: &PanicInfo) -> ! {
    unsafe {
        print::break_print_locks();
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

    #[cfg(test)]
    test_runner::exit_qemu(test_runner::TestExitCode::Failure);

    loop {}
}

pub fn kernel_main(boot_info: *const u8) -> ! {
    let mut l = devices::DEFAULT_DISPLAY.lock();
    l.clear();
    drop(l);

    println!("Epiphyllum kernel starting...");

    let addr: usize = unsafe { mem::transmute(boot_info) };
    println!("Boot info structure address: {:#016x}", addr);

    loop {}

    #[cfg(test)]
    test_main();

    loop {}
}
