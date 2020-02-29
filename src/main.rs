#![no_std]
#![no_main]
#![feature(panic_info_message)]
#![feature(custom_test_frameworks)]
#![test_runner(crate::test_runner::test_runner)]
#![reexport_test_harness_main = "test_main"]

#[macro_use]
mod print;

mod devices;

#[cfg(test)]
pub mod test_runner;

use core::panic::PanicInfo;

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

#[no_mangle]
pub extern "C" fn _rust_start() -> ! {
    use core::mem;
    println!("Hello world{}", "!");

    #[cfg(test)]
    test_main();

    let f: usize = unsafe { mem::transmute(&_rust_start) };
    println!("_rust_start is located at {:#016X}", f);

    loop {}
}
