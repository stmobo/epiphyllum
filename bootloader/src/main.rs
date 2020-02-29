#![no_std]
#![no_main]
#![feature(panic_info_message)]
#![feature(rustc_private)]

extern crate compiler_builtins;

#[macro_use]
mod print;

mod devices;

use core::panic::PanicInfo;

#[no_mangle]
pub extern "C" fn rust_start(_multiboot_struct: *const u8) -> ! {
    let mut l = devices::DEFAULT_DISPLAY.lock();
    l.clear();
    drop(l);

    println!("Epiphyllum-Loader starting...");

    panic!("test");

    loop {}
}

#[panic_handler]
fn panic(info: &PanicInfo) -> ! {
    unsafe {
        print::break_print_locks();
    };

    print!("panic: ");

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

    loop {}
}