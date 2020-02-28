#![no_std]
#![no_main]
#![feature(panic_info_message)]

use core::panic::PanicInfo;

mod vga;

#[panic_handler]
#[allow(unused_must_use)]
fn panic(info: &PanicInfo) -> ! {
    use core::fmt::Write;

    let mut disp = unsafe { vga::force_take_lock() };
    write!(disp, "kernel panic: ");

    if let Some(msg) = info.message() {
        write!(disp, "{}", msg);
    } else if let Some(msg) = info.payload().downcast_ref::<&'static str>() {
        write!(disp, "{}", msg);
    } else {
        write!(disp, "(no message provided)");
    }

    if let Some(loc) = info.location() {
        write!(disp, " at {}\n", loc);
    } else {
        write!(disp, " - no location information available\n");
    }

    loop {}
}

#[no_mangle]
pub extern "C" fn _start() -> ! {
    println!("Hello world{}", "!");
    panic!("test");

    loop {}
}
