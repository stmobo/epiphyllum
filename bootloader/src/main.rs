#![no_std]
#![no_main]
#![feature(panic_info_message)]
#![feature(rustc_private)]

extern crate compiler_builtins;

#[macro_use]
mod print;

mod devices;
mod multiboot;

use core::panic::PanicInfo;
use core::mem;

use multiboot::{MultibootInfo, MemoryInfo, MemoryType};

#[no_mangle]
pub extern "C" fn rust_start(multiboot_struct: *const MultibootInfo) -> ! {
    let mut l = devices::DEFAULT_DISPLAY.lock();
    l.clear();
    drop(l);

    let mb: MultibootInfo = unsafe { *multiboot_struct };

    println!("Epiphyllum-Loader starting (Multiboot 1 mode)...");

    let f: usize = unsafe { mem::transmute(multiboot_struct) };
    println!("Multiboot structure located at {:#016X}", f);

    println!("Kernel command line: {}", mb.get_command_line().unwrap_or(""));

    if let Some(mods) = mb.get_modules() {
        println!("Found {} loaded modules:", mods.len());
        for m in mods {
            println!(
                "    {}: {:#08x} - {:#08x}",
                m.get_string().unwrap_or("<unknown>"),
                m.mod_start,
                m.mod_end
            );
        }
    }

    if let Some(mmap) = mb.get_memory_info() {
        println!("Memory map:");
        for m in mmap {
            print!(
                "    {:#016x} - {:#016x} ({} bytes): ",
                m.base_addr,
                m.base_addr + m.length,
                m.length
            );

            match m.mem_type {
                MemoryType::Available => println!("Available"),
                MemoryType::ACPI => println!("ACPI information"),
                MemoryType::Defective => println!("Defective"),
                MemoryType::MustPreserve => println!("System Reserved"),
                _ => println!("Reserved"),
            }
        }
    }

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