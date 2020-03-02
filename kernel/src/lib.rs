#![no_std]
#![feature(panic_info_message)]
#![feature(rustc_private)]
#![feature(custom_test_frameworks)]
#![feature(abi_x86_interrupt)]
#![test_runner(crate::test_runner::test_runner)]
#![reexport_test_harness_main = "test_main"]

extern crate compiler_builtins;

#[macro_use]
pub mod print;
pub mod devices;
pub mod multiboot;
pub mod paging;
pub mod exception_handler;

#[cfg(test)]
pub mod test_runner;

use core::panic::PanicInfo;
use core::mem;
use x86_64::structures::idt::InterruptDescriptorTable;
use x86_64::instructions::tlb;

use multiboot::{MultibootInfo, MemoryType};
use paging::PageTable;

#[repr(C)]
pub struct KernelLoaderInfo {
    multiboot_info: *const MultibootInfo,
    idt_phys: *mut InterruptDescriptorTable,
}

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

pub fn kernel_main(boot_info: *const KernelLoaderInfo) -> ! {
    let mut l = devices::DEFAULT_DISPLAY.lock();
    l.clear();
    drop(l);

    println!("Epiphyllum kernel starting...");
    println!("Boot info structure address: {:#016x}", boot_info as usize);

    paging::remap_boot_identity_paging();

    let boot_info = paging::offset_physical_memory_ptr(boot_info).unwrap();
    let mb: MultibootInfo;
    let mut idt_phys: &'static mut InterruptDescriptorTable;

    unsafe {
        mb = *(*boot_info).multiboot_info;

        let offset_ptr = paging::offset_physical_memory_ptr_mut((*boot_info).idt_phys).unwrap();
        idt_phys = mem::transmute(offset_ptr);
    }

    println!("IDT at physical address {:#016x}", unsafe { (*boot_info).idt_phys as usize });

    exception_handler::initialize_idt(&mut idt_phys);
    idt_phys.load();

    //drop(idt_phys);

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
    } else {
        panic!("Loader did not provide a memory map");
    }

    // exception_handler::initialize_idt(&mut idt_phys);
    unsafe {
        use core::ptr;

        let mut foo: *const u8 = 0x0000_0000_0000_5000 as *mut u8;
        let bar = ptr::read_volatile(foo);
    }

    loop {}

    #[cfg(test)]
    test_main();

    loop {}
}
