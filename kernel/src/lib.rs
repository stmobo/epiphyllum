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
pub mod exception_handler;
pub mod multiboot;
pub mod paging;

#[cfg(test)]
pub mod test_runner;

use core::mem;
use core::panic::PanicInfo;
use x86_64::structures::idt::InterruptDescriptorTable;

use multiboot::{MemoryType, MultibootInfo};

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
    paging::remap_boot_identity_paging();
    let mut l = devices::DEFAULT_DISPLAY.lock();

    l.change_base_addr(paging::physical_memory_offset(0xB8000).unwrap());
    l.clear();
    drop(l);

    println!("Epiphyllum kernel starting...");
    println!("Boot info structure address: {:#016x}", boot_info as usize);

    let boot_info = paging::physical_memory(boot_info).unwrap();
    let mb: MultibootInfo;
    let mut idt_phys: &'static mut InterruptDescriptorTable;

    unsafe {
        let mb_addr = (*boot_info).multiboot_info as *const MultibootInfo;
        mb = *(paging::physical_memory(mb_addr).unwrap());

        let offset_ptr = paging::physical_memory_mut((*boot_info).idt_phys).unwrap();
        idt_phys = mem::transmute(offset_ptr);
    }

    println!("IDT at physical address {:#016x}", unsafe {
        (*boot_info).idt_phys as usize
    });

    exception_handler::initialize_idt(&mut idt_phys);
    idt_phys.load();

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

    #[cfg(test)]
    test_main();

    loop {}
}
