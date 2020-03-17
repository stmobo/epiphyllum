#![no_std]
#![feature(panic_info_message)]
#![feature(rustc_private)]
#![feature(custom_test_frameworks)]
#![feature(abi_x86_interrupt)]
#![feature(maybe_uninit_ref)]
#![feature(alloc_error_handler)]
#![feature(const_in_array_repeat_expressions)]
#![feature(asm)]
#![test_runner(crate::test_runner::test_runner)]
#![reexport_test_harness_main = "test_main"]

#[macro_use]
extern crate alloc;

extern crate compiler_builtins;

#[macro_use]
pub mod print;
pub mod asm;
pub mod avl_tree;
pub mod devices;
pub mod gdt;
pub mod interrupts;
pub mod malloc;
pub mod multiboot;
pub mod paging;
pub mod stack_trace;

#[cfg(test)]
pub mod test_runner;

use core::panic::PanicInfo;
use x86_64::structures::idt::InterruptDescriptorTable;

use multiboot::{MemoryType, MultibootInfo};

#[derive(Debug, Clone)]
#[repr(C)]
pub struct KernelLoaderInfo {
    multiboot_info: *const MultibootInfo,
    idt_phys: *mut InterruptDescriptorTable,
    heap_pages: u64,
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

    println!("Stack trace:");
    for frame in stack_trace::trace_stack() {
        println!("    {:#016x}", frame.frame_ip);
    }

    #[cfg(test)]
    test_runner::exit_qemu(test_runner::TestExitCode::Failure);

    loop {}
}

pub fn kernel_main(boot_info: *const KernelLoaderInfo) -> ! {
    paging::remap_boot_identity_paging();

    let mut l = devices::DEFAULT_DISPLAY.lock();
    l.clear();
    drop(l);

    println!("Epiphyllum kernel starting...");
    println!("Boot info structure address: {:#016x}", boot_info as usize);

    let boot_info_ptr = paging::direct_map_pointer(boot_info);
    let boot_info: KernelLoaderInfo = unsafe { (*boot_info_ptr).clone() };

    let mb: MultibootInfo;
    let idt_phys_addr: usize;
    let idt_phys: usize;

    unsafe {
        let mb_addr = boot_info.multiboot_info as *const MultibootInfo;
        mb = (*(paging::direct_map_pointer(mb_addr))).clone();

        idt_phys_addr = boot_info.idt_phys as usize;
        idt_phys = paging::offset_direct_map(boot_info.idt_phys as usize);

        println!(
            "IDT at physical address {:#016x}, virtual address {:#016x}",
            idt_phys_addr, idt_phys
        );
    }

    gdt::initialize_gdt();
    unsafe {
        interrupts::initialize_idt(idt_phys);
    }

    unsafe {
        println!(
            "Initializing kernel heap: {} pages at {:#016x}",
            boot_info.heap_pages,
            malloc::KERNEL_HEAP_BASE
        );

        malloc::initialize_small_heap(malloc::KERNEL_HEAP_BASE, boot_info.heap_pages as usize);
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
                MemoryType::Available => {
                    println!("Available");

                    unsafe {
                        malloc::physical_mem::register(m.base_addr as usize, m.length as usize);
                    }
                }
                MemoryType::ACPI => println!("ACPI information"),
                MemoryType::Defective => println!("Defective"),
                MemoryType::MustPreserve => println!("System Reserved"),
                _ => println!("Reserved"),
            }
        }
    } else {
        panic!("Loader did not provide a memory map");
    }

    interrupts::claim_idt_page(idt_phys_addr);
    paging::reserve_bootstrap_physical_pages();

    println!("Physical memory allocator initialized.");

    unsafe {
        malloc::virtual_mem::initialize(boot_info.heap_pages);
    }

    println!("Heap virtual memory allocator initialized.");

    let lapic = devices::pic::initialize();
    println!("Local APIC initialized.");

    unsafe {
        asm::interrupts::set_if(true);
    }

    interrupts::register_handler(0x20, |vector: u8| -> interrupts::InterruptHandlerStatus {
        println!("handled interrupt 0x20");
        interrupts::InterruptHandlerStatus::Handled
    });

    lapic
        .configure_timer(devices::pic::local_apic::TimerMode::OneShot, 1, 0x20)
        .unwrap();

    lapic.set_timer_ticks(0xFFFF);

    interrupts::register_handler(0x40, |vector: u8| -> interrupts::InterruptHandlerStatus {
        println!("handled interrupt 0x40");

        interrupts::InterruptHandlerStatus::Handled
    });

    #[cfg(test)]
    test_main();

    loop {}
}
