#![no_std]
#![no_main]
#![feature(custom_test_frameworks)]
#![feature(panic_info_message)]
#![feature(rustc_private)]
#![feature(abi_x86_interrupt)]
#![feature(maybe_uninit_ref)]
#![feature(alloc_error_handler)]
#![feature(const_in_array_repeat_expressions)]
#![feature(asm)]
#![feature(llvm_asm)]
#![feature(try_trait)]
#![feature(arbitrary_self_types)]
#![feature(option_unwrap_none)]
#![feature(option_expect_none)]
#![feature(new_uninit)]
#![feature(maybe_uninit_extra)]
#![feature(alloc_layout_extra)]
#![feature(weak_into_raw)]
#![feature(raw)]
#![test_runner(crate::test::test_runner)]
#![reexport_test_harness_main = "test_main"]
#![allow(dead_code)]

#[macro_use]
extern crate alloc as alloc_crate;

extern crate compiler_builtins;
extern crate crossbeam;

#[macro_use]
mod print;
mod acpica;
mod asm;
mod devices;
mod gdt;
mod interrupts;
mod lock;
mod malloc;
mod multiboot;
mod paging;
mod stack_trace;
mod structures;
mod task;
mod timer;

#[cfg(test)]
mod test;

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

#[no_mangle]
pub extern "C" fn _rust_start(boot_info: *const KernelLoaderInfo) -> ! {
    kernel_main(boot_info);
}

#[panic_handler]
fn panic(info: &PanicInfo) -> ! {
    print::do_panic(info);
}

pub fn kernel_main(boot_info: *const KernelLoaderInfo) -> ! {
    paging::remap_boot_identity_paging();

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
        let lza_pages = boot_info.heap_pages / 2;
        let sma_pages = boot_info.heap_pages / 2;

        let sma_start = malloc::KERNEL_HEAP_BASE;
        let lza_start = sma_start + ((sma_pages as usize) * 0x1000);

        println!(
            "Initializing kernel heap:\n    - SMA: {} pages at {:#016x}\n    - LZA: {} pages at {:#016x}",
            sma_pages, sma_start, lza_pages, lza_start
        );

        malloc::small_zone_alloc::initialize(sma_start, sma_pages as usize);
        malloc::large_zone_alloc::initialize(lza_start, lza_pages as usize);
    }

    paging::init_paging_metadata();

    malloc::physical_mem::initialize();
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

    const EXTRA_PAGES: usize = 512;
    unsafe {
        for _ in 0..(EXTRA_PAGES / 128) {
            let sma_alloc = malloc::heap_pages::allocate(128 * 0x1000)
                .expect("Could not allocate extra space for SMA");
            let lza_alloc = malloc::heap_pages::allocate(128 * 0x1000)
                .expect("Could not allocate extra space for LZA");

            malloc::small_zone_alloc::add_pages(sma_alloc, 128);
            malloc::large_zone_alloc::add_pages(lza_alloc, 128);
        }

        println!("SMA/LZA bootstrap complete.");
    }

    acpica::initialize().expect("could not initialize ACPICA");

    devices::local_apic::initialize();
    devices::io_apic::initialize();

    task::initialize();

    let h = task::Task::new(kernel_stage2_main, 10).expect("could not spawn initial task");
    h.schedule();
    unsafe {
        task::scheduler().force_context_switch();
    }
}

fn kernel_stage2_main(arg: u64) -> u64 {
    println!("init: arg = {}", arg);

    unsafe {
        asm::interrupts::set_if(true);
    }

    devices::timer::calibrate_apic_timer();
    timer::initialize();
    devices::timer::start_ticks();

    #[cfg(test)]
    test_main();

    let h = task::Task::new(test_task, 0).expect("could not spawn task");
    h.schedule();

    let foo = 25;
    task::Task::from_closure(move || {
        println!("hello from closure task, foo = {}", foo);
        0
    })
    .expect("could not spawn closure task")
    .schedule();

    0
}

fn test_task(_: u64) -> u64 {
    let handle = task::current_task();
    let mut val: u64 = 0;

    task::run_future(async {
        println!("async block starting");

        let deadline = timer::TimerDeadline::Relative(8192 * 2);
        timer::sleep_async(deadline).unwrap().await;

        println!("async block exiting");
    });

    loop {
        println!("tick {}", val);
        val += 1;

        schedule_timer(handle.clone());
        task::yield_cpu();
    }
}

fn schedule_timer(handle: task::TaskHandle) {
    let deadline = timer::TimerDeadline::Relative(8192);
    let timer = timer::TimerData::new(
        move || {
            handle.schedule();
        },
        deadline,
    );

    timer.start().expect("could not start timer");
}
