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
#![feature(deque_make_contiguous)]
#![feature(leading_trailing_ones)]
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
mod rng;
mod stack_trace;
mod structures;
mod task;
mod timer;

#[cfg(test)]
mod test;

use alloc_crate::sync::Arc;
use core::panic::PanicInfo;

use x86_64::structures::idt::InterruptDescriptorTable;

use lock::NoIRQSpinlock;
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
    asm::initialize_sse();
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

    unsafe { paging::initialize_direct_physical_mappings() };
    paging::init_paging_metadata(&mb);

    // Get a reference to the boot address space to ensure that it doesn't
    // unexpectedly go away, and also since we're going to be passing it to the
    // initial task.
    let space = unsafe { paging::AddressSpace::current() };

    const EXTRA_PAGES: usize = 512;
    unsafe {
        for _ in 0..EXTRA_PAGES {
            let sma_alloc = malloc::heap_pages::allocate(0x1000)
                .expect("Could not allocate extra space for SMA");
            malloc::small_zone_alloc::add_page(sma_alloc);
        }

        println!("SMA bootstrap complete.");

        for _ in 0..(EXTRA_PAGES / 2) {
            let lza_alloc = malloc::heap_pages::allocate(0x2000)
                .expect("Could not allocate extra space for LZA");
            malloc::large_zone_alloc::add_page(lza_alloc);
        }

        println!("LZA bootstrap complete.");
    }

    acpica::initialize().expect("could not initialize ACPICA");

    devices::local_apic::initialize();
    devices::io_apic::initialize();

    let address_space = Arc::new(NoIRQSpinlock::new(space));
    task::initialize(address_space.clone());

    unsafe {
        let h = task::Task::new_raw(kernel_stage2_main as usize, 10, address_space)
            .expect("could not spawn initial task");

        h.schedule();
        let scheduler = task::scheduler();
        scheduler.force_set_running_task(h);
        scheduler.force_context_switch();
    }
}

fn kernel_stage2_main(arg: u64) -> u64 {
    println!("init: arg = {}", arg);

    unsafe {
        asm::interrupts::set_if(true);
    }

    timer::initialize();
    devices::timer::initialize();
    print::initialize();
    devices::pci::initialize();

    #[cfg(test)]
    test_main();

    let h = task::Task::new(test_task, 0, false).expect("could not spawn task");
    h.schedule();

    let foo = 25;
    task::Task::from_closure(true, move || {
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
        handle.set_wakeup_pending(false);

        schedule_timer(handle.clone());

        handle.set_status(task::TaskStatus::Sleeping);
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
