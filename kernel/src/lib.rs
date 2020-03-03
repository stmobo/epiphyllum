#![no_std]
#![feature(panic_info_message)]
#![feature(rustc_private)]
#![feature(custom_test_frameworks)]
#![feature(abi_x86_interrupt)]
#![feature(maybe_uninit_ref)]
#![feature(alloc_error_handler)]
#![test_runner(crate::test_runner::test_runner)]
#![reexport_test_harness_main = "test_main"]

extern crate alloc;
extern crate compiler_builtins;

#[macro_use]
pub mod print;
pub mod devices;
pub mod exception_handler;
pub mod malloc;
pub mod multiboot;
pub mod paging;

#[cfg(test)]
pub mod test_runner;

use core::panic::PanicInfo;
use x86_64::structures::idt::InterruptDescriptorTable;

use malloc::BuddyAllocator;
use multiboot::{MemoryType, MultibootInfo};

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

    let boot_info = paging::physical_memory(boot_info).unwrap();
    let mb: MultibootInfo;
    let mut idt_phys: &'static mut InterruptDescriptorTable;

    unsafe {
        let mb_addr = (*boot_info).multiboot_info as *const MultibootInfo;
        mb = *(paging::physical_memory(mb_addr).unwrap());

        let offset_ptr = paging::physical_memory_mut((*boot_info).idt_phys).unwrap();
        idt_phys = &mut *offset_ptr;
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

    unsafe {
        println!(
            "Initializing kernel heap: {} pages at {:#016x}",
            (*boot_info).heap_pages,
            malloc::KERNEL_HEAP_BASE
        );

        use ::alloc::alloc;
        use ::alloc::alloc::Layout;

        malloc::initialize_small_heap(malloc::KERNEL_HEAP_BASE, (*boot_info).heap_pages as usize);
        println!("Testing allocations:");

        let layout_1 = Layout::from_size_align_unchecked(8, 8);
        let layout_2 = Layout::from_size_align_unchecked(64, 64);
        let layout_3 = Layout::from_size_align_unchecked(128, 128);

        let a1 = alloc::alloc(layout_1) as usize;
        let a2 = alloc::alloc(layout_2) as usize;

        println!(
            "a1 = {:#016x} (mod 8 = {})\na2 = {:#016x} (mod 64 = {})",
            a1,
            a1 % 8,
            a2,
            a2 % 64
        );

        alloc::dealloc(a1 as *mut u8, layout_1);
        let a3 = alloc::alloc(layout_3) as usize;
        println!("a3 = {:#016x} (mod 128 = {})", a3, a3 % 128);

        let a4 = alloc::alloc(layout_1) as usize;
        println!("a4 = {:#016x} (mod 8 = {})", a4, a4 % 8);
        alloc::dealloc(a4 as *mut u8, layout_1);

        let mut buddy = BuddyAllocator::new(0, 0x1000usize << 8).unwrap();

        let p1 = buddy.allocate(0x2000).unwrap();
        let p2 = buddy.allocate(0x5000).unwrap();

        println!("p1 = {:#08x}", p1);
        println!("p2 = {:#08x}", p2);

        buddy.deallocate(p1, 0x2000);
        let p3 = buddy.allocate(0x1000).unwrap();
        println!("p3 = {:#08x}", p3);
    }

    #[cfg(test)]
    test_main();

    loop {}
}
