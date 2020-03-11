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
pub mod avl_tree;
pub mod devices;
pub mod exception_handler;
pub mod gdt;
pub mod malloc;
pub mod multiboot;
pub mod paging;

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
    for frame in exception_handler::trace_stack() {
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

    let boot_info_ptr = paging::physical_memory(boot_info).unwrap();
    let boot_info: KernelLoaderInfo = unsafe { (*boot_info_ptr).clone() };

    let mb: MultibootInfo;
    let idt_phys_addr: usize;
    let mut idt_phys: &'static mut InterruptDescriptorTable;

    unsafe {
        let mb_addr = boot_info.multiboot_info as *const MultibootInfo;
        mb = (*(paging::physical_memory(mb_addr).unwrap())).clone();

        idt_phys_addr = boot_info.idt_phys as usize;
        let offset_ptr = paging::physical_memory_mut(boot_info.idt_phys).unwrap();
        idt_phys = &mut *offset_ptr;

        println!(
            "IDT at physical address {:#016x}, virtual address {:#016x}",
            idt_phys_addr, offset_ptr as usize
        );
    }

    gdt::initialize_gdt();
    exception_handler::initialize_idt(&mut idt_phys);
    idt_phys.load();

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

    exception_handler::claim_idt_page(idt_phys_addr);
    paging::reserve_bootstrap_physical_pages();

    println!("Physical memory allocator initialized.");

    unsafe {
        malloc::virtual_mem::initialize(boot_info.heap_pages);
    }

    println!("Heap virtual memory allocator initialized.");

    let addr = malloc::virtual_mem::allocate(0x1000).unwrap();
    println!("Test allocation: {:#016x}", addr);
    /*
        use avl_tree::AVLTree;
        let mut t: AVLTree<u64, u64> = AVLTree::new();
        for i in 0..25 {
            t.insert(i, i);
        }
        t.traverse(|k, _| println!("{:?}", *k));

        loop {}
    */
    malloc::virtual_mem::deallocate(addr, 0x1000);

    println!("Test allocation freed.");

    let test_addr: usize = 0xA_BAD_1DEA_000;
    paging::map_virtual_address(test_addr, 0);

    unsafe {
        use core::ptr;
        ptr::write_volatile(test_addr as *mut u64, 0xDEADBEEF);
        println!(
            "test read: {:#08x}",
            ptr::read_volatile(test_addr as *const u64)
        );
    }

    paging::unmap_virtual_address(test_addr);
    println!("Test address unmapped...");

    #[cfg(test)]
    test_main();

    loop {}
}
