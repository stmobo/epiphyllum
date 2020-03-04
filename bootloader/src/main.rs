#![no_std]
#![no_main]
#![feature(abi_x86_interrupt)]
#![feature(panic_info_message)]
#![feature(rustc_private)]

extern crate compiler_builtins;

#[macro_use]
mod print;

mod devices;
mod multiboot;
mod exception_handler;
mod paging;
mod elf;

use core::panic::PanicInfo;
use compiler_builtins::mem::{memset, memcpy};
use x86_64::structures::idt::InterruptDescriptorTable;

use multiboot::{MultibootInfo, ModuleInfo, MemoryType};
use paging::PageFrameAllocator;
use elf::Elf64Header;

extern "C" {
    static mut long_mode_idt: InterruptDescriptorTable;
    static _loader_start: u8;
    static _loader_end: u8;

    fn higher_half_trampoline(entry_point_addr: usize, stack_addr: usize, boot_info_addr: usize);
}

#[repr(C)]
pub struct KernelLoaderInfo {
    multiboot_info: *const MultibootInfo,
    idt_phys: *mut InterruptDescriptorTable,
    heap_pages: u64,
}

#[no_mangle]
pub extern "C" fn rust_start(multiboot_struct: *const MultibootInfo) -> ! {
    let mut l = devices::DEFAULT_DISPLAY.lock();
    l.clear();
    drop(l);

    let mb: MultibootInfo = unsafe { *multiboot_struct };

    println!("Epiphyllum-Loader starting (Multiboot 1 mode)...");

    /* Right now, our IDT is still set up to point at 32-bit code,
     * so any CPU exceptions we cause are generally going to cause a 
     * triple fault. Fix this now.
     */
    let idt: &'static mut InterruptDescriptorTable;
    unsafe {
        long_mode_idt = InterruptDescriptorTable::new();
        idt = &mut long_mode_idt;
    }

    exception_handler::initialize_idt(idt);
    idt.load();

    unsafe {
        let loader_start: usize = (&_loader_start as *const u8) as usize;
        let loader_end: usize = (&_loader_end as *const u8) as usize;
        println!("Bootloader at memory range {:#x} - {:#x}", loader_start, loader_end);
    }

    let f: usize = multiboot_struct as usize;
    println!("Multiboot structure located at {:#016X}", f);
    println!("Kernel command line: {}", mb.get_command_line().unwrap_or(""));

    let mut pf_allocator = PageFrameAllocator::new();
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

                    let start_page = (m.base_addr & !0xFFF) + 0x1000;
                    let end_page = (m.base_addr + m.length) & !0xFFF;
                    pf_allocator.add_range(
                        start_page as usize,
                        end_page as usize
                    );
                },
                MemoryType::ACPI => println!("ACPI information"),
                MemoryType::Defective => println!("Defective"),
                MemoryType::MustPreserve => println!("System Reserved"),
                _ => println!("Reserved"),
            }
        }
    } else {
        panic!("BIOS did not provide a memory map");
    }

    if let Some(mods) = mb.get_modules() {
        println!("Found {} loaded modules:", mods.len());
        for m in mods {
            println!(
                "    {}: {:#08x} - {:#08x}",
                m.get_string().unwrap_or("<unknown>"),
                m.mod_start,
                m.mod_end
            );

            pf_allocator.restrict_range(m.mod_start as usize, m.mod_end as usize);
        }
    } else {
        panic!("Bootloader did not load modules");
    }

    if pf_allocator.n_ranges() == 0 {
        panic!("Could not find any usable memory ranges");
    }

    let mods = mb.get_modules().unwrap();
    let kernel_mod: &ModuleInfo = mods.iter().find(|m| {
        if let Some(s) = m.get_string() {
            s == "kernel"
        } else {
            false
        }
    }).expect("Could not find kernel module");

    let kheader_ptr = (kernel_mod.mod_start as usize) as *const Elf64Header;
    let kernel_header: &'static Elf64Header = unsafe { &*kheader_ptr };
    if !kernel_header.is_valid() {
        panic!("kernel ELF header not valid");
    }

    println!("Found valid kernel image at {:#x}", kernel_mod.mod_start);
    println!("    Entry point: {:#016x}", kernel_header.entry_point());

    for (i, ph) in kernel_header.program_header_table().iter().enumerate() {
        /* We only need to deal with PT_LOAD segments for now... */
        if ph.p_type != 1 {
            continue;
        }

        /* Figure out how many pages need to be mapped in. */
        let mut total_pages = (ph.p_memsz / 0x1000) as usize;
        if ph.p_memsz % 0x1000 > 0 {
            total_pages += 1;
        }

        println!(
            "    Segment {}: {:#016x} => {:#016x}",
            i, ph.p_offset, ph.p_vaddr
        );

        println!(
            "    file size: {:#x}, mem size: {:#x} ({} pages)",
            ph.p_filesz, ph.p_memsz, total_pages
        );

        /* Allocate a buffer to copy the segment into. */
        let dest_buf_addr = pf_allocator.allocate(total_pages as u64);
        let to_base: usize = (ph.p_vaddr as usize) & paging::PAGE_MASK;

        /* Map the segment into memory at the specified virtual address. */
        for i in 0..total_pages {
            let paddr = dest_buf_addr + (i * 0x1000);
            let vaddr = to_base + (i * 0x1000);

            paging::map_address(&mut pf_allocator, paddr, vaddr);
        }

        unsafe {
            /* Zero out the segment pages first. */
            let p = to_base as *mut u8;
            memset(p, 0, total_pages * 0x1000);

            /* Now copy over the kernel bytes starting from the specified segment offset in memory. */
            let from_addr = (kernel_mod.mod_start as u64) + ph.p_offset;
            let from_ptr = (from_addr as usize) as *const u8;
            let to_ptr = (ph.p_vaddr as usize) as *mut u8;

            memcpy(to_ptr, from_ptr, ph.p_filesz as usize);
        }
    }

    println!("All segments mapped, initializing kernel stack and heap...");

    /* Map in a few pages for our higher-half stack. */
    let higher_half_stack_addr = 0xFFFF_FF00_0000_0000;
    let n_stack_pages: usize = 64; // 64 * 4 KiB = 0.25 MiB
    let stack_phys = pf_allocator.allocate(n_stack_pages as u64);

    for i in 0..n_stack_pages {
        let paddr = stack_phys + (i * 0x1000);
        let vaddr = higher_half_stack_addr - (i * 0x1000);

        paging::map_address(&mut pf_allocator, paddr, vaddr);
    }

    /* Map in an initial kernel heap. */
    let higher_half_heap_base = 0xFFFF_C080_0000_0000;
    let n_heap_pages = 64;
    let heap_phys = pf_allocator.allocate(n_heap_pages);
    for i in 0..n_stack_pages {
        let paddr = heap_phys + (i * 0x1000);
        let vaddr = higher_half_heap_base + (i * 0x1000);

        paging::map_address(&mut pf_allocator, paddr, vaddr);
    }

    println!("Initialization complete, calling kernel entry point...");

    let idt_phys: usize = unsafe { (&long_mode_idt as *const InterruptDescriptorTable) as usize };
    let loader_info = KernelLoaderInfo {
        multiboot_info: &mb,
        idt_phys: unsafe { &mut long_mode_idt as *mut InterruptDescriptorTable },
        heap_pages: n_heap_pages
    };

    /* Let's cross our fingers and hope this works... */
    unsafe {
        higher_half_trampoline(
            kernel_header.entry_point(),
            higher_half_stack_addr,
            &loader_info as *const KernelLoaderInfo as usize
        );
    }

    panic!("kernel entry failed");
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
