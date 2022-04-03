use core::mem;
use core::arch::asm;

static KERNEL_GDT: GDT = GDT::kernel_gdt();

#[repr(C)]
struct GDTEntry {
    limit_0_15: u16,
    base_0_15: u16,
    base_16_23: u8,
    access: u8,
    lim_flags: u8,
    base_24_31: u8,
}

impl GDTEntry {
    const fn null_segment() -> GDTEntry {
        GDTEntry {
            limit_0_15: 0,
            base_0_15: 0,
            base_16_23: 0,
            access: 0,
            lim_flags: 0,
            base_24_31: 0,
        }
    }

    const fn kernel_code_segment() -> GDTEntry {
        GDTEntry {
            limit_0_15: 0xFFFF,
            base_0_15: 0,
            base_16_23: 0,
            access: 0b10011010,
            lim_flags: 0b10101111,
            base_24_31: 0,
        }
    }

    const fn kernel_data_segment() -> GDTEntry {
        GDTEntry {
            limit_0_15: 0xFFFF,
            base_0_15: 0,
            base_16_23: 0,
            access: 0b10010010,
            lim_flags: 0b11001111,
            base_24_31: 0,
        }
    }
}

#[allow(dead_code)]
#[repr(transparent)]
struct GDT {
    entries: [GDTEntry; 3],
}

impl GDT {
    const fn kernel_gdt() -> GDT {
        GDT {
            entries: [
                GDTEntry::null_segment(),
                GDTEntry::kernel_code_segment(),
                GDTEntry::kernel_data_segment(),
            ],
        }
    }
}

#[repr(C, packed)]
struct GDTDescriptor {
    size: u16,
    offset: u64,
}

pub fn initialize_gdt() {
    let gdt_addr: usize = (&KERNEL_GDT as *const GDT) as usize;
    let gdt_size = mem::size_of::<GDT>() - 1;
    unsafe {
        let descriptor = GDTDescriptor {
            size: gdt_size as u16,
            offset: gdt_addr as u64,
        };

        asm!(
            "lgdt [{0}]",
            in(reg) &descriptor
        );
    }
}
