use crate::malloc;

#[repr(C)]
struct IDTEntry {
    offset_1: u16,
    selector: u16,
    ist: u8,
    type_attr: u8,
    offset_2: u16,
    offset_3: u32,
    zero: u32,
}

#[repr(transparent)]
struct IDT {
    entries: [IDTEntry; 256],
}

#[repr(C, packed)]
struct IDTDescriptor {
    size: u16,
    offset: u64,
}

impl IDTEntry {
    fn set_address(&mut self, address: usize, present: bool) {
        self.offset_1 = (address & 0xFFFF) as u16;
        self.offset_2 = ((address >> 16) & 0xFFFF) as u16;
        self.offset_3 = ((address >> 32) & 0xFFFF_FFFF) as u32;
        self.selector = 0x08;
        self.ist = 0;
        if present {
            self.type_attr = 0x8E;
        } else {
            self.type_attr = 0x0E;
        }

        self.zero = 0;
    }
}

extern "C" {
    static exceptions_start: u8;
    static external_isr_start: u8;
}

fn load_idt(idt_addr: usize) {
    use core::mem;

    let idt_size = mem::size_of::<IDT>() - 1;
    unsafe {
        let descriptor = IDTDescriptor {
            size: idt_size as u16,
            offset: idt_addr as u64,
        };

        llvm_asm!("lidt [$0]" :: "r"(&descriptor) :: "volatile", "intel");
    }
}

pub unsafe fn initialize_idt(idt_addr: usize) {
    let idt = idt_addr as *mut IDT;
    let mut cur_addr = (&exceptions_start as *const u8) as usize;

    for i in 0..32 {
        (*idt).entries[i].set_address(cur_addr, true);
        cur_addr += 16;
    }

    cur_addr = (&external_isr_start as *const u8) as usize;
    for i in 32..256 {
        (*idt).entries[i].set_address(cur_addr, true);
        cur_addr += 16;
    }

    load_idt(idt_addr);
}

pub fn claim_idt_page(addr: usize) {
    malloc::physical_mem::allocate_at(addr, 0).expect("could not claim IDT physical memory page");
}
