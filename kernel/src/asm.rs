pub mod cpuid;

fn get_flags() -> u64 {
    let flags: u64;
    unsafe {
        llvm_asm!("pushfq; popq $0" : "=r"(flags) ::: "volatile");
    }

    return flags;
}

pub fn get_cr2() -> usize {
    let cr2: u64;
    unsafe {
        llvm_asm!("mov %cr2, $0" : "=r"(cr2) ::: "volatile");
    }

    return cr2 as usize;
}

pub mod interrupts {
    pub fn enabled() -> bool {
        let flags = super::get_flags();
        (flags & (1 << 9)) != 0
    }

    pub unsafe fn set_if(enabled: bool) {
        if enabled {
            llvm_asm!("sti" :::: "volatile");
        } else {
            llvm_asm!("cli" :::: "volatile");
        }
    }

    pub struct InterruptDisableGuard(bool);
    impl InterruptDisableGuard {
        pub fn new() -> InterruptDisableGuard {
            unsafe {
                let ret = InterruptDisableGuard(enabled());
                set_if(false);

                ret
            }
        }
    }

    impl Drop for InterruptDisableGuard {
        fn drop(&mut self) {
            unsafe {
                set_if(self.0);
            }
        }
    }
}

pub mod ports {
    pub unsafe fn inb(addr: u16) -> u8 {
        let ret: u8;
        llvm_asm!("inb %dx" : "={al}"(ret) : "{dx}"(addr) :: "volatile");
        ret
    }

    pub unsafe fn inw(addr: u16) -> u16 {
        let ret: u16;
        llvm_asm!("inb %dx" : "={ax}"(ret) : "{dx}"(addr) :: "volatile");
        ret
    }

    pub unsafe fn ind(addr: u16) -> u32 {
        let ret: u32;
        llvm_asm!("inl %dx" : "={eax}"(ret) : "{dx}"(addr) :: "volatile");
        ret
    }

    pub unsafe fn outb(addr: u16, data: u8) {
        llvm_asm!("outb %al, %dx" :: "{dx}"(addr), "{al}"(data) :: "volatile");
    }

    pub unsafe fn outw(addr: u16, data: u16) {
        llvm_asm!("outw %ax, %dx" :: "{dx}"(addr), "{ax}"(data) :: "volatile");
    }

    pub unsafe fn outd(addr: u16, data: u32) {
        llvm_asm!("outl %eax, %dx" :: "{dx}"(addr), "{eax}"(data) :: "volatile");
    }

    pub fn io_wait() {
        unsafe {
            llvm_asm!("outb %al, $$0x80" :: "{al}"(0) :: "volatile");
        }
    }
}

pub mod msr {
    pub unsafe fn rdmsr(register_id: u32) -> u64 {
        let lo: u32;
        let hi: u32;
        llvm_asm!("rdmsr" : "={eax}"(lo), "={edx}"(hi) : "{ecx}"(register_id) :: "volatile");
        ((hi as u64) << 32) | (lo as u64)
    }

    pub unsafe fn wrmsr(register_id: u32, value: u64) {
        let lo = (value & 0xFFFF_FFFF) as u32;
        let hi = ((value >> 32) & 0xFFFF_FFFF) as u32;
        llvm_asm!("wrmsr" :: "{ecx}"(register_id), "{eax}"(lo), "{edx}"(hi) :: "volatile");
    }
}
