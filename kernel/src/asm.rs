pub mod cpuid;

use crate::paging::{PageTable, PhysicalPointer};
use crate::structures::Bitmask64;

fn get_flags() -> u64 {
    let flags: u64;
    unsafe {
        llvm_asm!("pushfq; popq $0" : "=r"(flags) ::: "volatile");
    }

    return flags;
}

/// Gets the current value of CR0 (Control Register 0) on the current processor.
///
/// This contains various control flags.
/// For more details, see https://wiki.osdev.org/CPU_Registers_x86-64#CR0 .
pub fn get_cr0() -> Bitmask64 {
    let reg: u64;
    unsafe {
        llvm_asm!("mov %cr0, $0" : "=r"(reg) ::: "volatile");
    }

    Bitmask64(reg)
}

/// Sets the value of CR0.
///
/// # Safety
/// Changing the control flags in CR0 can have many effects on memory and the
/// runtime state of the system, therefore this function is unsafe.
///
/// The caller must ensure that a valid set of control flags are passed to this
/// function.
pub unsafe fn set_cr0(flags: Bitmask64) {
    llvm_asm!("mov $0, %cr0" :: "r"(flags.0) :: "volatile");
}

/// Gets the value of CR2.
///
/// When executed from a page fault interrupt handler, CR2 will contain the
/// virtual address that triggered the page fault.
pub fn get_cr2() -> usize {
    let cr2: u64;
    unsafe {
        llvm_asm!("mov %cr2, $0" : "=r"(cr2) ::: "volatile");
    }

    cr2 as usize
}

/// Gets the value of CR3.
///
/// This contains the current physical address of the PML4T.
pub fn get_cr3() -> PhysicalPointer<PageTable> {
    let reg: u64;
    unsafe {
        llvm_asm!("mov %cr3, $0" : "=r"(reg) ::: "volatile");
    }

    // If CR3 is invalid then we almost certainly have bigger problems.
    // But there's no harm in checking, right?
    PhysicalPointer::new(reg as usize).expect("CR3 is invalid?")
}

/// Sets the value of CR3.
///
/// This will load or reload new page table mappings, by changing the current
/// PML4T.
///
/// # Safety
/// This function will completely reload paging structures and mappings.
///
/// The caller must ensure that `pml4t` points to a valid page table, and
/// should remember that pointers into non-shared areas of the address space
/// now most likely point to (effectively) uninitialized data.
pub unsafe fn set_cr3(pml4t: PhysicalPointer<PageTable>) {
    llvm_asm!("mov $0, %cr3" :: "r"(pml4t.address() as u64) :: "volatile");
}

/// Flushes the TLB by reloading CR3 with the same value.
pub fn reload_cr3() {
    unsafe { set_cr3(get_cr3()) };
}

/// Gets the value of CR4.
///
/// Like CR0, this control register contains more feature enable flags.
pub fn get_cr4() -> Bitmask64 {
    let reg: u64;
    unsafe {
        llvm_asm!("mov %cr4, $0" : "=r"(reg) ::: "volatile");
    }

    Bitmask64(reg)
}

/// Sets the value of CR4.
///
/// # Safety
/// Changing the control flags in CR4 can have many effects on memory and the
/// runtime state of the system, therefore this function is unsafe.
///
/// The caller must ensure that a valid set of control flags are passed to this
/// function.
pub unsafe fn set_cr4(flags: Bitmask64) {
    llvm_asm!("mov $0, %cr4" :: "r"(flags.0) :: "volatile");
}

/// Flush a specific page from the TLB by using the `invlpg` instruction.
pub fn invlpg(page: usize) {
    let page = page as u64;
    unsafe {
        llvm_asm!("invlpg ($0)" :: "r"(page) :: "volatile");
    }
}

/// Enables SSE instructions in user mode.
///
/// This operation is idempotent.
pub fn initialize_sse() {
    unsafe {
        // set MP flag, clear EM flag
        let cr0 = get_cr0().set(1, true).set(2, false);

        // set OSFXSR and OSXMMEXCPT flags
        let cr4 = get_cr4().set(9, true).set(10, true);

        // SAFETY: The bitmask changes above should be valid, and they shouldn't
        // significantly affect kernel code (which does not use SSE).
        set_cr0(cr0);
        set_cr4(cr4);
    }
}

pub mod interrupts {
    /// Gets whether interrupts are enabled on the current processor by looking
    /// at the value of RFLAGS.
    pub fn enabled() -> bool {
        let flags = super::get_flags();
        (flags & (1 << 9)) != 0
    }

    /// Enables or disables interrupts on the current processor.
    ///
    /// # Safety
    /// Many functions require that interrupts are either enabled or (more often)
    /// disabled prior to calling them.
    /// If you ever set IF to a particular value, you most likely should also
    /// store the previous value of IF, then restore it after your work is
    /// complete. InterruptDisableGuard and NoIRQSpinlock both help here.
    pub unsafe fn set_if(enabled: bool) {
        if enabled {
            llvm_asm!("sti" :::: "volatile");
        } else {
            llvm_asm!("cli" :::: "volatile");
        }
    }

    /// A helper for disabling interrupts, while making sure that the previous
    /// interrupt flag value is saved and restored after exiting a scope.
    #[repr(transparent)]
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
    /// Read 8 bits in from an I/O port.
    ///
    /// # Safety
    /// This function can and may have arbitrary effects on hardware.
    pub unsafe fn inb(addr: u16) -> u8 {
        let ret: u8;
        llvm_asm!("inb %dx" : "={al}"(ret) : "{dx}"(addr) :: "volatile");
        ret
    }

    /// Read 16 bits in from an I/O port.
    ///
    /// # Safety
    /// This function can and may have arbitrary effects on hardware.
    pub unsafe fn inw(addr: u16) -> u16 {
        let ret: u16;
        llvm_asm!("inb %dx" : "={ax}"(ret) : "{dx}"(addr) :: "volatile");
        ret
    }

    /// Read 32 bits in from an I/O port.
    ///
    /// # Safety
    /// This function can and may have arbitrary effects on hardware.
    pub unsafe fn ind(addr: u16) -> u32 {
        let ret: u32;
        llvm_asm!("inl %dx" : "={eax}"(ret) : "{dx}"(addr) :: "volatile");
        ret
    }

    /// Write 8 bits out to an I/O port.
    ///
    /// # Safety
    /// This function can and may have arbitrary effects on hardware.
    pub unsafe fn outb(addr: u16, data: u8) {
        llvm_asm!("outb %al, %dx" :: "{dx}"(addr), "{al}"(data) :: "volatile");
    }

    /// Write 16 bits out to an I/O port.
    ///
    /// # Safety
    /// This function can and may have arbitrary effects on hardware.
    pub unsafe fn outw(addr: u16, data: u16) {
        llvm_asm!("outw %ax, %dx" :: "{dx}"(addr), "{ax}"(data) :: "volatile");
    }

    /// Write 32 bits out to an I/O port.
    ///
    /// # Safety
    /// This function can and may have arbitrary effects on hardware.
    pub unsafe fn outd(addr: u16, data: u32) {
        llvm_asm!("outl %eax, %dx" :: "{dx}"(addr), "{eax}"(data) :: "volatile");
    }

    /// Add a tiny pause to the program by outputting data to a dummy I/O port.
    pub fn io_wait() {
        unsafe {
            llvm_asm!("outb %al, $$0x80" :: "{al}"(0) :: "volatile");
        }
    }
}

pub mod msr {
    /// Read a 64-bit Model-Specific Register.
    pub fn rdmsr(register_id: u32) -> u64 {
        let lo: u32;
        let hi: u32;
        unsafe {
            llvm_asm!("rdmsr" : "={eax}"(lo), "={edx}"(hi) : "{ecx}"(register_id) :: "volatile");
        }
        ((hi as u64) << 32) | (lo as u64)
    }

    /// Write to 64-bit Model-Specific Register.
    ///
    /// # Safety
    /// This can potentially have many different effects on memory and system
    /// state. The caller must ensure that the register ID and value to be written
    /// form a valid combination.
    pub unsafe fn wrmsr(register_id: u32, value: u64) {
        let lo = (value & 0xFFFF_FFFF) as u32;
        let hi = ((value >> 32) & 0xFFFF_FFFF) as u32;
        llvm_asm!("wrmsr" :: "{ecx}"(register_id), "{eax}"(lo), "{edx}"(hi) :: "volatile");
    }
}
