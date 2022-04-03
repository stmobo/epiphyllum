pub mod cpuid;

use crate::structures::Bitmask64;
use core::arch::asm;

fn get_flags() -> u64 {
    let flags: u64;
    unsafe {
        asm!(
            "pushf",
            "pop {0}",
            out(reg) flags
        );
    }

    flags
}

/// Gets the current value of CR0 (Control Register 0) on the current processor.
///
/// This contains various control flags.
/// For more details, see https://wiki.osdev.org/CPU_Registers_x86-64#CR0 .
pub fn get_cr0() -> Bitmask64 {
    let out: u64;
    unsafe {
        asm!(
            "mov {0}, cr0",
            out(reg) out
        );
    }

    Bitmask64(out)
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
    asm!(
        "mov cr0, {0}",
        in(reg) flags.0
    );
}

/// Gets the value of CR2.
///
/// When executed from a page fault interrupt handler, CR2 will contain the
/// virtual address that triggered the page fault.
pub fn get_cr2() -> usize {
    let out: u64;
    unsafe {
        asm!(
            "mov {0}, cr2",
            out(reg) out
        );
    }

    out as usize
}

/// Gets the value of CR3.
///
/// This contains the current physical address of the PML4T.
pub fn get_cr3() -> usize {
    let out: u64;
    unsafe {
        asm!(
            "mov {0}, cr3",
            out(reg) out
        );
    }

    out as usize
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
pub unsafe fn set_cr3(pml4t_addr: usize) {
    asm!(
        "mov cr3, {0}",
        in(reg) pml4t_addr
    );
}

/// Flushes the TLB by reloading CR3 with the same value.
pub fn reload_cr3() {
    unsafe {
        asm!(
            "mov {tmp}, cr3",
            "mov cr3, {tmp}",
            tmp = out(reg) _
        );
    }
}

/// Gets the value of CR4.
///
/// Like CR0, this control register contains more feature enable flags.
pub fn get_cr4() -> Bitmask64 {
    let out: u64;
    unsafe {
        asm!(
            "mov {0}, cr4",
            out(reg) out
        );
    }
    Bitmask64(out)
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
    asm!(
        "mov cr4, {0}",
        in(reg) flags.0
    );
}

/// Flush a specific page from the TLB by using the `invlpg` instruction.
pub fn invlpg(page: usize) {
    unsafe {
        asm!(
            "invlpg [{0}]",
            in(reg) (page as u64)
        );
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
    use core::arch::asm;

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
            asm!("sti");
        } else {
            asm!("cli");
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
    use core::arch::asm;

    /// Read 8 bits in from an I/O port.
    ///
    /// # Safety
    /// This function can and may have arbitrary effects on hardware.
    pub unsafe fn inb(addr: u16) -> u8 {
        let ret: u8;
        asm!(
            "in al, dx",
            in("dx") addr,
            out("al") ret
        );

        ret
    }

    /// Read 16 bits in from an I/O port.
    ///
    /// # Safety
    /// This function can and may have arbitrary effects on hardware.
    pub unsafe fn inw(addr: u16) -> u16 {
        let ret: u16;
        asm!(
            "in ax, dx",
            in("dx") addr,
            out("ax") ret
        );

        ret
    }

    /// Read 32 bits in from an I/O port.
    ///
    /// # Safety
    /// This function can and may have arbitrary effects on hardware.
    pub unsafe fn ind(addr: u16) -> u32 {
        let ret: u32;
        asm!(
            "in eax, dx",
            in("dx") addr,
            out("eax") ret
        );

        ret
    }

    /// Write 8 bits out to an I/O port.
    ///
    /// # Safety
    /// This function can and may have arbitrary effects on hardware.
    pub unsafe fn outb(addr: u16, data: u8) {
        asm!(
            "out dx, al",
            in("dx") addr,
            in("al") data
        );
    }

    /// Write 16 bits out to an I/O port.
    ///
    /// # Safety
    /// This function can and may have arbitrary effects on hardware.
    pub unsafe fn outw(addr: u16, data: u16) {
        asm!(
            "out dx, ax",
            in("dx") addr,
            in("ax") data
        );
    }

    /// Write 32 bits out to an I/O port.
    ///
    /// # Safety
    /// This function can and may have arbitrary effects on hardware.
    pub unsafe fn outd(addr: u16, data: u32) {
        asm!(
            "out dx, eax",
            in("dx") addr,
            in("eax") data
        );
    }

    /// Add a tiny pause to the program by outputting data to a dummy I/O port.
    pub fn io_wait() {
        unsafe {
            asm!(
                "out 0x80, al",
                out("al") _
            );
        }
    }
}

pub mod msr {
    use core::arch::asm;

    /// Read a 64-bit Model-Specific Register.
    pub fn rdmsr(register_id: u32) -> u64 {
        let lo: u32;
        let hi: u32;
        unsafe {
            asm!(
                "rdmsr",
                out("eax") lo,
                out("edx") hi,
                in("ecx") register_id
            );
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
        asm!(
            "wrmsr",
            in("eax") lo,
            in("edx") hi,
            in("ecx") register_id
        );
    }
}
