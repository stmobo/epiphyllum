mod exceptions;
mod handler;
mod idt;

// use crate::task;
pub use handler::{register_handler, unregister_handler, InterruptHandlerStatus};
pub use idt::{claim_idt_page, initialize_idt};

use core::fmt;
use core::sync::atomic::{AtomicBool, Ordering};

use crate::task;

static INTERRUPT_CONTEXT_FLAG: AtomicBool = AtomicBool::new(false);

#[repr(C)]
pub struct GeneralRegisterState {
    pub r15: u64,
    pub r14: u64,
    pub r13: u64,
    pub r12: u64,
    pub r11: u64,
    pub r10: u64,
    pub r9: u64,
    pub r8: u64,
    pub rdi: u64,
    pub rsi: u64,
    pub rdx: u64,
    pub rcx: u64,
    pub rbx: u64,
    pub rax: u64,
    pub rbp: u64,
}

impl GeneralRegisterState {
    pub fn new() -> GeneralRegisterState {
        GeneralRegisterState {
            r15: 0,
            r14: 0,
            r13: 0,
            r12: 0,
            r11: 0,
            r10: 0,
            r9: 0,
            r8: 0,
            rdi: 0,
            rsi: 0,
            rdx: 0,
            rcx: 0,
            rbx: 0,
            rax: 0,
            rbp: 0,
        }
    }
}

#[repr(C)]
pub struct InterruptFrame {
    pub registers: GeneralRegisterState,
    pub interrupt_no: u64,
    pub error_code: u64,
    pub rip: u64,
    pub cs: u64,
    pub rflags: u64,
    pub rsp: u64,
    pub ss: u64,
}

impl InterruptFrame {
    pub fn new(start_addr: usize, rsp: usize) -> InterruptFrame {
        InterruptFrame {
            registers: GeneralRegisterState::new(),
            interrupt_no: 0,
            error_code: 0,
            rip: start_addr as u64,
            cs: 0x08,
            rflags: (1 << 9),
            rsp: rsp as u64,
            ss: 0x10,
        }
    }
}

impl fmt::Display for InterruptFrame {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "RIP: {:#018x}\n", self.rip)?;

        write!(
            f,
            "RAX: {:#018x}    RBX: {:#018x}\n",
            self.registers.rax, self.registers.rbx
        )?;

        write!(
            f,
            "RCX: {:#018x}    RDX: {:#018x}\n",
            self.registers.rcx, self.registers.rdx
        )?;

        write!(
            f,
            "RSI: {:#018x}    RDI: {:#018x}\n",
            self.registers.rsi, self.registers.rdi
        )?;

        write!(
            f,
            "R8 : {:#018x}    R9 : {:#018x}\n",
            self.registers.r8, self.registers.r9
        )?;

        write!(
            f,
            "R10: {:#018x}    R11: {:#018x}\n",
            self.registers.r10, self.registers.r11
        )?;

        write!(
            f,
            "R12: {:#018x}    R13: {:#018x}\n",
            self.registers.r12, self.registers.r13
        )?;

        write!(
            f,
            "R14: {:#018x}    R15: {:#018x}\n",
            self.registers.r14, self.registers.r15
        )?;

        write!(
            f,
            "RBP: {:#018x}    RSP: {:#018x}\n",
            self.registers.rbp, self.rsp
        )?;

        write!(
            f,
            "Flags: {:#010x}  CS: {:#06x}  SS: {:#06x}\n",
            self.rflags, self.cs, self.ss
        )?;

        write!(
            f,
            "Interrupt: {:#04x} ({})    Error Code: {:#010x} ({})",
            self.interrupt_no, self.interrupt_no, self.error_code, self.error_code
        )
    }
}

pub fn in_interrupt_context() -> bool {
    INTERRUPT_CONTEXT_FLAG.load(Ordering::Relaxed)
}

#[no_mangle]
pub extern "C" fn kernel_entry(frame: *mut InterruptFrame) -> *mut InterruptFrame {
    INTERRUPT_CONTEXT_FLAG.store(true, Ordering::Relaxed);

    task::scheduler().update_cur_context(frame);
    handler::handle_interrupt(unsafe { &mut *frame });

    INTERRUPT_CONTEXT_FLAG.store(false, Ordering::Relaxed);

    if let Some(new_ctx) = task::current_context() {
        new_ctx
    } else {
        frame
    }
}
