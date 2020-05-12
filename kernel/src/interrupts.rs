mod exceptions;
mod handler;
mod idt;

// use crate::task;
pub use handler::{register_handler, unregister_handler, InterruptHandlerStatus};
pub use idt::{claim_idt_page, initialize_idt};

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
