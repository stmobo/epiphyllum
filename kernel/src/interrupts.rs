mod exceptions;
mod handler;
mod idt;

// use crate::task;
pub use handler::{register_handler, unregister_handler, InterruptHandlerStatus};
pub use idt::{claim_idt_page, initialize_idt};

use core::sync::atomic::{AtomicBool, Ordering};

static INTERRUPT_CONTEXT_FLAG: AtomicBool = AtomicBool::new(false);

#[repr(C)]
pub struct GeneralRegisterState {
    r15: u64,
    r14: u64,
    r13: u64,
    r12: u64,
    r11: u64,
    r10: u64,
    r9: u64,
    r8: u64,
    rdi: u64,
    rsi: u64,
    rdx: u64,
    rcx: u64,
    rbx: u64,
    rax: u64,
    rbp: u64,
}

impl GeneralRegisterState {
    pub fn new(rdi: u64) -> GeneralRegisterState {
        GeneralRegisterState {
            r15: 0,
            r14: 0,
            r13: 0,
            r12: 0,
            r11: 0,
            r10: 0,
            r9: 0,
            r8: 0,
            rdi,
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
    gpr: GeneralRegisterState,
    interrupt_no: u64,
    error_code: u64,
    rip: u64,
    cs: u64,
    rflags: u64,
    rsp: u64,
    ss: u64,
}

impl InterruptFrame {
    pub fn new(start_addr: usize, rsp: u64, init_arg: u64) -> InterruptFrame {
        InterruptFrame {
            gpr: GeneralRegisterState::new(init_arg),
            interrupt_no: 0,
            error_code: 0,
            rip: start_addr as u64,
            cs: 0x08,
            rflags: (1 << 9),
            rsp,
            ss: 0x10,
        }
    }
}

pub fn in_interrupt_context() -> bool {
    INTERRUPT_CONTEXT_FLAG.load(Ordering::Relaxed)
}

#[no_mangle]
pub extern "C" fn kernel_entry(mut frame: InterruptFrame) -> *mut InterruptFrame {
    INTERRUPT_CONTEXT_FLAG.store(true, Ordering::Relaxed);

    handler::handle_interrupt(&mut frame);

    INTERRUPT_CONTEXT_FLAG.store(false, Ordering::Relaxed);

    &mut frame
    /*
    unsafe {
        let cur_task = task::get_current_task();
        if cur_task != ptr::null_mut() && (*cur_task).get_context() != ptr::null_mut() {
            (*cur_task).get_context()
        } else {
            &mut frame
        }
    }

    */
}
