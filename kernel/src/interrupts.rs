mod exceptions;
mod handler;
mod idt;

pub use handler::{register_handler, InterruptHandlerStatus};
pub use idt::{claim_idt_page, initialize_idt};

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

#[no_mangle]
pub extern "C" fn kernel_entry(frame: InterruptFrame) {
    if frame.interrupt_no < 32 {
        return exceptions::handle_exception(&frame);
    } else {
        return handler::handle_interrupt(&frame);
    }
}
