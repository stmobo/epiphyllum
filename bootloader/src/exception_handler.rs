use x86_64::structures::idt::{InterruptDescriptorTable, InterruptStackFrame, PageFaultErrorCode};

pub fn initialize_idt(idt: &mut InterruptDescriptorTable) {
    idt.divide_error.set_handler_fn(divide_error);
    idt.debug.set_handler_fn(debug_exception);
    idt.non_maskable_interrupt.set_handler_fn(nmi);
    idt.breakpoint.set_handler_fn(breakpoint);
    idt.overflow.set_handler_fn(overflow_error);
    idt.bound_range_exceeded
        .set_handler_fn(bound_range_exceeded);
    idt.invalid_opcode.set_handler_fn(invalid_instruction_error);
    idt.device_not_available
        .set_handler_fn(device_not_available_error);
    idt.double_fault.set_handler_fn(double_fault_error);
    idt.invalid_tss.set_handler_fn(invalid_tss_error);
    idt.segment_not_present
        .set_handler_fn(segment_not_present_error);
    idt.stack_segment_fault.set_handler_fn(stack_segment_fault);
    idt.general_protection_fault
        .set_handler_fn(protection_fault);
    idt.page_fault.set_handler_fn(page_fault);
    idt.x87_floating_point.set_handler_fn(fp_fault);
    idt.alignment_check.set_handler_fn(alignment_check);
    idt.machine_check.set_handler_fn(machine_check);
    idt.simd_floating_point.set_handler_fn(simd_error);
    idt.virtualization.set_handler_fn(virtualization_error);
    idt.security_exception.set_handler_fn(security_exception);

    for i in 32..256 {
        idt[i].set_handler_fn(unhandled_interrupt);
    }
}

extern "x86-interrupt" fn divide_error(isf: InterruptStackFrame) {
    panic!(
        "divide-by-zero (#DE) at {:#016x}",
        isf.instruction_pointer.as_u64()
    );
}

extern "x86-interrupt" fn debug_exception(isf: InterruptStackFrame) {
    println!(
        "debug interrupt at {:#016x}?",
        isf.instruction_pointer.as_u64()
    );
}

extern "x86-interrupt" fn nmi(isf: InterruptStackFrame) {
    panic!("NMI at {:#016x}", isf.instruction_pointer.as_u64());
}

extern "x86-interrupt" fn breakpoint(isf: InterruptStackFrame) {
    println!(
        "ignoring breakpoint at {:#016x}",
        isf.instruction_pointer.as_u64()
    );
}

extern "x86-interrupt" fn overflow_error(isf: InterruptStackFrame) {
    panic!(
        "overflow exception (#OF) at {:#016x}",
        isf.instruction_pointer.as_u64()
    );
}

extern "x86-interrupt" fn bound_range_exceeded(isf: InterruptStackFrame) {
    panic!(
        "bound range exceeded (#BR) at {:#016x}",
        isf.instruction_pointer.as_u64()
    );
}

extern "x86-interrupt" fn invalid_instruction_error(isf: InterruptStackFrame) {
    panic!(
        "invalid instruction (#UD) at {:#016x}",
        isf.instruction_pointer.as_u64()
    );
}

extern "x86-interrupt" fn device_not_available_error(isf: InterruptStackFrame) {
    panic!(
        "device not available (#NM) at {:#016x}",
        isf.instruction_pointer.as_u64()
    );
}

extern "x86-interrupt" fn double_fault_error(_isf: InterruptStackFrame, _: u64) -> ! {
    panic!("double fault (#DF) error");
}

extern "x86-interrupt" fn invalid_tss_error(isf: InterruptStackFrame, _code: u64) {
    panic!(
        "invalid TSS error (#TS) at {:#016x}",
        isf.instruction_pointer.as_u64()
    );
}

extern "x86-interrupt" fn segment_not_present_error(isf: InterruptStackFrame, _code: u64) {
    panic!(
        "segment not present error (#NP) at {:#016x}",
        isf.instruction_pointer.as_u64()
    );
}

extern "x86-interrupt" fn stack_segment_fault(isf: InterruptStackFrame, _code: u64) {
    panic!(
        "stack segment fault (#SS) at {:#016x}",
        isf.instruction_pointer.as_u64()
    );
}

extern "x86-interrupt" fn protection_fault(isf: InterruptStackFrame, _code: u64) {
    panic!(
        "general protection fault (#GP) at {:#016x}",
        isf.instruction_pointer.as_u64()
    );
}

extern "x86-interrupt" fn page_fault(isf: InterruptStackFrame, _code: PageFaultErrorCode) {
    panic!(
        "unhandled page fault (#GP) at {:#016x}",
        isf.instruction_pointer.as_u64()
    );
}

extern "x86-interrupt" fn fp_fault(isf: InterruptStackFrame) {
    panic!(
        "x87 floating point error (#MF) at {:#016x}",
        isf.instruction_pointer.as_u64()
    );
}

extern "x86-interrupt" fn alignment_check(isf: InterruptStackFrame, _code: u64) {
    panic!(
        "alignment check error (#AC) at {:#016x}",
        isf.instruction_pointer.as_u64()
    );
}

extern "x86-interrupt" fn machine_check(isf: InterruptStackFrame) -> ! {
    panic!(
        "machine check error (#MC) at {:#016x}",
        isf.instruction_pointer.as_u64()
    );
}

extern "x86-interrupt" fn simd_error(isf: InterruptStackFrame) {
    panic!(
        "SIMD FP error (#XF) at {:#016x}",
        isf.instruction_pointer.as_u64()
    );
}

extern "x86-interrupt" fn virtualization_error(isf: InterruptStackFrame) {
    panic!(
        "virtualization error (#VE) at {:#016x}",
        isf.instruction_pointer.as_u64()
    );
}

extern "x86-interrupt" fn security_exception(isf: InterruptStackFrame, _code: u64) {
    panic!(
        "security exception (#SX) at {:#016x}",
        isf.instruction_pointer.as_u64()
    );
}

extern "x86-interrupt" fn unhandled_interrupt(_isf: InterruptStackFrame) {
    panic!("unhandled interrupt");
}
