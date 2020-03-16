use super::InterruptFrame;

pub fn handle_exception(frame: &InterruptFrame) {
    match frame.interrupt_no {
        0 => divide_error(frame),
        1 => debug_exception(frame),
        2 => nmi(frame),
        3 => breakpoint(frame),
        4 => overflow_error(frame),
        5 => bound_range_exceeded(frame),
        6 => invalid_instruction_error(frame),
        7 => device_not_available_error(frame),
        8 => double_fault_error(frame),
        10 => invalid_tss_error(frame),
        11 => segment_not_present_error(frame),
        12 => stack_segment_fault(frame),
        13 => protection_fault(frame),
        14 => page_fault(frame),
        16 => fp_fault(frame),
        17 => alignment_check(frame),
        18 => machine_check(frame),
        19 => simd_error(frame),
        20 => virtualization_error(frame),
        30 => security_exception(frame),
        _ => panic!(
            "unrecognized exception number {} at {:#016x}",
            frame.interrupt_no, frame.rip
        ),
    }
}

fn divide_error(frame: &InterruptFrame) {
    panic!("divide-by-zero (#DE) at {:#016x}", frame.rip);
}

fn debug_exception(frame: &InterruptFrame) {
    println!("debug interrupt at {:#016x}?", frame.rip);
}

fn nmi(frame: &InterruptFrame) {
    panic!("NMI at {:#016x}", frame.rip);
}

fn breakpoint(frame: &InterruptFrame) {
    println!("ignoring breakpoint at {:#016x}", frame.rip);
}

fn overflow_error(frame: &InterruptFrame) {
    panic!("overflow exception (#OF) at {:#016x}", frame.rip);
}

fn bound_range_exceeded(frame: &InterruptFrame) {
    panic!("bound range exceeded (#BR) at {:#016x}", frame.rip);
}

fn invalid_instruction_error(frame: &InterruptFrame) {
    panic!("invalid instruction (#UD) at {:#016x}", frame.rip);
}

fn device_not_available_error(frame: &InterruptFrame) {
    panic!("device not available (#NM) at {:#016x}", frame.rip);
}

fn double_fault_error(frame: &InterruptFrame) -> ! {
    panic!("double fault (#DF) error");
}

fn invalid_tss_error(frame: &InterruptFrame) {
    panic!("invalid TSS error (#TS) at {:#016x}", frame.rip);
}

fn segment_not_present_error(frame: &InterruptFrame) {
    panic!("segment not present error (#NP) at {:#016x}", frame.rip);
}

fn stack_segment_fault(frame: &InterruptFrame) {
    panic!("stack segment fault (#SS) at {:#016x}", frame.rip);
}

fn protection_fault(frame: &InterruptFrame) {
    panic!("general protection fault (#GP) at {:#016x}", frame.rip,);
}

fn page_fault(frame: &InterruptFrame) {
    panic!("unhandled page fault (#PG) at {:#016x}", frame.rip);
}

fn fp_fault(frame: &InterruptFrame) {
    panic!("x87 floating point error (#MF) at {:#016x}", frame.rip);
}

fn alignment_check(frame: &InterruptFrame) {
    panic!("alignment check error (#AC) at {:#016x}", frame.rip);
}

fn machine_check(frame: &InterruptFrame) -> ! {
    panic!("machine check error (#MC) at {:#016x}", frame.rip);
}

fn simd_error(frame: &InterruptFrame) {
    panic!("SIMD FP error (#XF) at {:#016x}", frame.rip);
}

fn virtualization_error(frame: &InterruptFrame) {
    panic!("virtualization error (#VE) at {:#016x}", frame.rip);
}

fn security_exception(frame: &InterruptFrame) {
    panic!("security exception (#SX) at {:#016x}", frame.rip);
}
