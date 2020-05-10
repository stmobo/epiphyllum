use super::InterruptFrame;

pub fn unhandled_exception(frame: &mut InterruptFrame) {
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
    panic!(
        "unhandled divide-by-zero error (#DE) at {:#016x}",
        frame.rip
    );
}

fn debug_exception(frame: &InterruptFrame) {
    println!("unhandled debug interrupt at {:#016x}?", frame.rip);
}

fn nmi(frame: &InterruptFrame) {
    panic!("unhandled NMI at {:#016x}", frame.rip);
}

fn breakpoint(frame: &InterruptFrame) {
    println!("ignoring breakpoint at {:#016x}", frame.rip);
}

fn overflow_error(frame: &InterruptFrame) {
    panic!("unhandled overflow exception (#OF) at {:#016x}", frame.rip);
}

fn bound_range_exceeded(frame: &InterruptFrame) {
    panic!(
        "unhandled bound range exceeded error(#BR) at {:#016x}",
        frame.rip
    );
}

fn invalid_instruction_error(frame: &InterruptFrame) {
    panic!("unhandled invalid instruction (#UD) at {:#016x}", frame.rip);
}

fn device_not_available_error(frame: &InterruptFrame) {
    panic!(
        "unhandled device not available error(#NM) at {:#016x}",
        frame.rip
    );
}

fn double_fault_error(_frame: &InterruptFrame) -> ! {
    panic!("unhandled double fault (#DF) error");
}

fn invalid_tss_error(frame: &InterruptFrame) {
    panic!("unhandled invalid TSS error (#TS) at {:#016x}", frame.rip);
}

fn segment_not_present_error(frame: &InterruptFrame) {
    panic!(
        "unhandled segment not present error (#NP) at {:#016x}",
        frame.rip
    );
}

fn stack_segment_fault(frame: &InterruptFrame) {
    panic!("unhandled stack segment fault (#SS) at {:#016x}", frame.rip);
}

fn protection_fault(frame: &InterruptFrame) {
    panic!(
        "unhandled general protection fault (#GP) at {:#016x}",
        frame.rip,
    );
}

fn page_fault(frame: &InterruptFrame) {
    let cr2 = crate::asm::get_cr2();

    panic!(
        "unhandled page fault (#PG) at {:#016x}\n    faulting address: {:#016x}\n    error code: {:#08x}\n   ",
        frame.rip, cr2, frame.error_code
    );
}

fn fp_fault(frame: &InterruptFrame) {
    panic!(
        "unhandled x87 floating point error (#MF) at {:#016x}",
        frame.rip
    );
}

fn alignment_check(frame: &InterruptFrame) {
    panic!(
        "unhandled alignment check error (#AC) at {:#016x}",
        frame.rip
    );
}

fn machine_check(frame: &InterruptFrame) -> ! {
    panic!("unhandled machine check error (#MC) at {:#016x}", frame.rip);
}

fn simd_error(frame: &InterruptFrame) {
    panic!("unhandled SIMD FP error (#XF) at {:#016x}", frame.rip);
}

fn virtualization_error(frame: &InterruptFrame) {
    panic!(
        "unhandled virtualization error (#VE) at {:#016x}",
        frame.rip
    );
}

fn security_exception(frame: &InterruptFrame) {
    panic!("unhandled security exception (#SX) at {:#016x}", frame.rip);
}
