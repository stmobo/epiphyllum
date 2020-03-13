use x86_64::structures::idt::{
    HandlerFunc, InterruptDescriptorTable, InterruptStackFrame, PageFaultErrorCode,
};

use crate::malloc::PhysicalMemory;
use crate::paging::KERNEL_BASE;

static mut IDT_PAGE: Option<PhysicalMemory> = None;
static mut IDT: Option<&'static mut InterruptDescriptorTable> = None;

#[repr(C, packed)]
struct IDTDescriptor {
    size: u16,
    offset: u64,
}

fn load_idt(idt_addr: usize) {
    use core::mem;

    let idt_size = mem::size_of::<InterruptDescriptorTable>() - 1;
    unsafe {
        let descriptor = IDTDescriptor {
            size: idt_size as u16,
            offset: idt_addr as u64,
        };

        asm!("lidt [$0]" :: "r"(&descriptor) :: "volatile", "intel");
    }
}

pub fn initialize_idt(idt: &'static mut InterruptDescriptorTable) {
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

    unsafe {
        load_idt((idt as *mut InterruptDescriptorTable) as usize);
        IDT = Some(idt);
    }
}

pub fn claim_idt_page(addr: usize) {
    unsafe {
        IDT_PAGE = PhysicalMemory::new_at(addr, 0x1000);
        if !IDT_PAGE.is_some() {
            panic!("could not claim IDT physical memory page");
        }
    }
}

pub fn register_handler(vector: usize, func: HandlerFunc) {
    unsafe {
        if let Some(idt) = IDT.as_deref_mut() {
            idt[vector].set_handler_fn(func);
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub struct StackFrame {
    pub frame_ip: usize,
    pub frame_bp: usize,
}

#[derive(Debug, Copy, Clone)]
#[repr(transparent)]
pub struct StackFrameIterator {
    cur_frame: StackFrame,
}

impl StackFrameIterator {
    fn new() -> StackFrameIterator {
        unsafe {
            let mut frame_ip: usize;
            let mut frame_bp: usize;

            asm!("mov $0, [rbp]" : "=r"(frame_bp) ::: "intel");
            asm!("mov $0, [rbp+8]" : "=r"(frame_ip) ::: "intel");

            StackFrameIterator {
                cur_frame: StackFrame { frame_ip, frame_bp },
            }
        }
    }
}

impl Iterator for StackFrameIterator {
    type Item = StackFrame;

    fn next(&mut self) -> Option<Self::Item> {
        let frame_bp = self.cur_frame.frame_bp;
        if frame_bp < KERNEL_BASE {
            return None;
        }

        let ret_frame = self.cur_frame;
        unsafe {
            let frame_bp = frame_bp as *const usize;

            self.cur_frame.frame_ip = *(frame_bp.offset(1));
            self.cur_frame.frame_bp = *frame_bp;
        }

        Some(ret_frame)
    }
}

pub fn trace_stack() -> impl Iterator<Item = StackFrame> {
    let mut it = StackFrameIterator::new();
    it.next();
    it.next();
    it.filter(|frame| frame.frame_ip >= KERNEL_BASE)
}

extern "x86-interrupt" fn divide_error(isf: &mut InterruptStackFrame) {
    panic!(
        "divide-by-zero (#DE) at {:#016x}",
        isf.instruction_pointer.as_u64()
    );
}

extern "x86-interrupt" fn debug_exception(isf: &mut InterruptStackFrame) {
    println!(
        "debug interrupt at {:#016x}?",
        isf.instruction_pointer.as_u64()
    );
}

extern "x86-interrupt" fn nmi(isf: &mut InterruptStackFrame) {
    panic!("NMI at {:#016x}", isf.instruction_pointer.as_u64());
}

extern "x86-interrupt" fn breakpoint(isf: &mut InterruptStackFrame) {
    println!(
        "ignoring breakpoint at {:#016x}",
        isf.instruction_pointer.as_u64()
    );
}

extern "x86-interrupt" fn overflow_error(isf: &mut InterruptStackFrame) {
    panic!(
        "overflow exception (#OF) at {:#016x}",
        isf.instruction_pointer.as_u64()
    );
}

extern "x86-interrupt" fn bound_range_exceeded(isf: &mut InterruptStackFrame) {
    panic!(
        "bound range exceeded (#BR) at {:#016x}",
        isf.instruction_pointer.as_u64()
    );
}

extern "x86-interrupt" fn invalid_instruction_error(isf: &mut InterruptStackFrame) {
    panic!(
        "invalid instruction (#UD) at {:#016x}",
        isf.instruction_pointer.as_u64()
    );
}

extern "x86-interrupt" fn device_not_available_error(isf: &mut InterruptStackFrame) {
    panic!(
        "device not available (#NM) at {:#016x}",
        isf.instruction_pointer.as_u64()
    );
}

extern "x86-interrupt" fn double_fault_error(_isf: &mut InterruptStackFrame, _: u64) -> ! {
    panic!("double fault (#DF) error");
}

extern "x86-interrupt" fn invalid_tss_error(isf: &mut InterruptStackFrame, _code: u64) {
    panic!(
        "invalid TSS error (#TS) at {:#016x}",
        isf.instruction_pointer.as_u64()
    );
}

extern "x86-interrupt" fn segment_not_present_error(isf: &mut InterruptStackFrame, _code: u64) {
    panic!(
        "segment not present error (#NP) at {:#016x}",
        isf.instruction_pointer.as_u64()
    );
}

extern "x86-interrupt" fn stack_segment_fault(isf: &mut InterruptStackFrame, _code: u64) {
    panic!(
        "stack segment fault (#SS) at {:#016x}",
        isf.instruction_pointer.as_u64()
    );
}

extern "x86-interrupt" fn protection_fault(isf: &mut InterruptStackFrame, code: u64) {
    panic!(
        "general protection fault (#GP) at {:#016x} (code {})",
        isf.instruction_pointer.as_u64(),
        code
    );
}

extern "x86-interrupt" fn page_fault(isf: &mut InterruptStackFrame, _code: PageFaultErrorCode) {
    panic!(
        "unhandled page fault (#PG) at {:#016x}",
        isf.instruction_pointer.as_u64()
    );
}

extern "x86-interrupt" fn fp_fault(isf: &mut InterruptStackFrame) {
    panic!(
        "x87 floating point error (#MF) at {:#016x}",
        isf.instruction_pointer.as_u64()
    );
}

extern "x86-interrupt" fn alignment_check(isf: &mut InterruptStackFrame, _code: u64) {
    panic!(
        "alignment check error (#AC) at {:#016x}",
        isf.instruction_pointer.as_u64()
    );
}

extern "x86-interrupt" fn machine_check(isf: &mut InterruptStackFrame) -> ! {
    panic!(
        "machine check error (#MC) at {:#016x}",
        isf.instruction_pointer.as_u64()
    );
}

extern "x86-interrupt" fn simd_error(isf: &mut InterruptStackFrame) {
    panic!(
        "SIMD FP error (#XF) at {:#016x}",
        isf.instruction_pointer.as_u64()
    );
}

extern "x86-interrupt" fn virtualization_error(isf: &mut InterruptStackFrame) {
    panic!(
        "virtualization error (#VE) at {:#016x}",
        isf.instruction_pointer.as_u64()
    );
}

extern "x86-interrupt" fn security_exception(isf: &mut InterruptStackFrame, _code: u64) {
    panic!(
        "security exception (#SX) at {:#016x}",
        isf.instruction_pointer.as_u64()
    );
}

extern "x86-interrupt" fn unhandled_interrupt(_isf: &mut InterruptStackFrame) {
    panic!("unhandled interrupt");
}
