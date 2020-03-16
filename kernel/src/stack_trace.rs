use crate::paging::KERNEL_BASE;

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
