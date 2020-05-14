use crate::paging;

#[derive(Debug, Copy, Clone)]
pub struct StackFrame {
    pub frame_ip: usize,
    pub frame_bp: usize,
}

#[derive(Debug, Copy, Clone)]
#[repr(transparent)]
pub struct StackFrameIterator {
    cur_frame: Option<StackFrame>,
}

impl StackFrameIterator {
    fn new() -> StackFrameIterator {
        unsafe {
            let mut frame_ip: usize;
            let mut frame_bp: usize;

            llvm_asm!("mov $0, [rbp]" : "=r"(frame_bp) ::: "intel");
            llvm_asm!("mov $0, [rbp+8]" : "=r"(frame_ip) ::: "intel");

            StackFrameIterator {
                cur_frame: Some(StackFrame { frame_ip, frame_bp }),
            }
        }
    }
}

impl Iterator for StackFrameIterator {
    type Item = StackFrame;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(frame) = self.cur_frame.take() {
            let frame_bp = frame.frame_bp;
            if frame_bp < paging::KERNEL_HEAP_BASE {
                return None;
            }

            if paging::get_mapping(frame_bp).is_some() {
                unsafe {
                    let next_frame = frame_bp as *const usize;
                    let next_bp = *next_frame;

                    // ensure that we're always travelling _up_ the stack
                    if next_bp > frame_bp {
                        self.cur_frame = Some(StackFrame {
                            frame_ip: *(next_frame.offset(1)),
                            frame_bp: *next_frame,
                        });
                    }
                }
            }

            Some(frame)
        } else {
            None
        }
    }
}

pub fn trace_stack() -> impl Iterator<Item = StackFrame> {
    let mut it = StackFrameIterator::new();
    it.next();
    it.next();
    it
    //it.filter(|frame| frame.frame_ip >= KERNEL_BASE)
}
