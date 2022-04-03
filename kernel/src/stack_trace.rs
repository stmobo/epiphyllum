use crate::paging;
use crate::task::Task;

use core::arch::asm;

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
    pub fn new() -> StackFrameIterator {
        unsafe {
            let mut frame_ip: usize;
            let mut frame_bp: usize;

            asm!(
                "mov {bp_out}, [rbp]",
                "mov {ip_out}, [rbp+8]",
                bp_out = out(reg) frame_bp,
                ip_out = out(reg) frame_ip
            );

            StackFrameIterator {
                cur_frame: Some(StackFrame { frame_ip, frame_bp }),
            }
        }
    }

    pub unsafe fn start_at(frame_ip: usize, frame_bp: usize) -> StackFrameIterator {
        StackFrameIterator {
            cur_frame: Some(StackFrame { frame_ip, frame_bp }),
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

            unsafe {
                if paging::direct_get_mapping(frame_bp).is_some() {
                    if let Some(cur_task) = Task::get_current_task() {
                        if !cur_task.in_stack_bounds(frame_bp + 8) {
                            return None;
                        }
                    }

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
