use super::InterruptFrame;
use alloc::boxed::Box;
use alloc::vec::Vec;
use core::mem::MaybeUninit;
use lazy_static::lazy_static;
use spin::RwLock;

pub type InterruptHandler = fn(u8) -> InterruptHandlerStatus;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum InterruptHandlerStatus {
    Handled,
    NotHandled,
}

struct IRQInfo {
    handlers: Vec<InterruptHandler>,
}

lazy_static! {
    static ref INTERRUPT_VECTORS: [RwLock<Option<Box<IRQInfo>>>; 224] = unsafe {
        let mut arr: [MaybeUninit<RwLock<Option<Box<IRQInfo>>>>; 224] =
            MaybeUninit::uninit().assume_init();

        for i in 0..224 {
            arr[i] = MaybeUninit::new(RwLock::new(None));
        }

        core::mem::transmute::<_, [RwLock<Option<Box<IRQInfo>>>; 224]>(arr)
    };
}

pub fn register_handler(interrupt_no: u8, handler: InterruptHandler) {
    if interrupt_no < 32 {
        return;
    }

    let mut lock = INTERRUPT_VECTORS[(interrupt_no - 32) as usize].write();

    if lock.is_none() {
        lock.replace(Box::new(IRQInfo {
            handlers: vec![handler],
        }));
        return;
    } else {
        let info: &mut IRQInfo = lock.as_deref_mut().unwrap();
        info.handlers.push(handler);
    }
}

pub fn handle_interrupt(frame: &InterruptFrame) {
    if frame.interrupt_no < 32 {
        return;
    }

    let mut found_handler = false;
    let lock = INTERRUPT_VECTORS[(frame.interrupt_no as usize) - 32].read();

    if let Some(vector_data) = lock.as_deref() {
        for handler in vector_data.handlers.iter() {
            if handler(frame.interrupt_no as u8) == InterruptHandlerStatus::Handled {
                found_handler = true;
                break;
            }
        }
    }

    if !found_handler {
        println!("spurious interrupt {}", frame.interrupt_no);
    }
}
