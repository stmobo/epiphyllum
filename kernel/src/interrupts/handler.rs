use alloc_crate::boxed::Box;
use alloc_crate::vec::Vec;
use core::mem::MaybeUninit;
use lazy_static::lazy_static;
use spin::RwLock;

use super::exceptions;
use super::InterruptFrame;
use crate::devices::pic::local_apic;

struct IRQInfo {
    handlers: Vec<InterruptHandler>,
    cur_id: u64,
}

lazy_static! {
    static ref INTERRUPT_VECTORS: [RwLock<Option<Box<IRQInfo>>>; 255] = unsafe {
        let mut arr: [MaybeUninit<RwLock<Option<Box<IRQInfo>>>>; 255] =
            MaybeUninit::uninit().assume_init();

        for i in 0..224 {
            arr[i] = MaybeUninit::new(RwLock::new(None));
        }

        core::mem::transmute::<_, [RwLock<Option<Box<IRQInfo>>>; 255]>(arr)
    };
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum InterruptHandlerStatus {
    Handled,
    NotHandled,
}

struct InterruptHandler {
    handler: Box<dyn Fn() -> InterruptHandlerStatus + Send + Sync + 'static>,
    id: u64,
}

impl InterruptHandler {
    fn new<T>(handler: T) -> InterruptHandler
    where
        T: Fn() -> InterruptHandlerStatus + Send + Sync + 'static,
    {
        InterruptHandler {
            handler: Box::new(handler),
            id: 0,
        }
    }

    fn run(&self) -> InterruptHandlerStatus {
        (self.handler)()
    }
}

pub fn register_handler<T>(interrupt_no: u8, handler: T) -> Result<u64, ()>
where
    T: Fn() -> InterruptHandlerStatus + Send + Sync + 'static,
{
    let mut lock = INTERRUPT_VECTORS[interrupt_no as usize].write();
    let mut handler = InterruptHandler::new(handler);

    if lock.is_none() {
        handler.id = 0;
        lock.replace(Box::new(IRQInfo {
            handlers: vec![handler],
            cur_id: 1,
        }));

        return Ok(0);
    } else {
        let info: &mut IRQInfo = lock.as_deref_mut().unwrap();
        let id = info.cur_id;

        handler.id = id;
        info.cur_id += 1;

        info.handlers.push(handler);
        return Ok(id);
    }
}

pub fn unregister_handler(interrupt_no: u8, id: u64) {
    if interrupt_no < 32 {
        return;
    }

    let mut lock = INTERRUPT_VECTORS[interrupt_no as usize].write();

    if lock.is_some() {
        let info: &mut IRQInfo = lock.as_deref_mut().unwrap();
        for (i, handler) in info.handlers.iter().enumerate() {
            if handler.id == id {
                info.handlers.swap_remove(i);
                return;
            }
        }
    }
}

pub fn handle_interrupt(frame: &mut InterruptFrame) {
    if frame.interrupt_no == 0xFF {
        println!("Received spurious interrupt 0xFF");
        return;
    }

    let mut found_handler = false;
    let lock = INTERRUPT_VECTORS[frame.interrupt_no as usize].read();

    if let Some(vector_data) = lock.as_deref() {
        for handler in vector_data.handlers.iter() {
            if handler.run() == InterruptHandlerStatus::Handled {
                found_handler = true;
                break;
            }
        }
    }

    if !found_handler {
        if frame.interrupt_no < 32 {
            exceptions::unhandled_exception(frame);
        }

        println!("spurious interrupt {:#2x}", frame.interrupt_no);
    }

    let lapic = local_apic::LocalAPIC::new();
    if frame.interrupt_no >= 32 && lapic.has_irqs_in_service() {
        lapic.send_eoi();
    }
}
