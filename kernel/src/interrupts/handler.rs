use alloc_crate::boxed::Box;

use super::exceptions;
use super::InterruptFrame;
use crate::devices::pic::local_apic;
use crate::structures::handle_list::NodeHandle;
use crate::structures::HandleList;

static HANDLERS: [HandleList<BoxedInterruptHandler>; 255] = [HandleList::new(); 255];

type BoxedInterruptHandler = Box<dyn (FnMut() -> InterruptHandlerStatus) + Send + 'static>;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum InterruptHandlerStatus {
    Handled,
    NotHandled,
}

pub struct IRQHandler(NodeHandle<'static, BoxedInterruptHandler>);

pub fn register_handler<T>(interrupt_no: u8, handler: T) -> IRQHandler
where
    T: (FnMut() -> InterruptHandlerStatus) + Send + 'static,
{
    let idx = interrupt_no as usize;

    IRQHandler(HANDLERS[idx].push_back(Box::new(handler)))
}

pub fn handle_interrupt(frame: &mut InterruptFrame) {
    if frame.interrupt_no == 0xFF {
        println!("Received spurious interrupt 0xFF");
        return;
    }

    let idx = frame.interrupt_no as usize;

    let mut found_handler = false;
    let mut lock = HANDLERS[idx].lock();

    for handler in lock.iter_mut() {
        if (**handler)() == InterruptHandlerStatus::Handled {
            found_handler = true;
            break;
        }
    }

    if !found_handler {
        if frame.interrupt_no < 32 {
            exceptions::unhandled_exception(frame);
        } else {
            println!("spurious interrupt {:#04x}", frame.interrupt_no);
        }
    }

    let lapic = local_apic::LocalAPIC::new();
    if frame.interrupt_no >= 32 && lapic.has_irqs_in_service() {
        lapic.send_eoi();
    }
}
