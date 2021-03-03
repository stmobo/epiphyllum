use core::mem::MaybeUninit;

use alloc_crate::boxed::Box;

use super::exceptions;
use super::InterruptFrame;
use crate::devices::pic::local_apic;
use crate::lock::NoIRQSpinlock;
use crate::structures::handle_list::NodeHandle;
use crate::structures::HandleList;

static mut HANDLERS: [MaybeUninit<HandleList<BoxedInterruptHandler>>; 255] = MaybeUninit::uninit_array();
static HANDLER_STATUS: NoIRQSpinlock<[InterruptAllocation; 255]> =
    NoIRQSpinlock::new([InterruptAllocation::Unallocated; 255]);

type BoxedInterruptHandler = Box<dyn (FnMut() -> InterruptHandlerStatus) + Send + 'static>;

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum InterruptAllocation {
    Unallocated,
    Exclusive,
    Shared(usize),
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum InterruptHandlerStatus {
    Handled,
    NotHandled,
}

/// Represents an allocated IRQ handler.
///
/// The associated IRQ vector allocation will be freed on drop.
pub struct IRQHandler(u8, NodeHandle<'static, BoxedInterruptHandler>);

impl IRQHandler {
    /// Get the interrupt vector associated with this handler.
    pub fn interrupt_vector(&self) -> u8 {
        self.0
    }
}

impl Drop for IRQHandler {
    fn drop(&mut self) {
        let mut lock = HANDLER_STATUS.lock();
        unsafe {
            remove_interrupt_allocation(&mut *lock, self.0);
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub enum InterruptAllocationError {
    NoFreeInterrupts,
    AlreadyAllocated,
}

/// Initialize the interrupt handler list array.
/// Strictly speaking, this shouldn't be necessary, but initializing large
/// arrays of non-Copy types is very painful, and this is doubly-painful since
/// the interrupt handler list array is static.
///
/// This function must only be called once.
pub unsafe fn init() {
    for i in 0..255usize {
        HANDLERS[i].write(HandleList::<BoxedInterruptHandler>::new());
    }
}

/// Get a reference to an interrupt handler list.
fn get_handler_list(idx: usize) -> &'static HandleList<BoxedInterruptHandler> {
    unsafe {
        // SAFETY: This function will never be called prior to init(),
        // since that function is called prior to IDT installation.
        //
        // Therefore, we don't have to worry about the possibility of
        // concurrent mutable access to HANDLERS.
        //
        // Additionally, we never have to worry about HANDLERS[idx] being
        // uninitialized, for the same reason.
        HANDLERS[idx].assume_init_ref()
    }
}

/// Increments the number of allocations for the given interrupt by one.
///
/// If `exclusive` is true, then the given interrupt will also be allocated
/// exclusively.
///
/// On success, returns the new number of allocations for that interrupt.
/// On error, returns the current (unchanged) allocation state for the
/// interrupt.
fn add_interrupt_allocation(
    allocs: &mut [InterruptAllocation],
    interrupt: u8,
    exclusive: bool,
) -> Result<usize, InterruptAllocation> {
    let idx = interrupt as usize;
    match allocs[idx] {
        InterruptAllocation::Exclusive => Err(allocs[idx]),
        InterruptAllocation::Unallocated => {
            allocs[idx] = if exclusive {
                InterruptAllocation::Exclusive
            } else {
                InterruptAllocation::Shared(1)
            };
            Ok(1)
        }
        InterruptAllocation::Shared(count) => {
            if exclusive {
                Err(allocs[idx])
            } else {
                allocs[idx] = InterruptAllocation::Shared(count + 1);
                Ok(count + 1)
            }
        }
    }
}

/// Decrements the number of allocations for the given interrupt by one.
///
/// If the number of allocations for that interrupt was already one, or if the
/// interrupt was exclusively allocated, then the given interrupt will be
/// marked as Unallocated.
unsafe fn remove_interrupt_allocation(allocs: &mut [InterruptAllocation], interrupt: u8) {
    let idx = interrupt as usize;
    allocs[idx] = match allocs[idx] {
        InterruptAllocation::Unallocated => panic!(
            "attempted to deallocate unallocated interrupt {}",
            interrupt
        ),
        InterruptAllocation::Exclusive => InterruptAllocation::Unallocated,
        InterruptAllocation::Shared(count) => {
            if count == 1 {
                InterruptAllocation::Unallocated
            } else {
                InterruptAllocation::Shared(count - 1)
            }
        }
    };
}

/// Allocate a specific interrupt number.
///
/// If `exclusive` is true, then the given interrupt will be allocated exclusively.
///
/// On error, returns the current (unchanged) allocation state for the
/// interrupt.
pub fn allocate_specific(interrupt: u8, exclusive: bool) -> Result<(), InterruptAllocation> {
    let mut lock = HANDLER_STATUS.lock();
    add_interrupt_allocation(&mut *lock, interrupt, exclusive)?;
    Ok(())
}

/// Free a specific interrupt number for other use.
pub unsafe fn deallocate_specific(interrupt: u8) {
    let mut lock = HANDLER_STATUS.lock();
    remove_interrupt_allocation(&mut *lock, interrupt);
}

/// Get the current allocation status for an interrupt number.
pub fn get_interrupt_allocation(interrupt: u8) -> InterruptAllocation {
    let lock = HANDLER_STATUS.lock();
    let idx = interrupt as usize;
    (*lock)[idx]
}

/// Attempt to find and allocate an interrupt number.
///
/// This method will find the lowest unallocated interrupt number and allocate
/// that.
///
/// If (somehow) all interrupt numbers are allocated and `exclusive` is false,
/// then the interrupt with the least number of current allocations will be
/// used instead.
///
/// `exclusive` otherwise behaves the same as for `allocate_specific`.
pub fn allocate_interrupt(exclusive: bool) -> Result<u8, ()> {
    let mut lock = HANDLER_STATUS.lock();

    let mut allocated: Option<usize> = None;
    let mut min_share_count: usize = usize::MAX;

    for irq in 32..256 {
        if (*lock)[irq] == InterruptAllocation::Unallocated {
            allocated = Some(irq);
            break;
        } else if !exclusive {
            if let InterruptAllocation::Shared(count) = (*lock)[irq] {
                if count < min_share_count {
                    allocated = Some(irq);
                    min_share_count = count;
                }
            }
        }
    }

    if let Some(idx) = allocated {
        if let Err(e) = add_interrupt_allocation(&mut *lock, idx as u8, exclusive) {
            panic!("could not allocate interrupt {} with status {:?}", idx, e);
        }

        Ok(idx as u8)
    } else {
        Err(())
    }
}

/// Register an interrupt handler.
///
/// `interrupt_no` can either be a specific interrupt vector to allocate, or
/// `None` to automatically find a free vector if possible.
///
/// `exclusive` can be set to true to ensure that no other handlers will be
/// registered for the allocated vector (if any).
///
/// On success, returns an IRQHandler object.
pub fn register_handler<T>(
    interrupt_no: Option<u8>,
    exclusive: bool,
    handler: T,
) -> Result<IRQHandler, InterruptAllocationError>
where
    T: (FnMut() -> InterruptHandlerStatus) + Send + 'static,
{
    let allocated = if let Some(irq) = interrupt_no {
        let mut lock = HANDLER_STATUS.lock();
        add_interrupt_allocation(&mut *lock, irq, exclusive)
            .or(Err(InterruptAllocationError::AlreadyAllocated))?;

        drop(lock);
        irq
    } else {
        allocate_interrupt(exclusive).or(Err(InterruptAllocationError::NoFreeInterrupts))?
    };

    let idx = allocated as usize;
    Ok(IRQHandler(
        allocated,
        get_handler_list(idx).push_back(Box::new(handler)),
    ))
}

/// Dispatch an interrupt.
pub fn handle_interrupt(frame: &mut InterruptFrame) {
    if frame.interrupt_no == 0xFF {
        println!("Received spurious interrupt 0xFF");
        return;
    }

    let idx = frame.interrupt_no as usize;
    let mut found_handler = false;
    let mut lock = get_handler_list(idx).lock();

    for handler in lock.iter_mut() {
        if (**handler)() == InterruptHandlerStatus::Handled {
            found_handler = true;
            break;
        }
    }

    drop(lock);

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
