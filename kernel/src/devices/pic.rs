//! Intel 8529A-compatible and APIC support.

use crate::asm::{msr, ports};
use crate::paging;

use core::ptr;
use spin::Once;

static LAPIC_BASE: Once<usize> = Once::new();
const PIC1: u16 = 0x0020;
const PIC2: u16 = 0x00A0;

fn initialize_8529() {
    unsafe {
        /* Initialization Command Word 1 */
        ports::outb(PIC1, 0b0001_0001);
        ports::io_wait();

        ports::outb(PIC2, 0b0001_0001);
        ports::io_wait();

        /* ICW 2: interrupt vectors */
        ports::outb(PIC1 + 1, 0xF0);
        ports::io_wait();

        ports::outb(PIC2 + 1, 0xF8);
        ports::io_wait();

        /* ICW 3 */
        ports::outb(PIC1 + 1, 0b0000_0100);
        ports::io_wait();

        ports::outb(PIC2 + 1, 0b0000_0010);
        ports::io_wait();

        /* ICW 4 */
        ports::outb(PIC1 + 1, 0b0000_0001);
        ports::io_wait();

        ports::outb(PIC2 + 1, 0b0000_0001);
        ports::io_wait();

        /* Mask all interrupts */
        ports::outb(PIC1 + 1, 0xFF);
        ports::io_wait();

        ports::outb(PIC2 + 1, 0xFF);
        ports::io_wait();
    }
}

pub mod local_apic {
    use super::*;

    #[derive(Debug, Copy, Clone)]
    #[repr(transparent)]
    pub struct LocalAPIC {
        base: *mut u32,
    }

    impl LocalAPIC {
        pub fn new() -> LocalAPIC {
            let base_addr = *LAPIC_BASE.call_once(|| {
                let base_phys_addr: usize =
                    unsafe { msr::rdmsr(0x1B) & 0xFFFF_FFFF_FFFF_F000 } as usize;

                let vaddr = paging::offset_direct_map(base_phys_addr);
                if !paging::map_virtual_address(vaddr, base_phys_addr) {
                    panic!("lapic: could not map LAPIC base address into virtual memory");
                } else {
                    println!("LAPIC base address: {:#016x}", base_phys_addr);
                }

                vaddr
            });

            LocalAPIC {
                base: base_addr as *mut u32,
            }
        }

        fn read_register(&self, register: ReadableRegisters) -> u32 {
            let idx = (register as isize) >> 2;
            unsafe { ptr::read_volatile(self.base.offset(idx)) }
        }

        fn write_register(&self, register: WritableRegisters, value: u32) {
            let idx = (register as isize) >> 2;
            unsafe {
                ptr::write_volatile(self.base.offset(idx), value);
            }
        }

        pub fn read_irr(&self, irq_no: u8) -> bool {
            let bit_no = (irq_no % 32) as u32;
            let offset = 0x200 + (((irq_no as isize) / 32) * 16);

            unsafe { (ptr::read_volatile(self.base.offset(offset >> 2)) & (1 << bit_no)) != 0 }
        }

        pub fn read_isr(&self, irq_no: u8) -> bool {
            let bit_no = (irq_no % 32) as u32;
            let offset = 0x100 + (((irq_no as isize) / 32) * 16);

            unsafe { (ptr::read_volatile(self.base.offset(offset >> 2)) & (1 << bit_no)) != 0 }
        }

        pub fn read_tmr(&self, irq_no: u8) -> bool {
            let bit_no = (irq_no % 32) as u32;
            let offset = 0x180 + (((irq_no as isize) / 32) * 16);

            unsafe { (ptr::read_volatile(self.base.offset(offset >> 2)) & (1 << bit_no)) != 0 }
        }

        pub fn send_eoi(&self) {
            self.write_register(WritableRegisters::EndOfInterrupt, 0);
        }

        pub fn has_irqs_in_service(&self) -> bool {
            let base_idx = (ReadableRegisters::InService as isize) >> 2;
            for i in 0..8 {
                let isr = unsafe { ptr::read_volatile(self.base.offset(base_idx + (i * 4))) };
                if isr != 0 {
                    return true;
                }
            }

            false
        }

        pub fn has_pending_irqs(&self) -> bool {
            let base_idx = (ReadableRegisters::InterruptRequest as isize) >> 2;
            for i in 0..8 {
                let irr = unsafe { ptr::read_volatile(self.base.offset(base_idx + (i * 4))) };
                if irr != 0 {
                    return true;
                }
            }

            false
        }

        pub fn enable_apic(&self) {
            self.write_register(WritableRegisters::SpuriousInterruptVector, 0x1FF);
        }

        pub fn set_timer_ticks(&self, ticks: u32) {
            self.write_register(WritableRegisters::TimerInitialCount, ticks);
        }

        pub fn configure_timer(
            &self,
            mode: TimerMode,
            divisor: u8,
            interrupt_no: u8,
        ) -> Result<(), u8> {
            let divide_config: u32 = match divisor {
                1 => 0b1011,
                2 => 0b0000,
                4 => 0b0001,
                8 => 0b0010,
                16 => 0b0011,
                32 => 0b1000,
                64 => 0b1001,
                128 => 0b1010,
                _ => return Err(divisor),
            };

            let lvt = match mode {
                TimerMode::OneShot => (interrupt_no as u32),
                TimerMode::Periodic => (interrupt_no as u32) | (1 << 17),
                TimerMode::Deadline => (interrupt_no as u32) | (2 << 17),
            };

            self.write_register(WritableRegisters::TimerDivideConfig, divide_config);
            self.write_register(WritableRegisters::TimerLVT, lvt);

            Ok(())
        }
    }

    #[derive(Debug, Copy, Clone, PartialEq, Eq)]
    #[allow(dead_code)]
    pub enum TimerMode {
        OneShot,
        Periodic,
        Deadline,
    }

    #[derive(Debug, Copy, Clone, PartialEq, Eq)]
    #[repr(isize)]
    #[allow(dead_code)]
    enum ReadableRegisters {
        ID = 0x020,
        Version = 0x030,
        TaskPriority = 0x080,
        ArbitrationPriority = 0x090,
        ProcessorPriority = 0x0A0,
        RemoteRead = 0x0C0,
        LogicalDestination = 0x0D0,
        DestinationFormat = 0x0E0,
        SpuriousInterruptVector = 0x0F0,
        InService = 0x100,
        TriggerMode = 0x180,
        InterruptRequest = 0x200,
        ErrorStatus = 0x280,
        CMCI = 0x2F0,
        InterruptCommandLow = 0x300,
        InterruptCommandHigh = 0x310,
        TimerLVT = 0x320,
        ThermalLVT = 0x330,
        PerformanceCounterLVT = 0x340,
        LINT0 = 0x350,
        LINT1 = 0x360,
        ErrorVectorTableEntry = 0x370,
        TimerInitialCount = 0x380,
        TimerCurrentCount = 0x390,
        TimerDivideConfig = 0x3E0,
    }

    #[derive(Debug, Copy, Clone, PartialEq, Eq)]
    #[repr(isize)]
    #[allow(dead_code)]
    enum WritableRegisters {
        ID = 0x020,
        TaskPriority = 0x080,
        EndOfInterrupt = 0x0B0,
        LogicalDestination = 0x0D0,
        DestinationFormat = 0x0E0,
        SpuriousInterruptVector = 0x0F0,
        CMCI = 0x2F0,
        InterruptCommandLow = 0x300,
        InterruptCommandHigh = 0x310,
        TimerLVT = 0x320,
        ThermalLVT = 0x330,
        PerformanceCounterLVT = 0x340,
        LINT0 = 0x350,
        LINT1 = 0x360,
        ErrorVectorTableEntry = 0x370,
        TimerInitialCount = 0x380,
        TimerDivideConfig = 0x3E0,
    }
}

pub fn initialize() -> local_apic::LocalAPIC {
    initialize_8529();

    let lapic = local_apic::LocalAPIC::new();
    lapic.enable_apic();

    lapic
}
