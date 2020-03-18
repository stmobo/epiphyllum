//! Intel 8529A-compatible and APIC support.

use crate::asm::{msr, ports};
use crate::paging;

use core::ptr;
use spin::{Mutex, MutexGuard, Once};

static LAPIC_BASE: Once<usize> = Once::new();
static DEFAULT_IOAPIC: Once<Mutex<io_apic::IOAPIC>> = Once::new();
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

        pub fn id(&self) -> u8 {
            let data = self.read_register(ReadableRegisters::ID);
            ((data >> 24) & 0xFF) as u8
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
            self.write_register(WritableRegisters::TaskPriority, 0);

            println!("lapic: initialized lapic {}", self.id());
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

pub mod io_apic {
    use super::*;

    #[derive(Debug, Copy, Clone)]
    #[repr(transparent)]
    pub struct IOAPIC {
        base_addr: *mut u32,
    }

    impl IOAPIC {
        unsafe fn read_direct(&self, index: u32) -> u32 {
            ptr::write_volatile(self.base_addr, index);
            ptr::read_volatile(self.base_addr.offset(4))
        }

        unsafe fn write_direct(&mut self, index: u32, value: u32) {
            ptr::write_volatile(self.base_addr, index);
            ptr::write_volatile(self.base_addr.offset(4), value);
        }

        pub fn default() -> MutexGuard<'static, IOAPIC> {
            DEFAULT_IOAPIC
                .call_once(|| {
                    let vaddr = paging::offset_direct_map(0xFEC00000u64);
                    paging::map_virtual_address(vaddr, 0xFEC00000);

                    Mutex::new(IOAPIC {
                        base_addr: vaddr as *mut u32,
                    })
                })
                .lock()
        }

        pub fn id(&self) -> u8 {
            unsafe { ((self.read_direct(0) >> 24) & 0xF) as u8 }
        }

        pub fn max_redirection_entries(&self) -> u8 {
            unsafe { ((self.read_direct(1) >> 16) & 0xFF) as u8 }
        }

        pub fn apic_version(&self) -> u8 {
            unsafe { (self.read_direct(1) & 0xFF) as u8 }
        }

        pub fn get_redirection_entry(&self, index: u8) -> Result<RedirectionEntry, u8> {
            let max_ent = self.max_redirection_entries();
            if index > max_ent {
                return Err(max_ent);
            }

            let lo = unsafe { self.read_direct(16 + (2 * index as u32)) };
            let hi = unsafe { self.read_direct(17 + (2 * index as u32)) };

            let data = ((hi as u64) << 32) | (lo as u64);
            Ok(RedirectionEntry { data })
        }

        pub fn set_redirection_entry(
            &mut self,
            index: u8,
            entry: RedirectionEntry,
        ) -> Result<(), u8> {
            let max_ent = self.max_redirection_entries();
            if index > max_ent {
                return Err(max_ent);
            }

            let lo = (entry.data & 0xFFFF_FFFF) as u32;
            let hi = ((entry.data >> 32) & 0xFFFF_FFFF) as u32;

            unsafe {
                self.write_direct(16 + (2 * index as u32), lo);
                self.write_direct(17 + (2 * index as u32), hi);
            }

            Ok(())
        }
    }

    unsafe impl Send for IOAPIC {}
    unsafe impl Sync for IOAPIC {}

    #[derive(Debug, Copy, Clone, Eq, PartialEq)]
    #[repr(transparent)]
    pub struct RedirectionEntry {
        data: u64,
    }

    impl RedirectionEntry {
        pub fn new() -> RedirectionEntry {
            RedirectionEntry { data: 0 }
        }

        pub fn interrupt_vector(&self) -> u8 {
            (self.data & 0xFF) as u8
        }

        pub fn set_vector(&mut self, vector: u8) {
            self.data = (self.data & !0xFF) | (vector as u64);
        }

        pub fn delivery_status(&self) -> bool {
            (self.data & (1 << 12)) != 0
        }

        pub fn pin_polarity(&self) -> bool {
            (self.data & (1 << 13)) != 0
        }

        pub fn set_pin_polarity(&mut self, low_active: bool) {
            if low_active {
                self.data |= 1 << 13;
            } else {
                self.data &= !(1 << 13);
            }
        }

        pub fn remote_irr(&self) -> bool {
            (self.data & (1 << 14)) != 0
        }

        pub fn trigger_mode(&self) -> bool {
            (self.data & (1 << 15)) != 0
        }

        pub fn set_trigger_mode(&mut self, level_sensitive: bool) {
            if level_sensitive {
                self.data |= 1 << 15;
            } else {
                self.data &= !(1 << 15);
            }
        }

        pub fn is_masked(&self) -> bool {
            (self.data & (1 << 16)) != 0
        }

        pub fn set_masked(&mut self, masked: bool) {
            if masked {
                self.data |= 1 << 16;
            } else {
                self.data &= !(1 << 16);
            }
        }

        pub fn destination_apic(&self) -> u8 {
            ((self.data >> 56) & 0xFF) as u8
        }

        pub fn set_destination_apic(&mut self, destination: u8) {
            self.data = (self.data & 0x00FF_FFFF_FFFF_FFFF) | ((destination as u64) << 56);
        }
    }
}

pub fn initialize() -> local_apic::LocalAPIC {
    initialize_8529();

    let lapic = local_apic::LocalAPIC::new();
    lapic.enable_apic();

    let mut iapic = io_apic::IOAPIC::default();
    println!("ioapic: initializing IOAPIC {}", iapic.id());
    println!(
        "ioapic: version {:#02x} / {} redirection entries",
        iapic.apic_version(),
        iapic.max_redirection_entries() + 1
    );

    for i in 0..(iapic.max_redirection_entries() + 1) {
        let cur_entry = iapic.get_redirection_entry(i).unwrap();
        let mut entry = io_apic::RedirectionEntry::new();

        entry.set_vector(0x30 + i);
        entry.set_pin_polarity(cur_entry.pin_polarity());
        entry.set_trigger_mode(cur_entry.trigger_mode());
        entry.set_destination_apic(lapic.id());

        iapic.set_redirection_entry(i, entry).unwrap();
    }

    lapic
}