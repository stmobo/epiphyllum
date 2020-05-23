//! Intel 8529A-compatible and APIC support.

use crate::acpica::madt::MADT;
use crate::asm::{msr, ports};
use crate::lock::{LockedGlobal, NoIRQSpinlock, NoIRQSpinlockGuard};

use crate::paging::PhysicalPointer;

use alloc_crate::vec::Vec;
use core::ptr;
use spin::Once;

static LAPIC_BASE: Once<usize> = Once::new();
static IO_APICS: Once<Vec<(u8, NoIRQSpinlock<io_apic::IOAPIC>)>> = Once::new();
static GSI_LIST: LockedGlobal<Vec<io_apic::GSIEntry>> = LockedGlobal::new();

const PIC1: u16 = 0x0020;
const PIC2: u16 = 0x00A0;

const ISA_IRQ_BASE: u8 = 0x20;

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
                let base_phys_addr: usize = (msr::rdmsr(0x1B) & 0xFFFF_FFFF_FFFF_F000) as usize;

                println!("lapic: LAPIC base address is {:#016x}", base_phys_addr);

                base_phys_addr
            });

            let base = unsafe { PhysicalPointer::<u32>::new_unchecked(base_addr).as_mut_ptr() };
            LocalAPIC { base }
        }

        pub fn processor_id(&self) -> u8 {
            let apic_id = self.id();
            let madt = MADT::get();

            for cpu in madt.processors.iter() {
                if cpu.apic_id == apic_id {
                    return cpu.processor_id;
                }
            }

            panic!("local APIC {} not found in MADT", apic_id);
        }

        pub fn initialize_nmis(&self) {
            let cpu_id = self.processor_id();
            let madt = MADT::get();

            for nmi in madt.nmis.iter() {
                if nmi.processor_id != 0xFF && nmi.processor_id != cpu_id {
                    continue;
                }

                let write_reg: WritableRegisters;
                if nmi.local_int == 0 {
                    write_reg = WritableRegisters::LINT0;
                } else if nmi.local_int == 1 {
                    write_reg = WritableRegisters::LINT1;
                } else {
                    println!(
                        "lapic: unsupported local interrupt line {} in MADT",
                        nmi.local_int
                    );
                    continue;
                }

                self.write_register(write_reg, 0b100_0000_0000);
            }

            println!("lapic: configured NMI for CPU {}", cpu_id);
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

        fn read_irq_bit(&self, base: isize, irq_no: u8) -> bool {
            let bit_no = (irq_no % 32) as u32;
            let off = base + (((irq_no as isize) / 32) * 16);

            let reg = unsafe { self.base.offset(off >> 2).read_volatile() };
            (reg & (1 << bit_no)) != 0
        }

        pub fn read_irr(&self, irq_no: u8) -> bool {
            self.read_irq_bit(0x200, irq_no)
        }

        pub fn read_isr(&self, irq_no: u8) -> bool {
            self.read_irq_bit(0x100, irq_no)
        }

        pub fn read_tmr(&self, irq_no: u8) -> bool {
            self.read_irq_bit(0x180, irq_no)
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

        pub fn get_timer_ticks(&self) -> u32 {
            self.read_register(ReadableRegisters::TimerCurrentCount)
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

            self.write_register(WritableRegisters::TimerLVT, lvt);
            self.write_register(WritableRegisters::TimerDivideConfig, divide_config);

            Ok(())
        }

        pub fn disable_timer(&self) {
            self.write_register(WritableRegisters::TimerLVT, (1 << 16) | 0x30);
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

    pub fn initialize() -> LocalAPIC {
        initialize_8529();

        let lapic = local_apic::LocalAPIC::new();
        lapic.enable_apic();
        lapic.initialize_nmis();

        println!("lapic: local APIC initialized");

        lapic
    }
}

pub mod io_apic {
    use super::*;

    #[derive(Debug, Copy, Clone)]
    pub struct IOAPIC {
        base_addr: *mut u32,
        irq_base: u8,
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

        fn initialize(&mut self) {
            println!("ioapic: initializing IOAPIC {}", self.id());
            println!(
                "ioapic: version {:#02x} / {} redirection entries",
                self.apic_version(),
                self.max_redirection_entries() + 1
            );

            let madt = MADT::get();
            let min_irq = self.irq_base;
            let max_irq = self.irq_base + self.max_redirection_entries();

            let mut gsi_list = GSI_LIST.lock();

            for irq in madt.irqs.iter() {
                let gsi = irq.gsi as u8;

                if gsi >= min_irq && gsi < max_irq {
                    let idx = gsi - min_irq;
                    let mut entry = RedirectionEntry::new();

                    entry.set_vector(ISA_IRQ_BASE + irq.irq_src);
                    entry.set_pin_polarity(irq.active_low);
                    entry.set_trigger_mode(irq.level_triggered);
                    entry.set_masked(false);
                    entry.set_destination_apic(0);

                    self.set_redirection_entry(idx, entry).unwrap();

                    gsi_list.push(GSIEntry {
                        gsi,
                        vector: ISA_IRQ_BASE + irq.irq_src,
                        io_apic_id: self.id(),
                    });
                }
            }
        }

        fn initialize_list() -> Vec<(u8, NoIRQSpinlock<IOAPIC>)> {
            let madt = MADT::get();
            let mut ret = Vec::new();

            for io_apic in madt.io_apics.iter() {
                let paddr = io_apic.address as usize;
                let base_addr =
                    unsafe { PhysicalPointer::<u32>::new_unchecked(paddr).as_mut_ptr() };

                let mut s = IOAPIC {
                    base_addr,
                    irq_base: io_apic.gsi_base as u8,
                };

                s.initialize();
                ret.push((io_apic.apic_id, NoIRQSpinlock::new(s)));
            }

            ret
        }

        pub fn initialize_all() {
            IO_APICS.call_once(IOAPIC::initialize_list);
        }

        pub fn get(id: u8) -> Option<NoIRQSpinlockGuard<'static, IOAPIC>> {
            let apics_list = IO_APICS.call_once(IOAPIC::initialize_list);
            for (apic_id, apic_lock) in apics_list.iter() {
                if *apic_id == id {
                    return Some(apic_lock.lock());
                }
            }

            None
        }

        pub fn irq_base(&self) -> u8 {
            self.irq_base
        }

        pub fn max_irq(&self) -> u8 {
            self.irq_base + self.max_redirection_entries()
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

        pub fn mask_interrupt(irq: u8, masked: bool) -> Result<bool, u8> {
            let mut gsi_list = GSI_LIST.lock();
            let entry = gsi_list.iter_mut().find(|e| e.vector == irq).ok_or(irq)?;

            Ok(entry.set_masked(masked))
        }
    }

    unsafe impl Send for IOAPIC {}
    unsafe impl Sync for IOAPIC {}

    pub struct GSIEntry {
        gsi: u8,
        vector: u8,
        io_apic_id: u8,
    }

    impl GSIEntry {
        fn get_io_apic(&self) -> Option<NoIRQSpinlockGuard<'static, IOAPIC>> {
            for (id, lock) in IO_APICS.wait().unwrap() {
                let apic = lock.lock();
                if *id == self.io_apic_id {
                    return Some(apic);
                }
            }

            None
        }

        fn set_masked(&mut self, masked: bool) -> bool {
            let mut apic = self.get_io_apic().unwrap();
            let idx = self.gsi - apic.irq_base();

            let mut entry = apic
                .get_redirection_entry(idx)
                .expect("could not get redirection entry for IRQ");

            let prev = entry.is_masked();
            entry.set_masked(masked);

            apic.set_redirection_entry(idx, entry)
                .expect("could not set redirection entry for IRQ");

            prev
        }
    }

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

    pub fn initialize() {
        GSI_LIST.init(|| Vec::new());
        io_apic::IOAPIC::initialize_all();
        println!("ioapic: I/O APICs initialized");
    }
}
