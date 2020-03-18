use super::bindings::*;
use alloc::vec::Vec;
use core::ptr;

use spin::Once;

/// ACPI Multiple APIC Description Table
pub struct MADT {
    pub local_apic_addr: u64,
    pub legacy_pic_installed: bool,

    pub processors: Vec<LocalAPICEntry>,
    pub io_apics: Vec<IOAPICEntry>,
    pub irqs: Vec<InterruptSourceOverride>,
    pub nmis: Vec<NonMaskableInterrupt>,
}

static MADT_DATA: Once<MADT> = Once::new();

impl MADT {
    fn parse() -> MADT {
        let table_addr: usize = super::get_table(b"APIC", 0).expect("could not find MADT");
        let table_base = table_addr as *const ACPI_TABLE_MADT;

        unsafe {
            let mut madt = MADT {
                local_apic_addr: (*table_base).Address as u64,
                legacy_pic_installed: (*table_base).Flags == 1,
                processors: Vec::new(),
                io_apics: Vec::new(),
                irqs: Vec::new(),
                nmis: Vec::new(),
            };

            let mut entries: &'static Entry = &*((table_addr + 0x2C) as *const Entry);
            let table_len = (*table_base).Header.Length as usize;

            while entries.addr() < table_addr + table_len {
                match entries.entry_type {
                    0 => madt.processors.push(entries.read_lapic_entry()),
                    1 => madt.io_apics.push(entries.read_io_apic_entry()),
                    2 => madt.irqs.push(entries.read_irq_override_entry()),
                    4 => madt.nmis.push(entries.read_nmi_entry()),
                    5 => madt.local_apic_addr = entries.read_lapic_address_override(),
                    _ => println!("madt: unrecognized entry type {:#02x}", entries.entry_type),
                };

                entries = entries.next_entry();
            }

            madt
        }
    }

    pub fn get() -> &'static MADT {
        MADT_DATA.call_once(MADT::parse)
    }
}

#[repr(C)]
struct Entry {
    entry_type: u8,
    entry_length: u8,
}

impl Entry {
    fn addr(&self) -> usize {
        (self as *const Entry) as usize
    }

    fn next_entry(&self) -> &Entry {
        let addr = (self as *const Entry) as usize;
        let p = (addr + (self.entry_length as usize)) as *const Entry;

        unsafe { &*p }
    }

    fn read_lapic_entry(&self) -> LocalAPICEntry {
        unsafe {
            let addr = self.addr();
            let flags = ptr::read((addr + 4) as *const u32);

            LocalAPICEntry {
                processor_id: ptr::read((addr + 2) as *const u8),
                apic_id: ptr::read((addr + 3) as *const u8),
                enabled: (flags & 1) != 0,
                online_capable: (flags & 2) != 0,
            }
        }
    }

    fn read_io_apic_entry(&self) -> IOAPICEntry {
        unsafe {
            let addr = self.addr();
            IOAPICEntry {
                apic_id: ptr::read((addr + 2) as *const u8),
                address: ptr::read((addr + 4) as *const u32),
                gsi_base: ptr::read((addr + 8) as *const u32),
            }
        }
    }

    fn read_irq_override_entry(&self) -> InterruptSourceOverride {
        unsafe {
            let addr = self.addr();
            let flags = ptr::read((addr + 8) as *const u16);

            InterruptSourceOverride {
                bus_src: ptr::read((addr + 2) as *const u8),
                irq_src: ptr::read((addr + 3) as *const u8),
                gsi: ptr::read((addr + 4) as *const u32),
                active_low: (flags & 2) != 0,
                level_triggered: (flags & 8) != 0,
            }
        }
    }

    fn read_nmi_entry(&self) -> NonMaskableInterrupt {
        unsafe {
            let addr = self.addr();
            let flags = ptr::read((addr + 3) as *const u16);

            NonMaskableInterrupt {
                processor_id: ptr::read((addr + 2) as *const u8),
                local_int: ptr::read((addr + 5) as *const u8),
                active_low: (flags & 2) != 0,
                level_triggered: (flags & 8) != 0,
            }
        }
    }

    fn read_lapic_address_override(&self) -> u64 {
        unsafe {
            let addr = self.addr();
            ptr::read((addr + 4) as *const u64)
        }
    }
}

pub struct LocalAPICEntry {
    pub processor_id: u8,
    pub apic_id: u8,
    pub enabled: bool,
    pub online_capable: bool,
}

pub struct IOAPICEntry {
    pub apic_id: u8,
    pub address: u32,
    pub gsi_base: u32,
}

pub struct InterruptSourceOverride {
    pub bus_src: u8,
    pub irq_src: u8,
    pub gsi: u32,
    pub active_low: bool,
    pub level_triggered: bool,
}

pub struct NonMaskableInterrupt {
    pub processor_id: u8,
    pub active_low: bool,
    pub level_triggered: bool,
    pub local_int: u8,
}

pub struct LAPICAddressOverride {
    pub address: u64,
}
