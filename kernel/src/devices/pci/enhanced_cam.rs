use alloc_crate::vec::Vec;
use core::ops::Range;

use super::PCISegmentConfigSpace;
use crate::acpica::mcfg::MCFG;
use crate::lock::{NoIRQSpinlock, OnceCell};
use crate::paging::PhysicalPointer;
use crate::structures::HashMap;

static SEGMENTS: OnceCell<Option<HashMap<u16, PCISegment>>> = OnceCell::new();

pub struct PCIExtendedHostBridge {
    bus_start: u8,
    bus_end: u8,
    base_address: usize,
    lock: NoIRQSpinlock<()>,
}

impl PCIExtendedHostBridge {
    fn config_space_address(&self, bus: u8, device: u8, function: u8) -> PhysicalPointer<u32> {
        assert!(
            bus >= self.bus_start,
            "invalid bus number {} >= {}",
            bus,
            self.bus_start
        );

        assert!(
            bus <= self.bus_end,
            "invalid bus number {} <= {}",
            bus,
            self.bus_end
        );

        assert!(device < 32, "invalid device number {}", device);
        assert!(function < 8, "invalid function number {}", function);

        let bus_offset = bus - self.bus_start;
        let addr = self.base_address
            + (((bus_offset as usize) << 20)
                | ((device as usize) << 15)
                | ((function as usize) << 12));

        PhysicalPointer::new(addr).unwrap()
    }

    unsafe fn read(&self, bus: u8, device: u8, function: u8, offset: u16) -> u32 {
        assert!((offset & 0x03) == 0, "offset {:#06x} not aligned", offset);

        let phys = self.config_space_address(bus, device, function);
        let _lock = self.lock.lock();

        phys.as_ptr().add((offset >> 2).into()).read_volatile()
    }

    unsafe fn write(&self, bus: u8, device: u8, function: u8, offset: u16, value: u32) {
        assert!((offset & 0x03) == 0, "offset {:#06x} not aligned", offset);

        let phys = self.config_space_address(bus, device, function);
        let _lock = self.lock.lock();

        phys.as_mut_ptr()
            .add((offset >> 2).into())
            .write_volatile(value);
    }
}

pub struct PCISegment {
    segment: u16,
    bridges: Vec<PCIExtendedHostBridge>,
}

impl PCISegment {
    fn find_bridge(&self, bus: u8) -> Option<&PCIExtendedHostBridge> {
        for bridge in self.bridges.iter() {
            if bus >= bridge.bus_start && bus <= bridge.bus_end {
                return Some(bridge);
            }
        }

        None
    }
}

impl PCISegmentConfigSpace for PCISegment {
    fn segment_number(&self) -> u16 {
        self.segment
    }

    unsafe fn read(&self, bus: u8, device: u8, function: u8, offset: u16) -> u32 {
        let bridge = self
            .find_bridge(bus)
            .expect("could not find bridge for bus");

        bridge.read(bus, device, function, offset)
    }

    unsafe fn write(&self, bus: u8, device: u8, function: u8, offset: u16, value: u32) {
        let bridge = self
            .find_bridge(bus)
            .expect("could not find bridge for bus");

        bridge.write(bus, device, function, offset, value)
    }
}

pub fn initialize() {
    let mcfg = match MCFG::get() {
        Some(mcfg) => mcfg,
        None => {
            if SEGMENTS.set(None).is_err() {
                panic!("already initialized");
            }

            return;
        }
    };

    let mut segments: HashMap<u16, PCISegment> = HashMap::new();
    for bridge in mcfg.iter() {
        if !segments.contains_key(&bridge.segment_group) {
            segments.insert(
                bridge.segment_group,
                PCISegment {
                    segment: bridge.segment_group,
                    bridges: Vec::new(),
                },
            );
        }

        let v = segments.get_mut(&bridge.segment_group).unwrap();
        v.bridges.push(PCIExtendedHostBridge {
            bus_start: bridge.start_bus,
            bus_end: bridge.end_bus,
            base_address: bridge.address,
            lock: NoIRQSpinlock::new(()),
        });
    }

    for v in segments.values_mut() {
        v.bridges.sort_unstable_by_key(|elem| elem.bus_start);
    }

    println!("pci: loaded MCFG table");

    if SEGMENTS.set(Some(segments)).is_err() {
        panic!("already initialized");
    }
}

pub fn ecam_supported() -> bool {
    SEGMENTS.get().expect("not initialized").is_some()
}

pub fn segments() -> Option<&'static HashMap<u16, PCISegment>> {
    SEGMENTS.get().expect("not initialized").as_ref()
}

pub fn busses() -> impl Iterator<Item = (u16, Range<u8>)> {
    segments().unwrap().iter().flat_map(|(segment, v)| {
        v.bridges
            .iter()
            .map(move |bridge| (*segment, (bridge.bus_start)..(bridge.bus_end)))
    })
}
