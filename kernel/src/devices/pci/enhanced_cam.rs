use alloc_crate::vec::Vec;
use core::ops::Range;

use super::{PCIAddress, PCISegmentConfigSpace};
use crate::acpica::mcfg::MCFG;
use crate::lock::OnceCell;
use crate::paging::PhysicalPointer;
use crate::structures::HashMap;

static SEGMENTS: OnceCell<Option<HashMap<u16, PCISegment>>> = OnceCell::new();

pub struct PCIExtendedHostBridge {
    bus_start: u8,
    bus_end: u8,
    base_address: usize,
}

impl PCIExtendedHostBridge {
    fn config_space_address(&self, address: PCIAddress) -> PhysicalPointer<u32> {
        debug_assert!(
            address.bus() >= self.bus_start,
            "invalid bus number {} >= {}",
            address.bus(),
            self.bus_start
        );

        debug_assert!(
            address.bus() <= self.bus_end,
            "invalid bus number {} <= {}",
            address.bus(),
            self.bus_end
        );

        let bus_min = (self.bus_start as u64) << 20;
        let shifted = address.extended_cam_shift();

        let offset = (shifted - bus_min) as usize;
        PhysicalPointer::new(self.base_address + offset).unwrap()
    }

    unsafe fn read(&self, address: PCIAddress, offset: u16) -> u32 {
        assert_eq!(offset & 0x03, 0, "offset {:#06x} not aligned", offset);
        assert!(
            offset < 0x1000,
            "offset {:#06x} too large (limit 0x1000)",
            offset
        );

        let phys = self.config_space_address(address);
        phys.as_ptr().add((offset >> 2).into()).read_volatile()
    }

    unsafe fn write(&self, address: PCIAddress, offset: u16, value: u32) {
        assert_eq!(offset & 0x03, 0, "offset {:#06x} not aligned", offset);
        assert!(
            offset < 0x1000,
            "offset {:#06x} too large (limit 0x1000)",
            offset
        );

        let phys = self.config_space_address(address);
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

    unsafe fn read(&self, address: PCIAddress, offset: u16) -> u32 {
        let bridge = self
            .find_bridge(address.bus())
            .expect("could not find bridge for bus");

        bridge.read(address, offset)
    }

    unsafe fn write(&self, address: PCIAddress, offset: u16, value: u32) {
        let bridge = self
            .find_bridge(address.bus())
            .expect("could not find bridge for bus");

        bridge.write(address, offset, value)
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
