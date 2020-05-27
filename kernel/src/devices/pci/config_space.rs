use super::PCIAddress;
use super::{enhanced_cam, legacy_cam};

pub trait PCISegmentConfigSpace {
    fn segment_number(&self) -> u16;

    unsafe fn read(&self, address: PCIAddress, offset: u16) -> u32;
    unsafe fn write(&self, address: PCIAddress, offset: u16, value: u32);
}

pub unsafe fn read_config(address: PCIAddress, offset: u16) -> u32 {
    let segment = address.segment();

    if let Some(segments) = enhanced_cam::segments() {
        let seg = match segments.get(&segment) {
            Some(s) => s,
            None => panic!("invalid segment {}", segment),
        };

        seg.read(address, offset)
    } else {
        let legacy_cfg = legacy_cam::get();
        legacy_cfg.read(address, offset)
    }
}

pub unsafe fn write_config(address: PCIAddress, offset: u16, value: u32) {
    let segment = address.segment();

    if let Some(segments) = enhanced_cam::segments() {
        let seg = match segments.get(&segment) {
            Some(s) => s,
            None => panic!("invalid segment {}", segment),
        };

        seg.write(address, offset, value)
    } else {
        let legacy_cfg = legacy_cam::get();
        legacy_cfg.write(address, offset, value)
    }
}

pub unsafe fn read_config_split(
    segment: u16,
    bus: u8,
    device: u8,
    function: u8,
    offset: u16,
) -> u32 {
    read_config(PCIAddress::new(segment, bus, device, function), offset)
}

pub unsafe fn write_config_split(
    segment: u16,
    bus: u8,
    device: u8,
    function: u8,
    offset: u16,
    value: u32,
) {
    write_config(
        PCIAddress::new(segment, bus, device, function),
        offset,
        value,
    )
}

pub fn initialize() {
    enhanced_cam::initialize();

    if !enhanced_cam::ecam_supported() {
        legacy_cam::initialize();
    }
}
