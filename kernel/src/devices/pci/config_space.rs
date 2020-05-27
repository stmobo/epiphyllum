use super::{enhanced_cam, legacy_cam};

#[derive(Debug, Copy, Clone)]
#[repr(u8)]
pub enum HeaderType {
    Standard = 0x00,
    PciPciBridge = 0x01,
    CardbusBridge = 0x02,
}

#[derive(Debug, Copy, Clone)]
pub struct PCIHeaderType(u8);

impl PCIHeaderType {
    pub fn is_multi_function(self) -> bool {
        (self.0 & 0x80) != 0
    }

    pub fn get_type(self) -> HeaderType {
        match self.0 & 0x7F {
            0x00 => HeaderType::Standard,
            0x01 => HeaderType::PciPciBridge,
            0x02 => HeaderType::CardbusBridge,
            _ => panic!("unrecognized PCI header type: {:#04x}", self.0),
        }
    }
}

pub trait PCISegmentConfigSpace {
    fn segment_number(&self) -> u16;

    unsafe fn read(&self, bus: u8, device: u8, function: u8, offset: u16) -> u32;
    unsafe fn write(&self, bus: u8, device: u8, function: u8, offset: u16, value: u32);
}

pub unsafe fn read_config(segment: u16, bus: u8, device: u8, function: u8, offset: u16) -> u32 {
    if let Some(segments) = enhanced_cam::segments() {
        let seg = match segments.get(&segment) {
            Some(s) => s,
            None => panic!("invalid segment {}", segment),
        };

        seg.read(bus, device, function, offset)
    } else {
        assert_eq!(segment, 0, "nonzero segments only supported with ECAM");

        let legacy_cfg = legacy_cam::get();
        legacy_cfg.read(bus, device, function, offset)
    }
}

pub fn read_vendor_id(segment: u16, bus: u8, device: u8, function: u8) -> u16 {
    let data = unsafe { read_config(segment, bus, device, function, 0) };
    (data & 0xFFFF) as u16
}

pub fn device_present(segment: u16, bus: u8, device: u8, function: u8) -> bool {
    read_vendor_id(segment, bus, device, function) != 0xFFFF
}

pub fn read_header_type(segment: u16, bus: u8, device: u8, function: u8) -> PCIHeaderType {
    let data = unsafe { read_config(segment, bus, device, function, 12) };
    PCIHeaderType(((data >> 16) & 0xFF) as u8)
}

pub fn read_class(segment: u16, bus: u8, device: u8, function: u8) -> u16 {
    let data = unsafe { read_config(segment, bus, device, function, 8) };
    ((data >> 16) & 0xFFFF) as u16
}

pub unsafe fn write_config(
    segment: u16,
    bus: u8,
    device: u8,
    function: u8,
    offset: u16,
    value: u32,
) {
    if let Some(segments) = enhanced_cam::segments() {
        let seg = match segments.get(&segment) {
            Some(s) => s,
            None => panic!("invalid segment {}", segment),
        };

        seg.write(bus, device, function, offset, value)
    } else {
        assert_eq!(segment, 0, "nonzero segments only supported with ECAM");

        let legacy_cfg = legacy_cam::get();
        legacy_cfg.write(bus, device, function, offset, value)
    }
}

pub fn initialize() {
    enhanced_cam::initialize();

    if !enhanced_cam::ecam_supported() {
        legacy_cam::initialize();
    }
}
