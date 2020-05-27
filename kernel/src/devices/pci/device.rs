use super::config_space;
use super::enhanced_cam;
use super::PCIAddress;

use alloc_crate::vec::Vec;

#[derive(Debug, Clone)]
pub struct PCIDevice {
    address: PCIAddress,
    device_id: u16,
    vendor_id: u16,
    major_class: u8,
    minor_class: u8,
    prog_if: u8,
}

impl PCIDevice {
    pub fn address(&self) -> PCIAddress {
        self.address
    }

    pub fn device_id(&self) -> u16 {
        self.device_id
    }

    pub fn vendor_id(&self) -> u16 {
        self.vendor_id
    }

    pub fn major_class(&self) -> u8 {
        self.major_class
    }

    pub fn minor_class(&self) -> u8 {
        self.minor_class
    }

    pub fn prog_if(&self) -> u8 {
        self.prog_if
    }

    pub fn read_config(&self, offset: u16) -> u32 {
        unsafe { config_space::read_config(self.address, offset) }
    }

    pub fn write_config(&mut self, offset: u16, value: u32) {
        unsafe { config_space::write_config(self.address, offset, value) }
    }
}

fn read_dev_vendor_id(segment: u16, bus: u8, device: u8, function: u8) -> (u16, u16) {
    let data = unsafe { config_space::read_config_split(segment, bus, device, function, 0) };
    let vendor_id = (data & 0xFFFF) as u16;
    let device_id = ((data >> 16) & 0xFFFF) as u16;
    (vendor_id, device_id)
}

fn device_present(segment: u16, bus: u8, device: u8, function: u8) -> bool {
    let (vendor_id, _) = read_dev_vendor_id(segment, bus, device, function);
    vendor_id != 0xFFFF
}

fn is_multi_function(segment: u16, bus: u8, device: u8, function: u8) -> bool {
    let data = unsafe { config_space::read_config_split(segment, bus, device, function, 12) };
    let raw_header_type = ((data >> 16) & 0xFF) as u8;

    (raw_header_type & 0x80) != 0
}

fn read_class(segment: u16, bus: u8, device: u8, function: u8) -> (u8, u8, u8) {
    let data = unsafe { config_space::read_config_split(segment, bus, device, function, 8) };
    let major_class = ((data >> 24) & 0xFF) as u8;
    let minor_class = ((data >> 16) & 0xFF) as u8;
    let prog_if = ((data >> 8) & 0xFF) as u8;

    (major_class, minor_class, prog_if)
}

fn enumerate_function(
    segment: u16,
    bus: u8,
    device: u8,
    function: u8,
    out_list: &mut Vec<PCIDevice>,
) {
    let (major_class, minor_class, prog_if) = read_class(segment, bus, device, function);

    if (major_class == 0x06) && (minor_class == 0x04) {
        // PCI to PCI bridge
        let secondary_bus =
            unsafe { config_space::read_config_split(segment, bus, device, function, 0x18) };
        let secondary_bus = ((secondary_bus >> 8) & 0xFF) as u8;
        enumerate_bus(segment, secondary_bus, out_list);
    } else {
        let address = PCIAddress::new(segment, bus, device, function);
        let (vendor_id, device_id) = read_dev_vendor_id(segment, bus, device, function);
        let device = PCIDevice {
            address,
            major_class,
            minor_class,
            prog_if,
            vendor_id,
            device_id,
        };

        println!(
            "pci: enumerated device {}\npci:    Vendor: {:04x}\npci:    Device: {:04x}\npci:    Class: {:02x}.{:02x}.{:02x}",
            address, device.vendor_id, device.device_id, device.major_class, device.minor_class, device.prog_if
        );

        out_list.push(device);
    }
}

fn enumerate_device(segment: u16, bus: u8, device: u8, out_list: &mut Vec<PCIDevice>) {
    if !device_present(segment, bus, device, 0) {
        // no device here
        return;
    }

    enumerate_function(segment, bus, device, 0, out_list);
    if is_multi_function(segment, bus, device, 0) {
        for func in 1..8 {
            if device_present(segment, bus, device, func) {
                enumerate_function(segment, bus, device, func, out_list);
            }
        }
    }
}

fn enumerate_bus(segment: u16, bus: u8, out_list: &mut Vec<PCIDevice>) {
    for device in 0..32 {
        enumerate_device(segment, bus, device, out_list)
    }
}

pub fn enumerate_devices() -> Vec<PCIDevice> {
    let mut devices: Vec<PCIDevice> = Vec::new();

    if enhanced_cam::ecam_supported() {
        for (segment, busses) in enhanced_cam::busses() {
            for bus in busses {
                enumerate_bus(segment, bus, &mut devices);
            }
        }
    } else {
        if is_multi_function(0, 0, 0, 0) {
            // possibly multiple PCI host controllers
            for i in 0..8 {
                if device_present(0, 0, 0, i) {
                    enumerate_bus(0, i, &mut devices);
                }
            }
        } else {
            // single PCI host controller
            enumerate_bus(0, 0, &mut devices);
        }
    }

    devices
}
