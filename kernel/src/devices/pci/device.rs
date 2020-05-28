use alloc_crate::vec::Vec;
use core::fmt;
use core::fmt::Display;

use super::config_space;
use super::enhanced_cam;
use super::PCIAddress;
use crate::malloc::physical_mem;

#[derive(Debug)]
pub struct PCIDevice {
    address: PCIAddress,
    device_id: u16,
    vendor_id: u16,
    major_class: u8,
    minor_class: u8,
    prog_if: u8,
    bars: Vec<BAR>,
}

impl PCIDevice {
    pub fn new(address: PCIAddress) -> PCIDevice {
        let segment = address.segment();
        let bus = address.bus();
        let device = address.device();
        let function = address.function();

        let (major_class, minor_class, prog_if) = read_class(segment, bus, device, function);
        let (vendor_id, device_id) = read_dev_vendor_id(segment, bus, device, function);

        let data = unsafe { config_space::read_config(address, 12) };
        let header_type = (((data >> 16) & 0xFF) as u8) & 0x7F;
        let mut bars = Vec::new();

        unsafe {
            if header_type == 0x00 {
                // Enumerate BARs:
                let mut offset: u16 = 0x10;
                while offset <= 0x24 {
                    if let Some(bar) = BAR::new(address, offset) {
                        if bar.large {
                            offset += 8;
                        } else {
                            offset += 4;
                        }

                        bars.push(bar);
                    } else {
                        offset += 4;
                    }
                }
            } else if header_type == 0x01 {
                // PCI-to-PCI bridges have up to two BARs:

                let test_bar1;
                if let Some(bar) = BAR::new(address, 0x10) {
                    test_bar1 = !bar.large;
                    bars.push(bar);
                } else {
                    test_bar1 = true;
                }

                if test_bar1 {
                    if let Some(bar) = BAR::new(address, 0x14) {
                        bars.push(bar);
                    }
                }
            }
        }

        println!(
            "pci: enumerated device {}\npci:    Vendor: {:04x}\npci:    Device: {:04x}\npci:    Class: {:02x}.{:02x}.{:02x}",
            address, vendor_id, device_id, major_class, minor_class, prog_if
        );

        if bars.len() > 0 {
            println!("pci:    Device BARs:");
            for bar in bars.iter() {
                println!("pci:        {}", bar);

                // if !bar.io {
                //     physical_mem::reserve_page_range(bar.address, bar.size >> 12);
                // }
            }
        }

        PCIDevice {
            address,
            major_class,
            minor_class,
            prog_if,
            vendor_id,
            device_id,
            bars,
        }
    }

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

#[derive(Debug)]
pub struct BAR {
    address: usize,
    size: usize,
    io: bool,
    prefetch: bool,
    large: bool, // if true, this is a 64-bit BAR
    offset: u16,
}

impl BAR {
    unsafe fn new(address: PCIAddress, offset: u16) -> Option<BAR> {
        let d1 = config_space::read_config(address, offset);
        let io = (d1 & 1) == 1;
        let large = (d1 & 0b110) == 0b100;
        let prefetch = (d1 & 0b1000) != 0;

        let bar_addr: usize;
        let size: usize;
        if large {
            let d2 = config_space::read_config(address, offset + 4);
            bar_addr = ((d2 as usize) << 32) | ((d1 & 0xFFFF_FFF0) as usize);

            config_space::write_config(address, offset, 0xFFFF_FFFF);
            config_space::write_config(address, offset + 4, 0xFFFF_FFFF);

            let s1 = config_space::read_config(address, offset);
            let s2 = config_space::read_config(address, offset + 4);

            let t = ((s2 as usize) << 32) | ((s1 & 0xFFFF_FFF0) as usize);
            if t == 0 {
                return None;
            }

            size = (!t) + 1;
            config_space::write_config(address, offset, d1);
            config_space::write_config(address, offset + 4, d2);
        } else {
            bar_addr = (d1 & 0xFFFF_FFF0) as usize;
            config_space::write_config(address, offset, 0xFFFF_FFFF);

            let s1 = config_space::read_config(address, offset);
            let t = s1 & 0xFFFF_FFF0;
            if t == 0 {
                return None;
            }

            size = ((!t) + 1) as usize;
            config_space::write_config(address, offset, d1);
        }

        Some(BAR {
            address: bar_addr,
            size,
            io,
            large,
            prefetch,
            offset,
        })
    }
}

impl Display for BAR {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "BAR #{}: ", (self.offset - 0x10) / 4)?;

        if !self.io {
            let pf = if self.prefetch {
                "prefetchable"
            } else {
                "un-prefetchable"
            };

            if self.large {
                write!(f, "64-bit {} memory at {:#018x} ", pf, self.address)?;
            } else {
                write!(f, "32-bit {} memory at {:#010x} ", pf, self.address)?;
            }
        } else {
            write!(f, "I/O ports at {:#06x} ", self.address)?;
        }

        match self.size {
            0..=0x400 => write!(f, "({}B)", self.size),
            0x401..=0x100000 => write!(f, "({}K)", self.size >> 10),
            0x100001..=0x40000000 => write!(f, "({}M)", self.size >> 20),
            _ => write!(f, "({}G)", self.size >> 30),
        }
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
    let address = PCIAddress::new(segment, bus, device, function);
    let dev = PCIDevice::new(address);
    let is_bridge = (dev.major_class == 0x06) && (dev.minor_class == 0x04);

    out_list.push(dev);

    if is_bridge {
        // enumerate devices behind bridge
        let secondary_bus =
            unsafe { config_space::read_config_split(segment, bus, device, function, 0x18) };
        let secondary_bus = ((secondary_bus >> 8) & 0xFF) as u8;
        enumerate_bus(segment, secondary_bus, out_list);
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
