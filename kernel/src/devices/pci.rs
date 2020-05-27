use alloc_crate::vec::Vec;

use crate::lock::{NoIRQSpinlock, OnceCell};
use crate::structures::HashMap;

mod address;
mod config_space;
mod enhanced_cam;
mod legacy_cam;

use address::PCIAddress;
use config_space::PCISegmentConfigSpace;

static DEVICES: OnceCell<Vec<NoIRQSpinlock<PCIDevice>>> = OnceCell::new();
static DEV_MAP: OnceCell<HashMap<PCIAddress, &'static NoIRQSpinlock<PCIDevice>>> = OnceCell::new();

pub struct PCIDevice {
    address: PCIAddress,
}

fn enumerate_function(
    segment: u16,
    bus: u8,
    device: u8,
    function: u8,
    out_list: &mut Vec<PCIDevice>,
) {
    let device_class = config_space::read_class(segment, bus, device, function);
    if device_class == 0x0604 {
        // PCI to PCI bridge
        let secondary_bus =
            unsafe { config_space::read_config(segment, bus, device, function, 0x18) };
        let secondary_bus = ((secondary_bus >> 8) & 0xFF) as u8;
        enumerate_bus(segment, secondary_bus, out_list);
    } else {
        let addr = PCIAddress::new(segment, bus, device, function);
        out_list.push(PCIDevice { address: addr });

        println!(
            "pci: enumerated device {:04x}:{:02x}:{:02x}:{:01x} (class {:04x})",
            segment, bus, device, function, device_class
        );
    }
}

fn enumerate_device(segment: u16, bus: u8, device: u8, out_list: &mut Vec<PCIDevice>) {
    if !config_space::device_present(segment, bus, device, 0) {
        // no device here
        return;
    }

    enumerate_function(segment, bus, device, 0, out_list);
    let header_type = config_space::read_header_type(segment, bus, device, 0);
    if header_type.is_multi_function() {
        for func in 1..8 {
            if config_space::device_present(segment, bus, device, func) {
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

fn enumerate_root() {
    let mut devices: Vec<PCIDevice> = Vec::new();

    if enhanced_cam::ecam_supported() {
        for (segment, busses) in enhanced_cam::busses() {
            for bus in busses {
                enumerate_bus(segment, bus, &mut devices);
            }
        }
    } else {
        let header_type = config_space::read_header_type(0, 0, 0, 0);
        if header_type.is_multi_function() {
            // possibly multiple PCI host controllers
            for i in 0..8 {
                if config_space::device_present(0, 0, 0, i) {
                    enumerate_bus(0, i, &mut devices);
                }
            }
        } else {
            // single PCI host controller
            enumerate_bus(0, 0, &mut devices);
        }
    }

    let locks: Vec<NoIRQSpinlock<PCIDevice>> =
        devices.into_iter().map(NoIRQSpinlock::new).collect();

    if DEVICES.set(locks).is_err() {
        panic!("already initialized");
    }

    let mut map: HashMap<PCIAddress, &'static NoIRQSpinlock<PCIDevice>> = HashMap::new();
    for device in DEVICES.get().unwrap() {
        let addr = device.lock().address;
        map.insert(addr, device);
    }

    if DEV_MAP.set(map).is_err() {
        panic!("already initialized");
    }
}

pub fn initialize() {
    config_space::initialize();
    enumerate_root();
}
