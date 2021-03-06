use alloc_crate::sync::{Arc, Weak};
use alloc_crate::vec::Vec;
use core::fmt;
use core::fmt::Display;

use crate::acpica::AcpiDevice;
use crate::lock::OnceCell;
use crate::malloc::physical_mem;
use crate::paging;
use crate::paging::PhysicalPointer;
use crate::structures::HashMap;

use super::acpi;
use super::config_space;
use super::enhanced_cam;
use super::enumeration;
use super::interrupts::{InterruptAssignment, PCIInterruptPin};
use super::PCIAddress;

static DEVICES: OnceCell<HashMap<PCIAddress, Arc<PCIDevice>>> = OnceCell::new();
static ROOT_BUSSES: OnceCell<Vec<Arc<PCIBus>>> = OnceCell::new();

pub struct PCIDevice {
    address: PCIAddress,
    device_id: u16,
    vendor_id: u16,
    major_class: u8,
    minor_class: u8,
    prog_if: u8,
    bars: Vec<BAR>,
    parent_bus: Weak<PCIBus>,
    child_bus: OnceCell<Option<Arc<PCIBus>>>,
    acpi_device: Option<&'static AcpiDevice>,
}

impl PCIDevice {
    fn new(
        segment: u16,
        bus: u8,
        device: u8,
        function: u8,
        parent_bus: Weak<PCIBus>,
    ) -> Arc<PCIDevice> {
        let address = PCIAddress::new(segment, bus, device, function);
        let (major_class, minor_class, prog_if) =
            enumeration::read_class(segment, bus, device, function);
        let (vendor_id, device_id) =
            enumeration::read_dev_vendor_id(segment, bus, device, function);

        println!(
            "pci: enumerated device {}\npci:    Vendor: {:04x}\npci:    Device: {:04x}\npci:    Class: {:02x}.{:02x}.{:02x}",
            address, vendor_id, device_id, major_class, minor_class, prog_if
        );

        let data = unsafe { config_space::read_config(address, 12) };
        let header_type = (((data >> 16) & 0xFF) as u8) & 0x7F;
        let mut bars = Vec::new();

        let mut nonzero_bars = false;
        unsafe {
            if header_type == 0x00 {
                // Enumerate BARs:
                let mut offset: u16 = 0x10;
                while offset <= 0x24 {
                    let bar = BAR::new(address, offset);
                    if bar.size > 0 {
                        nonzero_bars = true;
                    }

                    if bar.large {
                        offset += 8;
                    } else {
                        offset += 4;
                    }

                    bars.push(bar);
                }
            } else if header_type == 0x01 {
                // PCI-to-PCI bridges have up to two BARs:

                let bar0 = BAR::new(address, 0x10);
                if bar0.size > 0 {
                    nonzero_bars = true;
                }

                if !bar0.large {
                    let bar1 = BAR::new(address, 0x14);
                    if bar1.size > 0 {
                        nonzero_bars = true;
                    }

                    bars.push(bar0);
                    bars.push(bar1);
                } else {
                    bars.push(bar0);
                }
            }
        }

        if nonzero_bars {
            println!("pci:    Device BARs:");
            for bar in bars.iter() {
                if bar.size == 0 {
                    continue;
                }

                println!("pci:        {}", bar);

                if !bar.io {
                    unsafe {
                        physical_mem::reserve_page_range(bar.address, bar.size >> 12)
                            .expect("could not reserve page range for BAR");
                    }

                    paging::set_page_caching(
                        paging::offset_direct_map(bar.address),
                        bar.size >> 12,
                        paging::CacheType::Uncacheable,
                    );
                }
            }
        }

        let acpi_device = acpi::get_acpi_device(address);
        if let Some(d) = acpi_device {
            print!("pci:    ACPI device: {} ", d.full_name());

            if let Some(hid) = d.hardware_id() {
                print!("[HID: {}] ", hid);
            } else if let Some(adr) = d.address() {
                print!("[ADR: {:08x}] ", adr);
            }

            if let Some(uid) = d.unique_id() {
                print!("[UID: {}] ", uid);
            }

            if d.is_pci_root() {
                print!("[pci root] ");
            }

            print!("\n");
        } else {
            println!("pci:    could not find ACPI device object");
        }

        let device_info = Arc::new(PCIDevice {
            address,
            major_class,
            minor_class,
            prog_if,
            vendor_id,
            device_id,
            bars,
            child_bus: OnceCell::new(),
            acpi_device,
            parent_bus,
        });

        if (major_class == 0x06) && (minor_class == 0x04) {
            // This is a PCI-PCI bridge, enumerate the child bus
            let secondary_bus = enumeration::get_secondary_bus(segment, bus, device, function);
            println!(
                "pci:    PCI-PCI bridge to secondary bus {:02x}",
                secondary_bus
            );

            let weak = Arc::downgrade(&device_info);
            let bus_info = PCIBus::new(segment, secondary_bus, Some(&weak));
            assert!(device_info.child_bus.set(Some(bus_info)).is_ok());
        } else {
            assert!(device_info.child_bus.set(None).is_ok());
        }

        device_info
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

    fn bridge_data(&self) -> Option<&PCIBus> {
        self.child_bus.get().unwrap().as_deref()
    }

    pub fn is_bridge(&self) -> bool {
        self.bridge_data().is_some()
    }

    pub fn secondary_bus(&self) -> Option<u8> {
        let r = self.bridge_data()?;
        Some(r.bus_id())
    }

    pub fn parent_bus(&self) -> Arc<PCIBus> {
        self.parent_bus.upgrade().expect("parent bus was dropped")
    }

    pub fn child_devices(&self) -> Option<&Vec<Arc<PCIDevice>>> {
        let r = self.bridge_data()?;
        Some(r.devices())
    }

    pub fn get_interrupt(&self, pin: PCIInterruptPin) -> InterruptAssignment {
        match InterruptAssignment::get(self.address, pin) {
            Some(v) => v,
            None => panic!(
                "could not get interrupt assignment for device {}",
                self.address
            ),
        }
    }

    /// Gets the vector mapped to the given interrupt pin for this device.
    pub fn get_interrupt_vector(&self, pin: PCIInterruptPin) -> u8 {
        self.get_interrupt(pin).interrupt_vector()
    }

    /// Get the ACPI device object that corresponds to this device, if any.
    pub fn acpi_device(&self) -> Option<&'static AcpiDevice> {
        self.acpi_device
    }

    /// Get the Base Address Registers for this device.
    ///
    /// Registers not listed here were read as having a value of zero during
    /// device enumeration and initialization.
    pub fn bars(&self) -> &Vec<BAR> {
        &self.bars
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
    unsafe fn new(address: PCIAddress, offset: u16) -> BAR {
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

            size = (!t).overflowing_add(1).0;
            config_space::write_config(address, offset, d1);
            config_space::write_config(address, offset + 4, d2);
        } else {
            bar_addr = (d1 & 0xFFFF_FFF0) as usize;
            config_space::write_config(address, offset, 0xFFFF_FFFF);

            let s1 = config_space::read_config(address, offset);
            let t = s1 & 0xFFFF_FFF0;

            size = (!t).overflowing_add(1).0 as usize;
            config_space::write_config(address, offset, d1);
        }

        BAR {
            address: bar_addr,
            size,
            io,
            large,
            prefetch,
            offset,
        }
    }

    /// The number of this BAR in its device's PCI configuration space.
    ///
    /// For ordinary devices, BAR numbers range from 0 to 5 (inclusive).
    /// For PCI-PCI bridges, BAR numbers can be either 0 or 1.
    pub fn number(&self) -> usize {
        let offset = self.offset as usize;
        (offset - 0x10) / 4
    }

    /// Gets whether this BAR refers to a region in memory or to a region in
    /// the I/O port address space.
    pub fn io(&self) -> bool {
        self.io
    }

    /// For memory BARs, if this flag is set, reads from this region will not
    /// cause any side effects.
    ///
    /// When this flag is set, the memory region covered by this BAR can be
    /// safely mapped as Write-Through instead of as purely Uncacheable to
    /// improve performance.
    pub fn prefetch(&self) -> bool {
        self.prefetch
    }

    /// For memory BARs, gets whether this region supports 64-bit addresses.
    pub fn large(&self) -> bool {
        self.large
    }

    /// Gets the size of this region in its address space.
    pub fn size(&self) -> usize {
        self.size
    }

    /// Gets the address in memory referenced by this BAR.
    ///
    /// If this returns None, this BAR either refers to an I/O port address, or
    /// is otherwise an invalid address in memory.
    pub fn memory_address<T>(&self) -> Option<PhysicalPointer<T>> {
        if self.io {
            return None;
        }

        PhysicalPointer::new(self.address)
    }

    /// Gets the address in I/O port space referenced by this BAR.
    ///
    /// If this returns None, this BAR refers to an address in memory instead.
    pub fn io_address(&self) -> Option<u16> {
        if !self.io {
            return None;
        }

        assert!(
            self.address < 0xFFFF,
            "invalid IO BAR address {:#x}",
            self.address
        );

        Some(self.address as u16)
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

pub struct PCIBus {
    segment: u16,
    secondary_bus: u8,
    devices: OnceCell<Vec<Arc<PCIDevice>>>,
    bridge: Option<Weak<PCIDevice>>,
    acpi_device: &'static AcpiDevice,
}

impl PCIBus {
    fn new(segment: u16, bus: u8, bridge: Option<&Weak<PCIDevice>>) -> Arc<PCIBus> {
        let acpi_device = if let Some(dev) = bridge {
            // get the ACPI device for the parent bridge
            let dev = dev.upgrade().unwrap();
            if let Some(acpi_device) = dev.acpi_device {
                acpi_device
            } else {
                panic!(
                    "could not find ACPI device for PCI bus {:04x}:{:02x}",
                    segment, bus
                );
            }
        } else {
            // This is a root bus, so get the ACPI device for the root bridge
            // (i.e. \_SB_.PCI0)
            //
            // TODO: this will probably explode in systems with multiple host
            // bridges
            acpi::get_root_bridge_device()
        };

        let obj = Arc::new(PCIBus {
            segment,
            secondary_bus: bus,
            devices: OnceCell::new(),
            bridge: bridge.cloned(),
            acpi_device,
        });

        let mut devices = Vec::new();
        let parent_bus = Arc::downgrade(&obj);

        for device in 0..32 {
            if !enumeration::device_present(segment, bus, device, 0) {
                // no device here
                continue;
            }

            devices.push(PCIDevice::new(segment, bus, device, 0, parent_bus.clone()));

            if enumeration::is_multi_function(segment, bus, device, 0) {
                for function in 1..8 {
                    if enumeration::device_present(segment, bus, device, function) {
                        devices.push(PCIDevice::new(
                            segment,
                            bus,
                            device,
                            function,
                            parent_bus.clone(),
                        ));
                    }
                }
            }
        }

        assert!(obj.devices.set(devices).is_ok());

        obj
    }

    pub fn segment_id(&self) -> u16 {
        self.segment
    }

    pub fn bus_id(&self) -> u8 {
        self.secondary_bus
    }

    pub fn bridge(&self) -> Option<Arc<PCIDevice>> {
        self.bridge
            .clone()
            .map(|weak| weak.upgrade().expect("bus bridge device was dropped"))
    }

    pub fn devices(&self) -> &Vec<Arc<PCIDevice>> {
        self.devices.get().unwrap()
    }

    pub fn acpi_device(&self) -> &'static AcpiDevice {
        self.acpi_device
    }
}

pub fn enumerate_devices() {
    let mut root_busses: Vec<Arc<PCIBus>> = Vec::new();

    println!("pci: enumerating PCI bus topology...");

    if enhanced_cam::ecam_supported() {
        for (segment, busses) in enhanced_cam::busses() {
            for bus in busses {
                let bus_obj = PCIBus::new(segment, bus, None);
                root_busses.push(bus_obj);
            }
        }
    } else {
        // Assume 00:00.0 is the host bridge.
        if enumeration::is_multi_function(0, 0, 0, 0) {
            // Multiple PCI host controllers
            for bus in 0..8 {
                if enumeration::device_present(0, 0, 0, bus) {
                    let bus_obj = PCIBus::new(0, bus, None);
                    root_busses.push(bus_obj);
                }
            }
        } else {
            // Single PCI host controller
            root_busses.push(PCIBus::new(0, 0, None));
        }
    }

    assert!(root_busses.len() > 0, "could not find any PCI root busses?");
    if root_busses.len() == 1 {
        println!("pci: enumerated 1 root bus");
    } else {
        println!("pci: enumerated {} root busses", root_busses.len());
    }

    if ROOT_BUSSES.set(root_busses).is_err() {
        panic!("already initialized");
    }

    // Now walk the PCI topology again to build a map from addresses to device
    // structs.
    let mut map: HashMap<PCIAddress, Arc<PCIDevice>> = HashMap::new();

    for pci_bus in ROOT_BUSSES.get().unwrap().iter() {
        for device in pci_bus.devices() {
            init_pci_map(device, &mut map);
        }
    }

    if DEVICES.set(map).is_err() {
        panic!("already initialized");
    }

    println!("pci: detected PCI bus topology:");
    print_pci_topology(ROOT_BUSSES.get().unwrap());
}

fn init_pci_map(cur: &Arc<PCIDevice>, map: &mut HashMap<PCIAddress, Arc<PCIDevice>>) {
    let address = cur.address();
    if map.insert(address, cur.clone()).is_some() {
        panic!("device {} enumerated twice", address);
    }

    if let Some(children) = cur.child_devices() {
        for child in children.iter() {
            init_pci_map(child, map);
        }
    }
}

fn print_pci_topology(roots: &Vec<Arc<PCIBus>>) {
    for bus in roots.iter() {
        let mut device_count = Vec::new();

        print!("pci: [{:04x}:{:02x}]-", bus.segment_id(), bus.bus_id());
        print_pci_topology_bus(&*bus, &mut device_count);
        print!("\n");
    }
}

fn print_pci_topology_bus(bus: &PCIBus, device_count: &mut Vec<usize>) {
    let devices = bus.devices();
    if devices.len() == 0 {
        return;
    }

    device_count.push(devices.len());

    if devices.len() == 1 {
        print_pci_topology_device(&devices[0], device_count, true);
    } else {
        for (i, device) in devices.iter().enumerate() {
            let l = device_count.last_mut().unwrap();
            *l -= 1;

            if i > 0 {
                print_pci_topology_indent(device_count);
            }

            print_pci_topology_device(device, device_count, false);

            if i != (devices.len() - 1) {
                print!("\n");
            }
        }
    }

    device_count.pop();
}

fn print_pci_topology_device(
    device: &Arc<PCIDevice>,
    device_count: &mut Vec<usize>,
    only_child: bool,
) {
    if only_child {
        print!("--{}", device.address());
    } else {
        let count = *device_count.last().unwrap();
        if count > 0 {
            print!("+-{}", device.address());
        } else {
            print!("\\-{}", device.address());
        }
    }

    if !device.is_bridge() {
        return;
    }

    print!("-[{:02x}]-", device.secondary_bus().unwrap());
    print_pci_topology_bus(device.bridge_data().unwrap(), device_count);
}

fn print_pci_topology_indent(device_count: &Vec<usize>) {
    print!("pci:           ");

    for idx in device_count.iter().take(device_count.len() - 1) {
        if *idx > 0 {
            print!("|");
        } else {
            print!(" ");
        }

        print!("              ");
    }
}

pub fn get_root_busses() -> &'static Vec<Arc<PCIBus>> {
    ROOT_BUSSES.get().unwrap()
}

pub fn get_device_map() -> &'static HashMap<PCIAddress, Arc<PCIDevice>> {
    DEVICES.get().unwrap()
}
