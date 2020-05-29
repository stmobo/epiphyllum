use alloc_crate::boxed::Box;
use alloc_crate::sync::{Arc, Weak};
use alloc_crate::vec::Vec;
use core::fmt;
use core::fmt::Display;

use crate::acpica::AcpiDevice;
use crate::lock::OnceCell;
use crate::malloc::physical_mem;
use crate::paging;
use crate::structures::HashMap;

use super::acpi;
use super::config_space;
use super::enhanced_cam;
use super::enumeration;
use super::PCIAddress;

static DEVICES: OnceCell<HashMap<PCIAddress, Arc<PCIDevice>>> = OnceCell::new();
static ROOT_BUSSES: OnceCell<Vec<PCIBus>> = OnceCell::new();

pub struct PCIDevice {
    address: PCIAddress,
    parent: Option<Weak<PCIDevice>>,
    device_id: u16,
    vendor_id: u16,
    major_class: u8,
    minor_class: u8,
    prog_if: u8,
    bars: Vec<BAR>,
    bus_data: OnceCell<Option<Box<PCIBus>>>,
    acpi_device: Option<&'static AcpiDevice>,
}

impl PCIDevice {
    fn new(
        segment: u16,
        bus: u8,
        device: u8,
        function: u8,
        parent: Option<Weak<PCIDevice>>,
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

        if bars.len() > 0 {
            println!("pci:    Device BARs:");
            for bar in bars.iter() {
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
            bus_data: OnceCell::new(),
            acpi_device,
            parent,
        });

        if (major_class == 0x06) && (minor_class == 0x04) {
            // This is a PCI-PCI bridge, enumerate the child bus
            let secondary_bus = enumeration::get_secondary_bus(segment, bus, device, function);
            println!(
                "pci:    PCI-PCI bridge to secondary bus {:02x}",
                secondary_bus
            );

            let weak = Arc::downgrade(&device_info);
            let bus_info = Box::new(PCIBus::new(segment, secondary_bus, Some(&weak)));
            assert!(device_info.bus_data.set(Some(bus_info)).is_ok());
        } else {
            assert!(device_info.bus_data.set(None).is_ok());
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

    fn bus_data(&self) -> Option<&PCIBus> {
        self.bus_data.get().unwrap().as_deref()
    }

    pub fn is_bridge(&self) -> bool {
        self.bus_data().is_some()
    }

    pub fn secondary_bus(&self) -> Option<u8> {
        let r = self.bus_data()?;
        Some(r.bus_id())
    }

    pub fn child_devices(&self) -> Option<&Vec<Arc<PCIDevice>>> {
        let r = self.bus_data()?;
        Some(r.devices())
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

#[derive(Debug, Copy, Clone)]
#[repr(u8)]
pub enum PCIInterruptPin {
    LNKA = 0x00,
    LNKB = 0x01,
    LNKC = 0x02,
    LNKD = 0x03,
}

impl PCIInterruptPin {
    /// Maps an interrupt pin on a device downstream of a PCI-PCI bridge to the
    /// corresponding upstream interrupt pin.
    ///
    /// # Examples
    /// For device 0, this is simply an identity map: LNKA on the child maps to
    /// LNKA on the parent bus, and so on.
    ///
    /// For device 1, all interrupt pins shift 1 over to the right: LNKA on the
    /// child maps to LNK_B_ on the parent bus, etc.
    ///
    /// This should also carry over to nested busses as well.
    /// Consider the following (contrived) PCI topology:
    /// ```text
    /// [0000:00]-+-00:00.0                                (Host Bridge)
    ///           \-00:02.0-[01]-+-01:00.0                 (PCI-PCI bridge from bus 00 -> 01)
    ///                          +-01:03.0-[02]-+-02:00.0  (PCI-PCI bridge from bus 01 -> 02)
    ///                          |              \-02:02.0  (Device)
    ///                          \-01:05.0                 (Device)
    /// ```
    ///
    /// The routing of pin `LNKA` from device `02:02.0` would look like:
    /// ```text
    /// LNKA      -> LNKC      -> LNKB
    /// (02:02.0)    (01:03.0)    (00:02.0)
    /// [0]          [0+2 = 2]    [2+3 = 5 mod 4 = 1]
    /// ```
    ///
    /// The routing of pin `LNKC` from device `01:05.0` is:
    /// ```text
    /// LNKC      -> LNKD
    /// (01:05.0)    (00:02.0)
    /// [2]          [2+5 = 7 mod 4 = 3]
    /// ```
    ///
    /// For devices on the root bridge, the ACPI `_PRT` table specifies what
    /// PCI interrupt link devices correspond to each interrupt pin.
    pub fn bridge_swizzle(self, device_no: u8) -> PCIInterruptPin {
        debug_assert!(device_no < 0x1F, "invalid device number {:02x}", device_no);

        let new_pin = ((self as u8) + device_no) & 0x03;
        match new_pin {
            0 => PCIInterruptPin::LNKA,
            1 => PCIInterruptPin::LNKB,
            2 => PCIInterruptPin::LNKC,
            3 => PCIInterruptPin::LNKD,
            _ => unreachable!(),
        }
    }
}

impl Display for PCIInterruptPin {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            PCIInterruptPin::LNKA => write!(f, "LNKA"),
            PCIInterruptPin::LNKB => write!(f, "LNKB"),
            PCIInterruptPin::LNKC => write!(f, "LNKC"),
            PCIInterruptPin::LNKD => write!(f, "LNKD"),
        }
    }
}

pub struct PCIBus {
    segment: u16,
    secondary_bus: u8,
    devices: Vec<Arc<PCIDevice>>,
}

impl PCIBus {
    fn new(segment: u16, bus: u8, bridge: Option<&Weak<PCIDevice>>) -> PCIBus {
        let mut devices = Vec::new();

        for device in 0..32 {
            if !enumeration::device_present(segment, bus, device, 0) {
                // no device here
                continue;
            }

            let parent = bridge.cloned();
            devices.push(PCIDevice::new(segment, bus, device, 0, parent));

            if enumeration::is_multi_function(segment, bus, device, 0) {
                for function in 1..8 {
                    let parent = bridge.cloned();
                    if enumeration::device_present(segment, bus, device, function) {
                        devices.push(PCIDevice::new(segment, bus, device, function, parent));
                    }
                }
            }
        }

        PCIBus {
            segment,
            secondary_bus: bus,
            devices,
        }
    }

    pub fn segment_id(&self) -> u16 {
        self.segment
    }

    pub fn bus_id(&self) -> u8 {
        self.secondary_bus
    }

    pub fn devices(&self) -> &Vec<Arc<PCIDevice>> {
        &self.devices
    }
}

pub fn enumerate_devices() {
    let mut root_busses: Vec<PCIBus> = Vec::new();

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

fn print_pci_topology(roots: &Vec<PCIBus>) {
    for bus in roots.iter() {
        let mut device_count = Vec::new();

        print!("pci: [{:04x}:{:02x}]-", bus.segment_id(), bus.bus_id());
        print_pci_topology_bus(bus, &mut device_count);
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
    print_pci_topology_bus(device.bus_data().unwrap(), device_count);
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
