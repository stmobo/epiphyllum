use alloc_crate::boxed::Box;
use alloc_crate::sync::Arc;
use alloc_crate::vec::Vec;
use core::fmt;
use core::fmt::Display;

use super::config_space;
use super::enhanced_cam;
use super::PCIAddress;
use crate::acpica;
use crate::acpica::AcpiDevice;
use crate::lock::OnceCell;
use crate::malloc::physical_mem;
use crate::paging;
use crate::structures::HashMap;

static ACPI_BUS_LIST: OnceCell<Vec<(u8, &'static AcpiDevice)>> = OnceCell::new();
static ACPI_MAP: OnceCell<HashMap<PCIAddress, &'static AcpiDevice>> = OnceCell::new();
static DEVICES: OnceCell<HashMap<PCIAddress, Arc<PCIDevice>>> = OnceCell::new();
static ROOT_BUSSES: OnceCell<Vec<Arc<PCIDevice>>> = OnceCell::new();

pub struct PCIDevice {
    address: PCIAddress,
    parent: Option<Arc<PCIDevice>>,
    device_id: u16,
    vendor_id: u16,
    major_class: u8,
    minor_class: u8,
    prog_if: u8,
    bars: Vec<BAR>,
    bus_data: OnceCell<Option<Box<PCIBusInfo>>>,
    acpi_device: Option<&'static AcpiDevice>,
}

impl PCIDevice {
    fn new(
        segment: u16,
        bus: u8,
        device: u8,
        function: u8,
        parent: Option<Arc<PCIDevice>>,
    ) -> Arc<PCIDevice> {
        let address = PCIAddress::new(segment, bus, device, function);
        let (major_class, minor_class, prog_if) = read_class(segment, bus, device, function);
        let (vendor_id, device_id) = read_dev_vendor_id(segment, bus, device, function);

        let data = unsafe { config_space::read_config(address, 12) };
        let header_type = (((data >> 16) & 0xFF) as u8) & 0x7F;
        let mut bars = Vec::new();

        let dev_map = ACPI_MAP.get().unwrap();
        let acpi_device = dev_map.get(&address).copied();

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
            let secondary_bus = get_secondary_bus(segment, bus, device, function);
            println!(
                "pci:    PCI-PCI bridge to secondary bus {:02x}",
                secondary_bus
            );

            let children = enumerate_bus(segment, secondary_bus, Some(&device_info));

            assert!(device_info
                .bus_data
                .set(Some(Box::new(PCIBusInfo {
                    secondary_bus,
                    children,
                })))
                .is_ok());
        } else if (major_class == 0x06) && (minor_class == 0x00) && (bus == 0) && (device == 0) {
            // This is the host PCI bridge, treat all subfunctions as being child busses
            let children = enumerate_bus(segment, function, Some(&device_info));
            println!("pci:    host PCI bridge to bus {:02x}", function);

            assert!(device_info
                .bus_data
                .set(Some(Box::new(PCIBusInfo {
                    secondary_bus: function,
                    children,
                })))
                .is_ok());
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

    fn bus_data(&self) -> Option<&PCIBusInfo> {
        self.bus_data.get().unwrap().as_deref()
    }

    pub fn is_bridge(&self) -> bool {
        self.bus_data().is_some()
    }

    pub fn secondary_bus(&self) -> Option<u8> {
        let r = self.bus_data()?;
        Some(r.secondary_bus)
    }

    pub fn child_devices(&self) -> Option<&Vec<Arc<PCIDevice>>> {
        let r = self.bus_data()?;
        Some(&r.children)
    }

    pub fn read_config(&self, offset: u16) -> u32 {
        unsafe { config_space::read_config(self.address, offset) }
    }

    pub fn write_config(&mut self, offset: u16, value: u32) {
        unsafe { config_space::write_config(self.address, offset, value) }
    }
}

pub struct PCIBusInfo {
    secondary_bus: u8,
    children: Vec<Arc<PCIDevice>>,
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

fn get_secondary_bus(segment: u16, bus: u8, device: u8, function: u8) -> u8 {
    let t = unsafe { config_space::read_config_split(segment, bus, device, function, 0x18) };
    ((t >> 8) & 0xFF) as u8
}

fn enumerate_device(
    segment: u16,
    bus: u8,
    device: u8,
    parent: Option<&Arc<PCIDevice>>,
    out_list: &mut Vec<Arc<PCIDevice>>,
) {
    if !device_present(segment, bus, device, 0) {
        // no device here
        return;
    }

    out_list.push(PCIDevice::new(segment, bus, device, 0, parent.cloned()));
    if is_multi_function(segment, bus, device, 0) {
        for function in 1..8 {
            if device_present(segment, bus, device, function) {
                out_list.push(PCIDevice::new(
                    segment,
                    bus,
                    device,
                    function,
                    parent.cloned(),
                ));
            }
        }
    }
}

fn enumerate_bus(segment: u16, bus: u8, parent: Option<&Arc<PCIDevice>>) -> Vec<Arc<PCIDevice>> {
    let mut out_list = Vec::new();

    for device in 0..32 {
        // HACK: avoid infinite recursion at the root bridge
        if (segment == 0) && (bus == 0) && (device == 0) {
            continue;
        }

        enumerate_device(segment, bus, device, parent, &mut out_list)
    }

    out_list
}

pub fn enumerate_devices() {
    let mut root_busses: Vec<Arc<PCIDevice>> = Vec::new();

    if enhanced_cam::ecam_supported() {
        for (segment, busses) in enhanced_cam::busses() {
            for bus in busses {
                enumerate_device(segment, bus, 0, None, &mut root_busses);
            }
        }
    } else {
        // Assume 00:00.0 is the host bridge.
        // Each child of the host bridge corresponds to a bus.
        enumerate_device(0, 0, 0, None, &mut root_busses);
    }

    if ROOT_BUSSES.set(root_busses).is_err() {
        panic!("already initialized");
    }

    // Now walk the PCI topology again to build a map from addresses to device
    // structs.
    let mut map: HashMap<PCIAddress, Arc<PCIDevice>> = HashMap::new();

    println!("pci: detected PCI bus topology:");
    for bus_device in ROOT_BUSSES.get().unwrap().iter() {
        init_pci_map(bus_device, &mut map);
        print_pci_topology(bus_device, 0, true);
    }

    if DEVICES.set(map).is_err() {
        panic!("already initialized");
    }
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

/// Displays the PCI topology rooted at this device in an lspci-ish tree form.
fn print_pci_topology(cur: &Arc<PCIDevice>, level: u64) {
    print!("pci: ");

    for _ in 0..level {
        print!("               ");
    }

    if !is_last_child {
        print!("+-");
    } else if level != 0 {
        print!("\\-");
    } else {
        print!("  ");
    }

    print_pci_topology_child(cur, level);
}

fn print_pci_topology_child(cur: &Arc<PCIDevice>, level: u64) {
    print!("{}", cur.address());

    if cur.is_bridge() {
        let bus = cur.secondary_bus().unwrap();
        let children = cur.child_devices().unwrap();

        if children.len() > 0 {
            if children.len() > 1 {
                print!("-[{:02x}]-+-", bus);
                print_pci_topology_child(&children[0], level + 1);

                for i in 1..(children.len() - 1) {
                    print_pci_topology(&children[i], level + 1);
                }

                print_pci_topology(&children[children.len() - 1], level + 1);
            } else {
                print!("-[{:02x}]---", bus);
                print_pci_topology_child(&children[0], level + 1);
            }
        } else {
            print!("\n");
        }
    } else {
        print!("\n");
    }
}

fn get_root_acpi_device() -> Option<&'static AcpiDevice> {
    for (_, device) in acpica::get_device_map().iter() {
        if device.is_pci_root() {
            return Some(device);
        }
    }

    None
}

fn enumerate_bus_acpi_devices(
    bus: u8,
    device: &'static AcpiDevice,
    bus_list: &mut Vec<(u8, &'static AcpiDevice)>,
    dev_map: &mut HashMap<PCIAddress, &'static AcpiDevice>,
) {
    bus_list.push((bus, device));
    for child in device.children() {
        if let Some(addr) = child.address() {
            let function = (addr & 0x07) as u8;
            let dev_id = ((addr >> 16) & 0x1F) as u8;

            let pci_addr = PCIAddress::new(0, bus, dev_id, function);
            if dev_map.insert(pci_addr, child).is_some() {
                panic!("PCI address collision in dev map");
            }

            let (major_class, minor_class, _) = read_class(0, bus, dev_id, function);
            if (major_class != 0x06) || (minor_class != 0x04) {
                // not a PCI-PCI bridge
                continue;
            }

            let child_bus = get_secondary_bus(0, bus, dev_id, function);
            enumerate_bus_acpi_devices(child_bus, child, bus_list, dev_map);
        }
    }
}

// Enumerate all PCI devices in the ACPI namespace.
pub fn enumerate_acpi() {
    let mut bus_list = Vec::new();
    let mut dev_map: HashMap<PCIAddress, &'static AcpiDevice> = HashMap::new();
    let root = get_root_acpi_device().expect("could not find ACPI device for PCI root bridge");

    // Assume that the root bridge is bus 0.
    enumerate_bus_acpi_devices(0, root, &mut bus_list, &mut dev_map);

    if ACPI_BUS_LIST.set(bus_list).is_err() {
        panic!("already initialized");
    }

    if ACPI_MAP.set(dev_map).is_err() {
        panic!("already initialized");
    }
}
