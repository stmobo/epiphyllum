use alloc_crate::sync::Arc;
use alloc_crate::vec::Vec;
use core::fmt;
use core::fmt::Display;
use core::sync::atomic::{AtomicU32, AtomicU8, Ordering};

use super::device;
use super::{PCIAddress, PCIDevice};
use crate::acpica::resource::{ExtendedIrq, Polarity, TriggerMode};
use crate::acpica::{AcpiDevice, AcpiResult, PCIInterruptSource};
use crate::devices::io_apic::IOAPIC;
use crate::lock::OnceCell;
use crate::structures::HashMap;

static INT_LINKS: OnceCell<Vec<InterruptLinkDevice>> = OnceCell::new();
static INT_ASSIGNMENTS: OnceCell<HashMap<PCIAddress, Vec<InterruptAssignment>>> = OnceCell::new();

#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd)]
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

    fn next_pin(self) -> PCIInterruptPin {
        match self {
            PCIInterruptPin::LNKA => PCIInterruptPin::LNKB,
            PCIInterruptPin::LNKB => PCIInterruptPin::LNKC,
            PCIInterruptPin::LNKC => PCIInterruptPin::LNKD,
            PCIInterruptPin::LNKD => PCIInterruptPin::LNKA,
        }
    }

    fn prev_pin(self) -> PCIInterruptPin {
        match self {
            PCIInterruptPin::LNKA => PCIInterruptPin::LNKD,
            PCIInterruptPin::LNKB => PCIInterruptPin::LNKA,
            PCIInterruptPin::LNKC => PCIInterruptPin::LNKB,
            PCIInterruptPin::LNKD => PCIInterruptPin::LNKC,
        }
    }

    fn extend(self) -> [PCIInterruptPin; 4] {
        [
            self,
            self.next_pin(),
            self.next_pin().next_pin(),
            self.prev_pin(),
        ]
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

fn get_root_pin_map(device: Arc<PCIDevice>) -> (PCIInterruptPin, PCIAddress) {
    let mut cur_pin = PCIInterruptPin::LNKA;
    let mut cur_device = device;

    loop {
        let bus = cur_device.parent_bus();
        if let Some(bridge) = bus.bridge() {
            cur_pin = cur_pin.bridge_swizzle(cur_device.address().device());
            cur_device = bridge;
        } else {
            // we have reached the root node
            break;
        }
    }

    (cur_pin, cur_device.address())
}

pub struct InterruptLinkDevice {
    segment_id: u16,
    bus_id: u8,
    acpi_device: &'static AcpiDevice,
    current_irq: AtomicU32,
    possible_irqs: ExtendedIrq,
    interrupt_vector: AtomicU8,
    weight: u64,
    link_device_number: usize,
}

impl InterruptLinkDevice {
    pub fn set_irq_number(&self, irq_no: u32) -> AcpiResult<()> {
        assert!(self.possible_irqs.interrupts.contains(&irq_no));

        let mut new_rsc = self.possible_irqs.clone();
        new_rsc.interrupts = vec![irq_no];

        let resources = vec![new_rsc.serialize()];
        unsafe { self.acpi_device.set_current_resources(&resources)? };

        let new_cur_rsc = match self.acpi_device.current_resources::<ExtendedIrq>() {
            Ok(r) => {
                assert_eq!(
                    r.len(),
                    1,
                    "invalid resource vector length for device {}",
                    self.acpi_device
                );

                let rsc: ExtendedIrq = r[0].clone();
                assert_eq!(
                    rsc.interrupts.len(),
                    1,
                    "invalid number of interrupts for device {}",
                    self.acpi_device
                );
                rsc
            }
            Err(e) => panic!("could not get CRS for {}: {:?}", self.acpi_device, e),
        };

        let gsi: u32 = new_cur_rsc.interrupts[0];
        assert_eq!(gsi, irq_no);

        let low_active = match new_cur_rsc.polarity {
            Polarity::Low | Polarity::Both => true,
            Polarity::High => false,
        };

        let level_sensitive = match new_cur_rsc.triggering {
            TriggerMode::LevelSensitive => true,
            TriggerMode::EdgeSensitive => false,
        };

        if let Err(_) = IOAPIC::configure_gsi(gsi as u8, low_active, level_sensitive, false) {
            panic!("could not reconfigure GSI {} at IOAPIC", gsi);
        }

        println!(
            "pci: {} => IRQ {} (weight {})",
            self.acpi_device, irq_no, self.weight
        );

        print!("pci:     ");
        if low_active {
            print!("active low, ");
        } else {
            print!("active high, ");
        }

        if level_sensitive {
            print!("level-triggered, ");
        } else {
            print!("edge-triggered, ");
        }

        let vector = IOAPIC::get_gsi_vector(gsi as u8).unwrap();
        println!("vector {:02x}", vector);

        self.current_irq.store(gsi, Ordering::SeqCst);
        self.interrupt_vector.store(vector, Ordering::SeqCst);

        Ok(())
    }

    pub fn irq_number(&self) -> u32 {
        self.current_irq.load(Ordering::SeqCst)
    }

    pub fn interrupt_vector(&self) -> u8 {
        let vector = self.interrupt_vector.load(Ordering::SeqCst);
        assert_ne!(
            vector, 0,
            "interrupt vector for device {} not configured",
            self.acpi_device
        );

        vector
    }

    pub fn possible_irqs(&self) -> ExtendedIrq {
        self.possible_irqs.clone()
    }
}

#[derive(Debug, Copy, Clone)]
pub enum InterruptAssignment {
    Device(usize),
    Hardwired(u8),
}

impl InterruptAssignment {
    pub fn get(address: PCIAddress, pin: PCIInterruptPin) -> Option<InterruptAssignment> {
        let map = INT_ASSIGNMENTS.get().expect("not initialized");
        let assignments = map.get(&address)?;

        Some(match pin {
            PCIInterruptPin::LNKA => assignments[0],
            PCIInterruptPin::LNKB => assignments[1],
            PCIInterruptPin::LNKC => assignments[2],
            PCIInterruptPin::LNKD => assignments[3],
        })
    }

    pub fn gsi(self) -> u32 {
        match self {
            InterruptAssignment::Hardwired(gsi) => gsi as u32,
            InterruptAssignment::Device(device_no) => {
                let link_devices = INT_LINKS.get().expect("not initialized");
                link_devices[device_no].irq_number()
            }
        }
    }

    pub fn interrupt_vector(self) -> u8 {
        match self {
            InterruptAssignment::Hardwired(gsi) => IOAPIC::get_gsi_vector(gsi).unwrap(),
            InterruptAssignment::Device(device_no) => {
                let link_devices = INT_LINKS.get().expect("not initialized");
                link_devices[device_no].interrupt_vector()
            }
        }
    }
}

pub fn enumerate_device_interrupts() {
    let mut link_devices: Vec<InterruptLinkDevice> = Vec::new();
    let mut prts = Vec::new();

    // Get interrupt routing tables for all root busses
    for bus in device::get_root_busses().iter() {
        let acpi_device = bus.acpi_device();
        let prt = match acpi_device.pci_irq_routing() {
            Ok(prt) => prt,
            Err(e) => panic!(
                "could not get PCI IRQ routing table for bus {:04x}:{:02x} - {:?}",
                bus.segment_id(),
                bus.bus_id(),
                e
            ),
        };

        // Build a list of all interrupt link devices
        for entry in prt.iter() {
            if let PCIInterruptSource::Device(link_device) = entry.interrupt_source() {
                if link_devices
                    .iter()
                    .find(|link| {
                        (link.segment_id == bus.segment_id())
                            && (link.bus_id == bus.bus_id())
                            && (link.acpi_device == link_device)
                    })
                    .is_none()
                {
                    let prs = match link_device.all_possible_resources() {
                        Ok(r) => r,
                        Err(e) => panic!(
                            "could not get possible resource settings for device {}: {:?}",
                            link_device, e
                        ),
                    };

                    let crs = match link_device.all_current_resources() {
                        Ok(r) => r,
                        Err(e) => panic!(
                            "could not get current resource settings for device {}: {:?}",
                            link_device, e
                        ),
                    };

                    assert_eq!(
                        prs.len(),
                        1,
                        "invalid number of possible resources for device {}",
                        link_device
                    );

                    assert_eq!(
                        crs.len(),
                        1,
                        "invalid number of current resources for device {}",
                        link_device
                    );

                    let current_irq: ExtendedIrq = crs[0].parse::<ExtendedIrq>().unwrap();
                    let possible_irqs: ExtendedIrq = prs[0].parse::<ExtendedIrq>().unwrap();

                    assert_eq!(
                        current_irq.interrupts.len(),
                        1,
                        "invalid number of current IRQs for device {}",
                        link_device
                    );

                    let link_dev = InterruptLinkDevice {
                        segment_id: bus.segment_id(),
                        bus_id: bus.bus_id(),
                        acpi_device: link_device,
                        current_irq: AtomicU32::new(current_irq.interrupts[0]),
                        possible_irqs,
                        weight: 0,
                        link_device_number: link_devices.len(),
                        interrupt_vector: AtomicU8::new(0),
                    };

                    link_devices.push(link_dev);
                }
            }
        }

        prts.push((bus.segment_id(), bus.bus_id(), prt));
    }

    let mut int_map: HashMap<PCIAddress, Vec<InterruptAssignment>> = HashMap::new();

    // Now go through all devices and map interrupt numbers:
    for (address, device) in device::get_device_map().iter() {
        let address = *address;
        let (root_pin, bridge_address) = get_root_pin_map(device.clone());

        // Find the PRT for this device:
        let prt = prts
            .iter()
            .find(|t| (t.0 == bridge_address.segment()) && (t.1 == bridge_address.bus()));

        assert!(
            prt.is_some(),
            "could not find PRT for PCI device {} (bridge address {})",
            address,
            bridge_address
        );
        let prt = prt.unwrap();

        // Get the PRT entries for each of the four interrupt pins...
        let pins = root_pin.extend();
        let routing_entries = pins.iter().map(|pin| {
            let bridge_pin = *pin;
            let entry = prt
                .2
                .iter()
                .find(|e| (e.pin() == bridge_pin) && (e.device_id() == bridge_address.device()));

            assert!(
                entry.is_some(),
                "could not find PRT entry for PCI device {}, pin {}",
                bridge_address,
                bridge_pin
            );

            entry.unwrap().clone()
        });

        //println!("pci:     device {}:", address);

        // Convert those PRT entries into InterruptAssignments...
        let assignments: Vec<InterruptAssignment> = routing_entries
            .enumerate()
            .map(|(i, entry)| {
                let device_pin = match i {
                    0 => PCIInterruptPin::LNKA,
                    1 => PCIInterruptPin::LNKB,
                    2 => PCIInterruptPin::LNKC,
                    3 => PCIInterruptPin::LNKD,
                    _ => unreachable!(),
                };

                match entry.interrupt_source() {
                    PCIInterruptSource::Hardwired(gsi) => {
                        // Configure GSI as level-triggered, active low as per
                        // PCI spec by default
                        if let Err(_) = IOAPIC::configure_gsi(gsi, true, true, false) {
                            panic!("could not configure hardwired GSI {}", gsi);
                        }

                        InterruptAssignment::Hardwired(gsi)
                    }
                    PCIInterruptSource::Device(d) => {
                        // Find the given interrupt link device
                        let linked = link_devices.iter_mut().find(|l| {
                            l.acpi_device == d
                        });
                        assert!(
                            linked.is_some(),
                            "could not find interrupt link device for PCI device {} (bridge address {}), device pin {}",
                            address,
                            bridge_address,
                            device_pin
                        );

                        let linked = linked.unwrap();

                        // increase the weight (# of linked interrupts) for this
                        // interrupt device
                        linked.weight += 1;

                        // Get its number, and use that for the interrupt asssignment
                        InterruptAssignment::Device(linked.link_device_number)
                    }
                }
            })
            .collect();

        int_map.insert(address, assignments);
    }

    // Now reassign interrupts based on each link device's weight.

    // Initialize a map from IRQ numbers to linked interrupt counts:
    let mut int_counts: HashMap<u32, u64> = HashMap::new();
    for device in link_devices.iter() {
        for irq in device.possible_irqs.interrupts.iter() {
            int_counts.insert(*irq, 0);
        }
    }

    // Give interrupt devices with more linked interrupts first pick for IRQ
    // numbers.
    link_devices.sort_unstable_by(|a, b| a.weight.cmp(&b.weight).reverse());

    println!(
        "pci: enumerated {} interrupt link devices",
        link_devices.len()
    );

    for device in link_devices.iter() {
        // Out of the possible IRQs for this device, find the one with the least
        // number of currently-linked interrupts
        let min_irq = *device
            .possible_irqs
            .interrupts
            .iter()
            .min_by_key(|irq| *int_counts.get(*irq).unwrap())
            .unwrap();

        let count = *int_counts.get(&min_irq).unwrap();
        if let Err(e) = device.set_irq_number(min_irq) {
            panic!(
                "could not set IRQ number for interrupt link device {}: {:?}",
                device.acpi_device, e
            );
        }

        // Update the new count of linked interrupts for this IRQ number
        int_counts.insert(min_irq, count + device.weight);
    }

    if INT_LINKS.set(link_devices).is_err() {
        panic!("already initialized");
    }

    if INT_ASSIGNMENTS.set(int_map).is_err() {
        panic!("already initialized");
    }
}
