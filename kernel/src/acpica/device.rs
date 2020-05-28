use alloc_crate::string::String;
use alloc_crate::vec::Vec;
use core::fmt;
use core::fmt::Display;
use core::mem;
use core::ptr;
use core::slice;
use core::str;

use super::bindings::*;
use super::get_name;
use super::os_services;
use super::{AcpiError, AcpiResult, AcpiStatus};
use crate::lock::OnceCell;
use crate::structures::AVLTree;

const ACPI_TYPE_DEVICE: u32 = 0x06;

static DEVICES: OnceCell<AVLTree<ACPI_HANDLE, AcpiDevice>> = OnceCell::new();

// Wrapper around an ACPI_HANDLE pointing to a Device.
pub struct AcpiDevice {
    handle: ACPI_HANDLE,
    full_name: String,
    single_name: String,
    hardware_id: Option<String>,
    unique_id: Option<String>,
    address: Option<u64>,
    compatible_ids: Option<Vec<String>>,
    highest_d_states: Option<[u8; 4]>,
    lowest_d_states: Option<[u8; 5]>,
    is_pci_root: bool,
}

impl AcpiDevice {
    fn new(handle: ACPI_HANDLE) -> AcpiResult<AcpiDevice> {
        let full_name = get_name(handle, true).expect("could not get ACPI device full name");
        let mut device_info: *mut ACPI_DEVICE_INFO = ptr::null_mut();

        unsafe {
            AcpiStatus::from(AcpiGetObjectInfo(handle, &mut device_info))?;
            if device_info.is_null() {
                return Err(AcpiError::AE_NO_MEMORY);
            }

            if (*device_info).Type != ACPI_TYPE_DEVICE {
                // handle does not point to a device
                return Err(AcpiError::AE_TYPE);
            }

            let is_pci_root = ((*device_info).Flags & 0x01) != 0;

            let lowest_d_states: Option<[u8; 5]>;
            if ((*device_info).Valid & 0x0200) != 0 {
                // _SxW is valid:
                lowest_d_states = Some((*device_info).LowestDstates);
            } else {
                lowest_d_states = None;
            }

            let highest_d_states: Option<[u8; 4]>;
            if ((*device_info).Valid & 0x0100) != 0 {
                // _SxD is valid:
                highest_d_states = Some((*device_info).HighestDstates);
            } else {
                highest_d_states = None;
            }

            let compatible_ids: Option<Vec<String>>;
            if ((*device_info).Valid & 0x0020) != 0 {
                // _CID is valid:
                compatible_ids = Some(
                    Self::copy_pnp_id_list((*device_info).CompatibleIdList)
                        .or(Err(AcpiError::AE_ERROR))?,
                );
            } else {
                compatible_ids = None;
            }

            let hardware_id: Option<String>;
            if ((*device_info).Valid & 0x0004) != 0 {
                // _HID is valid:
                hardware_id = Some(
                    Self::copy_pnp_id((*device_info).HardwareId).or(Err(AcpiError::AE_ERROR))?,
                );
            } else {
                hardware_id = None;
            }

            let unique_id: Option<String>;
            if ((*device_info).Valid & 0x0008) != 0 {
                // _UID is valid:
                unique_id =
                    Some(Self::copy_pnp_id((*device_info).UniqueId).or(Err(AcpiError::AE_ERROR))?);
            } else {
                unique_id = None;
            }

            let address: Option<u64>;
            if ((*device_info).Valid & 0x0002) != 0 {
                // _ADR is valid:
                address = Some((*device_info).Address);
            } else {
                address = None;
            }

            let name_bytes = ((*device_info).Name as u32).to_le_bytes();
            let single_name =
                String::from(str::from_utf8(&name_bytes).or(Err(AcpiError::AE_ERROR))?);

            let device = AcpiDevice {
                handle,
                full_name,
                single_name,
                hardware_id,
                unique_id,
                address,
                compatible_ids,
                highest_d_states,
                lowest_d_states,
                is_pci_root,
            };

            os_services::AcpiOsFree(device_info as *mut cty::c_void);

            Ok(device)
        }
    }

    fn copy_pnp_id(device_id: ACPI_PNP_DEVICE_ID) -> Result<String, str::Utf8Error> {
        unsafe {
            let data = device_id.String as *const u8;
            let len = device_id.Length as usize;
            let byte_slice = slice::from_raw_parts(data, len - 1);
            Ok(String::from(str::from_utf8(byte_slice)?))
        }
    }

    fn copy_pnp_id_list(list: ACPI_PNP_DEVICE_ID_LIST) -> Result<Vec<String>, str::Utf8Error> {
        unsafe {
            let len = list.Count as usize;
            let id_ptr: *const ACPI_PNP_DEVICE_ID = list.Ids.as_ptr();
            let list_slice = slice::from_raw_parts(id_ptr, len);

            let mut out = Vec::new();
            for id in list_slice.iter() {
                out.push(Self::copy_pnp_id(*id)?);
            }

            Ok(out)
        }
    }

    pub fn full_name(&self) -> &str {
        &self.full_name
    }

    pub fn single_name(&self) -> &str {
        &self.single_name
    }

    pub fn hardware_id(&self) -> Option<&str> {
        self.hardware_id.as_deref()
    }

    pub fn unique_id(&self) -> Option<&str> {
        self.unique_id.as_deref()
    }

    pub fn address(&self) -> Option<u64> {
        self.address
    }

    pub fn compatible_ids(&self) -> Option<&Vec<String>> {
        self.compatible_ids.as_ref()
    }

    pub fn highest_d_states(&self) -> Option<&[u8; 4]> {
        self.highest_d_states.as_ref()
    }

    pub fn lowest_d_states(&self) -> Option<&[u8; 5]> {
        self.lowest_d_states.as_ref()
    }

    pub fn is_pci_root(&self) -> bool {
        self.is_pci_root
    }

    pub fn handle(&self) -> ACPI_HANDLE {
        self.handle
    }

    pub fn children(&self) -> DeviceIter {
        DeviceIter::new(self)
    }

    pub fn pci_irq_routing(&self) -> AcpiResult<Vec<PCIRoutingEntry>> {
        let mut buf = ACPI_BUFFER {
            Length: u64::MAX,
            Pointer: ptr::null_mut(),
        };

        let mut out_vec = Vec::new();

        unsafe {
            let status = AcpiGetIrqRoutingTable(self.handle, &mut buf);
            if let Err(e) = *AcpiStatus::from(status) {
                if !buf.Pointer.is_null() {
                    os_services::AcpiOsFree(buf.Pointer);
                }

                return Err(e);
            }

            let mut offset: usize = 0;

            while offset < buf.Length as usize {
                let addr = (buf.Pointer as usize) + offset;
                let entry_ptr = addr as *const ACPI_PCI_ROUTING_TABLE;

                if (*entry_ptr).Length == 0 {
                    break;
                }

                if let Ok(entry) = PCIRoutingEntry::new(entry_ptr) {
                    out_vec.push(entry);
                } else {
                    os_services::AcpiOsFree(buf.Pointer);
                    return Err(AcpiError::AE_ERROR);
                }

                offset += (*entry_ptr).Length as usize;
            }
        }

        Ok(out_vec)
    }
}

unsafe impl Send for AcpiDevice {}
unsafe impl Sync for AcpiDevice {}

pub struct DeviceIter {
    parent: ACPI_HANDLE,
    cur_child: ACPI_HANDLE,
}

impl DeviceIter {
    fn new(device: &AcpiDevice) -> DeviceIter {
        DeviceIter {
            parent: device.handle,
            cur_child: ptr::null_mut(),
        }
    }
}

impl Iterator for DeviceIter {
    type Item = &'static AcpiDevice;

    fn next(&mut self) -> Option<Self::Item> {
        unsafe {
            let mut out_handle: ACPI_HANDLE = ptr::null_mut();

            if AcpiGetNextObject(
                ACPI_TYPE_DEVICE,
                self.parent,
                self.cur_child,
                &mut out_handle,
            ) == AE_OK
            {
                self.cur_child = out_handle;
                // The device map should contain every ACPI device in the
                // system, so it should be an legitimate error for us to not
                // find the handle in the map.
                let res = get_device_map().get(&out_handle);

                if res.is_none() {
                    let name = get_name(out_handle, true).unwrap();
                    println!("acpi: could not find device {} in device map?", name);
                }

                res
            } else {
                None
            }
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

#[derive(Debug, Clone)]
pub struct PCIRoutingEntry {
    pin: PCIInterruptPin,
    address: u64,
    source: String,
    source_idx: usize,
}

impl PCIRoutingEntry {
    unsafe fn new(table: *const ACPI_PCI_ROUTING_TABLE) -> Result<PCIRoutingEntry, str::Utf8Error> {
        let address: u64 = (*table).Address;
        let pin_byte = ((*table).Pin & 0xFF) as u8;
        let source_idx = ((*table).SourceIndex & 0xFF) as usize;

        assert!(
            pin_byte <= 0x03,
            "invalid PCI interrupt pin byte {:02x}",
            pin_byte
        );
        let pin: PCIInterruptPin = mem::transmute(pin_byte);

        let src_ptr = (*table).Source.as_ptr() as *const u8;
        let src_string_len = ((*table).Length as usize) - 20;
        let src_bytes = slice::from_raw_parts(src_ptr, src_string_len);
        let source = String::from(str::from_utf8(src_bytes)?);

        Ok(PCIRoutingEntry {
            address,
            pin,
            source,
            source_idx,
        })
    }
}

impl Display for PCIRoutingEntry {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "device {:02x}: {} routed via interrupt device {} (index {})",
            (self.address >> 16) & 0x1F,
            self.pin,
            self.source,
            self.source_idx
        )
    }
}

unsafe extern "C" fn get_device_callback(
    handle: ACPI_HANDLE,
    _nest_level: UINT32,
    context: *mut cty::c_void,
    _rv: *mut *mut cty::c_void,
) -> ACPI_STATUS {
    let out_list = context as *mut Vec<AcpiDevice>;
    let device = AcpiDevice::new(handle).expect("could not create ACPI device");
    (*out_list).push(device);

    AE_OK
}

pub fn find_devices(hid: Option<&[u8]>) -> AcpiResult<Vec<AcpiDevice>> {
    let mut ret_list: Vec<AcpiDevice> = Vec::new();

    unsafe {
        let hid_ptr: *const u8;
        if let Some(hid_slice) = hid {
            hid_ptr = hid_slice.as_ptr();
        } else {
            hid_ptr = ptr::null_mut();
        }

        let output_ptr = (&mut ret_list) as *mut Vec<AcpiDevice>;
        let mut _rv: *mut cty::c_void = ptr::null_mut();

        AcpiStatus::from(AcpiGetDevices(
            mem::transmute(hid_ptr),
            Some(get_device_callback),
            output_ptr as *mut cty::c_void,
            &mut _rv,
        ))?;
    }

    Ok(ret_list)
}

pub fn enumerate_devices() {
    let devices = find_devices(None).expect("could not enumerate devices");
    let mut device_map = AVLTree::new();

    println!("acpi: found {} devices in ACPI namespace:", devices.len());

    for device in devices {
        print!("acpi:    {} ", device.full_name());

        if let Some(hid) = device.hardware_id() {
            print!("[HID: {}] ", hid);
        } else if let Some(adr) = device.address() {
            print!("[ADR: {:08x}] ", adr);
        }

        if let Some(uid) = device.unique_id() {
            print!("[UID: {}] ", uid);
        }

        if device.is_pci_root() {
            println!("[PCI root]");
        } else {
            print!("\n");
        }

        if device_map.insert(device.handle, device).is_err() {
            panic!("duplicate device handles found");
        }
    }

    if DEVICES.set(device_map).is_err() {
        panic!("already initialized");
    }
}

pub fn get_device_map() -> &'static AVLTree<ACPI_HANDLE, AcpiDevice> {
    DEVICES.get().expect("not initialized")
}

#[cfg(test)]
mod tests {
    use super::*;
    use kernel_test_macro::kernel_test;

    fn find_pci_root() -> Option<&'static AcpiDevice> {
        for (_, device) in get_device_map().iter() {
            if device.is_pci_root() {
                return Some(device);
            }
        }

        None
    }

    #[kernel_test]
    fn test_find_pci_root() {
        let pci_root = find_pci_root().expect("could not find PCI root bridge");

        // just iterate over all children and ensure nothing explodes
        for child in pci_root.children() {
            drop(child);
        }
    }
}
