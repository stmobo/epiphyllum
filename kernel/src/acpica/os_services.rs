use super::bindings::*;
use crate::lock::LockedGlobal;
use crate::paging;
use crate::paging::PhysicalPointer;

use alloc_crate::alloc::Layout;
use alloc_crate::boxed::Box;
use alloc_crate::collections::BTreeMap;
use core::mem;
use core::ptr;
use spin::Mutex;

#[no_mangle]
pub extern "C" fn AcpiOsInitialize() -> ACPI_STATUS {
    AE_OK
}

#[no_mangle]
pub extern "C" fn AcpiOsTerminate() -> ACPI_STATUS {
    AE_OK
}

#[no_mangle]
pub extern "C" fn AcpiOsPrintf() {}

#[no_mangle]
pub extern "C" fn AcpiOsVprintf() {}

const RSDP_SIGNATURE: &'static [u8] = b"RSD PTR ";

fn do_rsdp_search(start_addr: usize, end_addr: usize) -> Option<usize> {
    let mut addr = paging::offset_direct_map(start_addr) & !0xF;
    let mut phys_addr = start_addr & !0xF;
    let end_addr = paging::offset_direct_map(end_addr) & !0xF;

    while addr < end_addr {
        let p = addr as *const u8;
        let mut is_match = true;

        for i in 0..RSDP_SIGNATURE.len() {
            unsafe {
                if *(p.offset(i as isize)) != RSDP_SIGNATURE[i] {
                    is_match = false;
                    break;
                }
            }
        }

        if is_match {
            println!("acpi: found RSDP at {:#08x}", phys_addr);
            return Some(phys_addr);
        }

        addr += 16;
        phys_addr += 16;
    }

    None
}

#[no_mangle]
pub extern "C" fn AcpiOsGetRootPointer() -> ACPI_PHYSICAL_ADDRESS {
    if let Some(addr) = do_rsdp_search(0x0008_0000, 0x0009_FFFF) {
        return addr as ACPI_PHYSICAL_ADDRESS;
    }

    if let Some(addr) = do_rsdp_search(0x000E_0000, 0x000F_FFFF) {
        return addr as ACPI_PHYSICAL_ADDRESS;
    }

    0
}

#[no_mangle]
pub extern "C" fn AcpiOsPredefinedOverride(
    _InitVal: *const ACPI_PREDEFINED_NAMES,
    NewVal: *mut ACPI_STRING,
) -> ACPI_STATUS {
    unsafe {
        (*NewVal) = ptr::null_mut();
    }

    AE_OK
}

#[no_mangle]
pub extern "C" fn AcpiOsTableOverride(
    _ExistingTable: *mut ACPI_TABLE_HEADER,
    NewTable: *mut *mut ACPI_TABLE_HEADER,
) -> ACPI_STATUS {
    unsafe {
        (*NewTable) = ptr::null_mut();
    }

    AE_OK
}

#[no_mangle]
pub extern "C" fn AcpiOsPhysicalTableOverride(
    ExistingTable: *mut ACPI_TABLE_HEADER,
    NewAddress: *mut ACPI_PHYSICAL_ADDRESS,
    NewTableLength: *mut UINT32,
) -> ACPI_STATUS {
    unsafe {
        (*NewAddress) = 0;
        (*NewTableLength) = (*ExistingTable).Length;
    }

    AE_OK
}

#[no_mangle]
pub extern "C" fn AcpiOsMapMemory(Where: ACPI_PHYSICAL_ADDRESS, _: ACPI_SIZE) -> *mut cty::c_void {
    paging::offset_direct_map(Where as usize) as *mut cty::c_void
}

#[no_mangle]
pub extern "C" fn AcpiOsUnmapMemory(_: *mut cty::c_void, _: ACPI_SIZE) {
    return;
}

#[no_mangle]
pub extern "C" fn AcpiOsGetPhysicalAddress(
    LogicalAddress: *mut cty::c_void,
    PhysicalAddress: *mut ACPI_PHYSICAL_ADDRESS,
) -> ACPI_STATUS {
    if LogicalAddress == ptr::null_mut() || PhysicalAddress == ptr::null_mut() {
        return AcpiError::AE_BAD_PARAMETER.into();
    }

    let vaddr = LogicalAddress as usize;
    if let Some((level, entry)) = paging::get_page_mapping(vaddr) {
        if entry.present() {
            let page_offset = vaddr & level.alignment_mask().unwrap();
            let paddr = entry.physical_address();

            unsafe {
                (*PhysicalAddress) = (paddr + page_offset) as ACPI_PHYSICAL_ADDRESS;
            }

            return AE_OK;
        }
    }

    AcpiError::AE_ERROR.into()
}

#[no_mangle]
pub extern "C" fn AcpiOsReadable(Pointer: *mut cty::c_void, Length: ACPI_SIZE) -> BOOLEAN {
    let start = paging::round_to_prev_page(Pointer as usize);
    let len = paging::round_to_next_page(Length as usize);
    let n_pages = len / 0x1000;

    for i in 0..n_pages {
        let address = start + (0x1000 * i);
        if paging::get_page_mapping(address).is_none() {
            return false as BOOLEAN;
        }
    }

    true as BOOLEAN
}

#[no_mangle]
pub extern "C" fn AcpiOsWritable(Pointer: *mut cty::c_void, Length: ACPI_SIZE) -> BOOLEAN {
    let start = paging::round_to_prev_page(Pointer as usize);
    let len = paging::round_to_next_page(Length as usize);
    let n_pages = len / 0x1000;

    for i in 0..n_pages {
        let address = start + (0x1000 * i);
        if let Some((_, entry)) = paging::get_page_mapping(address) {
            if !entry.writable() {
                return false as BOOLEAN;
            }
        } else {
            return false as BOOLEAN;
        }
    }

    true as BOOLEAN
}

static ACPI_ALLOC_MAP: LockedGlobal<BTreeMap<usize, Layout>> = LockedGlobal::new();
pub fn init_alloc_map() {
    ACPI_ALLOC_MAP.init(|| BTreeMap::new());
}

#[no_mangle]
pub extern "C" fn AcpiOsAllocate(Size: ACPI_SIZE) -> *mut cty::c_void {
    use alloc_crate::alloc::alloc;

    let layout = Layout::from_size_align(Size as usize, 8).expect("could not create layout");
    let ret: *mut cty::c_void = unsafe { mem::transmute(alloc(layout)) };

    if ret != ptr::null_mut() {
        let mut map = ACPI_ALLOC_MAP.lock();
        map.insert(ret as usize, layout);
    }

    ret
}

#[no_mangle]
pub extern "C" fn AcpiOsFree(Memory: *mut cty::c_void) {
    use alloc_crate::alloc::dealloc;

    if Memory != ptr::null_mut() {
        let addr = Memory as usize;
        let map = ACPI_ALLOC_MAP.lock();
        if let Some(layout) = map.get(&addr) {
            unsafe {
                let ptr = addr as *mut u8;
                dealloc(ptr, *layout);
            }
        }
    }
}

#[no_mangle]
pub extern "C" fn AcpiOsReadPort(
    Address: ACPI_IO_ADDRESS,
    Value: *mut UINT32,
    Width: UINT32,
) -> ACPI_STATUS {
    use crate::asm::ports;

    let addr = Address as u16;
    match Width {
        8 => unsafe {
            let ret = ports::inb(addr);
            *Value = ret as u32;
            AE_OK
        },
        16 => unsafe {
            let ret = ports::inw(addr);
            *Value = ret as u32;
            AE_OK
        },
        32 => unsafe {
            let ret = ports::ind(addr);
            *Value = ret;
            AE_OK
        },
        _ => AcpiError::AE_BAD_PARAMETER.into(),
    }
}

#[no_mangle]
pub extern "C" fn AcpiOsWritePort(
    Address: ACPI_IO_ADDRESS,
    Value: UINT32,
    Width: UINT32,
) -> ACPI_STATUS {
    use crate::asm::ports;

    let addr = Address as u16;
    match Width {
        8 => unsafe {
            ports::outb(addr, (Value & 0xFF) as u8);
            AE_OK
        },
        16 => unsafe {
            ports::outw(addr, (Value & 0xFFFF) as u16);
            AE_OK
        },
        32 => unsafe {
            ports::outd(addr, Value);
            AE_OK
        },
        _ => AcpiError::AE_BAD_PARAMETER.into(),
    }
}

#[no_mangle]
pub fn AcpiOsReadMemory(
    Address: ACPI_PHYSICAL_ADDRESS,
    Value: *mut UINT64,
    Width: UINT32,
) -> ACPI_STATUS {
    if Address == 0 {
        return AcpiError::AE_BAD_PARAMETER.into();
    }

    unsafe {
        let v = match Width {
            8 => PhysicalPointer::<u8>::new(Address as usize)
                .map(|p| p.as_ptr().read_unaligned() as u64),
            16 => PhysicalPointer::<u16>::new(Address as usize)
                .map(|p| p.as_ptr().read_unaligned() as u64),
            32 => PhysicalPointer::<u32>::new(Address as usize)
                .map(|p| p.as_ptr().read_unaligned() as u64),
            64 => {
                PhysicalPointer::<u64>::new(Address as usize).map(|p| p.as_ptr().read_unaligned())
            }
            _ => return AcpiError::AE_BAD_PARAMETER.into(),
        };

        if let Some(value) = v {
            *Value = value;
            AE_OK
        } else {
            AcpiError::AE_BAD_PARAMETER.into()
        }
    }
}

#[no_mangle]
pub fn AcpiOsWriteMemory(
    Address: ACPI_PHYSICAL_ADDRESS,
    Value: UINT64,
    Width: UINT32,
) -> ACPI_STATUS {
    if Address == 0 {
        return AcpiError::AE_BAD_PARAMETER.into();
    }

    unsafe {
        match Width {
            8 => {
                if let Some(p) = PhysicalPointer::<u8>::new(Address as usize) {
                    p.as_mut_ptr().write_unaligned((Value & 0xFF) as u8);
                    AE_OK
                } else {
                    AcpiError::AE_BAD_PARAMETER.into()
                }
            }
            16 => {
                if let Some(p) = PhysicalPointer::<u16>::new(Address as usize) {
                    p.as_mut_ptr().write_unaligned((Value & 0xFFFF) as u16);
                    AE_OK
                } else {
                    AcpiError::AE_BAD_PARAMETER.into()
                }
            }
            32 => {
                if let Some(p) = PhysicalPointer::<u32>::new(Address as usize) {
                    p.as_mut_ptr().write_unaligned((Value & 0xFFFF_FFFF) as u32);
                    AE_OK
                } else {
                    AcpiError::AE_BAD_PARAMETER.into()
                }
            }
            64 => {
                if let Some(p) = PhysicalPointer::<u64>::new(Address as usize) {
                    p.as_mut_ptr().write_unaligned(Value);
                    AE_OK
                } else {
                    AcpiError::AE_BAD_PARAMETER.into()
                }
            }
            _ => AcpiError::AE_BAD_PARAMETER.into(),
        }
    }
}

#[no_mangle]
pub extern "C" fn AcpiOsReadPciConfiguration(
    PciId: *mut ACPI_PCI_ID,
    Reg: UINT32,
    Value: *mut UINT64,
    Width: UINT32,
) -> ACPI_STATUS {
    use crate::asm::ports;
    unsafe {
        let addr: u32 = ((((*PciId).Bus as u32) & 0xFF) << 16)
            | ((((*PciId).Device as u32) & 0x1F) << 11)
            | ((((*PciId).Function as u32) & 0x07) << 11)
            | (Reg & 0xFC)
            | 0x8000_0000;

        ports::outd(0xCF8, addr);
        let val = ports::ind(0xCFC) as u64;

        /* TODO: Implement 64-bit read at some point */
        match Width {
            8 => (*Value) = val & 0xFF,
            16 => (*Value) = val & 0xFFFF,
            32 => (*Value) = val & 0xFFFF_FFFF,
            _ => return AcpiError::AE_BAD_PARAMETER.into(),
        };

        AE_OK
    }
}

#[no_mangle]
pub extern "C" fn AcpiOsWritePciConfiguration(
    PciId: *mut ACPI_PCI_ID,
    Reg: UINT32,
    Value: UINT64,
    Width: UINT32,
) -> ACPI_STATUS {
    use crate::asm::ports;
    unsafe {
        let addr: u32 = ((((*PciId).Bus as u32) & 0xFF) << 16)
            | ((((*PciId).Device as u32) & 0x1F) << 11)
            | ((((*PciId).Function as u32) & 0x07) << 11)
            | (Reg & 0xFC)
            | 0x8000_0000;

        /* Read in value, then selectively update parts of it */
        ports::outd(0xCF8, addr);
        let mut val = ports::ind(0xCFC) as u64;

        match Width {
            8 => val = (val & !0xFF) | (Value & 0xFF),
            16 => val = (val & !0xFFFF) | (Value & 0xFFFF),
            32 => val = (val & !0xFFFF_FFFF) | (Value & 0xFFFF_FFFF),
            _ => return AcpiError::AE_BAD_PARAMETER.into(),
        };

        ports::outd(0xCF8, addr);
        ports::outd(0xCFC, val as u32);

        AE_OK
    }
}

#[no_mangle]
pub extern "C" fn AcpiOsCreateMutex(OutHandle: *mut *mut cty::c_void) -> ACPI_STATUS {
    if OutHandle == ptr::null_mut() {
        return AcpiError::AE_BAD_PARAMETER.into();
    }

    let b: Box<Mutex<()>> = Box::new(Mutex::new(()));
    let addr = Box::into_raw(b) as usize;

    unsafe {
        (*OutHandle) = addr as *mut cty::c_void;
    }

    AE_OK
}

#[no_mangle]
pub extern "C" fn AcpiOsDeleteMutex(Handle: *mut cty::c_void) {
    if Handle == ptr::null_mut() {
        return;
    }

    let b: *mut Mutex<()> = (Handle as usize) as *mut Mutex<()>;
    unsafe {
        let b = Box::from_raw(b);
        drop(b);
    }
}

#[no_mangle]
pub extern "C" fn AcpiOsAcquireMutex(Handle: *mut cty::c_void, _Timeout: UINT16) -> ACPI_STATUS {
    if Handle == ptr::null_mut() {
        return AcpiError::AE_BAD_PARAMETER.into();
    }

    let b: *mut Mutex<()> = (Handle as usize) as *mut Mutex<()>;
    unsafe {
        mem::forget((*b).lock());
    }

    return AE_OK;
}

#[no_mangle]
pub extern "C" fn AcpiOsReleaseMutex(Handle: *mut cty::c_void) {
    if Handle == ptr::null_mut() {
        return;
    }

    let b: *mut Mutex<()> = (Handle as usize) as *mut Mutex<()>;
    unsafe {
        (*b).force_unlock();
    }
}

#[no_mangle]
pub extern "C" fn AcpiOsCreateLock(OutHandle: *mut *mut cty::c_void) -> ACPI_STATUS {
    if OutHandle == ptr::null_mut() {
        return AcpiError::AE_BAD_PARAMETER.into();
    }

    let b: Box<Mutex<bool>> = Box::new(Mutex::new(false));
    let addr = Box::into_raw(b) as usize;

    unsafe {
        (*OutHandle) = addr as *mut cty::c_void;
    }

    AE_OK
}

#[no_mangle]
pub extern "C" fn AcpiOsDeleteLock(Handle: *mut cty::c_void) {
    if Handle == ptr::null_mut() {
        return;
    }

    let b: *mut Mutex<bool> = (Handle as usize) as *mut Mutex<bool>;
    unsafe {
        let b = Box::from_raw(b);
        drop(b);
    }
}

#[no_mangle]
pub extern "C" fn AcpiOsAcquireLock(Handle: *mut cty::c_void, _Timeout: UINT16) -> ACPI_STATUS {
    use crate::asm::interrupts;

    if Handle == ptr::null_mut() {
        return AcpiError::AE_BAD_PARAMETER.into();
    }

    let b: *mut Mutex<bool> = (Handle as usize) as *mut Mutex<bool>;
    unsafe {
        let mut l = (*b).lock();
        *l = interrupts::enabled();
        interrupts::set_if(false);

        mem::forget(l);
    }

    return AE_OK;
}

#[no_mangle]
pub extern "C" fn AcpiOsReleaseLock(Handle: *mut cty::c_void) {
    use crate::asm::interrupts;

    if Handle == ptr::null_mut() {
        return;
    }

    let b: *mut Mutex<bool> = (Handle as usize) as *mut Mutex<bool>;
    unsafe {
        (*b).force_unlock();
        let l = (*b).lock();
        let iflag = *l;
        drop(l);

        interrupts::set_if(iflag);
    }
}

#[no_mangle]
pub extern "C" fn AcpiOsCreateSemaphore(
    _MaxUnits: UINT32,
    _InitialUnits: UINT32,
    OutHandle: *mut *mut cty::c_void,
) -> ACPI_STATUS {
    if OutHandle == ptr::null_mut() {
        return AcpiError::AE_BAD_PARAMETER.into();
    }

    AE_OK
}

#[no_mangle]
pub extern "C" fn AcpiOsDeleteSemaphore(Handle: *mut cty::c_void) -> ACPI_STATUS {
    if Handle == ptr::null_mut() {
        return AcpiError::AE_BAD_PARAMETER.into();
    }

    AE_OK
}

#[no_mangle]
pub extern "C" fn AcpiOsWaitSemaphore(
    Handle: *mut cty::c_void,
    _Units: UINT32,
    _Timeout: UINT16,
) -> ACPI_STATUS {
    if Handle == ptr::null_mut() {
        return AcpiError::AE_BAD_PARAMETER.into();
    }

    AE_OK
}
#[no_mangle]
pub extern "C" fn AcpiOsSignalSemaphore(Handle: *mut cty::c_void, _Units: UINT32) -> ACPI_STATUS {
    if Handle == ptr::null_mut() {
        return AcpiError::AE_BAD_PARAMETER.into();
    }

    AE_OK
}

#[no_mangle]
pub extern "C" fn AcpiOsGetThreadId() -> UINT64 {
    return 0;
}

#[no_mangle]
pub extern "C" fn AcpiOsExecute(
    _Type: ACPI_EXECUTE_TYPE,
    _Function: ACPI_OSD_EXEC_CALLBACK,
    _Context: *mut cty::c_void,
) -> ACPI_STATUS {
    AcpiError::AE_BAD_PARAMETER.into()
}

#[no_mangle]
pub extern "C" fn AcpiOsSleep(_Milliseconds: UINT64) {}

#[no_mangle]
pub extern "C" fn AcpiOsStall(_Microseconds: UINT32) {}

/// TODO: implement this
#[no_mangle]
pub extern "C" fn AcpiOsGetTimer() -> UINT64 {
    0
}

static ACPI_ISR_MAP: LockedGlobal<BTreeMap<usize, u64>> = LockedGlobal::new();
pub fn init_isr_map() {
    ACPI_ISR_MAP.init(|| BTreeMap::new());
}

#[no_mangle]
pub extern "C" fn AcpiOsInstallInterruptHandler(
    InterruptNumber: UINT32,
    ServiceRoutine: ACPI_OSD_HANDLER,
    Context: *mut cty::c_void,
) -> ACPI_STATUS {
    use crate::interrupts;

    if InterruptNumber > 255 || ServiceRoutine.is_none() {
        return AcpiError::AE_BAD_PARAMETER.into();
    }

    let ctx = ISRContext(Context);

    let isr = ServiceRoutine.unwrap();
    let isr_id = interrupts::register_handler(
        InterruptNumber as u8,
        move || -> interrupts::InterruptHandlerStatus {
            unsafe {
                if isr(ctx.0) == ACPI_INTERRUPT_HANDLED {
                    return interrupts::InterruptHandlerStatus::Handled;
                } else {
                    return interrupts::InterruptHandlerStatus::NotHandled;
                }
            }
        },
    )
    .unwrap();

    let mut map = ACPI_ISR_MAP.lock();
    map.insert(isr as usize, isr_id);

    0
}

#[no_mangle]
pub extern "C" fn AcpiOsRemoveInterruptHandler(
    InterruptNumber: UINT32,
    ServiceRoutine: ACPI_OSD_HANDLER,
) -> ACPI_STATUS {
    use crate::interrupts;

    if InterruptNumber > 255 || ServiceRoutine.is_none() {
        return AcpiError::AE_BAD_PARAMETER.into();
    }

    let isr = ServiceRoutine.unwrap() as usize;
    let mut map = ACPI_ISR_MAP.lock();

    if let Some(isr_id) = map.get(&isr) {
        let isr_id = *isr_id;
        interrupts::unregister_handler(InterruptNumber as u8, isr_id);
        map.remove(&isr);

        return AE_OK;
    } else {
        return AcpiError::AE_NOT_EXIST.into();
    }
}

#[repr(transparent)]
struct ISRContext(*mut cty::c_void);
unsafe impl Send for ISRContext {}
unsafe impl Sync for ISRContext {}

#[repr(C)]
struct AcpiFatalInfo {
    info_type: u32,
    code: u32,
    argument: u32,
}

#[no_mangle]
pub extern "C" fn AcpiOsSignal(Function: UINT32, Info: *mut cty::c_void) -> ACPI_STATUS {
    use cstr_core::{c_char, CStr};

    if Function == ACPI_SIGNAL_FATAL {
        unsafe {
            let info: *mut AcpiFatalInfo = mem::transmute(Info);
            panic!(
                "fatal ACPI error: type {:#08x}, code {:#08x}, arg {:#08x}",
                (*info).info_type,
                (*info).code,
                (*info).argument,
            );
        }
    } else if Function == ACPI_SIGNAL_BREAKPOINT {
        unsafe {
            let info: *const c_char = mem::transmute(Info);
            if let Ok(s) = CStr::from_ptr(info).to_str() {
                println!("ignoring ACPI breakpoint: {}", s);
            } else {
                println!("ignoring ACPI breakpoint (invalid message)");
            }
        }
    }

    AE_OK
}
