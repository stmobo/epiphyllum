use super::bindings::*;
use crate::malloc::{physical_mem, virtual_mem};
use crate::paging;

use alloc_crate::alloc::Layout;
use alloc_crate::boxed::Box;
use alloc_crate::collections::BTreeMap;
use core::mem;
use core::ptr;
use spin::{Mutex, MutexGuard, Once};

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
pub extern "C" fn AcpiOsMapMemory(
    Where: ACPI_PHYSICAL_ADDRESS,
    Length: ACPI_SIZE,
) -> *mut cty::c_void {
    let alloc_start = paging::round_to_prev_page(Where as usize);
    let alloc_sz = paging::round_to_next_page(Length as usize);
    let n_pages = alloc_sz / 0x1000;

    let vaddr = virtual_mem::allocate(alloc_sz);
    if vaddr.is_err() {
        return ptr::null_mut();
    }

    let paddr;
    unsafe {
        paddr = physical_mem::allocate_at(alloc_start, alloc_sz);
    }

    if paddr.is_err() { /* Ignore it for now */ }

    let vaddr = vaddr.unwrap();
    let paddr = paddr.unwrap_or(alloc_start);
    let mut success = true;

    for i in 0..n_pages {
        if !paging::map_virtual_address(vaddr + (0x1000 * i), paddr + (0x1000 * i)) {
            println!(
                "acpi: failed to map physical page {:#016x}",
                alloc_start + (0x1000 * i)
            );

            success = false;
            break;
        }
    }

    if !success {
        /* Clean up mappings. */
        for i in 0..n_pages {
            paging::unmap_virtual_address(vaddr + (0x1000 * i));
        }

        virtual_mem::deallocate(vaddr, alloc_sz);

        return ptr::null_mut();
    }

    let page_offset = (Where as usize) - alloc_start;
    (vaddr + page_offset) as *mut cty::c_void
}

#[no_mangle]
pub extern "C" fn AcpiOsUnmapMemory(LogicalAddress: *mut cty::c_void, Size: ACPI_SIZE) {
    use paging::PageTableEntry;

    let alloc_start = paging::round_to_prev_page(LogicalAddress as usize);
    let alloc_sz = paging::round_to_next_page(Size as usize);

    let entry: PageTableEntry =
        paging::get_mapping(alloc_start).expect("attempted to free unallocated memory");

    let paddr = entry.physical_address();
    let n_pages = alloc_sz / 0x1000;

    for i in 0..n_pages {
        paging::unmap_virtual_address(alloc_start + (i * 0x1000));
    }

    unsafe {
        physical_mem::deallocate(paddr, alloc_sz);
    }

    virtual_mem::deallocate(alloc_start, alloc_sz);
}

#[no_mangle]
pub extern "C" fn AcpiOsGetPhysicalAddress(
    LogicalAddress: *mut cty::c_void,
    PhysicalAddress: *mut ACPI_PHYSICAL_ADDRESS,
) -> ACPI_STATUS {
    use paging::PageTableEntry;

    if LogicalAddress == ptr::null_mut() || PhysicalAddress == ptr::null_mut() {
        return AcpiError::AE_BAD_PARAMETER.into();
    }

    let vaddr = LogicalAddress as usize;
    let page_start = paging::round_to_prev_page(vaddr);
    let entry: Option<PageTableEntry> = paging::get_mapping(page_start);

    if entry.is_none() {
        return AcpiError::AE_ERROR.into();
    }

    let paddr = entry.unwrap().physical_address();
    let page_offset = vaddr - page_start;

    unsafe {
        (*PhysicalAddress) = (paddr + page_offset) as ACPI_PHYSICAL_ADDRESS;
    }

    AE_OK
}

#[no_mangle]
pub extern "C" fn AcpiOsReadable(Pointer: *mut cty::c_void, Length: ACPI_SIZE) -> BOOLEAN {
    let start = paging::round_to_prev_page(Pointer as usize);
    let len = paging::round_to_next_page(Length as usize);
    let n_pages = len / 0x1000;

    for i in 0..n_pages {
        let address = start + (0x1000 * i);
        if paging::get_mapping(address).is_none() {
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
        if let Some(entry) = paging::get_mapping(address) {
            if !entry.writable() {
                return false as BOOLEAN;
            }
        } else {
            return false as BOOLEAN;
        }
    }

    true as BOOLEAN
}

static ACPI_ALLOC_MAP: Once<Mutex<BTreeMap<usize, Layout>>> = Once::new();
fn get_acpi_alloc_map() -> MutexGuard<'static, BTreeMap<usize, Layout>> {
    ACPI_ALLOC_MAP
        .call_once(|| Mutex::new(BTreeMap::new()))
        .lock()
}

#[no_mangle]
pub extern "C" fn AcpiOsAllocate(Size: ACPI_SIZE) -> *mut cty::c_void {
    use alloc_crate::alloc::alloc;

    let layout = Layout::from_size_align(Size as usize, 8).expect("could not create layout");
    let ret: *mut cty::c_void = unsafe { mem::transmute(alloc(layout)) };

    if ret != ptr::null_mut() {
        get_acpi_alloc_map().insert(ret as usize, layout);
    }

    ret
}

#[no_mangle]
pub extern "C" fn AcpiOsFree(Memory: *mut cty::c_void) {
    use alloc_crate::alloc::dealloc;

    if Memory != ptr::null_mut() {
        let addr = Memory as usize;
        if let Some(layout) = get_acpi_alloc_map().get(&addr) {
            unsafe {
                dealloc(mem::transmute(Memory), *layout);
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

    let vaddr = paging::offset_direct_map(Address as usize);
    let virt_page = paging::round_to_prev_page(vaddr);
    let phys_page = paging::round_to_prev_page(Address as usize);

    if !paging::map_virtual_address(virt_page, phys_page) {
        return AcpiError::AE_NO_MEMORY.into();
    }

    unsafe {
        let ret = match Width {
            8 => ptr::read_unaligned(vaddr as *const u8) as u64,
            16 => ptr::read_unaligned(vaddr as *const u16) as u64,
            32 => ptr::read_unaligned(vaddr as *const u32) as u64,
            64 => ptr::read_unaligned(vaddr as *const u64) as u64,
            _ => return AcpiError::AE_BAD_PARAMETER.into(),
        };

        *Value = ret;

        paging::unmap_virtual_address(virt_page);

        AE_OK
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

    let vaddr = paging::offset_direct_map(Address as usize);
    let virt_page = paging::round_to_prev_page(vaddr);
    let phys_page = paging::round_to_prev_page(Address as usize);

    if !paging::map_virtual_address(virt_page, phys_page) {
        return AcpiError::AE_NO_MEMORY.into();
    }

    unsafe {
        match Width {
            8 => ptr::write_unaligned(vaddr as *mut u8, (Value & 0xFF) as u8),
            16 => ptr::write_unaligned(vaddr as *mut u16, (Value & 0xFFFF) as u16),
            32 => ptr::write_unaligned(vaddr as *mut u32, (Value & 0xFFFF_FFFF) as u32),
            64 => ptr::write_unaligned(vaddr as *mut u64, Value),
            _ => return AcpiError::AE_BAD_PARAMETER.into(),
        };

        paging::unmap_virtual_address(virt_page);

        AE_OK
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

static ACPI_ISR_MAP: Once<Mutex<BTreeMap<usize, u64>>> = Once::new();
fn get_acpi_isr_map() -> MutexGuard<'static, BTreeMap<usize, u64>> {
    ACPI_ISR_MAP
        .call_once(|| Mutex::new(BTreeMap::new()))
        .lock()
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

    get_acpi_isr_map().insert(isr as usize, isr_id);

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
    if let Some(isr_id) = get_acpi_isr_map().get(&isr) {
        interrupts::unregister_handler(InterruptNumber as u8, *isr_id);
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
