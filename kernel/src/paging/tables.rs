use core::convert::TryInto;
use core::ops::{Index, IndexMut};
use core::ptr;

use crate::asm;
use crate::asm::cpuid::FeatureFlags;
use crate::malloc::{AllocationError, PhysicalMemory};

use super::PhysicalPointer;
use super::PAGE_MASK;

const PML4T_RECURSIVE_BASE: usize = 0xFFFF_FFFF_FFFF_F000;
const PDPT_RECURSIVE_BASE: usize = 0xFFFF_FFFF_FFE0_0000;
const PD_RECURSIVE_BASE: usize = 0xFFFF_FFFF_C000_0000;
const PT_RECURSIVE_BASE: usize = 0xFFFF_FF80_0000_0000;

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
#[repr(transparent)]
pub struct PageTableEntry {
    entry: u64,
}

impl PageTableEntry {
    pub fn new() -> PageTableEntry {
        PageTableEntry { entry: 0 }
    }

    pub fn physical_address(&self) -> usize {
        ((self.entry as usize) & PAGE_MASK) as usize
    }

    pub fn set_physical_address(&mut self, addr: usize) {
        let aligned = (addr & PAGE_MASK) as u64;
        self.entry = aligned | (self.entry & 0xFFF);
    }

    pub fn page(&self) -> Option<PhysicalPointer<u8>> {
        PhysicalPointer::new(self.physical_address())
    }

    pub fn present(&self) -> bool {
        (self.entry & 1) > 0
    }

    pub fn set_present(&mut self, present: bool) {
        if present {
            self.entry = self.entry | 1;
        } else {
            self.entry = self.entry & !1;
        }
    }

    pub fn writable(&self) -> bool {
        (self.entry & 2) != 0
    }

    pub fn set_writable(&mut self, writable: bool) {
        if writable {
            self.entry = self.entry | 2;
        } else {
            self.entry = self.entry & !2;
        }
    }

    pub fn page_size(&self) -> bool {
        (self.entry & (1 << 7)) != 0
    }

    pub fn set_page_size(&mut self, ps: bool) {
        if ps {
            self.entry |= 1 << 7;
        } else {
            self.entry &= !(1 << 7);
        }
    }
}

#[repr(transparent)]
pub struct PageTable {
    entries: [PageTableEntry; 512],
}

impl PageTable {
    pub fn map_addr(&mut self, index: usize, phys_addr: usize) -> Result<(), usize> {
        let mut entry = self.get_entry(index)?;

        entry.set_physical_address(phys_addr);
        entry.set_present(true);

        self.set_entry(index, entry)
    }

    pub fn unmap_entry(&mut self, index: usize) -> Result<PageTableEntry, usize> {
        let mut entry = self.get_entry(index)?;
        entry.set_present(false);
        self.set_entry(index, entry)?;
        Ok(entry)
    }

    pub fn get_entry(&self, index: usize) -> Result<PageTableEntry, usize> {
        if index >= 512 {
            return Err(index);
        }

        let p = self.table_addr() as *const PageTableEntry;
        unsafe { Ok(ptr::read_volatile(p.offset(index as isize))) }
    }

    pub fn set_entry(&mut self, index: usize, entry: PageTableEntry) -> Result<(), usize> {
        if index >= 512 {
            return Err(index);
        }

        let p = self.table_addr() as *mut PageTableEntry;
        unsafe {
            ptr::write_volatile(p.offset(index as isize), entry);
        }

        Ok(())
    }

    pub fn table_addr(&self) -> usize {
        self.entries.as_ptr() as usize
    }

    pub fn table_mut_ptr(&mut self) -> *mut PageTableEntry {
        self.entries.as_mut_ptr()
    }

    pub fn table_ptr(&self) -> *const PageTableEntry {
        self.entries.as_ptr()
    }

    pub fn clear(&mut self) {
        for e in self.entries.iter_mut() {
            e.entry = 0;
        }
    }

    /// Get a reference to the recursively-mapped PML4T.
    pub fn get_pml4t() -> &'static mut PageTable {
        unsafe {
            let pml4t = PML4T_RECURSIVE_BASE as *mut PageTable;
            &mut *pml4t
        }
    }

    /// Get a reference to a recursively-mapped PD Pointer Table.
    pub unsafe fn get_pdpt(pdp_idx: usize) -> &'static mut PageTable {
        let pdp_addr = PDPT_RECURSIVE_BASE + (0x1000 * pdp_idx);
        &mut *(pdp_addr as *mut PageTable)
    }

    /// Get a reference to a recursively-mapped Page Directory.
    pub unsafe fn get_pd(pdp_idx: usize, pd_idx: usize) -> &'static mut PageTable {
        let pd_addr = PD_RECURSIVE_BASE + (0x20_0000 * pdp_idx) + (0x1000 * pd_idx);
        &mut *(pd_addr as *mut PageTable)
    }

    /// Get a reference to a recursively-mapped Page Table.
    pub unsafe fn get_pt(pdp_idx: usize, pd_idx: usize, pt_idx: usize) -> &'static mut PageTable {
        let pt_addr =
            PT_RECURSIVE_BASE + (0x4000_0000 * pdp_idx) + (0x20_0000 * pd_idx) + (0x1000 * pt_idx);
        &mut *(pt_addr as *mut PageTable)
    }

    pub fn iter(&self) -> impl Iterator<Item = &PageTableEntry> {
        self.entries.iter()
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut PageTableEntry> {
        self.entries.iter_mut()
    }
}

impl Index<usize> for PageTable {
    type Output = PageTableEntry;

    fn index(&self, index: usize) -> &Self::Output {
        &self.entries[index]
    }
}

impl IndexMut<usize> for PageTable {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.entries[index]
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd)]
pub enum PageLevel {
    PML4,
    PDP,
    PD,
    PT,
}

impl PageLevel {
    pub fn page_alignment(self) -> Option<usize> {
        match self {
            PageLevel::PDP => Some(1 << 30),
            PageLevel::PD => Some(1 << 21),
            PageLevel::PT => Some(1 << 12),
            PageLevel::PML4 => None,
        }
    }

    pub fn alignment_mask(self) -> Option<usize> {
        self.page_alignment().map(|a| a - 1)
    }

    pub fn child_level(self) -> Option<PageLevel> {
        match self {
            PageLevel::PML4 => Some(PageLevel::PDP),
            PageLevel::PDP => Some(PageLevel::PD),
            PageLevel::PD => Some(PageLevel::PT),
            PageLevel::PT => None,
        }
    }

    pub fn parent_level(self) -> Option<PageLevel> {
        match self {
            PageLevel::PML4 => None,
            PageLevel::PDP => Some(PageLevel::PML4),
            PageLevel::PD => Some(PageLevel::PDP),
            PageLevel::PT => Some(PageLevel::PD),
        }
    }
}

const fn pt_idx(vaddr: usize) -> usize {
    (vaddr >> 12) & 0x1FF
}

const fn pd_idx(vaddr: usize) -> usize {
    (vaddr >> 21) & 0x1FF
}

const fn pdp_idx(vaddr: usize) -> usize {
    (vaddr >> 30) & 0x1FF
}

const fn pml4_idx(vaddr: usize) -> usize {
    (vaddr >> 39) & 0x1FF
}

#[derive(Debug, Copy, Clone)]
pub enum MappingError {
    AllocationFailure(AllocationError),
    AlreadyMapped,
}

#[derive(Copy, Clone)]
struct Resolved(PhysicalPointer<PageTable>, PageLevel);

#[repr(transparent)]
pub struct AddressSpace {
    pml4t: PhysicalPointer<PageTable>,
}

impl AddressSpace {
    pub fn current() -> AddressSpace {
        unsafe {
            AddressSpace {
                pml4t: PhysicalPointer::new_unchecked(asm::get_cr3()),
            }
        }
    }

    pub fn new() -> Result<AddressSpace, AllocationError> {
        let page = PhysicalMemory::new(0x1000)?.into_address();
        PhysicalPointer::new(page)
            .map(|pml4t| AddressSpace { pml4t })
            .ok_or(AllocationError::InvalidAllocation)
    }

    /// Resolves a virtual address in this space into a (Table, Level) pair.
    ///
    /// If the result is Ok, then the virtual address is mapped into the
    /// address space, and the returned table contains the mapping for this page.
    ///
    /// If the result is Err, then the virtual address is _not_ mapped into the
    /// address space, and the returned table contains the closest ancestor
    /// table that is present in the address space.
    fn resolve_raw(&self, vaddr: usize) -> Result<Resolved, Resolved> {
        unsafe {
            let pml4e = self.pml4t.as_ref().get_entry(pml4_idx(vaddr)).unwrap();
            let pdpt: PhysicalPointer<PageTable> = pml4e
                .try_into()
                .or(Err(Resolved(self.pml4t, PageLevel::PML4)))?;

            let pdpe = pdpt.as_ref().get_entry(pdp_idx(vaddr)).unwrap();
            if pdpe.present() && pdpe.page_size() {
                // this is a 1GiB page
                return Ok(Resolved(pdpt, PageLevel::PDP));
            }

            let pd: PhysicalPointer<PageTable> =
                pdpe.try_into().or(Err(Resolved(pdpt, PageLevel::PDP)))?;
            let pde = pd.as_ref().get_entry(pd_idx(vaddr)).unwrap();
            if pde.present() && pde.page_size() {
                // this is a 2MiB page
                return Ok(Resolved(pd, PageLevel::PD));
            }

            // otherwise, it's a 4KiB page
            let pt: PhysicalPointer<PageTable> =
                pde.try_into().or(Err(Resolved(pd, PageLevel::PD)))?;
            let pte = pt.as_ref().get_entry(pt_idx(vaddr)).unwrap();
            let resolved = Resolved(pt, PageLevel::PT);

            if pte.present() {
                Ok(resolved)
            } else {
                Err(resolved)
            }
        }
    }

    pub fn get_mapping(&self, vaddr: usize) -> Option<PageTableEntry> {
        self.resolve_raw(vaddr).ok().map(|r| {
            let table = r.0;
            unsafe {
                match r.1 {
                    PageLevel::PML4 => unreachable!(), // should not get here
                    PageLevel::PDP => table.as_ref().get_entry(pdp_idx(vaddr)).unwrap(),
                    PageLevel::PD => table.as_ref().get_entry(pd_idx(vaddr)).unwrap(),
                    PageLevel::PT => table.as_ref().get_entry(pt_idx(vaddr)).unwrap(),
                }
            }
        })
    }

    pub fn is_mapped(&self, vaddr: usize) -> bool {
        self.get_mapping(vaddr).is_some()
    }

    fn create_child_table(mut cur: Resolved, index: usize) -> Result<Resolved, MappingError> {
        let page = PhysicalMemory::new(0x1000)
            .map_err(|e| MappingError::AllocationFailure(e))?
            .into_address();

        unsafe {
            let cur_table = cur.0.as_mut();
            cur_table.map_addr(index, page).unwrap();

            let child_table = PhysicalPointer::new_unchecked(page);
            Ok(Resolved(child_table, cur.1.child_level().unwrap()))
        }
    }

    pub fn set_mapping(
        &self,
        vaddr: usize,
        mut mapping: PageTableEntry,
        level: PageLevel,
    ) -> Result<(), MappingError> {
        assert_ne!(level, PageLevel::PML4, "invalid level for page mapping");
        assert_eq!(
            mapping.physical_address() & level.alignment_mask().unwrap(),
            0,
            "attempted to map unaligned page at {:#018x} to {:#018x}",
            vaddr,
            mapping.physical_address()
        );

        if level == PageLevel::PDP || level == PageLevel::PD {
            mapping.set_page_size(true);
        } else {
            mapping.set_page_size(false);
        }

        let mut cur = match self.resolve_raw(vaddr) {
            Ok(_) => return Err(MappingError::AlreadyMapped),
            Err(r) => r,
        };

        if cur.1 == PageLevel::PML4 {
            // map a new PDPT
            cur = Self::create_child_table(cur, pml4_idx(vaddr))?;
        }

        if cur.1 == PageLevel::PDP {
            // page directory does not exist
            if level == PageLevel::PDP {
                // directly map in this page
                assert!(
                    FeatureFlags::GB_PAGES.supported(),
                    "attempted to map in GB page without arch support"
                );

                unsafe {
                    cur.0.as_mut().set_entry(pdp_idx(vaddr), mapping).unwrap();
                }
                return Ok(());
            } else {
                // make a subordinate PD
                cur = Self::create_child_table(cur, pdp_idx(vaddr))?;
            }
        }

        if level == PageLevel::PDP {
            // requested a GB-page mapping when a more fine-grained table
            // already exists
            return Err(MappingError::AlreadyMapped);
        }

        if cur.1 == PageLevel::PD {
            if level == PageLevel::PD {
                unsafe {
                    cur.0.as_mut().set_entry(pd_idx(vaddr), mapping).unwrap();
                }
                return Ok(());
            } else {
                cur = Self::create_child_table(cur, pd_idx(vaddr))?;
            }
        }

        if level == PageLevel::PD {
            return Err(MappingError::AlreadyMapped);
        }

        unsafe {
            cur.0.as_mut().set_entry(pt_idx(vaddr), mapping).unwrap();
        }

        Ok(())
    }
}
