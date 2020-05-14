use core::ptr;

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

    pub fn unmap_entry(&mut self, index: usize) -> Result<(), usize> {
        let mut entry = self.get_entry(index)?;
        entry.set_present(false);
        self.set_entry(index, entry)
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
        (self as *const PageTable) as usize
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
