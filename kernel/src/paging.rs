use core::mem;
use core::ops;
use x86_64::instructions::tlb;
use x86_64::VirtAddr;

pub const PAGE_MASK: usize         = 0xFFFF_FFFF_FFFF_F000;

const PML4T_RECURSIVE_BASE: usize  = 0xFFFF_FFFF_FFFF_F000;
const PDPT_RECURSIVE_BASE: usize   = 0xFFFF_FFFF_FFE0_0000;
const PD_RECURSIVE_BASE: usize     = 0xFFFF_FFFF_C000_0000;
const PT_RECURSIVE_BASE: usize     = 0xFFFF_FF80_0000_0000;

pub const KERNEL_STACK_BASE: usize = 0xFFFF_FF00_0000_0000;
pub const KERNEL_BASE: usize       = 0xFFFF_C400_0000_0000;
pub const PHYSICAL_MAP_BASE: usize = 0xFFFF_8100_0000_0000;
pub const HIGHER_HALF_START: usize = 0xFFFF_8000_0000_0000;

const MAX_PHYSICAL_MEMORY: usize   = KERNEL_BASE - PHYSICAL_MAP_BASE;

const KERNEL_STACK_PML4_IDX: usize = 0b111_111_110;
const KERNEL_BASE_PML4_IDX: usize  = 0b110_001_000;
const PHYSICAL_MAP_PML4_IDX: usize = 0b100_000_010;

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
#[repr(transparent)]
pub struct PageTableEntry {
    entry: u64,
}

impl PageTableEntry {
    pub fn new() -> PageTableEntry {
        PageTableEntry {
            entry: 0
        }
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
}

#[repr(transparent)]
pub struct PageTable {
    entries: [PageTableEntry; 512]
}

impl PageTable {
    pub fn map_addr(&mut self, index: usize, phys_addr: usize) {
        self.entries[index].set_physical_address(phys_addr);
        self.entries[index].set_present(true);
    }

    pub fn table_addr(&self) -> usize {
        unsafe { mem::transmute(self) }
    }

    pub fn clear(&mut self) {
        for e in self.entries.iter_mut() {
            e.entry = 0;
        }
    }

    /// Get a reference to the recursively-mapped PML4T.
    pub fn get_pml4t() -> &'static mut PageTable {
        unsafe {
            mem::transmute(PML4T_RECURSIVE_BASE)
        }
    }

    /// Get a reference to a recursively-mapped PD Pointer Table.
    pub fn get_pdp(pdp_idx: usize) -> &'static mut PageTable {
        unsafe {
            mem::transmute(PDPT_RECURSIVE_BASE + (0x1000 * pdp_idx))
        }
    }

    /// Get a reference to a recursively-mapped Page Directory.
    pub fn get_pd(pdp_idx: usize, pd_idx: usize) -> &'static mut PageTable {
        unsafe {
            mem::transmute(
                PD_RECURSIVE_BASE +
                (0x20_0000 * pdp_idx) +
                (0x1000 * pd_idx)
            )
        }
    }

    /// Get a reference to a recursively-mapped Page Table
    pub fn get_pt(pdp_idx: usize, pd_idx: usize, pt_idx: usize) -> &'static mut PageTable {
        unsafe {
            mem::transmute(
                PT_RECURSIVE_BASE + 
                (0x4000_0000 * pdp_idx) + 
                (0x20_0000 * pd_idx) + 
                (0x1000 * pt_idx)
            )
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = &PageTableEntry> {
        self.entries.iter()
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut PageTableEntry> {
        self.entries.iter_mut()
    }
}

impl ops::Index<usize> for PageTable {
    type Output = PageTableEntry;

    fn index (&self, idx: usize) -> &Self::Output {
        &self.entries[idx]
    }
}

impl ops::IndexMut<usize> for PageTable {
    fn index_mut (&mut self, idx: usize) -> &mut Self::Output {
        &mut self.entries[idx]
    }
}

pub fn get_mapping (virt_addr: usize) -> Option<PageTableEntry> {
    if (virt_addr & 0xFFF) > 0 {
        return None;
    }

    let pml4_idx: usize = (virt_addr >> 39) & 0x1FF;
    let pdp_idx: usize = (virt_addr >> 30) & 0x1FF;
    let pd_idx: usize = (virt_addr >> 21) & 0x1FF;
    let pt_idx: usize = (virt_addr >> 12) & 0x1FF;

    let pml4t = PageTable::get_pml4t();
    if pml4t[pml4_idx].present() {
        let pdpt = PageTable::get_pdp(pml4_idx);

        if pdpt[pdp_idx].present() {
            let pd = PageTable::get_pd(pml4_idx, pdp_idx);

            if pd[pd_idx].present() {
                let pt = PageTable::get_pt(pml4_idx, pdp_idx, pd_idx);

                return Some(pt[pt_idx]);
            }
        }
    }

    None
}

pub fn remap_boot_identity_paging() {
    let n_remapped_pdpts = KERNEL_BASE_PML4_IDX - PHYSICAL_MAP_PML4_IDX;
    let mut pml4t = PageTable::get_pml4t();

    /* Remap as many PDPTs pointing to the lower half of the address
     * space into the higher half as we can.
     */
    for i in 0..n_remapped_pdpts {
        let mut from_ent = pml4t[i];
        let mut to_ent = pml4t[i + PHYSICAL_MAP_PML4_IDX];

        if from_ent.present() {
            to_ent.set_physical_address(from_ent.physical_address());
            to_ent.set_present(true);
            from_ent.set_present(false);
        }
    }

    tlb::flush_all();
}

pub fn physical_memory_offset (phys_addr: usize) -> Option<usize> {
    if phys_addr >= MAX_PHYSICAL_MEMORY {
        return None;
    }

    Some(PHYSICAL_MAP_BASE + phys_addr)
}

pub fn offset_physical_memory_ptr<T>(ptr: *const T) -> Option<*const T> {
    physical_memory_offset(ptr as usize).map(|v| v as *const T)
}

pub fn offset_physical_memory_ptr_mut<T>(ptr: *mut T) -> Option<*mut T> {
    physical_memory_offset(ptr as usize).map(|v| v as *mut T)
}
