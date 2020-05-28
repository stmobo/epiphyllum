use crate::asm;
use crate::malloc::AllocationError;

use super::table::*;
use super::{CacheType, PageLevel, PageStructure, PageTable, PageTableEntry, PhysicalPointer};

#[derive(Debug, Copy, Clone)]
pub enum MappingError {
    AllocationFailure(AllocationError),
    AlreadyMapped,
}

#[derive(Copy, Clone)]
struct Resolved(PhysicalPointer<PageTable>, PageLevel);

#[repr(transparent)]
pub struct AddressSpace {
    pml4t: PML4T,
}

impl AddressSpace {
    pub unsafe fn current() -> AddressSpace {
        AddressSpace {
            pml4t: PML4T::current(),
        }
    }

    pub fn new() -> Result<AddressSpace, AllocationError> {
        Ok(AddressSpace {
            pml4t: PML4T::new()?,
        })
    }

    /// Loads this address space into CR3.
    ///
    /// # Safety
    /// This function modifies processor control registers and additionally
    /// modifies processor page mappings.
    pub unsafe fn load(&self) {
        self.pml4t.load();
    }

    /// Get whether this address space is currently loaded into CR3.
    pub fn is_loaded(&self) -> bool {
        asm::get_cr3() == self.pml4t.address()
    }

    /// Get the physical address of the PML4T at the root of this address
    /// space.
    pub fn pml4t_address(&self) -> usize {
        self.pml4t.address()
    }

    /// Gets the physical page mapping for a virtual address in this address
    /// space, if one exists.
    pub fn get_mapping(&self, vaddr: usize) -> Option<(PageLevel, PageTableEntry)> {
        let pdpt = self.pml4t.get(vaddr)?;

        let pd = match pdpt.get(vaddr) {
            PageStructureChild::None => return None,
            PageStructureChild::Page(ent) => return Some((PageLevel::PDP, ent)),
            PageStructureChild::Table(t) => t,
        };

        let pt = match pd.get(vaddr) {
            PageStructureChild::None => return None,
            PageStructureChild::Page(ent) => return Some((PageLevel::PD, ent)),
            PageStructureChild::Table(t) => t,
        };

        Some((PageLevel::PT, pt.get(vaddr)?))
    }

    /// Clear the TLB for a given address range, if this address space is
    /// loaded.
    fn clear_tlb(&self, vaddr: usize, level: PageLevel) {
        if self.is_loaded() {
            unsafe {
                match level {
                    PageLevel::PML4 => unreachable!(),
                    PageLevel::PDP | PageLevel::PD => self.load(),
                    PageLevel::PT => asm::invlpg(vaddr),
                };
            }
        }
    }

    /// Sets a mapping without a TLB flush.
    fn _set_mapping(&mut self, vaddr: usize, mapping: PageTableEntry, level: PageLevel) {
        assert_ne!(level, PageLevel::PML4, "invalid level for page mapping");

        let mut pdpt = self.pml4t.ensure_table(vaddr);
        if level == PageLevel::PDP {
            pdpt.map_page(vaddr, mapping);
            return;
        }

        let mut pd = pdpt.ensure_table(vaddr);
        if level == PageLevel::PD {
            pd.map_page(vaddr, mapping);
            return;
        }

        let mut pt = pd.ensure_table(vaddr);
        pt.map_page(vaddr, mapping);
    }

    /// Sets a mapping within this address space, replacing any previous
    /// mapping(s) for that address.
    ///
    /// The granularity of the mapping is specified by the `level` parameter.
    /// For example, mapping pages with PDP granularity will create a 1GiB
    /// mapping that starts at the physical address specified in the given
    /// PageTableEntry.
    pub fn set_mapping(&mut self, vaddr: usize, mapping: PageTableEntry, level: PageLevel) {
        self._set_mapping(vaddr, mapping, level);
        self.clear_tlb(vaddr, level);
    }

    /// Clears a mapping without a TLB flush.
    fn _remove_mapping(&mut self, vaddr: usize, level: PageLevel) {
        if level == PageLevel::PML4 {
            self.pml4t.clear(vaddr);
            return;
        }

        if let Some(mut pdpt) = self.pml4t.get(vaddr) {
            if !pdpt.is_present(vaddr) {
                return;
            } else if level == PageLevel::PDP {
                pdpt.clear(vaddr);
                return;
            }

            let mut pd = pdpt.ensure_table(vaddr);
            if !pd.is_present(vaddr) {
                return;
            } else if level == PageLevel::PD {
                pd.clear(vaddr);
                return;
            }

            let mut pt = pd.ensure_table(vaddr);
            if !pt.is_present(vaddr) {
                return;
            }

            pt.clear(vaddr);
        }
    }

    /// Remove a range of mapped pages, with granularity corresponding to
    /// the given page-level.
    ///
    /// For example, removing pages with PDP granularity will unmap all pages
    /// with the same PML4 offset and PDP offset as the given virtual address.
    pub fn remove_mapping(&mut self, vaddr: usize, level: PageLevel) {
        self._remove_mapping(vaddr, level);
        self.clear_tlb(vaddr, level);
    }

    /// Convenience function for mapping a single page with 4K granularity.
    pub fn map_page(&mut self, vaddr: usize, paddr: usize) {
        let pte = PageTableEntry::from_address(paddr);
        self.set_mapping(vaddr, pte, PageLevel::PT);
    }

    /// Convenience function for unmapping a single page with 4K granularity.
    pub fn unmap_page(&mut self, vaddr: usize) {
        self.remove_mapping(vaddr, PageLevel::PT)
    }

    /// Convenience function for unmapping a range of pages with 4K granularity.
    pub fn unmap_page_range(&mut self, vaddr: usize, n_pages: usize) {
        for i in 0..n_pages {
            self._remove_mapping(vaddr + (0x1000 * i), PageLevel::PT);
        }

        if self.is_loaded() {
            unsafe { self.load() };
        }
    }

    /// Convenience function for mapping a range of pages with 4K granularity.
    pub fn map_page_range(&mut self, vaddr: usize, paddr: usize, n_pages: usize) {
        for i in 0..n_pages {
            let pte = PageTableEntry::from_address(paddr + (i * 0x1000));
            self._set_mapping(vaddr + (i * 0x1000), pte, PageLevel::PT);
        }

        if self.is_loaded() {
            unsafe { self.load() };
        }
    }

    /// Transform page table entries for a range of pages in the address space.
    fn _transform_entries<T>(&mut self, vaddr: usize, n_pages: usize, mut xfrm: T)
    where
        T: FnMut(PageTableEntry) -> PageTableEntry,
    {
        let mut page_count = n_pages;
        let mut cur_addr = vaddr;

        while page_count > 0 {
            let pml4e = self.pml4t.get_entry(cur_addr);
            if !pml4e.present() {
                // Skip this entire portion of the address range.
                page_count = page_count.saturating_sub(1 << 27);
                cur_addr += 1 << 39;
                continue;
            }

            let mut pdpt = self.pml4t.get(cur_addr).unwrap();

            let mut pd = match pdpt.get(cur_addr) {
                PageStructureChild::None => {
                    // Skip 1 GiB
                    page_count = page_count.saturating_sub(1 << 18); // 18 = 30 - 12
                    cur_addr += 1 << 30;
                    continue;
                }
                PageStructureChild::Table(pd) => pd,
                PageStructureChild::Page(entry) => {
                    // If possible, transform the map for the entire page at once.
                    if (page_count >= (1 << 18))
                        && (cur_addr & PageLevel::PDP.alignment_mask().unwrap() == 0)
                    {
                        pdpt.set_entry(cur_addr, xfrm(entry));
                        page_count = page_count.saturating_sub(1 << 18); // 18 = 30 - 12
                        cur_addr += 1 << 30;
                        continue;
                    } else {
                        // Otherwise, split this page mapping into a smaller map and continue.
                        pdpt.split_page_mapping(cur_addr).unwrap()
                    }
                }
            };

            let mut pt = match pd.get(cur_addr) {
                PageStructureChild::None => {
                    // Skip 2 MiB
                    page_count = page_count.saturating_sub(1 << 9);
                    cur_addr += 1 << 21;
                    continue;
                }
                PageStructureChild::Table(pt) => pt,
                PageStructureChild::Page(entry) => {
                    if (page_count >= (1 << 9))
                        && (cur_addr & PageLevel::PD.alignment_mask().unwrap() == 0)
                    {
                        pd.set_entry(cur_addr, xfrm(entry));
                        page_count = page_count.saturating_sub(1 << 9); // 18 = 30 - 12
                        cur_addr += 1 << 21;
                        continue;
                    } else {
                        // Otherwise, split this page mapping into a smaller map and continue.
                        pd.split_page_mapping(cur_addr).unwrap()
                    }
                }
            };

            let entry = pt.get_entry(cur_addr);
            if entry.present() {
                pt.set_entry(cur_addr, xfrm(entry));
            }

            page_count = page_count.saturating_sub(1);
            cur_addr += 1 << 12;
        }
    }

    pub fn set_caching(&mut self, vaddr: usize, n_pages: usize, caching: CacheType) {
        self._transform_entries(vaddr, n_pages, |entry| {
            let mut ent = entry;
            ent.set_cache_type(caching);
            ent
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::malloc::physical_mem;
    use crate::malloc::{PhysicalMemory, VirtualMemory};
    use crate::paging::PHYSICAL_MAP_BASE;
    use crate::rng::MersenneTwister64;
    use crate::test::TEST_SEED;
    use kernel_test_macro::kernel_test;

    use alloc_crate::vec::Vec;

    #[kernel_test]
    fn test_map() {
        let mut addr_space = unsafe { AddressSpace::current() };
        let pmem = PhysicalMemory::new(2).unwrap();
        let vmem = VirtualMemory::new(0x4000).unwrap();
        let paddr = pmem.address();
        let vaddr = vmem.address();

        addr_space.map_page_range(vaddr, paddr, 4);

        let mut rng = MersenneTwister64::new(TEST_SEED);
        unsafe {
            for i in 0..(0x4000 / 8) {
                let v = (vaddr as *mut u64).offset(i);
                let p = pmem.as_mut_ptr::<u64>().offset(i);

                if i & 1 == 0 {
                    v.write_volatile(rng.generate());
                } else {
                    p.write_volatile(rng.generate());
                }
            }

            rng.seed(TEST_SEED);
            for i in 0..(0x4000 / 8) {
                let v = (vaddr as *mut u64).offset(i);
                let p = pmem.as_mut_ptr::<u64>().offset(i);

                let val = rng.generate();
                assert_eq!(
                    v.read_volatile(),
                    val,
                    "read incorrect value from virtual address {:#018x}",
                    v as usize
                );

                assert_eq!(
                    p.read_volatile(),
                    val,
                    "read incorrect value from physical address {:#018x}",
                    paddr + (i as usize * 8)
                );
            }
        }

        drop(pmem);
        addr_space.unmap_page_range(vaddr, 4);
    }

    #[kernel_test]
    fn test_refcount() {
        let pmem = PhysicalMemory::new(0).unwrap();
        let paddr = pmem.address();
        let vaddr = 0x10000;
        let pfn = paddr >> 12;

        unsafe {
            let page_data = crate::paging::page_metadata().unwrap();
            let mut space = AddressSpace::current();

            // The refcount should be 1 after the PhysicalMemory constructor:
            assert_eq!(
                page_data[pfn].refcount(),
                1,
                "incorrect refcount for allocated page"
            );

            // Mapping the page adds a reference:
            space.map_page(vaddr, paddr);
            assert_eq!(
                page_data[pfn].refcount(),
                2,
                "incorrect refcount for mapped page"
            );

            // Ensure we can't overwrite the referenced page:
            let alloc_test = physical_mem::allocate_at(paddr, 0);
            assert_eq!(
                alloc_test,
                Err(AllocationError::AlreadyAllocated),
                "incorrectly overwrote test allocation"
            );

            // PhysicalMemory's Drop code should decrement the refcount:
            drop(pmem);
            assert_eq!(
                page_data[pfn].refcount(),
                1,
                "incorrect refcount for mapped page"
            );

            // The page should still be allocated however:
            let alloc_test = physical_mem::allocate_at(paddr, 0);
            assert_eq!(
                alloc_test,
                Err(AllocationError::AlreadyAllocated),
                "incorrectly overwrote test allocation"
            );

            // Check the reference counts on the page tables:
            // PML4T and PDPT are shared (most likely), but PDs and PTs should
            // be uniquely mapped.
            let pdpt = space.pml4t.get(vaddr).unwrap();

            let pd = match pdpt.get(vaddr) {
                PageStructureChild::None | PageStructureChild::Page(_) => {
                    panic!("could not find page directory for mapping")
                }
                PageStructureChild::Table(pd) => pd,
            };

            let pt = match pd.get(vaddr) {
                PageStructureChild::None | PageStructureChild::Page(_) => {
                    panic!("could not find page table for mapping")
                }
                PageStructureChild::Table(pt) => pt,
            };

            assert_eq!(
                page_data[pd.address() >> 12].refcount(),
                1,
                "incorrect refcount for page directory at {:#018x} (pfn {})",
                pd.address(),
                pd.address() >> 12
            );

            assert_eq!(
                page_data[pt.address() >> 12].refcount(),
                1,
                "incorrect refcount for page table at {:#018x} (pfn {})",
                pt.address(),
                pt.address() >> 12
            );

            // Unmapping the page should decrement its refcount:
            space.unmap_page(vaddr);
            assert_eq!(
                page_data[pfn].refcount(),
                0,
                "incorrect refcount for unmapped page"
            );

            // Since the refcount went to zero, it should be free for
            // re-allocation:
            let alloc_test = physical_mem::allocate_at(paddr, 0);
            assert_eq!(
                alloc_test,
                Ok(paddr),
                "could not re-allocate test allocation"
            );

            // Clean up:
            physical_mem::deallocate(paddr, 0);
            assert_eq!(
                page_data[pfn].refcount(),
                0,
                "incorrect refcount for deallocated page"
            );
        }
    }

    #[kernel_test]
    fn test_transform() {
        // This tests set_caching(), _transform_entries(), as well as the
        // split_page_mapping() methods for PDPT and PageDirectory.

        let transform_address: usize = PHYSICAL_MAP_BASE + (72 << 30);
        let n_pages: usize = (1 << 18) + (1 << 9) + 1;

        let mut addr_space = unsafe { AddressSpace::current() };

        let pdpt = addr_space.pml4t.get(transform_address).unwrap();
        let mut prev_pdpt_entries = Vec::with_capacity(512);

        // Copy the old physical map PDPT entries so we can check them later.
        for i in 0..512 {
            prev_pdpt_entries.push(pdpt.get_by_index(i));
        }

        drop(pdpt);

        // This _should_ transform exactly one of each page type (1G, 2M, and 4K).
        addr_space.set_caching(transform_address, n_pages, CacheType::Uncacheable);
        let pdpt = addr_space.pml4t.get(transform_address).unwrap();

        // The transform should not affect any other PDPT entries other than
        // the ones in the given range (in this case, entries 72 and 73):
        for i in 0..512 {
            if i == 72 || i == 73 {
                continue;
            }

            assert_eq!(
                pdpt.get_by_index(i),
                prev_pdpt_entries[i],
                "PDPT entry {} changed",
                i
            );
        }

        // This 1G page should have been transformed in its entirety:
        let pdpe_72 = pdpt.get_by_index(72);
        assert!(pdpe_72.present(), "transform unmapped page");
        assert_eq!(
            pdpe_72.cache_type(),
            CacheType::Uncacheable,
            "incorrect cache type"
        );
        assert_eq!(
            pdpe_72.physical_address(),
            72 << 30,
            "transform changed physical address"
        );
        assert!(pdpe_72.page_size(), "transform changed page size");
        assert!(!pdpe_72.writable(), "transform changed writability");

        // Get the page directory at PDPT offset 73:
        let pd = match pdpt.get(PHYSICAL_MAP_BASE + (73 << 30)) {
            PageStructureChild::Table(pd) => pd,
            PageStructureChild::Page(_) => {
                panic!("Physical mapping portion should have been a table")
            }
            PageStructureChild::None => panic!("Physical mapping portion unexpectedly disappeared"),
        };

        // This 2M page should have been transformed in its entirety:
        let pde = pd.get_by_index(0);
        assert!(pde.present(), "transform unmapped page");
        assert_eq!(
            pde.cache_type(),
            CacheType::Uncacheable,
            "incorrect cache type"
        );
        assert_eq!(
            pde.physical_address(),
            73 << 30,
            "transform changed physical address"
        );
        assert!(pde.page_size(), "transform changed page size");
        assert!(!pde.writable(), "transform changed writability");

        // Ensure entries 2 through 511 have all-default settings.
        // (Entry 1 should now point to a page table.)
        for i in 2..512 {
            let pde = pd.get_by_index(i);
            assert!(pde.present(), "transform unmapped page");
            assert_eq!(
                pde.cache_type(),
                CacheType::WriteBack,
                "incorrect cache type"
            );
            assert_eq!(
                pde.physical_address(),
                (73 << 30) + (i << 21),
                "transform changed physical address"
            );
            assert!(pde.page_size(), "transform changed page size");
            assert!(!pde.writable(), "transform changed writability");
        }

        // Get the page table at PD offset 1:
        let pt = match pd.get(PHYSICAL_MAP_BASE + (73 << 30) + (1 << 21)) {
            PageStructureChild::Table(pt) => pt,
            PageStructureChild::Page(_) => {
                panic!("Physical mapping portion should have been a table")
            }
            PageStructureChild::None => panic!("Physical mapping portion unexpectedly disappeared"),
        };

        // This 4K entry should have been transformed.
        let pte = pt.get_by_index(0);
        assert!(pte.present(), "transform unmapped page");
        assert_eq!(
            pte.cache_type(),
            CacheType::Uncacheable,
            "incorrect cache type"
        );
        assert_eq!(
            pte.physical_address(),
            (73 << 30) + (1 << 21),
            "transform changed physical address"
        );
        assert!(!pte.page_size(), "transform changed PAT bit");
        assert!(!pte.writable(), "transform changed writability");

        // Ensure entries 1 through 511 have all-default settings.
        for i in 1..512 {
            let pte = pt.get_by_index(i);
            assert!(pte.present(), "transform unmapped page");
            assert_eq!(
                pte.cache_type(),
                CacheType::WriteBack,
                "incorrect cache type"
            );
            assert_eq!(
                pte.physical_address(),
                (73 << 30) + (1 << 21) + (i << 12),
                "transform changed physical address"
            );
            assert!(!pte.page_size(), "transform changed PAT bit");
            assert!(!pte.writable(), "transform changed writability");
        }
    }
}
