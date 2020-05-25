use crate::asm;
use crate::malloc::AllocationError;

use super::table::*;
use super::{PageLevel, PageStructure, PageTable, PageTableEntry, PhysicalPointer};

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
    pub unsafe fn load(&self) {
        self.pml4t.load();
    }

    /// Get whether this address space is currently loaded into CR3.
    pub fn is_loaded(&self) -> bool {
        asm::get_cr3() == self.pml4t.address()
    }

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

    /// Sets a mapping within this address space, replacing any previous
    /// mapping(s) for that address.
    pub fn set_mapping(&mut self, vaddr: usize, mapping: PageTableEntry, level: PageLevel) {
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

    /// Remove a range of mapped pages, with granularity corresponding to
    /// the given page-level.
    ///
    /// For example, removing pages with PDP granularity will unmap all pages
    /// with the same PML4 offset and PDP offset as the given virtual address.
    ///
    /// Attempting to unmap an address with finer granularity than it was
    /// originally mapped with will result in an error, with the error value
    /// being the mapped page's granularity.
    pub fn remove_mapping(&mut self, vaddr: usize, level: PageLevel) -> Result<(), PageLevel> {
        if level == PageLevel::PML4 {
            self.pml4t.clear(vaddr);
            return Ok(());
        }

        if let Some(mut pdpt) = self.pml4t.get(vaddr) {
            if level == PageLevel::PDP {
                pdpt.clear(vaddr);
                return Ok(());
            }

            let mut pd = match pdpt.get(vaddr) {
                PageStructureChild::None => return Ok(()),
                PageStructureChild::Page(_) => return Err(PageLevel::PDP),
                PageStructureChild::Table(t) => t,
            };

            if level == PageLevel::PD {
                pd.clear(vaddr);
                return Ok(());
            }

            match pd.get(vaddr) {
                PageStructureChild::None => return Ok(()),
                PageStructureChild::Page(_) => return Err(PageLevel::PD),
                PageStructureChild::Table(mut pt) => pt.clear(vaddr),
            };
        }

        Ok(())
    }

    /// Convenience function for mapping a single page with 4K granularity.
    pub fn map_page(&mut self, vaddr: usize, paddr: usize) {
        let pte = PageTableEntry::from_address(paddr);
        self.set_mapping(vaddr, pte, PageLevel::PT);
    }

    /// Convenience function for unmapping a single page with 4K granularity.
    pub fn unmap_page(&mut self, vaddr: usize) -> Result<(), PageLevel> {
        self.remove_mapping(vaddr, PageLevel::PT)
    }

    /// Convenience function for unmapping a range of pages with 4K granularity.
    pub fn unmap_page_range(&mut self, vaddr: usize, n_pages: usize) -> Result<(), PageLevel> {
        for i in 0..n_pages {
            self.unmap_page(vaddr + (0x1000 * i))?;
        }

        Ok(())
    }

    /// Convenience function for mapping a range of pages with 4K granularity.
    pub fn map_page_range(&mut self, vaddr: usize, paddr: usize, n_pages: usize) {
        for i in 0..n_pages {
            self.map_page(vaddr + (i * 0x1000), paddr + (i * 0x1000));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::malloc::physical_mem;
    use crate::malloc::{PhysicalMemory, VirtualMemory};
    use crate::rng::MersenneTwister64;
    use crate::test::TEST_SEED;
    use kernel_test_macro::kernel_test;

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
        addr_space.unmap_page_range(vaddr, 4).unwrap();
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
            space.unmap_page(vaddr).unwrap();
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
}
