use super::{PhysicalPointer, PAGE_MASK};

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
#[repr(transparent)]
pub struct PageTableEntry {
    entry: u64,
}

impl PageTableEntry {
    pub fn new() -> PageTableEntry {
        PageTableEntry { entry: 0 }
    }

    pub fn from_address(address: usize) -> PageTableEntry {
        let mut pte = Self::new();
        pte.set_physical_address(address);
        pte.set_present(true);

        pte
    }

    pub fn physical_address(&self) -> usize {
        ((self.entry as usize) & PAGE_MASK) as usize
    }

    pub fn set_physical_address(&mut self, addr: usize) {
        let aligned = (addr & PAGE_MASK) as u64;
        self.entry = aligned | (self.entry & 0xFFF);
    }

    pub fn page<T>(&self) -> Option<PhysicalPointer<T>> {
        PhysicalPointer::new(self.physical_address())
    }

    pub fn present(&self) -> bool {
        (self.entry & 1) > 0
    }

    pub fn set_present(&mut self, present: bool) {
        if present {
            self.entry |= 1;
        } else {
            self.entry &= !1;
        }
    }

    pub fn writable(&self) -> bool {
        (self.entry & 2) != 0
    }

    pub fn set_writable(&mut self, writable: bool) {
        if writable {
            self.entry |= 2;
        } else {
            self.entry &= !2;
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

    pub fn cache_type(&self) -> CacheType {
        let pwt = (self.entry & (1 << 3)) != 0;
        let pcd = (self.entry & (1 << 4)) != 0;

        if pcd {
            CacheType::Uncacheable
        } else if pwt {
            CacheType::WriteThrough
        } else {
            CacheType::WriteBack
        }
    }

    pub fn set_cache_type(&mut self, caching: CacheType) {
        self.entry = (self.entry & !0b11000)
            | match caching {
                CacheType::WriteBack => 0,
                CacheType::WriteThrough => 0b01000,
                CacheType::Uncacheable => 0b11000,
            };
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum CacheType {
    WriteBack,
    WriteThrough,
    Uncacheable,
}
