use core::cmp::Ordering;
use core::fmt;
use core::fmt::{Debug, Display};

#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq)]
#[repr(transparent)]
pub struct Bitmask64(pub u64);

impl Bitmask64 {
    pub const fn all_ones() -> Bitmask64 {
        Bitmask64(u64::MAX)
    }

    pub const fn all_zeros() -> Bitmask64 {
        Bitmask64(0)
    }

    #[inline]
    pub fn n_ones(n: u64) -> Bitmask64 {
        debug_assert!(n <= 64);
        if n == 64 {
            Bitmask64(u64::MAX)
        } else {
            Bitmask64((1u64 << n) - 1)
        }
    }

    #[inline]
    pub fn get(self, index: usize) -> bool {
        debug_assert!(index < 64, "index out of bounds ({} >= 64)", index);
        (self.0 & (1u64 << (index as u64))) != 0
    }

    #[inline]
    pub fn set(self, index: usize, value: bool) -> Bitmask64 {
        debug_assert!(index < 64, "index out of bounds ({} >= 64)", index);
        if value {
            Bitmask64(self.0 | (1u64 << (index as u64)))
        } else {
            Bitmask64(self.0 & !(1u64 << (index as u64)))
        }
    }

    #[inline]
    pub fn invert(self) -> Bitmask64 {
        Bitmask64(!self.0)
    }

    #[inline]
    pub fn is_clear(self) -> bool {
        self.0 == 0
    }

    #[inline]
    pub fn first_set_bit(self) -> Option<usize> {
        if self.0 == 0 {
            None
        } else {
            Some(self.0.trailing_zeros() as usize)
        }
    }

    #[inline]
    pub fn last_set_bit(self) -> Option<usize> {
        if self.0 == 0 {
            None
        } else {
            Some(63 - (self.0.leading_zeros() as usize))
        }
    }

    #[inline]
    pub fn first_clear_bit(self) -> Option<usize> {
        if self.0 == u64::MAX {
            None
        } else {
            Some(self.0.trailing_ones() as usize)
        }
    }

    #[inline]
    pub fn last_clear_bit(self) -> Option<usize> {
        if self.0 == u64::MAX {
            None
        } else {
            Some(63 - (self.0.leading_ones() as usize))
        }
    }

    #[inline]
    pub fn remove_first_set_bit(self) -> Bitmask64 {
        Bitmask64(self.0 & self.0.saturating_sub(1))
    }

    #[inline]
    pub fn remove_last_set_bit(self) -> Bitmask64 {
        if self.0 <= 1 {
            Bitmask64(0)
        } else {
            Bitmask64(self.0 & (u64::MAX >> (self.0.leading_zeros() + 1)))
        }
    }

    #[inline]
    pub fn count_set(self) -> usize {
        self.0.count_ones() as usize
    }

    #[inline]
    pub fn count_clear(self) -> usize {
        self.0.count_zeros() as usize
    }
}

impl Debug for Bitmask64 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[{:#x}]", &self.0)
    }
}

impl Display for Bitmask64 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[{:#x}]", &self.0)
    }
}

impl PartialEq<u64> for Bitmask64 {
    #[inline]
    fn eq(&self, other: &u64) -> bool {
        self.0 == *other
    }
}

impl PartialOrd<u64> for Bitmask64 {
    #[inline]
    fn partial_cmp(&self, other: &u64) -> Option<Ordering> {
        self.0.partial_cmp(other)
    }
}

impl From<u64> for Bitmask64 {
    fn from(v: u64) -> Self {
        Bitmask64(v)
    }
}

impl From<Bitmask64> for u64 {
    fn from(bm: Bitmask64) -> Self {
        bm.0
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use kernel_test_macro::kernel_test;

    #[kernel_test]
    fn test_get() {
        assert!(Bitmask64(0xA5A5_A5A5_A5A5_A5A5).get(63));
        assert!(!Bitmask64(0xA5A5_A5A5_A5A5_A5A5).get(62));
        assert!(Bitmask64(0xA5A5_A5A5_A5A5_A5A5).get(61));
        assert!(!Bitmask64(0xA5A5_A5A5_A5A5_A5A5).get(60));
    }

    #[kernel_test]
    fn test_set() {
        assert_eq!(Bitmask64(0).set(0, true), Bitmask64(1));
        assert_eq!(Bitmask64(0).set(63, true), Bitmask64(0x8000_0000_0000_0000));

        assert_eq!(Bitmask64(1).set(0, true), Bitmask64(1));
        assert_eq!(
            Bitmask64(0x8000_0000_0000_0000).set(63, true),
            Bitmask64(0x8000_0000_0000_0000)
        );

        assert_eq!(Bitmask64(1).set(0, false), Bitmask64(0));
        assert_eq!(
            Bitmask64(0x8000_0000_0000_0000).set(63, false),
            Bitmask64(0)
        );

        assert_eq!(Bitmask64(0).set(0, false), Bitmask64(0));
        assert_eq!(Bitmask64(0).set(63, false), Bitmask64(0));
    }

    #[kernel_test]
    fn test_n_ones() {
        assert_eq!(Bitmask64::n_ones(0), 0);
        assert_eq!(Bitmask64::n_ones(64), u64::MAX);
        assert_eq!(Bitmask64::n_ones(4), 0xF);
    }

    #[kernel_test]
    fn test_invert() {
        assert_eq!(Bitmask64::all_zeros().invert(), Bitmask64::all_ones());
        assert_eq!(Bitmask64::all_ones().invert(), Bitmask64::all_zeros());
        assert_eq!(
            Bitmask64(0xA5A5_A5A5_A5A5_A5A5).invert(),
            Bitmask64(0x5A5A_5A5A_5A5A_5A5A)
        );
    }

    #[kernel_test]
    fn test_is_clear() {
        assert!(Bitmask64(0).is_clear());
        assert!(!Bitmask64(1).is_clear());
    }

    #[kernel_test]
    fn test_first_set_bit() {
        assert_eq!(Bitmask64(0).first_set_bit(), None);
        assert_eq!(Bitmask64(1).first_set_bit(), Some(0));
        assert_eq!(Bitmask64(0x8000_0000_0000_0000).first_set_bit(), Some(63));
        assert_eq!(Bitmask64(0x8000_0000_0000_0001).first_set_bit(), Some(0));
        assert_eq!(Bitmask64(6).first_set_bit(), Some(1));
    }

    #[kernel_test]
    fn test_last_set_bit() {
        assert_eq!(Bitmask64(0).last_set_bit(), None);
        assert_eq!(Bitmask64(1).last_set_bit(), Some(0));
        assert_eq!(Bitmask64(0x8000_0000_0000_0000).last_set_bit(), Some(63));
        assert_eq!(Bitmask64(0x8000_0000_0000_0001).last_set_bit(), Some(63));
        assert_eq!(Bitmask64(6).last_set_bit(), Some(2));
    }

    #[kernel_test]
    fn test_first_clear_bit() {
        assert_eq!(Bitmask64(u64::MAX).first_clear_bit(), None);
        assert_eq!(Bitmask64(0xFFFF_FFFF_FFFF_FFFE).first_clear_bit(), Some(0));
        assert_eq!(Bitmask64(0x7FFF_FFFF_FFFF_FFFF).first_clear_bit(), Some(63));
        assert_eq!(Bitmask64(0x7FFF_FFFF_FFFF_FFFE).first_clear_bit(), Some(0));
        assert_eq!(Bitmask64(0x9F).first_clear_bit(), Some(5));
    }

    #[kernel_test]
    fn test_last_clear_bit() {
        assert_eq!(Bitmask64(u64::MAX).last_clear_bit(), None);
        assert_eq!(Bitmask64(0xFFFF_FFFF_FFFF_FFFE).last_clear_bit(), Some(0));
        assert_eq!(Bitmask64(0x7FFF_FFFF_FFFF_FFFF).last_clear_bit(), Some(63));
        assert_eq!(Bitmask64(0x7FFF_FFFF_FFFF_FFFE).last_clear_bit(), Some(63));
        assert_eq!(Bitmask64(0xFFFF_FFFF_FFFF_FF90).last_clear_bit(), Some(6));
    }

    #[kernel_test]
    fn test_remove_first_set_bit() {
        assert_eq!(Bitmask64(0).remove_first_set_bit(), Bitmask64(0));
        assert_eq!(Bitmask64(1).remove_first_set_bit(), Bitmask64(0));
        assert_eq!(
            Bitmask64(0x8000_0000_0000_0000).remove_first_set_bit(),
            Bitmask64(0)
        );
        assert_eq!(Bitmask64(6).remove_first_set_bit(), Bitmask64(4));
        assert_eq!(Bitmask64(0x90).remove_first_set_bit(), Bitmask64(0x80));
    }

    #[kernel_test]
    fn test_remove_last_set_bit() {
        assert_eq!(Bitmask64(0).remove_last_set_bit(), Bitmask64(0));
        assert_eq!(Bitmask64(1).remove_last_set_bit(), Bitmask64(0));
        assert_eq!(
            Bitmask64(0x8000_0000_0000_0000).remove_last_set_bit(),
            Bitmask64(0)
        );
        assert_eq!(Bitmask64(6).remove_last_set_bit(), Bitmask64(2));
        assert_eq!(Bitmask64(0x90).remove_last_set_bit(), Bitmask64(0x10));
    }

    #[kernel_test]
    fn test_count_set() {
        assert_eq!(Bitmask64(0).count_set(), 0);
        assert_eq!(Bitmask64(1).count_set(), 1);
        assert_eq!(Bitmask64(0xFFFF_FFFF_FFFF_FFFF).count_set(), 64);
        assert_eq!(Bitmask64(0xA5).count_set(), 4);
    }

    #[kernel_test]
    fn test_count_clear() {
        assert_eq!(Bitmask64(0).count_clear(), 64);
        assert_eq!(Bitmask64(1).count_clear(), 63);
        assert_eq!(Bitmask64(0xFFFF_FFFF_FFFF_FFFF).count_clear(), 0);
        assert_eq!(Bitmask64(0xFFFF_FFFF_FFFF_FFA5).count_clear(), 4);
    }
}
