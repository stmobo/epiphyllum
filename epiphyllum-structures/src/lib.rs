#![no_std]
#![feature(allocator_api)]
#![feature(dropck_eyepatch)]

extern crate alloc;

#[cfg(test)]
#[macro_use]
extern crate std;

#[cfg(test)]
extern crate quickcheck;

#[cfg(test)]
#[macro_use(quickcheck)]
extern crate quickcheck_macros;

mod rb_tree;

pub use rb_tree::RBTree;
