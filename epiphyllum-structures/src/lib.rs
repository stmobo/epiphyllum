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

pub mod rb_tree;
pub mod vyukov_queue;

pub use rb_tree::RBTree;
pub use vyukov_queue::{Queue, QueueReader, QueueWriter, queue};
