use alloc_crate::alloc::Layout;
use alloc_crate::boxed::Box;
use alloc_crate::string::String;
use core::convert::{AsMut, AsRef};
use core::marker::PhantomData;
use core::mem;
use core::ops::{Deref, DerefMut, Index, IndexMut};
use core::ptr;
use core::slice;
use core::slice::SliceIndex;
use core::str;
use core::str::Utf8Error;

use super::bindings::*;
use super::os_services;

const ACPI_ALLOCATE_BUFFER: u64 = u64::MAX;

/// An uninitialized output buffer for ACPICA to put store data in.
///
/// This wraps an ACPI_BUFFER marked as ACPI_ALLOCATE_BUFFER. When passed to
/// an ACPICA function (using the `buffer_ptr` method), ACPICA will
/// automatically allocate a buffer of the appropriate length and store a
/// pointer to it in this structure.
///
/// Note: This does not call Drop on any data in the buffer.
/// This is safe, going by Rust's rules.
pub struct CalleeAllocatedBuffer<T> {
    buffer: ACPI_BUFFER,
    _marker: PhantomData<[T]>,
}

impl<T> CalleeAllocatedBuffer<T> {
    pub fn new() -> CalleeAllocatedBuffer<T> {
        CalleeAllocatedBuffer {
            buffer: ACPI_BUFFER {
                Length: ACPI_ALLOCATE_BUFFER,
                Pointer: ptr::null_mut(),
            },
            _marker: PhantomData,
        }
    }

    pub fn buffer_ptr(&mut self) -> *mut ACPI_BUFFER {
        &mut self.buffer
    }

    pub fn is_initialized(&self) -> bool {
        !self.buffer.Pointer.is_null() && self.buffer.Length != ACPI_ALLOCATE_BUFFER
    }

    pub fn initialized(mut self) -> Option<AcpiOutputBuffer<T>> {
        if self.is_initialized() {
            let elems = (self.buffer.Length as usize) / mem::size_of::<T>();

            let buffer = self.buffer;
            self.buffer = ACPI_BUFFER {
                Length: ACPI_ALLOCATE_BUFFER,
                Pointer: ptr::null_mut(),
            };

            Some(AcpiOutputBuffer {
                buffer,
                elems,
                _marker: PhantomData,
            })
        } else {
            None
        }
    }
}

impl<T> Drop for CalleeAllocatedBuffer<T> {
    fn drop(&mut self) {
        if self.is_initialized() {
            os_services::AcpiOsFree(self.buffer.Pointer);
        }
    }
}

macro_rules! slice_like {
    ( $name:ident ) => {
        impl<T> AsRef<[T]> for $name<T> {
            fn as_ref(&self) -> &[T] {
                &**self
            }
        }

        impl<T> AsMut<[T]> for $name<T> {
            fn as_mut(&mut self) -> &mut [T] {
                &mut **self
            }
        }

        impl<T, I: SliceIndex<[T]>> Index<I> for $name<T> {
            type Output = I::Output;

            fn index(&self, index: I) -> &Self::Output {
                Index::index(&**self, index)
            }
        }

        impl<T, I: SliceIndex<[T]>> IndexMut<I> for $name<T> {
            fn index_mut(&mut self, index: I) -> &mut Self::Output {
                IndexMut::index_mut(&mut **self, index)
            }
        }
    };
}

/// An initialized output buffer that ACPICA has stored data in.
///
/// You can get one of these by calling `initialized` on a
/// `CalleeInitializedBuffer` whose buffer has been previously passed to an
/// ACPICA function.
///
/// It supports the usual slice operations.
///
/// Note: This does not call Drop on any data in the buffer.
/// This is safe, going by Rust's rules.
pub struct AcpiOutputBuffer<T> {
    buffer: ACPI_BUFFER,
    elems: usize,
    _marker: PhantomData<[T]>,
}

impl<T> Deref for AcpiOutputBuffer<T> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        unsafe {
            let p = self.buffer.Pointer as *const T;
            slice::from_raw_parts(p, self.elems)
        }
    }
}

impl<T> DerefMut for AcpiOutputBuffer<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe {
            let p = self.buffer.Pointer as *mut T;
            slice::from_raw_parts_mut(p, self.elems)
        }
    }
}

impl<T> Drop for AcpiOutputBuffer<T> {
    fn drop(&mut self) {
        os_services::AcpiOsFree(self.buffer.Pointer);
    }
}

slice_like!(AcpiOutputBuffer);

pub fn buffer_to_string(buffer: AcpiOutputBuffer<u8>) -> Result<String, Utf8Error> {
    Ok(String::from(str::from_utf8(&*buffer)?))
}

/// An input buffer for you to store data within to be passed into ACPICA.
///
/// It supports the usual slice operations.
///
/// Unlike its output buffer brethren, this buffer _will_ call Drop on the data
/// it contains.
pub struct AcpiInputBuffer<T> {
    buffer: ACPI_BUFFER,
    ptr: *mut [T],
}

impl<T> AcpiInputBuffer<T> {
    pub fn new(data: Box<[T]>) -> AcpiInputBuffer<T> {
        let layout = Layout::array::<T>(data.len()).unwrap();
        let ptr = Box::into_raw(data);

        unsafe {
            let raw_ptr = (*ptr).as_mut_ptr() as *mut cty::c_void;
            let bytes = layout.size() as u64;

            AcpiInputBuffer {
                buffer: ACPI_BUFFER {
                    Pointer: raw_ptr,
                    Length: bytes,
                },
                ptr,
            }
        }
    }

    pub fn buffer_ptr(&mut self) -> *mut ACPI_BUFFER {
        &mut self.buffer
    }
}

impl<T> Drop for AcpiInputBuffer<T> {
    fn drop(&mut self) {
        unsafe {
            Box::from_raw(self.ptr);
        }
    }
}

impl<T> Deref for AcpiInputBuffer<T> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        unsafe { &*self.ptr }
    }
}

impl<T> DerefMut for AcpiInputBuffer<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { &mut *self.ptr }
    }
}

slice_like!(AcpiInputBuffer);
