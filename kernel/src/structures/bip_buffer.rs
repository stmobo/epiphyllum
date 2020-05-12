//! Bipartite circular ring buffer implementation
//! see https://ferrous-systems.com/blog/lock-free-ring-buffer/

use alloc_crate::alloc;
use alloc_crate::alloc::Layout;
use alloc_crate::sync::Arc;
use core::convert::{AsMut, AsRef};
use core::ops::{Deref, DerefMut};
use core::ptr;
use core::slice;
use core::sync::atomic::{AtomicUsize, Ordering};

pub struct RawWriteRSVP<T> {
    ptr: *mut T,
    offset: usize,
    watermark_start: Option<usize>,
}

pub struct BipBuffer<T> {
    data: *mut T,
    len: usize,
    read: AtomicUsize,
    write: AtomicUsize,
    watermark: AtomicUsize,
}

impl<T> BipBuffer<T> {
    pub fn new(len: usize) -> (BipReader<T>, BipWriter<T>) {
        let layout = Layout::array::<T>(len).unwrap();
        let buffer = unsafe {
            let p = alloc::alloc(layout);
            if p == ptr::null_mut() {
                alloc::handle_alloc_error(layout);
            }

            BipBuffer {
                data: p as *mut T,
                len,
                read: AtomicUsize::new(0),
                write: AtomicUsize::new(0),
                watermark: AtomicUsize::new(len),
            }
        };

        let buffer = Arc::new(buffer);
        let reader = BipReader {
            buffer: buffer.clone(),
        };

        let writer = BipWriter {
            buffer: buffer.clone(),
        };

        (reader, writer)
    }

    fn write_pos(&self) -> usize {
        self.write.load(Ordering::SeqCst)
    }

    fn read_pos(&self) -> usize {
        self.read.load(Ordering::SeqCst)
    }

    fn watermark_pos(&self) -> usize {
        self.watermark.load(Ordering::SeqCst)
    }

    /// Reserve a contiguous region of the buffer for writing.
    ///
    /// Returns a WriteReservation if successful.
    /// If there isn't enough space in the buffer to write in, then it returns
    /// the current available writing space in the buffer instead.
    ///
    /// ## Safety
    /// This should only be called by a single writer thread.
    unsafe fn reserve_write(&self, len: usize) -> Result<RawWriteRSVP<T>, usize> {
        // since this function is only called by one writer, the write_pos
        // shouldn't change suddenly
        let write_pos = self.write_pos();

        if self.len.saturating_sub(write_pos) >= len {
            // not wrapping around
            if write_pos < self.read_pos() {
                // make sure write does not overtake read before the latter
                // wraps around
                let avail = self.read_pos().saturating_sub(write_pos);
                if avail <= len {
                    return Err(avail);
                }
            }

            Ok(RawWriteRSVP {
                ptr: self.data.offset(write_pos as isize),
                offset: write_pos,
                watermark_start: None,
            })
        } else {
            // wrapping around
            if self.read_pos() <= write_pos {
                // ensure there's enough space at the beginning of the buffer
                let avail = self.read_pos() - 1;
                if avail < len {
                    return Err(avail);
                }
            } else {
                // don't overlap unread data at beginning of buffer
                return Err(self.read_pos() - write_pos + 1);
            }

            Ok(RawWriteRSVP {
                ptr: self.data,
                offset: 0,
                watermark_start: Some(write_pos),
            })
        }
    }

    /// Advances the write and watermark pointers.
    ///
    /// ## Safety
    /// This function must only be called from a single writer thread.
    /// This function also assumes that actual_len is a valid write length
    /// for the given RawWriteRSVP.
    unsafe fn commit_write(&self, rsvp: RawWriteRSVP<T>, actual_len: usize) {
        let new_write_pos = rsvp.offset + actual_len;
        let new_watermark = match rsvp.watermark_start {
            Some(p) => p,
            None => new_write_pos,
        };

        self.watermark.store(new_watermark, Ordering::SeqCst);
        self.write.store(new_write_pos, Ordering::SeqCst);
    }

    /// Ensure that a given region after the current read pointer is available
    /// for reading.
    ///
    /// ## Safety
    /// This should only be called by a single reader thread.
    unsafe fn reserve_read(&self, len: usize) -> Result<*mut T, usize> {
        let cur_read = self.read_pos();

        let avail: usize;
        if self.write_pos() >= cur_read {
            avail = self.write_pos().saturating_sub(cur_read);
        } else {
            avail = self.watermark_pos().saturating_sub(cur_read);

            if avail == 0 {
                // wrap around
                let avail = self.write_pos();
                if avail >= len {
                    return Ok(self.data);
                } else {
                    return Err(avail);
                }
            }
        }

        if avail >= len {
            return Ok(self.data.offset(cur_read as isize));
        } else {
            return Err(avail);
        }
    }

    /// Advances the read pointer.
    ///
    /// ## Safety
    /// This function must only be called from a single reader thread.
    /// This function assumes that len is a valid read length.
    unsafe fn commit_read(&self, len: usize) {
        let cur_read = self.read_pos();
        if cur_read > self.write_pos() && cur_read == self.watermark_pos() {
            // our reserve_read() call wrapped around
            self.read.store(len, Ordering::SeqCst);
        }

        let new_read = cur_read + len;
        if cur_read > self.write_pos() && new_read == self.watermark_pos() {
            // wrap around to beginning
            self.read.store(0, Ordering::SeqCst);
        } else {
            self.read.store(new_read, Ordering::SeqCst);
        }
    }

    fn read_space_available(&self) -> usize {
        if self.write_pos() >= self.read_pos() {
            self.write_pos().saturating_sub(self.read_pos())
        } else {
            self.watermark_pos().saturating_sub(self.read_pos())
        }
    }

    fn write_space_available(&self) -> usize {
        if self.write_pos() >= self.read_pos() {
            self.len.saturating_sub(self.write_pos())
        } else {
            self.read_pos().saturating_sub(self.write_pos() + 1)
        }
    }

    /// Reserve a contiguous slice of this buffer that can be read from.
    ///
    /// If there isn't enough space in the buffer to read from, then it returns
    /// the number of elements available to read from the buffer instead.
    unsafe fn read(&self, len: usize) -> Result<BufferRead<'_, T>, usize> {
        Ok(BufferRead {
            ptr: self.reserve_read(len)? as *const T,
            buffer: self,
            len,
        })
    }

    /// Reserve a contiguous slice of this buffer that can be written to.
    ///
    /// If there isn't enough space in the buffer to read from, then it returns
    /// the number of free spaces available that can be written into the buffer
    /// instead.
    unsafe fn write(&self, len: usize) -> Result<BufferWrite<'_, T>, usize> {
        Ok(BufferWrite {
            rsvp: self.reserve_write(len)?,
            buffer: self,
            len,
        })
    }
}

impl<T> Drop for BipBuffer<T> {
    fn drop(&mut self) {
        unsafe {
            let layout = Layout::array::<T>(self.len).unwrap();
            alloc::dealloc(self.data as *mut u8, layout);
        }
    }
}

pub struct BufferWrite<'a, T> {
    buffer: &'a BipBuffer<T>,
    rsvp: RawWriteRSVP<T>,
    len: usize,
}

impl<'a, T> BufferWrite<'a, T> {
    pub fn commit(self, actual_len: usize) {
        if actual_len > self.len {
            panic!(
                "invalid length for commit (len is {} but reserved {})",
                actual_len, self.len
            );
        }

        unsafe {
            self.buffer.commit_write(self.rsvp, actual_len);
        }
    }

    pub fn as_ptr(&self) -> *mut T {
        self.rsvp.ptr
    }

    pub fn len(&self) -> usize {
        self.len
    }
}

impl<'a, T> Deref for BufferWrite<'a, T> {
    type Target = [T];

    fn deref(&self) -> &[T] {
        unsafe { slice::from_raw_parts(self.rsvp.ptr as *const T, self.len) }
    }
}

impl<'a, T> DerefMut for BufferWrite<'a, T> {
    fn deref_mut(&mut self) -> &mut [T] {
        unsafe { slice::from_raw_parts_mut(self.rsvp.ptr, self.len) }
    }
}

impl<'a, T> AsRef<[T]> for BufferWrite<'a, T> {
    fn as_ref(&self) -> &[T] {
        &**self
    }
}

impl<'a, T> AsMut<[T]> for BufferWrite<'a, T> {
    fn as_mut(&mut self) -> &mut [T] {
        &mut **self
    }
}

unsafe impl<'a, T> Send for BufferWrite<'a, T> {}
unsafe impl<'a, T> Sync for BufferWrite<'a, T> {}

pub struct BufferRead<'a, T> {
    buffer: &'a BipBuffer<T>,
    ptr: *const T,
    len: usize,
}

impl<'a, T> BufferRead<'a, T> {
    pub fn commit(self, actual_len: usize) {
        if actual_len > self.len {
            panic!(
                "invalid length for commit (len is {} but reserved {})",
                actual_len, self.len
            );
        }

        unsafe {
            self.buffer.commit_read(actual_len);
        }
    }

    pub fn as_ptr(&self) -> *const T {
        self.ptr
    }

    pub fn len(&self) -> usize {
        self.len
    }
}

impl<'a, T> Deref for BufferRead<'a, T> {
    type Target = [T];

    fn deref(&self) -> &[T] {
        unsafe { slice::from_raw_parts(self.ptr, self.len) }
    }
}

impl<'a, T> AsRef<[T]> for BufferRead<'a, T> {
    fn as_ref(&self) -> &[T] {
        &**self
    }
}

unsafe impl<'a, T> Send for BufferRead<'a, T> {}
unsafe impl<'a, T> Sync for BufferRead<'a, T> {}

#[repr(transparent)]
pub struct BipReader<T> {
    buffer: Arc<BipBuffer<T>>,
}

impl<T> BipReader<T> {
    pub fn read(&self, len: usize) -> Result<BufferRead<'_, T>, usize> {
        unsafe { self.buffer.read(len) }
    }

    pub fn read_all(&self) -> BufferRead<'_, T> {
        unsafe { self.buffer.read(self.elements_available()).unwrap() }
    }

    pub fn elements_available(&self) -> usize {
        self.buffer.read_space_available()
    }
}

impl<T: Copy> BipReader<T> {
    pub fn read_into<U: AsMut<[T]>>(&self, buf: &mut U) -> bool {
        let dst = buf.as_mut();
        if let Ok(reader) = self.read(dst.len()) {
            dst.copy_from_slice(reader.as_ref());
            reader.commit(dst.len());
            true
        } else {
            false
        }
    }
}

unsafe impl<T> Send for BipReader<T> {}

#[repr(transparent)]
pub struct BipWriter<T> {
    buffer: Arc<BipBuffer<T>>,
}

impl<T> BipWriter<T> {
    pub fn write(&self, len: usize) -> Result<BufferWrite<'_, T>, usize> {
        unsafe { self.buffer.write(len) }
    }

    pub fn elements_available(&self) -> usize {
        self.buffer.write_space_available()
    }
}

impl<T: Copy> BipWriter<T> {
    pub fn write_from<U: AsRef<[T]>>(&self, buf: &U) -> bool {
        let src = buf.as_ref();
        if let Ok(mut writer) = self.write(src.len()) {
            writer.copy_from_slice(src);
            writer.commit(src.len());
            true
        } else {
            false
        }
    }
}

unsafe impl<T> Send for BipWriter<T> {}
