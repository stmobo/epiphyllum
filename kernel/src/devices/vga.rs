use core::fmt;
use core::ptr;

use crate::lock::{LockedGlobal, NoIRQSpinlockGuard};
use crate::paging;

const SCREEN_WIDTH: u64 = 80;
const SCREEN_HEIGHT: u64 = 25;
const DEFAULT_COLOR: Color = Color(0x0F);

static DEFAULT_VGA: LockedGlobal<VGATextMode> = LockedGlobal::new();

#[derive(Clone, Debug, Eq, PartialEq, Copy)]
#[repr(u8)]
#[allow(dead_code)]
pub enum Palette {
    Black = 0,
    Blue = 1,
    Green = 2,
    Cyan = 3,
    Red = 4,
    Magenta = 5,
    Brown = 6,
    Gray = 7,
    DarkGrey = 8,
    LightBlue = 9,
    LightGreen = 10,
    LightCyan = 11,
    LightRed = 12,
    LightMagenta = 13,
    Yellow = 14,
    White = 15,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct Color(u8);

impl Color {
    #[allow(dead_code)]
    pub fn new(fg: Palette, bg: Palette) -> Color {
        Color(((bg as u8) << 4) | fg as u8)
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
#[repr(C)]
pub struct VGACharacter {
    glyph: u8,
    color: Color,
}

pub struct VGATextMode {
    buf: &'static mut [VGACharacter],
    cur_x: u64,
    cur_y: u64,
}

impl VGATextMode {
    fn new(base_addr: usize) -> VGATextMode {
        let sz: usize = (SCREEN_WIDTH * SCREEN_HEIGHT) as usize;
        let base: *mut VGACharacter = paging::offset_direct_map(base_addr) as *mut VGACharacter;

        VGATextMode {
            buf: unsafe { &mut *ptr::slice_from_raw_parts_mut(base, sz) },
            cur_x: 0,
            cur_y: 0,
        }
    }

    fn offset(x: u64, y: u64) -> Option<usize> {
        if x >= SCREEN_WIDTH || y >= SCREEN_HEIGHT {
            None
        } else {
            Some((x + (y * SCREEN_WIDTH)) as usize)
        }
    }

    pub fn get_cell_mut(&mut self, x: u64, y: u64) -> Option<&mut VGACharacter> {
        if let Some(offset) = VGATextMode::offset(x, y) {
            Some(&mut self.buf[offset])
        } else {
            None
        }
    }

    pub fn get_cell(&self, x: u64, y: u64) -> Option<&VGACharacter> {
        if let Some(offset) = VGATextMode::offset(x, y) {
            Some(&self.buf[offset])
        } else {
            None
        }
    }

    /// Put a character on-screen with a specified color.
    pub fn put_char_color(&mut self, x: u64, y: u64, glyph: u8, color: Color) {
        if let Some(offset) = VGATextMode::offset(x, y) {
            self.buf[offset] = VGACharacter { color, glyph }
        }
    }

    /// Put a character on-screen with a default color.
    pub fn put_char(&mut self, x: u64, y: u64, glyph: u8) {
        self.put_char_color(x, y, glyph, DEFAULT_COLOR);
    }

    /// Scroll the display upwards.
    pub fn scroll(&mut self, lines: u64) {
        if lines == 0 || lines >= SCREEN_HEIGHT {
            return;
        }

        let copy_start = (SCREEN_WIDTH * lines) as usize;
        self.buf.copy_within(copy_start..self.buf.len(), 0);

        let clear_start = ((SCREEN_HEIGHT - lines) * SCREEN_WIDTH) as usize;
        for c in self.buf.iter_mut().skip(clear_start) {
            *c = VGACharacter {
                color: DEFAULT_COLOR,
                glyph: 0x20, // ASCII space
            }
        }
    }

    fn newline(&mut self) {
        if self.cur_y >= SCREEN_HEIGHT - 1 {
            self.cur_y = SCREEN_HEIGHT - 1;
            self.scroll(1);
        } else {
            self.cur_y += 1;
        }

        self.cur_x = 0;
    }

    /// Write a character to the screen.
    pub fn write_char(&mut self, c: u8) {
        match c {
            b'\n' => self.newline(),
            c => {
                if self.cur_x >= SCREEN_WIDTH {
                    self.newline()
                }

                self.put_char(self.cur_x, self.cur_y, c);
                self.cur_x += 1;
            }
        }
    }

    /// Write a string to the screen.
    pub fn write_str(&mut self, s: &str) {
        for c in s.bytes() {
            match c {
                (0x20..=0x7E) | b'\n' => self.write_char(c),
                _ => self.write_char(0xFE),
            };
        }
    }

    pub fn set_pos(&mut self, x: u64, y: u64) {
        if x >= SCREEN_WIDTH || y >= SCREEN_HEIGHT {
            return;
        }

        self.cur_x = x;
        self.cur_y = y;
    }

    pub fn clear(&mut self) {
        for c in self.buf.iter_mut() {
            *c = VGACharacter {
                color: DEFAULT_COLOR,
                glyph: 0x20, // ASCII space
            }
        }

        self.cur_x = 0;
        self.cur_y = 0;
    }
}

impl fmt::Write for VGATextMode {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        VGATextMode::write_str(self, s);
        Ok(())
    }
}

pub fn get_default_vga() -> NoIRQSpinlockGuard<'static, VGATextMode> {
    DEFAULT_VGA.init(|| VGATextMode::new(0xB8000)).lock()
}

/// Forcibly take the lock for the default VGA display.
///
/// Note that this is horrifically unsafe.
pub unsafe fn force_unlock() {
    DEFAULT_VGA
        .init(|| VGATextMode::new(0xB8000))
        .force_unlock();
}

/*
#[cfg(test)]
mod tests {
    use super::*;

    fn assert_display_char_eq(
        d: &mut spin::MutexGuard<'static, VGATextMode>,
        x: u64,
        y: u64,
        c: u8,
    ) {
        let glyph = d.get_cell(x, y).unwrap().glyph;

        assert_eq!(glyph, c);
    }

    #[kernel_test]
    fn test_write_str_basic() {
        print!("VGA - write_str_basic ... ");

        let mut d = DEFAULT_DISPLAY.lock();
        d.clear();
        d.write_str("foo");

        assert_display_char_eq(&mut d, 0, 0, b'f');
        assert_display_char_eq(&mut d, 1, 0, b'o');
        assert_display_char_eq(&mut d, 2, 0, b'o');
    }

    #[kernel_test]
    fn test_scroll() {
        print!("VGA - test_scroll ... ");

        let mut d = DEFAULT_DISPLAY.lock();

        d.clear();
        d.write_str("\n\n\nfoo");
        d.scroll(1);

        assert_display_char_eq(&mut d, 0, 2, b'f');
        assert_display_char_eq(&mut d, 1, 2, b'o');
        assert_display_char_eq(&mut d, 2, 2, b'o');

        assert_display_char_eq(&mut d, 0, 3, b' ');
    }
}
*/
