use core::ptr;
use core::fmt;

use lazy_static::lazy_static;
use spin::{Mutex, MutexGuard};

const SCREEN_WIDTH: u64  = 80;
const SCREEN_HEIGHT: u64 = 25;
const DEFAULT_COLOR: Color = Color(0x0F);

lazy_static! {
    pub static ref DEFAULT_DISPLAY: Mutex<VGATextMode> = Mutex::new(VGATextMode::new(0xB8000));
}

#[derive(Clone, Debug, Eq, PartialEq, Copy)]
#[repr(u8)]
#[allow(dead_code)]
pub enum Palette {
    Black        = 0,
    Blue         = 1,
    Green        = 2,
    Cyan         = 3,
    Red          = 4,
    Magenta      = 5,
    Brown        = 6,
    Gray         = 7,
    DarkGrey     = 8,
    LightBlue    = 9,
    LightGreen   = 10,
    LightCyan    = 11,
    LightRed     = 12,
    LightMagenta = 13,
    Yellow       = 14,
    White        = 15,
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
struct VGACharacter {
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
        let base = base_addr as *mut VGACharacter;

        VGATextMode {
            buf: unsafe { &mut *ptr::slice_from_raw_parts_mut(base, sz) },
            cur_x: 0,
            cur_y: 0,
        }
    }

    fn offset (x: u64, y: u64) -> Option<usize> {
        if x >= SCREEN_WIDTH || y >= SCREEN_HEIGHT {
            None
        } else {
            Some((x + (y * SCREEN_WIDTH)) as usize)
        }
    }

    /// Set the color of a particular cell on screen.
    pub fn set_color (&mut self, x: u64, y: u64, color: Color) {
        if let Some(offset) = VGATextMode::offset(x, y) {
            self.buf[offset].color = color;
        }        
    }

    /// Set the displayed glyph for a particular cell on screen.
    pub fn set_glyph (&mut self, x: u64, y: u64, glyph: u8) {
        if let Some(offset) = VGATextMode::offset(x, y) {
            self.buf[offset].glyph = glyph;
        }
    }

    /// Put a character on-screen with a specified color.
    pub fn put_char_color (&mut self, x: u64, y: u64, glyph: u8, color: Color) {
        if let Some(offset) = VGATextMode::offset(x, y) {
            self.buf[offset] = VGACharacter {
                color,
                glyph
            }
        }
    }

    /// Put a character on-screen with a default color.
    pub fn put_char (&mut self, x: u64, y: u64, glyph: u8) {
        self.put_char_color(x, y, glyph, DEFAULT_COLOR);
    }

    /// Scroll the display upwards.
    pub fn scroll (&mut self, lines: u64) {
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

    fn newline (&mut self) {
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
                _ => self.write_char(0xFE)
            };
        }
    }
}

impl fmt::Write for VGATextMode {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        VGATextMode::write_str(self, s);
        Ok(())
    }
}

#[macro_export]
macro_rules! print {
    ($($arg:tt)*) => ($crate::vga::_do_blocking_print(format_args!($($arg)*)));
}

#[macro_export]
macro_rules! println {
    () => ($crate::print!("\n"));
    ($($arg:tt)*) => ($crate::print!("{}\n", format_args!($($arg)*)));
}

#[doc(hidden)]
pub fn _do_blocking_print(args: fmt::Arguments) {
    use fmt::Write;
    DEFAULT_DISPLAY.lock().write_fmt(args).unwrap();
}

/// Forcibly take the lock for the default VGA display.
/// 
/// Note that this is horrifically unsafe.
pub unsafe fn force_take_lock() -> MutexGuard<'static, VGATextMode> {
    DEFAULT_DISPLAY.force_unlock();
    DEFAULT_DISPLAY.lock()
}