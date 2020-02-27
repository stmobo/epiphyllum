use core::ptr;

#[derive(Clone, Debug, Eq, PartialEq, Copy)]
#[repr(u8)]
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
struct Color(u8);

impl Color {
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

const SCREEN_WIDTH: usize  = 25;
const SCREEN_HEIGHT: usize = 80;
const DEFAULT_COLOR: Color = Color(0x0F);

pub struct VGATextMode {
    buf: *mut u8, 
}

impl VGATextMode {
    fn new(base_addr: *mut u8) -> VGATextMode {
        VGATextMode {
            buf: base_addr 
        }
    }

    pub fn set_color(&mut self, x: usize, y: usize, color: Color) {
        if x >= SCREEN_WIDTH || y >= SCREEN_HEIGHT {
            return;
        }

        let offset: isize = 2 * (x + (y * SCREEN_WIDTH)) as isize;
        unsafe {
            ptr::write_volatile(self.buf.offset(offset), color.0);
        }
    }

    pub fn set_glyph(&mut self, x: usize, y: usize, glyph: u8) {
        if x >= SCREEN_WIDTH || y >= SCREEN_HEIGHT {
            return;
        }

        let offset: isize = 2 * (x + (y * SCREEN_HEIGHT)) as isize;
        unsafe {
            ptr::write_volatile(self.buf.offset(offset+1), glyph);
        }
    }

    pub fn write_char_color(&mut self, x: usize, y: usize, c: char, color: Color) {
        if !c.is_ascii() {
            return;
        }

        let mut b = [0; 4];
        c.encode_utf8(&mut b);
        self.set_color(x, y, color);
        self.set_glyph(x, y, b[0]);
    }

    pub fn write_char(&mut self, x: usize, y: usize, c: char) {
        self.write_char_color(x, y, c, DEFAULT_COLOR);
    }
}

