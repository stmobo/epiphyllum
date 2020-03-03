use crate::paging;
use core::mem;
use core::slice;
use cstr_core::CStr;

#[derive(Debug, Clone, Copy)]
#[repr(C)]
pub struct MultibootInfo {
    flags: u32,
    mem_lower: u32,
    mem_upper: u32,

    boot_device: u32,

    cmdline_addr: u32,

    mods_count: u32,
    mods_addr: u32,

    elf_shdr_num: u32,
    elf_shdr_size: u32,
    elf_shdr_addr: u32,
    elf_shdr_shndx: u32,

    mmap_length: u32,
    mmap_addr: u32,

    drives_length: u32,
    drives_addr: u32,
    config_table: u32,
    boot_loader_name: u32,

    apm_table_addr: u32,

    vbe_control_info: u32,
    vbe_mode_info: u32,
    vbe_mode: u16,
    vbe_interface_seg: u16,
    vbe_interface_off: u16,
    vbe_interface_len: u16,

    framebuffer_addr: u64,
    framebuffer_pitch: u32,
    framebuffer_width: u32,
    framebuffer_height: u32,
    framebuffer_bpp: u8,
    framebuffer_type: u8,
    color_info: [u8; 5],
}

fn expand_to_ptr<T>(addr: u32) -> *const T {
    paging::physical_address(addr as usize).unwrap()
}

impl MultibootInfo {
    pub fn flag(&self, flag_no: u64) -> bool {
        if flag_no >= 32 {
            false
        } else {
            (self.flags & (1 << flag_no)) > 0
        }
    }

    pub fn get_command_line(&self) -> Option<&'static str> {
        if !self.flag(2) {
            return None;
        }

        unsafe {
            let slice = CStr::from_ptr(expand_to_ptr(self.cmdline_addr));
            slice.to_str().ok()
        }
    }

    pub fn get_modules(&self) -> Option<&'static [ModuleInfo]> {
        if !self.flag(3) {
            return None;
        }


        let ct = self.mods_count as usize;
        let ptr: *const ModuleInfo = expand_to_ptr(self.mods_addr);
        
        unsafe {
            Some(slice::from_raw_parts(ptr, ct))
        }
    }

    pub fn get_memory_info(&self) -> Option<MemoryInfoIter> {
        if !self.flag(6) {
            return None;
        }

        Some(MemoryInfoIter {
            buf_end: expand_to_ptr(self.mmap_addr + self.mmap_length),
            ptr: expand_to_ptr(self.mmap_addr),
        })
    }
}

#[derive(Debug, Clone, Copy)]
#[repr(C)]
pub struct ModuleInfo {
    pub mod_start: u32,
    pub mod_end: u32,
    string: u32,
    reserved: u32,
}

impl ModuleInfo {
    pub fn get_string(&self) -> Option<&'static str> {
        if self.string == 0 {
            None
        } else {
            unsafe {
                let slice = CStr::from_ptr(expand_to_ptr(self.string));
                slice.to_str().ok()
            }
        }
    }
}

#[derive(Debug, Clone, Copy)]
#[repr(C)]
pub struct MemoryInfo {
    pub base_addr: u64,
    pub length: u64,
    pub mem_type: MemoryType,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u32)]
#[non_exhaustive]
pub enum MemoryType {
    Available = 1,
    ACPI = 3,
    MustPreserve = 4,
    Defective = 5,
    NonExhaustive = 99,
}

pub struct MemoryInfoIter {
    buf_end: *const MemoryInfo,
    ptr: *const MemoryInfo,
}

impl Iterator for MemoryInfoIter {
    type Item = MemoryInfo;

    fn next(&mut self) -> Option<Self::Item> {
        unsafe {
            let cur_ptr: usize = mem::transmute(self.ptr);
            if self.ptr >= self.buf_end {
                return None;
            }

            let sz_ptr: *const u32 = mem::transmute(self.ptr);
            let sz = (*sz_ptr) as usize;

            self.ptr = mem::transmute(cur_ptr + sz + 4);
            let item_ptr: *const MemoryInfo = mem::transmute(cur_ptr + 4);

            Some(*item_ptr)
        }
    }
}
