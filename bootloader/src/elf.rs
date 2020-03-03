use core::ptr;

#[derive(Debug, Clone)]
#[repr(C)]
pub struct Elf64Ident {
    magic0: u8,
    magic1: u8,
    magic2: u8,
    magic3: u8,
    file_class: u8,
    data_encoding: u8,
    elf_version: u8,
    abi_ident: u8,
    abi_version: u8,
    padding: [u8; 6],
    n_ident: u8,
}

#[derive(Debug, Clone)]
#[repr(C)]
pub struct Elf64Header {
    ident: Elf64Ident,  /* Identification data */
    e_type: u16,        /* Object file type */
    machine_type: u16,  /* Machine type */
    version: u32,       /* Object file version */
    entry: u64,         /* Entry point address */
    ph_off: u64,        /* Program header table file offset */
    sh_off: u64,        /* Section header table file offset */
    flags: u32,         /* Processor-specific flags */
    header_sz: u16,     /* ELF header size */
    ph_ent_sz: u16,     /* Program header table entry size */
    ph_num: u16,        /* Number of program header table entries */
    sh_ent_sz: u16,     /* Section header table entry size */
    sh_num: u16,        /* Number of section header table entries */
    sh_str_ndx: u16,    /* Index for section name string table */
}

impl Elf64Header {
    pub fn is_valid(&self) -> bool {
        self.ident.magic0 == 0x7F && self.ident.magic1 == b'E' && self.ident.magic2 == b'L' && self.ident.magic3 == b'F'
    }

    pub fn entry_point(&self) -> usize {
        self.entry as usize
    }

    pub fn program_header_table(&self) -> &[Elf64Phdr] {
        let base_addr: usize = (self as *const Elf64Header) as usize;
        let ph_addr = base_addr + (self.ph_off as usize);

        unsafe {
            let ph_ptr = ph_addr as *const Elf64Phdr;
            &*ptr::slice_from_raw_parts(ph_ptr, self.ph_num as usize)
        }
    }
}

#[derive(Debug, Clone)]
#[repr(C)]
pub struct Elf64Phdr {
    pub p_type: u32,   /* Segment type */
    pub p_flags: u32,  /* Segment attributes */
    pub p_offset: u64, /* Offset in file */
    pub p_vaddr: u64,  /* Segment virtual address */
    pub p_paddr: u64,  /* Segment physical address */
    pub p_filesz: u64, /* Size of segment in file */
    pub p_memsz: u64,  /* Size of segment in memory */
    pub p_align: u64   /* Segment alignment constraint */
}
