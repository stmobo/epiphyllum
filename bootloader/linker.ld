ENTRY(multiboot_start)

SECTIONS
{
    __early_pmode_exc_low = early_pmode_exception & 0xFFFF;
    __early_pmode_exc_hi = (early_pmode_exception >> 16) & 0xFFFF;

    . = 0x500;

    .boot :
    {
        . = ALIGN(8);
        KEEP(*(.multiboot))

        *(.boot_gdt)
        *(.boot_idt)
        *(.boot_page_tables)

        _stack_end = .;
        . += 0x4000;
        _stack_start = .;

        *(.bootstrap_code)
    }

    .text : 
    {
        . = ALIGN(8);

        _code = .;
        KEEP(*(.text.start))
        *(.text)
        *(.text.*)
        *(.rodata*)
    }

   .data :
   {
        _data = .;
        *(.data)
   }

   .bss :
   {
       _bss = .;
       *(.bss)
       *(COMMON)
   }

   /DISCARD/ :
   {
        *(.comment*)
        *(.eh_frame*)
        *(.gcc_except_table*)
        *(.note*)
        *(.rel.eh_frame*)
   }
}