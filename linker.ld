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

    _kernel_start = 0xFFC0000000000000;
    . += _kernel_start;

    .text : AT(ADDR(.text) - _kernel_start)
    {
        . = ALIGN(8);

        _code = .;
        KEEP(*(.text.start))
        *(.text.*)
        *(.rodata*)
        . = ALIGN(4096);
    }

   .data : AT(ADDR(.data) - _kernel_start)
   {
        _data = .;
        *(.data)
        . = ALIGN(4096);
   }

   .eh_frame : AT(ADDR(.eh_frame) - _kernel_start)
   {
       _ehframe = .;
       *(.eh_frame)
        . = ALIGN(4096);
   }

   .bss : AT(ADDR(.bss) - _kernel_start)
   {
       _bss = .;
       *(.bss)

       /*
        * You usually need to include generated COMMON symbols
        * under kernel BSS section or use gcc's -fno-common
        */

       *(COMMON)
       . = ALIGN(4096);
   }

   _kernel_end = .;

   /DISCARD/ :
   {
        *(.comment)
        *(.dynamic)
   }
}