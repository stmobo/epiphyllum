ENTRY(_rust_start)

SECTIONS
{
    _kernel_base = 0xFFFFC40000000000;
    . = _kernel_base;

    .text : AT(ADDR(.text) - _kernel_base)
    {
        . = ALIGN(8);
        _kernel_start = .;
        _kernel_map_start = _kernel_start - _kernel_base;

        _code = .;
        KEEP(*(.text.start))
        *(.text.*)
        *(.rodata*)
        . = ALIGN(4096);
    }

   .data : AT(ADDR(.data) - _kernel_base)
   {
        _data = .;
        *(.data)
        . = ALIGN(4096);
   }

   .bss : AT(ADDR(.bss) - _kernel_base)
   {
       _bss = .;
       *(.bss)

       /*
        * You usually need to include generated COMMON symbols
        * under kernel BSS section or use gcc's -fno-common
        */

       *(COMMON)

        . = ALIGN(0x1000);
        _high_stack_end = .;
        . += 0x8000;
        _high_stack_start = .;

       . = ALIGN(4096);

       _kernel_end = .;
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