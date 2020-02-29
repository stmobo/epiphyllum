.global multiboot_start
.global multiboot_header_start
.global early_pmode_exception
.global multiboot_struct_addr
.global rust_start

.global pml4
.global pdpt

.intel_syntax noprefix
.code32

.section .multiboot
.set MAGIC,      0xE85250D6
.set ARCH,       0
.set HEADER_LEN, 0x00000040
.set CHECKSUM,   -(MAGIC + ARCH + HEADER_LEN)

.set MB1_MAGIC,    0x1BADB002
.set MB1_FLAGS,    0x00000002
.set MB1_CHECKSUM, -(MB1_MAGIC + MB1_FLAGS)

.align 4
multiboot1_header_start:
.long MB1_MAGIC
.long MB1_FLAGS
.long MB1_CHECKSUM
.long 0xFFFFFFFF

.align 4
multiboot2_header_start:
.long MAGIC
.long ARCH
.long HEADER_LEN
.long CHECKSUM

.align 8

# Info request:
.word 1
.word 0
.long 24 # 8 header bytes + 4 u32 requests
.long 1  # Boot command line 
.long 3  # Kernel modules
.long 5  # BIOS boot device
.long 6  # Memory map

# Entry address
.align 8
.word 3
.word 0
.long 12
.long multiboot_start

# final tag
.align 8
.word 0
.word 0
.long 0
multiboot2_header_end:

.section .bootstrap_code

multiboot_start:
    lea esp, _stack_start
    lea ebp, _stack_start

    lgdt [pmode_gdt_desc]
    mov cx, 0x10
    
    mov ds, cx
    mov es, cx
    mov fs, cx 
    mov gs, cx
    mov ss, cx

    jmp 0x08:load_cs32

load_cs32:
    lidt [pmode_idt_desc]

    mov [multiboot_struct_addr], ebx

    lea esi, stage2_mb_load_success
    call pmode_print_str

setup_paging:
    # Set up PML4 with recursive map and address of PDPT
    lea edx, pml4
    or edx, 3
    mov [pml4+0xFF8], edx
    mov DWORD PTR [pml4+0xFFC], 0

    lea edx, pdpt
    or edx, 3
    mov [pml4], edx
    mov DWORD PTR [pml4+4], 0

    # Set up higher-half mapping.
    mov eax, 0x188
    lea ebx, pml4
    lea ecx, pdpt
    or ecx, 1
    mov [ebx + (eax * 8)], ecx
    mov DWORD PTR [ebx + (eax * 8) + 4], 0

    # Set up PDPT with address of PD
    lea edx, pd
    or edx, 3
    mov [pdpt], edx
    mov DWORD PTR [pdpt+4], 0

    # Set up PD with address of PTs
    mov ecx, 4
    lea edi, pd
    lea edx, pts
    or edx, 3

map_page_table_loop:
    mov [edi], edx
    mov DWORD PTR [edi+4], 0
    add edx, 0x1000
    add edi, 8
    loop map_page_table_loop

    # Set up identity map across PTs
    mov ecx, (4 * 512)
    mov eax, 3
    lea edi, pts

setup_paging_loop:
    mov [edi], eax
    mov DWORD PTR [edi+4], 0
    add eax, 0x1000
    add edi, 8
    loop setup_paging_loop

setup_long_mode:
    lea esi, stage2_init_paging
    call pmode_print_str

    # Enable PAE
    mov eax, cr4
    or eax, 0x20
    mov cr4, eax

    # Load CR3 with address of PML4T
    lea eax, pml4
    mov cr3, eax

    # Enable long mode flag in EFER
    mov ecx, 0xC0000080
    rdmsr
    or eax, 0x100
    wrmsr

    # Enable paging!
    mov eax, cr0
    or eax, 0x80000001
    mov cr0, eax

    lea esi, paging_success
    call pmode_print_str

    # Set up 64-bit code segment.
    mov BYTE PTR [code_seg_flags], 0b10101111

    # Reload CS.
    jmp 0x08:long_mode_entry

die:
    cli
spin32:
    hlt
    jmp spin32


# Print a zero-terminated ASCII string at [SI] to display.
# Clobbers EAX and EDI.
pmode_print_str:
    cld
    mov edi, [cur_display_offset_y]
    add edi, 0xB8000
    xor eax, eax
    mov ah, 0x0F
pmode_print_loop:
    lodsb al, BYTE PTR [esi]
    test al, al # exit if al = 0
    jz pmode_print_done
    stosw
    jmp pmode_print_loop
pmode_print_done:
    mov eax, [cur_display_offset_y]
    add eax, 160
    mov [cur_display_offset_y], eax
    ret

# Protected mode exception handler.
early_pmode_exception:
    lea esi, stage2_exception
    call pmode_print_str
    jmp die

stage2_load_success: .asciz "Loaded stage 2..."
stage2_mb_load_success: .asciz "Loaded stage 2 (multiboot)..."
stage2_init_paging: .asciz "Initializing paging..."
paging_success: .asciz "Paging enabled..."
stage2_exception: .asciz "Fatal error: unhandled protected mode exception"

cur_display_offset_y: .long 0
multiboot_struct_addr: .quad 0

.section .boot_page_tables
.align 0x1000
__page_tables_start:
pml4:
.skip 0x1000, 0
pdpt:
.skip 0x1000, 0
pd:
.skip 0x1000, 0
pts:
.skip (4 * 512 * 8), 0

.section .boot_gdt
pmode_gdt_desc:
    .word pmode_gdt_end - pmode_gdt - 1
    .word pmode_gdt

pmode_gdt:
    .quad 0

code_seg:
    .byte 0xFF
    .byte 0xFF

    .byte 0x00
    .byte 0x00

    # base 16:23
    .byte 0x00

    # access byte:
    .byte 0b10011010

code_seg_flags:
    # flags + limit 16:19
    .byte 0b11001111

    # base 24:31
    .byte 0x00

data_seg:
    .byte 0xFF
    .byte 0xFF

    .byte 0x00
    .byte 0x00

    # base 16:23
    .byte 0x00

    # access byte:
    .byte 0b10010010

    # flags + limit 16:19
    .byte 0b11001111

    # base 24:31
    .byte 0x00
pmode_gdt_end:

.section .boot_idt
pmode_idt_desc:
    .word pmode_idt_end - pmode_idt - 1
    .long pmode_idt

pmode_idt:
.rept 16
    .word early_pmode_exception
    .word 0x08
    .byte 0
    .byte 0x8F
    .word 0
.endr
pmode_idt_end: