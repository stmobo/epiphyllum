.global long_mode_entry
.global cur_display_offset_y
.intel_syntax noprefix
.code64

.section .bootstrap_code

long_mode_entry:
    lea rsp, _stack_start
    lea rsi, long_mode_success
    call lmode_print_str

die:
    cli
spin64:
    hlt
    jmp spin64

lmode_print_str:
    xor rdi, rdi
    xor rax, rax
    cld

    mov edi, [cur_display_offset_y]
    add edi, 0xB8000
    mov ah, 0x0F
.lmode_print_loop:
    lodsb al, BYTE PTR [esi]
    test al, al # exit if al = 0
    jz .lmode_print_done
    stosw
    jmp .lmode_print_loop
.lmode_print_done:
    mov eax, [cur_display_offset_y]
    add eax, 160
    mov [cur_display_offset_y], eax
    ret

long_mode_success: .asciz "Long mode enabled!"