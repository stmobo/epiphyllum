.global long_mode_entry
.global rust_start
.global multiboot_struct_addr

.intel_syntax noprefix
.code64

.section .bootstrap_code

long_mode_entry:
    lea rsp, _stack_start
    lea rbp, _stack_start

.att_syntax
    movabsq $rust_start, %rax
.intel_syntax noprefix
    push rax

    # Clear registers.
    # Probably unnecessary, but good practice I guess?
    xor rax, rax
    mov rbx, rax
    mov rcx, rax
    mov rdx, rax
    mov rsi, rax
    mov r8, rax
    mov r9, rax
    mov r10, rax
    mov r11, rax
    mov r12, rax
    mov r13, rax
    mov r14, rax
    mov r15, rax

    # Load the multiboot struct address into first parameter register
    mov rdi, [multiboot_struct_addr]
    
    # go to rust_start
    ret
    
die:
    cli
spin64:
    hlt
    jmp spin64
