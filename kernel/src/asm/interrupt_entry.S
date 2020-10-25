.global external_isr_start
.global exceptions_start
.global kernel_entry

.code64

.macro SAVE_REGISTERS
    push %rbp    /* RSP+512+112 */
    mov %rsp, %rbp

    push %rax    /* RSP+512+104 */
    push %rbx    /* RSP+512+96 */
    push %rcx    /* RSP+512+88 */
    push %rdx    /* RSP+512+80 */
    push %rsi    /* RSP+512+72 */
    push %rdi    /* RSP+512+64 */
    push %r8     /* RSP+512+56 */
    push %r9     /* RSP+512+48 */
    push %r10    /* RSP+512+40 */
    push %r11    /* RSP+512+32 */
    push %r12    /* RSP+512+24 */
    push %r13    /* RSP+512+16 */
    push %r14    /* RSP+512+8 */
    push %r15    /* RSP+512 */

    sub $512, %rsp
    fxsave64 (%rsp)
.endm

.macro LOAD_REGISTERS
    fxrstor64 (%rsp)
    add $512, %rsp

    pop %r15
    pop %r14
    pop %r13
    pop %r12
    pop %r11
    pop %r10
    pop %r9
    pop %r8
    pop %rdi
    pop %rsi
    pop %rdx
    pop %rcx
    pop %rbx
    pop %rax
    pop %rbp
.endm

enter_kernel:
    /* The following is pushed onto the stack:
     *    SS            (RSP + 168)
     *    RSP           (RSP + 160)
     *    RFLAGS        (RSP + 152)
     *    CS            (RSP + 144)
     *    RIP           (RSP + 136)
     *    Error Code    (RSP + 128) (if applicable; otherwise padding)
     *    Interrupt #   (RSP + 120)
     *    ... GPRs ...  (RSP + 0 to RSP + 112)
     */
    SAVE_REGISTERS

    mov %rsp, %rdi

    movabs $kernel_entry, %rax
    call *%rax

    LOAD_REGISTERS

    add $16, %rsp
    iretq


.align 16
exceptions_start:
intr_no=0
.rept 8
    pushq $0
    pushq $intr_no
    jmp enter_kernel
    .align 16
    intr_no=intr_no+1
.endr

/* exception 8 (double fault) */
pushq $intr_no
jmp enter_kernel

.align 16
intr_no=intr_no+1

/* exception 9 */
pushq $0
pushq $intr_no
jmp enter_kernel

.align 16
intr_no=intr_no+1

/* Exceptions 10 - 14  */
.rept 5
    pushq $intr_no
    jmp enter_kernel
    .align 16
    intr_no=intr_no+1
.endr

/* Exceptions 15-16 */
.rept 2
    pushq $0
    pushq $intr_no
    jmp enter_kernel
    .align 16
    intr_no=intr_no+1
.endr

/* exception 17 */
pushq $intr_no
jmp enter_kernel

.align 16
intr_no=intr_no+1

/* Exceptions 18-29 */
.rept 12
    pushq $0
    pushq $intr_no
    jmp enter_kernel
    .align 16
    intr_no=intr_no+1
.endr

/* Exception 30 */
pushq $intr_no
jmp enter_kernel

.align 16
intr_no=intr_no+1

/* Exception 31 */
pushq $0
pushq $intr_no
jmp enter_kernel
intr_no=intr_no+1
exceptions_end:


.align 16
external_isr_start:
intr_no=32
.rept 224
    sub $8, %rsp
    pushq $intr_no
    jmp enter_kernel
    .align 16
    intr_no=intr_no+1
.endr
external_isr_end:

