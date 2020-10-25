.global do_context_switch
.global finalize_context_switch
.global initialize_task

.code64

/*
 * rdi = address to store outgoing task RSP to
 * rsi = address to load incoming task RSP from
 * rdx = address of outgoing task structure
 * rcx = address of incoming task structure
 * (we pass these separately, because the offset of the RSP field within the task
 * structure is not fixed)
 */
do_context_switch:
    /* Callee-saved registers: */
    push %rbp
    push %rbx
    push %r12
    push %r13
    push %r14
    push %r15

    /* Switch stacks / processes: */
    mov %rsp, (%rdi)
    mov (%rsi), %rsp

    /* call finalize_context_switch(prev, next) */
    mov %rdx, %rdi
    mov %rcx, %rsi

    pop %r15
    pop %r14
    pop %r13
    pop %r12
    pop %rbx
    pop %rbp

    jmp finalize_context_switch

    /* Should not get here-- finalize_context_switch returns directly to the
     * caller of this function.
     */

/* Newly-spawned Tasks context switch into this address. */
initialize_task:
    mov %rbx, %rdi
    mov %r12, %rsi
    mov %r13, %rdx
    mov %r14, %rcx

    push %r15
    ret
