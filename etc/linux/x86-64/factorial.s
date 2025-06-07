.intel_syntax noprefix
.section .note.GNU-stack,"",@progbits

.section .rodata
out_fmt: .asciz "%d! = %d\n"

.section .text

# factorial(0) = 1
# factorial(1) = 1
# factorial(n) = n * factorial (n - 1)
#
# rdi: n
# rax: return
.factorial:
    push    rbp
    mov     rbp, rsp

    cmp     rdi, 1
    jg      .factorial_gt1

    mov     rax, 1
    jmp     .factorial_end

.factorial_gt1:
    sub     rsp, 16         # Keep the stack 16-byte-aligned
    mov     [rsp + 8], rdi  # `push rdi`

    sub     rdi, 1
    call    .factorial

    mov    rdi, [rsp + 8]   # `pop rdi`
    add    rsp, 16

    #       rax    = rax * rdi
    #       result = factorial(n - 1) * n
    imul    rax, rdi

.factorial_end:
    pop     rbp
    ret


.global main
main:
    push    rbp
    mov     rbp, rsp

    mov     rdi, 0

.main_loop:
    cmp     rdi, 10
    jg      .main_end

    # Instead of saving on the stack, I could also have used some preserved
    # register here, such as `r12`. However, in that case, I'd also have to
    # preserve `r12` before using it, since this very `main` function is being
    # called by the C runtime!
    push    rdi
    sub     rsp, 8  # Align stack

    call    .factorial

    lea     rdi, [rip + out_fmt]
    mov     rsi, [rsp + 8]
    mov     rdx, rax
    call    printf

    add     rsp, 8
    pop     rdi

    inc rdi
    jmp .main_loop

.main_end:
    mov     rax, 0

    pop     rbp
    ret
