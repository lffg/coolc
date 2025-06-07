.intel_syntax

hello_world: .ascii "Hello, world!\n"

.text
.global _main
_main:
    push    rbp
    mov     rbp, rsp

    mov     rax, 32

    pop     rbp
    ret

.end
