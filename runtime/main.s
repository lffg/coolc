.intel_syntax noprefix
.section .note.GNU-stack,"",@progbits

.section .rodata
hello_world:   .ascii "Hello, world!\n"
hello_world_len: .quad . - hello_world

.section .text
.global main
main:
    push       rbp
    mov        rbp, rsp

    mov        rax, 1 # write
    mov        rdi, 0 # fd 0 - stdout
    lea        rsi, [rip + hello_world]
    mov        rdx, [rip + hello_world_len]
    syscall

    # Exit status (the return value of the main function).
    mov        rax, 0

    pop        rbp
    ret

.end
