.intel_syntax noprefix
.section .note.GNU-stack,"",@progbits

# `Animal`, the interface
#     `emit_noise`, the method
#
# Two classes
#     `Dog`, which implements `emit_noise` as:
#         "wof!"
#     `Duck`, which implements `emit_noise` as:
#         "quack!"
#
# `print_noise`, a function which takes an object and calls its corresponding
#   `emit_noise` function.

.section .rodata

initial_print_fmt: .asciz "Starting.\n"
print_noise_fmt:   .asciz "Emitting noise [%s].\n"

Dog_noise:   .asciz "wof!"
Duck_noise:  .asciz "quack!"



# data
# relocation
# read-only
.section .data.rel.ro

Dog_vtable:
    .quad Dog_emit_noise

Duck_vtable:
    .quad Duck_emit_noise



.section .text

Dog_emit_noise:
    lea         rax, [rip + Dog_noise]
    ret


Duck_emit_noise:
    lea         rax, [rip + Duck_noise]
    ret


# rdi: vtable
print_noise:
    push        rbp
    mov         rbp, rsp

    call        [rdi]

    lea         rdi, [rip + print_noise_fmt]
    mov         rsi, rax
    call        printf

    pop         rbp
    ret


.global main
main:
    push        rbp
    mov         rbp, rsp

    lea         rdi, [rip + initial_print_fmt]
    call        printf

    lea         rdi, [rip + Dog_vtable]
    call        print_noise

    lea         rdi, [rip + Duck_vtable]
    call        print_noise

    mov         rax, 0

    pop         rbp
    ret
