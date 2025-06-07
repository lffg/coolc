# In this example we try to emulate ./etc/linux/rust/rust-vtable.rs.
#
# DEFINITIONS
# ===========
#
# trait Add:
#     add(&self, a: i64, b: i64) -> i64;
#
# struct WithTerm(i64):
#     impl Add:
#         add(&self, a: i64, b: i64) -> i64:
#             self.0 + (a + b)
#
# struct WithFactorAndTerm(i64, i64):
#     impl Add:
#         add(&self, a: i64, b: i64) -> i64:
#             self.0 * (a + b) + self.1
#
# run(adder: &dyn Add, a: i64, b: i64) -> i64:
#     adder.add(a, b)
#
# main() -> i64:
#     t = WithTerm(13)            # alloc on the stack
#     f = WithFactorAndTerm(3, 15)   # alloc on the stack
#
#     res = run(&t, 2, 4)
#     printf(res)
#
#     res = run(&f, 2, 4)
#     printf(res)
#
#
# LAYOUT OF OBJECTS
# =================
#
# [vtable_ptr: usize, [... fields]]

.intel_syntax noprefix
.section .note.GNU-stack,"",@progbits

.extern printf

.section .rodata
.out_fmt:      .asciz "got: %ld\n"

.section .text
# rdi: pointer to object, rsi: i64, rdx: i64
.WithTerm__impl__Add_add:
    push    rbp
    mov     rbp, rsp
    # rdi + 0: vtable
    # rdi + 8: first field (term)
    # self.0 + (a + b)
    mov     rax, [rdi + 8]  # term
    add     rax, rsi
    add     rax, rdx

    pop     rbp
    ret

.section .data.rel.ro
.WithTerm_vtable:
    .quad .WithTerm__impl__Add_add


.section .text
# rdi: pointer to object, rsi: i64, rdx: i64
.WithFactorAndTerm__impl__Add_add:
    push    rbp
    mov     rbp, rsp
    # rdi + 0: vtable
    # rdi + 8: first field (factor)
    # rdi + 16: second field (term)
    # self.0 * (a + b) + self.1
    mov     rax, [rdi + 8]  # factor
    add     rsi, rdx
    imul    rax, rsi
    mov     rdx, [rdi + 16]
    add     rax, rdx

    pop     rbp
    ret

.section .data.rel.ro
.WithFactorAndTerm_vtable:
    .quad .WithFactorAndTerm__impl__Add_add


.section .text

# rdi: pointer to object, rsi: i64, rdx: i64
.run:
    push    rbp
    mov     rbp, rsp

    mov     r8, [rdi + 0]       # load vtable
    call    qword ptr [r8 + 0]

    pop     rbp
    ret


.global main
main:
    push    rbp
    mov     rbp, rsp

    # Allocate object1, WithTerm
    sub     rsp, 16
    lea     r8, [rip + .WithTerm_vtable]
    mov               [rsp + 0], r8   # store vtable
    mov     qword ptr [rsp + 8], 13   # term is 13
    mov     r8, rsp                   # object1 is in r8

    # Allocate object2, WithFactorAndTerm
    sub    rsp, 24
    lea    r9, [rip + .WithFactorAndTerm_vtable]
    mov              [rsp + 0], r9    # store vtable
    mov    qword ptr [rsp + 8], 3     # factor is 3
    mov    qword ptr [rsp + 16], 15   # term is 15
    mov    r9, rsp

    # Must preserve r9 since we'll call another function before using it.
    # This is also handy since it 16-aligns the stack (24 of previous object
    # + 8 for this register).
    push   r9

    # Call with object1 (WithTerm)
    mov     rdi, r8
    mov     rsi, 2
    mov     rdx, 4
    call    .run

    lea     rdi, [rip + .out_fmt]
    mov     rsi, rax
    call    printf

    # Call with object2 (WithFactorAndTerm)
    mov     rdi, [rsp]      # [rsp] = r9
    mov     rsi, 2
    mov     rdx, 4
    call    .run

    lea     rdi, [rip + .out_fmt]
    mov     rsi, rax
    call    printf

    mov     rax, 0

    add     rsp, 8 # deallocate r9
    add     rsp, 24 # deallocate object2
    add     rsp, 16 # deallocate object1

    pop     rbp
    ret
