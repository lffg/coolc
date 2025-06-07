use std::{
    fmt::{self, Write},
    format_args as f,
};

use crate::{ast::Program, types::Type};

#[cfg(test)]
mod tests;

const DEFAULT_CODE_CAPACITY: usize = 4 * 1024; // 4 KiB

pub struct CodeGen {
    code: String,
}

impl CodeGen {
    pub fn with_capacity() -> CodeGen {
        CodeGen {
            code: String::with_capacity(DEFAULT_CODE_CAPACITY),
        }
    }

    pub fn gen(mut self, program: &Program<Type>) -> String {
        self.gen_program(program);

        self.code
    }

    fn gen_program(&mut self, _program: &Program<Type>) {
        self.emit(f!("\
            .intel_syntax

            .text
            .global _main
            _main:
                push    rbp
                mov     rbp, rsp
                mov     dword ptr [rbp - 4], 0
                xor     eax, eax
                pop     rbp
                ret

            .end
        "));
    }
}

// Utility functions.
impl CodeGen {
    fn emit(&mut self, f: fmt::Arguments<'_>) {
        self.code
            .write_fmt(f)
            .expect("code emit should be infallible");
    }
}
