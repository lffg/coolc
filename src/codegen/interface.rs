use std::io;

use crate::{
    ast::{Program, Typed},
    codegen::{x86_64::Generator, x86_64_env},
    util::intern::Interner,
};

pub fn generate<W>(
    writer: W,
    ident_interner: &Interner<str>,
    target: Target,
    program: &Program<Typed>,
) where
    W: io::Write,
{
    type DarwinGenerator<'a, W> = Generator<'a, W, x86_64_env::Darwin>;
    type LinuxGenerator<'a, W> = Generator<'a, W, x86_64_env::Linux>;

    match target {
        Target::x86_64_darwin => DarwinGenerator::new(writer, ident_interner).generate(program),
        Target::x86_64_linux => LinuxGenerator::new(writer, ident_interner).generate(program),
    }
}

#[allow(non_camel_case_types)]
#[derive(Copy, Clone, PartialEq, Eq)]
pub enum Target {
    x86_64_darwin,
    x86_64_linux,
}

impl Target {
    pub const ALL: &[Target] = &[Target::x86_64_darwin, Target::x86_64_linux];

    pub const fn triple(&self) -> &'static str {
        match self {
            Target::x86_64_darwin => "x86_64-apple-darwin",
            Target::x86_64_linux => "x86_64-unknown-linux-gnu",
        }
    }
}

impl std::fmt::Display for Target {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Target::x86_64_darwin => f.write_str("x86_64_darwin"),
            Target::x86_64_linux => f.write_str("x86_64_linux"),
        }
    }
}
