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
        Target::none => unreachable!("must be handled during args validation"),
    }
}

#[allow(non_camel_case_types)]
#[derive(Copy, Clone, PartialEq, Eq, clap::ValueEnum)]
#[clap(rename_all = "snake_case")]
pub enum Target {
    x86_64_darwin,
    x86_64_linux,
    #[clap(skip)]
    none,
}

impl std::fmt::Display for Target {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Target::x86_64_darwin => f.write_str("x86_64_darwin"),
            Target::x86_64_linux => f.write_str("x86_64_linux"),
            Target::none => f.write_str("none"),
        }
    }
}

cfg_if::cfg_if! {
    if #[cfg(all(target_arch = "x86_64", target_os = "macos"))] {
        pub const DEFAULT_TARGET: Target = Target::x86_64_darwin;
    } else if #[cfg(all(target_arch = "x86_64", target_os = "linux"))] {
        pub const DEFAULT_TARGET: Target = Target::x86_64_linux;
    } else {
        pub const DEFAULT_TARGET: Target = Target::none;
    }
}
