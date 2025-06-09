#[allow(non_camel_case_types)]
#[derive(Copy, Clone, PartialEq, Eq, clap::ValueEnum)]
#[clap(rename_all = "snake_case")]
pub enum Target {
    x86_64_darwin,
    x86_64_linux,
    #[clap(skip)]
    None,
}

impl std::fmt::Display for Target {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if *self == Target::None {
            f.write_str("none")
        } else {
            cool::codegen::Target::from(*self).fmt(f)
        }
    }
}

impl Target {
    pub const fn get_runtime_bytes(&self) -> &'static [u8] {
        match self {
            Target::x86_64_darwin => include_bytes!(env!("COOL_RT_x86_64_darwin")),
            Target::x86_64_linux => include_bytes!(env!("COOL_RT_x86_64_linux")),
            Target::None => panic!("invalid target none"),
        }
    }
}

impl From<Target> for cool::codegen::Target {
    fn from(value: Target) -> Self {
        match value {
            Target::x86_64_darwin => cool::codegen::Target::x86_64_darwin,
            Target::x86_64_linux => cool::codegen::Target::x86_64_linux,
            Target::None => panic!("can't convert target"),
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
