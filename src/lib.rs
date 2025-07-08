/// The lexer takes the source input, mapping it into a sequence of tokens.
pub mod lexer;

/// The parser takes a sequence of tokens, mapping it into an AST.
pub mod parser;

/// The type checker takes an untyped AST, checks the soundness of its types,
/// and maps it into a typed AST.
pub mod type_checker;

/// The code generator takes a typed AST and generates target machine code.
pub mod codegen {
    mod interface;
    pub use interface::{generate, Target};

    mod x86_64;
    mod x86_64_env;
}

pub mod ast;
pub mod token;
pub mod types;

pub mod util {
    pub mod fmt;
    pub mod intern;
    #[cfg(test)]
    pub(crate) mod test_utils;
}
