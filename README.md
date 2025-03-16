# Cool Compiler

Luiz Felipe Gonçalves.

This repository contains an implementation for a compiler of the Cool
programming language, as described by [The Cool Reference Manual][ref].

As the authors of this implementation, we retain the liberty to make minor
changes upon explicitly stating and justifying them. As of now — having
currently only implemented the lexical analyzer — _no changes_ were made.

[ref]: https://theory.stanford.edu/~aiken/software/cool/cool-manual.pdf

## Building, Executing, and Testing

This work is implemented using the Rust programming language. Even though the
language offers several benefits compared to Java or to C++ (other suggestions
for this assignment), it was chosen only due to the authors' personal
preferences.

The version `1.85` of the Rust compiler and toolchain was used during
development. Before building, make sure the environment is properly configured
with the appropriate `rustc` and `cargo` versions. These can be installed using
[rustup].

[rustup]: https://rustup.rs/

The code can be built and executed using `cargo`.

To build, use:

```sh
cargo build
```

And to run, use:

```sh
cargo run -q -- ./path/to/source-file.cool
```

The `-q` option is used to suppress `cargo` output. The `--` tells `cargo` to
separate its own arguments from the ones that will be forwarded to the compiled
binary. If no source file path is provided to the compiler, it will read from
the standard input.

The project's test suite can be run using:

```sh
cargo test
```

# Implementation Remarks

## Lexical Analysis

The lexical analyzer (henceforth and by this project's source code referred to
as “lexer”) is implemented in a handwritten fashion rather than by using lexical
generators such as Flex or JLex. Even though the Rust ecosystem also offers
similar tools — such as [Logos] —, we decided to manually implement it for
learning purposes.

Not only that, a custom implementation also allows for better optimizations and
a better integration with the parser, if needed. While these kind of
optimization weren't explored by this implementation, some of them are described
by articles such as the excellent [Beating the Fastest Lexer Generator in
Rust][lex-opt-ref].

[Logos]: https://github.com/maciejhirsz/logos
[lex-opt-ref]: https://alic.dev/blog/fast-lexing

### Design and Code Structure

There are two common approaches for the design of lexical analyzers:
“incremental” or “on-demand” lexing, and “batch” lexing.

The first kind, on-demand lexer, consists of a [generator]-like routine that
incrementally produces tokens as needed. When the compilation pipeline uses an
incremental scanner, [control] starts at the parser which _pulls_ one token at a
time from the lexer and keeps going from and to the lexer until the input is
exhausted.

On the other hand, when the pipeline is assembled using a “batch” scanner,
control starts at the lexer, which scans the entire input and builds a buffer
with all the tokens at once, which are then handed to the parser for
consumption. In this case, the parser doesn't even know the existence of the
scanner, as it already has all the tokens.

The main cost of the latter approach is the allocation overhead. Hence, if a
large enough buffer (e.g. to handle the average source file size) is provided,
it can become more competitive than the former design. In fact, the batch one
may be even superior in modern computer architectures due to the fact that all
tokens are stored in a contiguous buffer, thus making a more efficient use of
caches.

The [lexer-bench] branch contains both implementations and a suite for
(micro)benchmarking them.

The batch scanning approach was used due to its simpler design.
Performance-wise, both were pretty much comparable, even though the batch has
more potential when we consider future optimization possibilities.

### Optimization Opportunities

#### Token Representation

The `Token` type is represented as:

```rs
struct Token {
    pub kind: TokenKind,
    lo: usize,
    len: u32,
}

enum TokenType {
    Class,
    Else,
    If,
    Fi,
    // ... all other (“trivial”) token kinds

    Identifier(String),
    Number(i64),
    // ... other “composite” token kinds
}
```

In this current design, which prioritizes simplicity, the size of a `Token`
object is 48 bytes! That's _bad_ and certainly hinders any meaningful proper
CPU-cache leverage as mentioned above.

The main type to blame for such a large size is `TokenKind`, which must have
enough capacity to hold its largest variant (which in this case is any one
containing a `String`). Even though the largest variant occupies 24 bytes, an
extra byte is required to serve as the tag to discriminate them. However, due to
the 8-byte alignment of this type, 8 more bytes are used.

With the 32 bytes of `TokenType`, the 8 from the `usize` and 4 from the `u32`
(which also grows to 8 due to padding to account for the 8-byte alignment), we
reach the (tremendous) 48-byte size.

This layout can be _extensively_ optimized by using [data-oriented design][dod]
techniques. A simple optimization would be to _not_ carry payloads inside the
`TokenKind` enum and defer the actual "parsing" of the payload of each token to
the parser. This is possible since the token already carries out span
information (currently _only_ for error reporting purposes), which can _also_ be
used to fetch the original substring from the source text to be used to parse
the payload in the parsing phase.

By also restricting the maximum size of the source text to 2^32 (~4 billion)
bytes and the maximum token size to 2^16 (65,536) bytes we can also further
optimize the `Token` space by using the following layout:

```rs
struct Token {
    pub kind: TokenKind,
    lo: u32,
    len: u16
}
```

Assuming that `TokenKind` is a trivial enum (without “payload” in any of its
variant), its size can be reduced to a single byte. In this 4-byte aligned
`Token` type, we can reach 8 bytes per token!

Even though this optimization would allow more tokens to fit in a single cache
line, directly embedding the token's parsed payloads inside the `TokenKind`
simplifies the code, which is the reason this current implementation uses the
previously mentioned (less efficient) layout.

#### SIMD

As described in the aforementioned post on lexer optimizations, we could also
leverage SIMD instructions to massively optimize the lexer phase.

[generator]: https://en.wikipedia.org/wiki/Generator_(computer_programming)
[control]: https://en.wikipedia.org/wiki/Control_flow
[lexer-bench]: https://github.com/lffg/coolc/pull/1
[dod]: https://en.wikipedia.org/wiki/Data-oriented_design

### Testing

In order to verify that this lexer implementation indeed conforms to Cool's
lexical structures, when developing the parser, carefully-constructed excerpts
of code were written to intentionally test the lexer against cases that may
reveal mis-implementations.

We also used the artifact of the first assignment (stack machine) to test
whether it successfully passes the scanning phase without errors—which it does.

Two other approaches that _could_ have been used are fuzzing and deterministic
simulation testing. The former would systematically try to crash the scanner by
providing all kinds of crazy inputs—which are expected to be gracefully handled
by this implementation. The latter, a more sophisticated approach, consists of a
program which deterministically constructs excerpts of valid code (using
predefined rules) which must then be correctly lexed by the scanner. Even though
such approaches would increase the confidence of a correct implementation, they
weren't used for practical reasons—they demand a lot of time to implement.
