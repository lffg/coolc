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
make test
```

This runs all Cargo tests (usual Rust-style tests) and the custom test harness
developed for this compiler, which is in the `scripts/tester` directory.

# Implementation Remarks

## Type checker

Basically runs through the AST in a top-down fashion to register types, scopes,
etc. Then bottom-up to propagate types from inner expressions to outer
expressions.

Different passes are required:

1. Collect all class definitions and their parent classes
2. Build the full inheritance, which forms a DAG
3. Collect all method definitions (to construct the "method environment")
4. Type check expressions and build the typed AST

The "typed AST" is a simple generalization of the AST constructed for the parser
assignment. A typed AST is essentially an AST, but every node which contained a
`TypeIdent` now contains a fully-resolved `Type`. To do this, every AST node is
now parameterized over a generic type `T`. For the untyped AST, `T` is
`TypeIdent`; for the typed AST, `T` is `Type`.

A `Type` is essentially an unique type identifier (the corresponding [interned]
identifier's handle), its parent `Type` and the `Span` for the type definition.
More information (such as the size of the type) could be added later when code
generation is implemented.

[interned]: https://en.wikipedia.org/wiki/String_interning

## Parser

Following the lexical analyzer's design, this compiler's Parser is also
implemented in a handwritten style by means of Recursive Descent and Pratt's
techniques. One should note that Rust's ecosystem also offer great options for
generating the parser, such as the excellent's [LALRPOP]. Another more
extensible approach, usually employed by text editors, is to use [tree-sitter]
with FFI.

[LALRPOP]: https://github.com/lalrpop/lalrpop
[tree-sitter]: https://tree-sitter.github.io/tree-sitter/

### Parser Implementation

The parser implementation can be divided into two: high-level constructs parsing
and expression parsing. These require different techniques to balance code
simplicity and maintainability.

To parse “high-level” language constructs, such as the program itself, classes,
features — methods or attributes —, we use a simple [recursive
descent][rec-desc] approach. It's simple and enough for these cases. No major
transformations were required from the grammar provided in the language
reference.

Expression parsing, however, requires a more intricate technique to avoid a deep
grammar transformation—which would also incur in a more verbose parser
implementation due to the need of manually encoding each “precedence” level as a
separate recursive procedure. This complexity is mostly derived from the fact
that the usual infix notation used for expressions contain implicit rules of
precedence and associativity. The Pratt Parsing approach is a simple extension
to the recursive descent model which by means of a precedence/associativity
table can elegantly parse expressions.

Alex Kladov's (A.K.A. matklad)'s excellent “[Simple but Powerful Pratt
Parsing][pratt-ref]” article was used to guide the initial implementation of
this parser's Pratt Parsing-style expression subsystem.

[rec-desc]: https://en.wikipedia.org/wiki/Recursive_descent_parser
[pratt-ref]:
  https://matklad.github.io/2020/04/13/simple-but-powerful-pratt-parsing.html

### AST Structure

AST nodes can be eloquently described by means of Rust's `enum`s and `struct`s
constructs due to their ability to encode sum types, which can perfectly model
inductive data structures, such as a programming language's AST. The [Expression
Problem][expr-probl] tradeoff should be remarked, however.

[expr-probl]: https://en.wikipedia.org/wiki/Expression_problem

In addition to the AST, we also provide a “pretty printer” implementation to
concisely format an AST value. This is a critical component of the Parser's
custom testing infrastructure.

### Error Handling

The parser is designed to be decently resilient by being able to report multiple
errors rather than halting upon encountering the first parsing issue.

When a syntax error occurs, it attempts to perform error recovery by means of
“synchronizing”, as described in Robert Nystrom's [Crafting
Interpreters][cr-int]. When an error is encountering, the parser enters in a
synchronization mode in which it discards tokens until it reaches a
synchronization point, where it can likely resume parsing correctly. As a
result, the parser returns both a (potentially partial) AST and a list
(`Vec<Spanned<Error>>`) of all syntax errors detected during the parse.

The requested recovery cases are tested in the `requested-recovery-cases.txt`
fixture.

[cr-int]: https://craftinginterpreters.com/

### Testing

In order to verify that this parser implementation indeed conforms to Cool's
syntactical structures, when developing the parser, carefully-constructed
excerpts of code were written to intentionally test the parser against cases
that may reveal mis-implementations.

Parser-related tests can be found at the `src/fixtures/parser` directory.
Individual fixtures are encoded in a specially crated DSL which is parsed and
executed by a custom test harness, implemented in `scripts/tester`. To speed up
the process, this harness implementation was mostly generated by GPT.

Each fixture can declare one or more test cases. Each test case contains a
program's source (which can be an entire program definition, or a single
expression) and the expected AST. The harness then parses the program and
compares the ASTs for equality, yielding an error in the case of a mismatch.

We also used the artifact of the first assignment (stack machine) to test
whether it successfully passes the parsing phase without errors—which it does.

Like previously mentioned for the lexer implementation, two other approaches
that _could_ have been used are fuzzing and deterministic simulation testing.
These were not implemented, though.

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
lexical structures, when developing the lexer, carefully-constructed excerpts of
code were written to intentionally test the lexer against cases that may reveal
mis-implementations.

Most of the lexer-related tests can be found at end of the `src/lexer.rs` file.
A `cases!` [declarative macro] was introduced to streamline the definition of
each test case.

[declarative macro]: https://doc.rust-lang.org/reference/macros-by-example.html

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
