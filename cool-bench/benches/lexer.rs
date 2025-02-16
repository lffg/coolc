use cool::{
    lexer::{lex, SUGGESTED_TOKENS_CAPACITY},
    token::{Token, TokenKind},
};
use criterion::{criterion_group, criterion_main, Criterion};
use std::hint::black_box;

static INPUT: &str = include_str!("../../examples/big.cool");

fn lexer(input: &str, tokens: &mut Vec<Token>) {
    lex(input, tokens);
    let mut i = 0;
    for token in tokens {
        if matches!(token.kind, TokenKind::Error(_)) {
            continue;
        }
        if matches!(token.kind, TokenKind::Eof) {
            break;
        }
        i += 1;
    }
    black_box(i);
}

fn criterion_benchmark(c: &mut Criterion) {
    let mut tokens = Vec::with_capacity(SUGGESTED_TOKENS_CAPACITY * 2);

    c.bench_function("lexer", |b| {
        b.iter(|| {
            tokens.clear();
            black_box(lexer(black_box(INPUT), &mut tokens));
        })
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
