use coolc::{
    lexer1, lexer2,
    token::{Token, TokenKind},
    util::BreakableIteratorExt,
};
use criterion::{criterion_group, criterion_main, Criterion};
use std::hint::black_box;

static INPUT: &str = include_str!("../examples/big.cool");

fn lexer_eager(input: &str) {
    let tokens = lexer2::lex(input);
    let mut i = 0;
    for token in tokens {
        if matches!(token.kind, TokenKind::Error(_)) {
            continue;
        }
        i += 1;
    }
    black_box(i);
}

fn lexer_incremental(input: &str) {
    let mut i = 0;
    for token in lexer1::Lexer::new(input).up_to(Token::is_eof) {
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
    c.bench_function("eager", |b| b.iter(|| lexer_eager(black_box(INPUT))));
    c.bench_function("incremental", |b| {
        b.iter(|| lexer_incremental(black_box(INPUT)))
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
