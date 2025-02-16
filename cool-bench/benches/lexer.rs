use cool::{
    lexer,
    token::{Token, TokenKind},
    util::BreakableIteratorExt,
};
use criterion::{criterion_group, criterion_main, Criterion};
use std::hint::black_box;

static INPUT: &str = include_str!("../../examples/big.cool");

fn lexer(input: &str) {
    let mut i = 0;
    for token in lexer::Lexer::new(input).up_to(Token::is_eof) {
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
    c.bench_function("lexer", |b| {
        b.iter(|| {
            black_box(lexer(black_box(INPUT)));
        })
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
