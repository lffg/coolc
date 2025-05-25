use cool::{lexer::SUGGESTED_TOKENS_CAPACITY, parser::parse_program, token::Token};
use criterion::{criterion_group, criterion_main, Criterion};
use std::hint::black_box;

static INPUT: &str = include_str!("../../examples/big.cool");

fn parser(input: &str, tokens: &mut Vec<Token>) {
    let program = parse_program(input, tokens).unwrap();
    _ = black_box(program);
}

fn criterion_benchmark(c: &mut Criterion) {
    let mut tokens = Vec::with_capacity(SUGGESTED_TOKENS_CAPACITY * 2);

    c.bench_function("parser", |b| {
        b.iter(|| {
            tokens.clear();
            black_box(parser(black_box(INPUT), &mut tokens));
        })
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
