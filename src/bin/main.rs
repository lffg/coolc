use std::{
    env,
    error::Error,
    fs,
    io::{self, Write},
};

use cool::{
    lexer::{lex, SUGGESTED_TOKENS_CAPACITY},
    token::TokenKind,
};

fn main() {
    if let Err(error) = run() {
        println!("failed to run: {error}");
    }
}

fn run() -> Result<(), Box<dyn Error>> {
    let mut args = env::args().skip(1);
    if let Some(prog) = args.next() {
        let input = fs::read_to_string(prog)?;
        pipeline(&input);
        return Ok(());
    }

    let mut input = String::new();
    loop {
        print!("> ");
        io::stdout().flush()?;

        input.clear();
        let n = io::stdin().read_line(&mut input)?;

        if n == 0 {
            println!("^D");
            return Ok(());
        }

        pipeline(&input);
    }
}

fn pipeline(input: &str) {
    let mut has_errors = false;
    let mut tokens = Vec::with_capacity(SUGGESTED_TOKENS_CAPACITY);

    lex(input, &mut tokens);

    println!("{tokens:?}");
    for token in tokens {
        if let TokenKind::Error(error) = token.kind {
            println!("error: {error:?} at {}", token.span());
            has_errors = true;
        }
    }
    println!("error?= {has_errors}");
}
