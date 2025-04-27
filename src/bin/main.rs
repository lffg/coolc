use std::{
    env,
    error::Error,
    fs,
    io::{self, Write},
};

use cool::lexer::{lex, SUGGESTED_TOKENS_CAPACITY};

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
    let mut errored = false;
    let mut tokens = Vec::with_capacity(SUGGESTED_TOKENS_CAPACITY);

    lex(input, &mut tokens);

    for token in tokens {
        println!("{:?} @ {}", token.kind, token.span());
        if token.kind.is_error() {
            errored = true;
        }
    }
    println!("\nerror?= {errored}");
}
