use std::{
    env,
    error::Error,
    fs,
    io::{self, Write},
};

use coolc::{
    lexer1::Lexer,
    token::{Token, TokenKind},
    util::BreakableIteratorExt,
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
    let mut error = false;
    let lexed: Vec<_> = Lexer::new(input)
        .up_to(Token::is_eof)
        .inspect(|t| {
            error |= matches!(t.kind, TokenKind::Error(_));
        })
        .collect();
    println!("{lexed:?}");
    println!("error?= {error}");
}
