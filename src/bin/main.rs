use std::{
    error::Error,
    io::{self, Write},
};

use coolc::{lexer::Lexer, token::Token, util::BreakableIteratorExt};

fn main() {
    if let Err(error) = run() {
        println!("failed to run: {error}");
    }
}

fn run() -> Result<(), Box<dyn Error>> {
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

        let lexed: Vec<_> = Lexer::new(&input).up_to(Token::is_eof).collect();
        println!("{lexed:?}");
    }
}
