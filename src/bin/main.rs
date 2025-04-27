use std::{
    env,
    error::Error,
    fs,
    io::{self, Write},
};

use cool::{parser::Parser, util::fmt::print_program};

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
    let mut buf = Vec::with_capacity(8 * 1024);

    let parser = Parser::new(input, &mut buf);
    let prog = parser.parse().unwrap();

    print_program(&mut io::stdout(), &prog).unwrap();
}
