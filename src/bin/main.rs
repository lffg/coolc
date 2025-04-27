use std::{
    env,
    error::Error,
    fs,
    io::{self, Write},
};

// Make sure these imports are correct based on your lib.rs structure
use cool::{
    parser::{self, Parser},
    token::Spanned,
    util::fmt::print_program,
};

fn main() {
    if let Err(error) = run() {
        eprintln!("Error: {error}"); // Use eprintln for errors
        std::process::exit(1);
    }
}

fn run() -> Result<(), Box<dyn Error>> {
    let mut args = env::args().skip(1);

    // File mode
    if let Some(prog_path) = args.next() {
        let input = fs::read_to_string(prog_path)?;
        pipeline(&input);
        return Ok(());
    }

    // Interactive REPL mode
    println!("Welcome to interactive coolc.");
    println!("Enter code, finish with empty line, or send Ctrl+D to exit.");

    let mut accumulated_input = String::new();

    loop {
        if accumulated_input.is_empty() {
            print!("> ");
        } else {
            print!("| ");
        }
        io::stdout().flush()?;

        let mut current_line = String::new();
        let n = io::stdin().read_line(&mut current_line)?;

        if n == 0 {
            println!();
            if accumulated_input.trim().is_empty() {
                println!("^D");
            } else {
                pipeline(&accumulated_input);
            }
            return Ok(());
        }

        // Empty line is another termination signal
        if current_line.trim().is_empty() {
            if !accumulated_input.trim().is_empty() {
                pipeline(&accumulated_input);
                accumulated_input.clear(); // Clear for next input
            }
        } else {
            accumulated_input.push_str(&current_line);
        }
    }
}

fn pipeline(input: &str) {
    let mut buf = Vec::with_capacity(8 * 1024);
    let parser = Parser::new(input, &mut buf);

    match parser.parse() {
        Ok(prog) => {
            print_program(&mut io::stdout(), &prog).unwrap();
        }
        Err(error) => {
            report_error(input, &error);
        }
    }
}

// Helper function to report errors with context
fn report_error(source: &str, error: &Spanned<parser::Error>) {
    let span = error.span;
    let error = error.inner;

    // Try to find line number and column
    let mut line = 1;
    let mut line_start = 0;
    let mut column = 0;

    // Calculate the start position (line and column)
    for (i, char) in source.char_indices() {
        if i >= span.lo as usize {
            column = i - line_start + 1;
            break;
        }
        if char == '\n' {
            line += 1;
            line_start = i + 1;
        }
    }
    // If span.lo is beyond the source length (e.g., EOF span at end)
    if span.lo as usize >= source.len() && !source.is_empty() {
        column = source.len() - line_start + 1;
    } else if source.is_empty() {
        column = 1;
    }

    eprintln!("Error (line {line}, col {column}): {error:?}");

    if let Some(line_content) = source.lines().nth(line - 1) {
        eprintln!("{line:>4} | {line_content}");
        // Add an indicator '^' under the approximate error location
        let indicator_padding = column.saturating_sub(1);
        let indicator_len = std::cmp::max(1, (span.hi - span.lo) as usize);
        eprintln!(
            "{:>4} | {}{}",
            "",
            " ".repeat(indicator_padding),
            "^".repeat(indicator_len)
        );
    }
}
