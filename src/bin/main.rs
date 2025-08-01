use std::{
    env,
    error::Error,
    fs,
    io::{self, Write},
};

use cool::{
    parser,
    token::{Spanned, Token},
    type_checker,
    util::{
        self,
        fmt::{Show, tree::print_program},
        intern::Interner,
    },
};

fn main() {
    if let Err(error) = run() {
        eprintln!("Error: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), Box<dyn Error>> {
    let mut args = env::args().skip(1);
    let mut tokens_buf = Vec::with_capacity(8 * 1024);
    let mut ident_interner = Interner::with_capacity(1024);

    // File mode
    if let Some(prog_path) = args.next() {
        let input = fs::read_to_string(prog_path)?;
        pipeline(&input, &mut tokens_buf, &mut ident_interner);
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
                pipeline(&accumulated_input, &mut tokens_buf, &mut ident_interner);
            }
            return Ok(());
        }

        // Empty line is another termination signal
        if current_line.trim().is_empty() {
            if !accumulated_input.trim().is_empty() {
                pipeline(&accumulated_input, &mut tokens_buf, &mut ident_interner);
                accumulated_input.clear(); // Clear for next input
            }
        } else {
            accumulated_input.push_str(&current_line);
        }
    }
}

fn pipeline(src: &str, tokens: &mut Vec<Token>, ident_interner: &mut Interner<str>) {
    tokens.clear();

    let prog = match parser::parse_program(src, tokens, ident_interner) {
        Ok(prog) => prog,
        Err((prog, errors)) => {
            eprintln!("Got {} errors", errors.len());
            eprintln!();
            eprintln!("Partial AST:");
            print_program(&mut io::stdout(), ident_interner, &prog).unwrap();
            eprintln!();
            for error in errors {
                report_error(src, &error, ident_interner);
            }
            return;
        }
    };

    println!("=== Untyped AST ===");
    print_program(&mut io::stdout(), ident_interner, &prog).unwrap();

    let checker =
        type_checker::Checker::with_capacity(ident_interner, 512, type_checker::flags::DEFAULT);
    let (typed_prog, _registry) = match checker.check(prog) {
        Ok(prog) => prog,
        Err((_prog, _registry, errors)) => {
            eprintln!("Got {} type errors", errors.len());
            for error in errors {
                report_error(src, &error, ident_interner);
            }
            return;
        }
    };

    println!();
    println!("=== Typed AST ===");
    print_program(&mut io::stdout(), ident_interner, &typed_prog).unwrap();
}

fn report_error<T>(src: &str, error: &Spanned<T>, ident_interner: &Interner<str>)
where
    Spanned<T>: Show,
{
    let span = error.span;

    // Try to find line number and column
    let mut line = 1;
    let mut line_start = 0;
    let mut column = 0;

    // Calculate the start position (line and column)
    for (i, char) in src.char_indices() {
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
    if span.lo as usize >= src.len() && !src.is_empty() {
        column = src.len() - line_start + 1;
    } else if src.is_empty() {
        column = 1;
    }

    let ctx = util::fmt::Context { ident_interner };
    let error_display = error.display(&ctx);
    eprintln!("Error (line {line}, col {column}): {error_display}");

    if let Some(line_content) = src.lines().nth(line - 1) {
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
