// This is GPT generated, needs rework.
// If works for now, though.

use std::{
    fs,
    io::{self, Write},
    path::{Path, PathBuf},
    process::exit,
};

use pretty_assertions::assert_str_eq;

use cool::{
    parser,
    token::Spanned,
    util::fmt::{print_expr_string, print_program_string},
};

// Constants remain the same
const FIXTURE_DIR: &str = "src/fixtures/parser";
const CASE_SEPARATOR: &str =
    "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%";
const CASE_PREFIX: &str = "%% CASE ";
const OK_WITH_PREFIX: &str = "%% OK WITH:";
const ERROR_WITH_PREFIX: &str = "%% ERROR WITH:";

// Data structures remain the same
#[derive(Debug)]
enum CaseType {
    Program,
    Expression,
}

#[derive(Debug, PartialEq)]
enum ExpectedOutcome {
    Ok,
    Error,
}

#[derive(Debug)]
struct TestCase<'a> {
    fixture_path: PathBuf,
    name: &'a str,
    case_type: CaseType,
    input: &'a str,
    expected_outcome: ExpectedOutcome,
    expected_output: String,
}

fn main() {
    println!("Running Cool Parser Fixture Tests (using std lib only)...");
    println!("Looking for fixtures in: {}", FIXTURE_DIR);

    let mut fixture_files = Vec::new();
    let fixture_dir_path = PathBuf::from(FIXTURE_DIR);

    // Use std::fs for directory traversal
    match find_fixtures(&fixture_dir_path, &mut fixture_files) {
        Ok(_) => {
            if fixture_files.is_empty() {
                eprintln!(
                    "Warning: No fixture files (.txt) found in {}",
                    fixture_dir_path.display()
                );
                exit(0); // No tests to run
            }
            // Sort for consistent execution order (optional but good practice)
            fixture_files.sort();
            println!("Found {} fixture file(s).", fixture_files.len());
        }
        Err(e) => {
            eprintln!(
                "Error reading fixture directory {}: {}",
                fixture_dir_path.display(),
                e
            );
            exit(1);
        }
    }

    let mut total_cases = 0;
    let mut passed_cases = 0;
    let mut failed_cases = 0;

    // Store file contents to avoid re-reading; pass slices to parsing
    let mut fixture_contents = Vec::new();
    for path in &fixture_files {
        match fs::read_to_string(path) {
            Ok(content) => fixture_contents.push(content),
            Err(e) => {
                eprintln!("ERROR reading fixture file {}: {}", path.display(), e);
                failed_cases += 1; // Count as failure
            }
        }
    }

    // Iterate using indices to correlate paths and contents
    for (idx, fixture_path) in fixture_files.iter().enumerate() {
        // Skip if reading failed
        if idx >= fixture_contents.len() {
            continue;
        }
        let content = &fixture_contents[idx]; // Use stored content

        println!("---> Processing fixture: {}", fixture_path.display());
        match parse_fixture_file(content, fixture_path) {
            // Pass content slice
            Ok(cases) => {
                if cases.is_empty() {
                    println!("     (No test cases found in this file)");
                    continue;
                }
                total_cases += cases.len();
                for test_case in cases {
                    print!("     Running case: '{}'... ", test_case.name);
                    io::stdout().flush().unwrap();

                    // run_test_case now uses standard assert_eq!
                    let result = run_test_case(&test_case);

                    if result.is_ok() {
                        println!("PASS");
                        passed_cases += 1;
                    } else {
                        println!("FAIL");
                        failed_cases += 1;
                        // Error details printed by panic from assert_eq! or outcome check
                    }
                }
            }
            Err(err) => {
                eprintln!(
                    "     ERROR parsing fixture content from {}: {}",
                    fixture_path.display(),
                    err
                );
                failed_cases += 1;
            }
        }
    }

    println!("\n--- Test Summary ---");
    println!("Total Files Processed: {}", fixture_files.len());
    println!("Total Cases Found:     {}", total_cases);
    println!("Passed:                {}", passed_cases);
    println!("Failed:                {}", failed_cases);

    if failed_cases > 0 {
        exit(1); // Indicate failure
    } else {
        exit(0); // Indicate success
    }
}

/// Finds all .txt fixture files recursively using std::fs.
fn find_fixtures(dir: &Path, fixtures: &mut Vec<PathBuf>) -> io::Result<()> {
    if !dir.exists() {
        return Err(io::Error::new(
            io::ErrorKind::NotFound,
            format!("Fixture directory not found: {}", dir.display()),
        ));
    }
    if dir.is_dir() {
        for entry_result in fs::read_dir(dir)? {
            let entry = entry_result?;
            let path = entry.path();
            if path.is_dir() {
                // Recurse into subdirectories
                find_fixtures(&path, fixtures)?;
            } else if path.is_file() {
                // Check if it's a .txt file
                if path.extension().map_or(false, |ext| ext == "txt") {
                    fixtures.push(path);
                }
            }
        }
    }
    Ok(())
}

/// Parses a fixture file content string into test cases.
/// Takes content as &str to avoid re-reading.
fn parse_fixture_file<'a>(content: &'a str, path: &Path) -> Result<Vec<TestCase<'a>>, String> {
    let mut cases = Vec::new();
    for case_block in content.split(CASE_SEPARATOR) {
        let trimmed_block = case_block.trim();
        if trimmed_block.is_empty() {
            continue;
        }
        // Pass the block slice and path to parse_case
        cases.push(parse_case(trimmed_block, path)?);
    }
    Ok(cases)
}

/// Parses a single test case block string.
/// Takes block as &str.
fn parse_case<'a>(block: &'a str, path: &Path) -> Result<TestCase<'a>, String> {
    let mut lines = block.lines().map(str::trim);

    // 1. Parse Header
    let header = lines
        .next()
        .ok_or_else(|| "Case block is empty".to_string())?;
    if !header.starts_with(CASE_PREFIX) {
        return Err(format!(
            "Case block does not start with '{}': {}",
            CASE_PREFIX, header
        ));
    }
    let header_rest = header.strip_prefix(CASE_PREFIX).unwrap();
    let (name, type_str) = header_rest
        .split_once(" OF ")
        .ok_or_else(|| format!("Malformed CASE header (missing ' OF '): {}", header))?;
    let case_type = match type_str.trim_end_matches(':').trim() {
        // Trim type string
        "PROGRAM" => CaseType::Program,
        "EXPRESSION" => CaseType::Expression,
        other => {
            return Err(format!(
                "Unknown case type '{}' in header: {}",
                other, header
            ))
        }
    };

    // 2. Parse Input Code
    let mut outcome_line_idx: Option<usize> = None;
    // Iterate over original block lines to find split point
    for (idx, line) in block.lines().enumerate() {
        // Skip header line index
        if idx == 0 {
            continue;
        }
        let trimmed_line = line.trim();
        if trimmed_line.starts_with(OK_WITH_PREFIX) || trimmed_line.starts_with(ERROR_WITH_PREFIX) {
            outcome_line_idx = Some(idx);
            break;
        }
        // We don't actually need to collect input lines here, just find the split
    }

    let outcome_line_idx = outcome_line_idx.ok_or_else(|| {
        format!(
            "Missing '{}' or '{}' line for case '{}'",
            OK_WITH_PREFIX, ERROR_WITH_PREFIX, name
        )
    })?;

    // Find the byte index of the start of the outcome line to split the block
    let mut current_byte_idx = 0;
    let mut outcome_line_start_byte = 0;
    for (idx, line) in block.lines().enumerate() {
        if idx == outcome_line_idx {
            outcome_line_start_byte = current_byte_idx;
            break;
        }
        current_byte_idx += line.len() + 1; // +1 for newline
    }

    // Split block to get input and expected output parts
    let (input_part, rest_part) = block.split_at(outcome_line_start_byte);
    let input_str = input_part
        .strip_prefix(header)
        .unwrap() // Remove header again
        .trim(); // Trim whitespace around input code

    // Process the rest (outcome line + expected output)
    let mut rest_lines = rest_part.lines();
    let outcome_line = rest_lines.next().unwrap().trim(); // Already found it exists
    let expected_outcome = if outcome_line.starts_with(OK_WITH_PREFIX) {
        ExpectedOutcome::Ok
    } else {
        ExpectedOutcome::Error
    };

    let expected_output = rest_lines.collect::<Vec<_>>().join("\n").trim().to_string();

    Ok(TestCase {
        fixture_path: path.to_path_buf(),
        name,
        case_type,
        input: input_str, // Store the trimmed input code slice
        expected_outcome,
        expected_output,
    })
}

/// Runs a single test case using standard assert_eq!.
fn run_test_case(test_case: &TestCase) -> Result<(), ()> {
    let mut tokens = Vec::with_capacity(1024);
    let input_src = test_case.input;
    let actual_output;
    let mut parse_successful = false;

    // --- Parser Invocation (same as before) ---
    match test_case.case_type {
        CaseType::Program => match parser::parse_program(input_src, &mut tokens) {
            Ok(prog) => {
                parse_successful = true;
                actual_output = print_program_string(&prog).trim().to_string();
            }
            Err((_prog, errors)) => {
                actual_output = format_errors(input_src, &errors).trim().to_string();
            }
        },
        CaseType::Expression => match parser::parse_expr(input_src, &mut tokens) {
            Ok(expr) => {
                parse_successful = true;
                actual_output = print_expr_string(&expr).trim().to_string();
            }
            Err((_expr, errors)) => {
                actual_output = format_errors(input_src, &errors).trim().to_string();
            }
        },
    }
    // --- End Parser Invocation ---

    // --- Outcome Check (same as before) ---
    let outcome_matches = match test_case.expected_outcome {
        ExpectedOutcome::Ok => parse_successful,
        ExpectedOutcome::Error => !parse_successful,
    };

    if !outcome_matches {
        let expected_str = match test_case.expected_outcome {
            ExpectedOutcome::Ok => "Successful Parse",
            ExpectedOutcome::Error => "Parse Error(s)",
        };
        let actual_str = if parse_successful {
            "Successful Parse"
        } else {
            "Parse Error(s)"
        };
        panic!(
            "\n\nOutcome mismatch for case '{}' in {}:\nExpected Outcome: {}\nActual Outcome:   {}\n\nExpected Output:\n---\n{}\n---\nActual Output:\n---\n{}\n---\n",
            test_case.name,
            test_case.fixture_path.display(),
            expected_str,
            actual_str,
            test_case.expected_output,
            actual_output
        );
    }
    // --- End Outcome Check ---

    // Compare the actual formatted output using standard assert_eq!
    // The panic message includes expected and actual values for comparison.
    assert_str_eq!(
        actual_output,
        test_case.expected_output,
        "\n\nOutput mismatch for case '{}' in {}\n", // Basic context
        test_case.name,
        test_case.fixture_path.display(),
    );

    Ok(()) // Test passed
}

// Helper function to format errors (same as before)
fn format_errors(_: &str, errors: &[Spanned<parser::Error>]) -> String {
    let mut error_report = String::new();
    for error in errors {
        let span = error.span;
        let error_kind = &error.inner;

        error_report.push_str(&format!("Error ({}): {:?}\n", span, error_kind));
    }
    error_report
}
