use crate::{
    ast, parser,
    token::Spanned,
    type_checker::Checker,
    util::{
        self,
        fmt::{tree, Show},
        intern::Interner,
    },
};

pub fn format_errors<E>(i: &Interner<str>, e: &[Spanned<E>]) -> Vec<String>
where
    Spanned<E>: Show,
{
    let ctx = util::fmt::Context { ident_interner: i };
    e.iter().map(|e| format!("{:#}", e.display(&ctx))).collect()
}

#[track_caller]
pub fn assert_errors<E>(i: &Interner<str>, actual: &[Spanned<E>], expected: &[&str])
where
    Spanned<E>: Show,
{
    let errors = format_errors(i, actual);
    assert_eq!(errors, expected);
}

/// Each variant contains the input.
pub enum Test {
    ParserProgram(&'static str),
    ParserExpr(&'static str),
    CheckerProgram(&'static str),
    CheckerExpr(&'static str),
}

pub enum Assertion {
    TreeOk(&'static str),
    TreeError(&'static str),
    ExpectedErrors(&'static [&'static str]),
}

#[track_caller]
pub fn run_pipeline(test: Test) -> (String, Vec<String>) {
    let tokens_buf = &mut Vec::with_capacity(1024);
    let interner = &mut Interner::with_capacity(128);

    match test {
        Test::ParserProgram(input) => {
            let (prog, errors) = match parser::parse_program(input, tokens_buf, interner) {
                Ok(prog) => (prog, vec![]),
                Err((prog, errors)) => (prog, errors),
            };
            let tree = tree::print_program_string(&interner, &prog);
            let errors = format_errors(interner, &errors);
            (tree, errors)
        }
        Test::ParserExpr(input) => {
            let (expr, errors) = match parser::parse_expr(input, tokens_buf, interner) {
                Ok(expr) => (expr, vec![]),
                Err((expr, errors)) => (expr, errors),
            };
            let tree = tree::print_expr_string(&interner, &expr);
            let errors = format_errors(interner, &errors);
            (tree, errors)
        }
        Test::CheckerProgram(input) => {
            let (prog, errors) = match parser::parse_program(input, tokens_buf, interner) {
                Ok(prog) => (prog, vec![]),
                Err((prog, errors)) => (prog, errors),
            };
            let mut fmt_errors = format_errors(interner, &errors);

            let checker = Checker::with_capacity(interner, 128);
            let (prog, errors) = match checker.check(prog) {
                Ok((prog, _reg)) => (prog, vec![]),
                Err((prog, _reg, errors)) => (prog, errors),
            };
            let tree = tree::print_program_string(&interner, &prog);
            fmt_errors.extend(format_errors(&interner, &errors));

            (tree, fmt_errors)
        }
        Test::CheckerExpr(input) => {
            let (expr, errors) = match parser::parse_expr(input, tokens_buf, interner) {
                Ok(expr) => (expr, vec![]),
                Err((expr, errors)) => (expr, errors),
            };
            let prog = ast::test_utils::from_expr_to_main_program(expr);
            let mut fmt_errors = format_errors(interner, &errors);

            let checker = Checker::with_capacity(interner, 128);
            let (prog, errors) = match checker.check(prog) {
                Ok((prog, _reg)) => (prog, vec![]),
                Err((prog, _reg, errors)) => (prog, errors),
            };
            let expr = ast::test_utils::from_main_program_to_expr(prog);
            let tree = tree::print_expr_string(&interner, &expr);
            fmt_errors.extend(format_errors(&interner, &errors));

            (tree, fmt_errors)
        }
    }
}

#[track_caller]
pub fn run_assertion(
    assertion: Assertion,
    formatted_actual_tree: &str,
    formatted_actual_errors: &[String],
) {
    match assertion {
        Assertion::TreeOk(expected_tree) => {
            let expected_errors: &[&str] = &[];
            ::pretty_assertions::assert_eq!(formatted_actual_errors, expected_errors);
            ::pretty_assertions::assert_eq!(formatted_actual_tree.trim(), expected_tree.trim());
        }
        Assertion::TreeError(expected_tree) => {
            ::pretty_assertions::assert_eq!(formatted_actual_tree.trim(), expected_tree.trim())
        }
        Assertion::ExpectedErrors(expected_errors) => {
            ::pretty_assertions::assert_eq!(formatted_actual_errors, expected_errors)
        }
    }
}

macro_rules! tree_tests {
    (
        use $test_kind:ident;

        $(
            fn $test_name:ident() {
                let $source_kind:ident = $source:expr;
                $($assertions_tt:tt)*
            }
        )*
    ) => {
        $(
            #[test]
            fn $test_name() {
                let test: crate::util::test_utils::Test =
                    tree_tests!(@@get_test($test_kind, $source_kind), $source);
                let (formatted_actual_tree, formatted_actual_errors) =
                    crate::util::test_utils::run_pipeline(test);
                let ctx = (&formatted_actual_tree, &formatted_actual_errors);
                tree_tests!(@@expand_assertions, ctx, [$($assertions_tt)*]);
            }
        )*
    };

    (@@expand_assertions, $ctx:expr, []) => {};
    (@@expand_assertions, $ctx:expr, [
        let $assertion:ident = $assertion_expected:expr;
        $($rest_assertions_tt:tt)*
    ]) => {
        crate::util::test_utils::run_assertion(
            tree_tests!(@@assertion, $assertion, $assertion_expected),
            $ctx.0,
            $ctx.1,
        );
        tree_tests!(@@expand_assertions, $ctx, [$($rest_assertions_tt)*]);
    };

    (@@assertion, tree_ok, $expected:expr) => {
        crate::util::test_utils::Assertion::TreeOk(::indoc::indoc! { $expected })
    };
    (@@assertion, tree_error, $expected:expr) => {
        crate::util::test_utils::Assertion::TreeError(::indoc::indoc! { $expected })
    };
    (@@assertion, expected_errors, $expected:expr) => {
        crate::util::test_utils::Assertion::ExpectedErrors($expected)
    };

    (@@get_test(parser, program), $source:expr) => {
        crate::util::test_utils::Test::ParserProgram($source)
    };
    (@@get_test(parser, expr), $source:expr) => {
        crate::util::test_utils::Test::ParserExpr($source)
    };
    (@@get_test(checker, program), $source:expr) => {
        crate::util::test_utils::Test::CheckerProgram($source)
    };
    (@@get_test(checker, expr), $source:expr) => {
        crate::util::test_utils::Test::CheckerExpr($source)
    };
}
pub(crate) use tree_tests;
