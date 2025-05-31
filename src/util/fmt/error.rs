#![allow(clippy::items_after_statements)]

use crate::{
    parser,
    token::{Spanned, TokenKind},
    type_checker,
    util::fmt::Show,
};

impl Show for Spanned<type_checker::Error> {
    fn show(&self, f: &mut std::fmt::Formatter<'_>, ctx: &super::Context<'_>) -> std::fmt::Result {
        let i = ctx.ident_interner;
        let Spanned { span, inner: error } = self;

        if f.alternate() {
            write!(f, "{span}: ")?;
        }

        use type_checker::Error::*;
        match error {
            DuplicateTypeDefinition {
                name,
                other_definition_span,
            } => {
                let name = i.get(name);
                write!(f, "class {name} already defined at {other_definition_span}")
            }
            DuplicateMethodInClass {
                other_definition_span,
            } => {
                write!(
                    f,
                    "method with same name already defined at {other_definition_span}"
                )
            }
            DuplicateAttributeInClass {
                other_definition_span,
            } => {
                write!(
                    f,
                    "attribute with same name already defined at {other_definition_span}"
                )
            }
            UndefinedType(name) => {
                let name = i.get(name);
                write!(f, "class {name} is not defined")
            }
            UndefinedName(name) => {
                let name = i.get(name);
                write!(f, "{name} is not defined")
            }
            Unassignable { dst, src } => {
                let dst = i.get(dst);
                let src = i.get(src);
                write!(f, "type {src} is not assignable to type {dst}")
            }
            Mismatch { actual, expected } => {
                let actual = i.get(actual);
                let expected = i.get(expected);
                write!(f, "expected type {expected}, but got {actual}")
            }
            IllegalSelfType => write!(f, "illegal use of SELF_TYPE"),
            MaximumNumberOfParametersExceeded { current } => {
                write!(
                    f,
                    "maximum number of parameters exceeded (current is {current})"
                )
            }
            OverriddenWithIncorrectNumberOfParameters { actual, expected } => {
                write!(
                    f,
                    "overriding method of originally {expected} parameters, \
                    but new definition has {actual}"
                )
            }
            OverriddenWithIncorrectParameterTypes { actual, expected } => {
                let actual = i.get(actual);
                let expected = i.get(expected);
                write!(
                    f,
                    "overriding method with incorrect parameter type: \
                    expected type {expected}, but got {actual}"
                )
            }
            OverriddenWithIncorrectReturnType { actual, expected } => {
                let actual = i.get(actual);
                let expected = i.get(expected);
                write!(
                    f,
                    "overriding method with incorrect return type: \
                    expected type {expected}, but got {actual}"
                )
            }
            IncorrectNumberOfArguments { actual, expected } => write!(
                f,
                "incorrect number of arguments. expected {expected}, but got {actual}"
            ),
            UndefinedMethod { class, method } => {
                let method = i.get(method);
                let class = i.get(class);
                write!(f, "undefined method {method} on class {class}")
            }
        }
    }
}

impl Show for Spanned<parser::Error> {
    fn show(&self, f: &mut std::fmt::Formatter<'_>, _: &super::Context<'_>) -> std::fmt::Result {
        let Spanned { span, inner: error } = self;

        if f.alternate() {
            write!(f, "{span}: ")?;
        }

        use parser::Error::*;
        match error {
            InvalidAssignmentTarget => write!(f, "invalid assignment target"),
            InvalidDispatch => write!(f, "invalid dispatch"),
            UnexpectedTokenInExpr { token } => {
                write!(f, "unexpected token {token:?} in expression")
            }
            Unexpected { actual, expected } => {
                write!(f, "expected token {expected:?}, but got {actual:?}")
            }
            UnexpectedAny { actual, expected } => {
                write!(f, "expected one of {expected:?}, but got {actual:?}")
            }
            UnexpectedOperator { actual } => write!(f, "unexpected operator {actual:?}"),
            EmptyProgram => write!(f, "empty program"),
            EmptyBlockBody => write!(f, "empty block or sequence"),
            EmptyCase => write!(f, "empty case"),
            MissingLetBinding => write!(f, "let without binding"),
            ParseInt => write!(f, "parse int error, out of bounds"),
            Lexer(TokenKind::ErrorUnexpectedChar) => write!(f, "unexpected character"),
            Lexer(TokenKind::ErrorUnclosedComment) => write!(f, "unclosed comment"),
            Lexer(TokenKind::ErrorUnclosedString) => write!(f, "unclosed string"),
            Lexer(TokenKind::ErrorUnescapedLineBreak) => write!(f, "unescaped line break"),
            Lexer(_) => unreachable!("not error token"),
        }
    }
}
