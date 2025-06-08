use crate::{
    ast::{
        BinaryOperator, Binding, CaseArm, Class, DispatchQualifier, Expr, ExprKind, Feature,
        Formal, Ident, Method, Program, TypeName, UnaryOperator, Untyped,
    },
    lexer::{self, extract},
    token::{Span, Spanned, Token, TokenKind},
    types::{builtins, well_known},
    util::intern::Interner,
};

type Result<T, E = ()> = std::result::Result<T, E>;

pub type ParseResult<T> = Result<T, (T, Vec<Spanned<Error>>)>;

pub fn parse_program(
    src: &str,
    tokens: &mut Vec<Token>,
    ident_interner: &mut Interner<str>,
) -> ParseResult<Program<Untyped>> {
    parse(
        src,
        tokens,
        ident_interner,
        Parser::parse_program,
        Program::default,
    )
}

pub fn parse_expr(
    src: &str,
    tokens: &mut Vec<Token>,
    ident_interner: &mut Interner<str>,
) -> ParseResult<Expr<Untyped>> {
    let default = || Expr::dummy(Span::new_of_length(u32::try_from(src.len()).unwrap(), 0));
    parse(src, tokens, ident_interner, Parser::parse_expr, default)
}

fn parse<'src, 'tok, 'ident, T>(
    src: &'src str,
    tokens: &'tok mut Vec<Token>,
    ident_interner: &'ident mut Interner<str>,
    f: impl for<'a> FnOnce(&'a mut Parser<'src, 'tok, 'ident>) -> Result<T>,
    default: impl FnOnce() -> T,
) -> ParseResult<T> {
    assert!(tokens.is_empty());

    if ident_interner.is_empty() {
        // Register builtin and well-known names
        for builtin in builtins::ALL {
            let handle = ident_interner.intern(builtin.name);
            assert_eq!(handle, builtin.id);
        }
        for &(expected_handle, name) in well_known::ALL {
            let handle = ident_interner.intern(name);
            assert_eq!(handle, expected_handle);
        }
    }

    // Lex and parse
    lexer::lex(src, tokens);
    let mut p = Parser::new(src, tokens, ident_interner);
    let parse_result = f(&mut p);

    // Error handling
    let success = parse_result.is_ok();
    let el = parse_result.unwrap_or_else(|()| default());
    if p.errors.is_empty() {
        assert!(success);
        Ok(el)
    } else {
        Err((el, p.errors))
    }
}

struct Parser<'src, 'tok, 'ident> {
    src: &'src str,
    tokens: &'tok mut Vec<Token>,
    ident_interner: &'ident mut Interner<str>,
    cursor: usize,
    errors: Vec<Spanned<Error>>,
}

impl Parser<'_, '_, '_> {
    fn parse_program(&mut self) -> Result<Program<Untyped>> {
        let mut classes = Vec::with_capacity(4);
        while self.except([]) {
            if let Ok(parsed) = self.synchronize(&[], &[TokenKind::Class], Parser::parse_class) {
                classes.push(parsed);
            }
        }
        self.consume(TokenKind::Eof)?;
        if classes.is_empty() && self.errors.is_empty() {
            let s = Span::new_of_length(0, u32::try_from(self.src.len()).unwrap());
            self.error(s.wrap(Error::EmptyProgram));
            Err(())
        } else {
            Ok(Program { classes })
        }
    }

    fn parse_class(&mut self) -> Result<Class<Untyped>> {
        self.consume(TokenKind::Class)?;
        let name = self.parse_type()?;

        let inherits = if self.take(TokenKind::Inherits) {
            let inherited = self.parse_type()?;
            Some(inherited)
        } else {
            None
        };

        self.consume(TokenKind::LBrace)?;
        let features = self.parse_list(TokenKind::RBrace, TokenKind::Semicolon, None, |p| {
            p.parse_feature()
        })?;
        self.consume(TokenKind::RBrace)?;
        self.consume(TokenKind::Semicolon)?;

        Ok(Class {
            name,
            inherits,
            features,
        })
    }

    fn parse_feature(&mut self) -> Result<Feature<Untyped>> {
        let name = self.parse_ident()?;

        match self
            .consume_any(&[TokenKind::Colon, TokenKind::LParen])?
            .kind
        {
            TokenKind::Colon => {
                let ty = self.parse_type()?;
                let initializer = self.parse_initializer()?;
                Ok(Feature::Attribute(Binding {
                    name,
                    ty,
                    initializer,
                }))
            }
            TokenKind::LParen => {
                let formals = self.parse_list(TokenKind::RParen, TokenKind::Comma, None, |p| {
                    p.parse_formal()
                })?;
                self.consume(TokenKind::RParen)?;
                self.consume(TokenKind::Colon)?;
                let return_ty = self.parse_type()?;
                self.consume(TokenKind::LBrace)?;
                let body = self.parse_expr()?;
                self.consume(TokenKind::RBrace)?;
                Ok(Feature::Method(Method {
                    name,
                    formals,
                    return_ty,
                    body,
                }))
            }
            _ => unreachable!(),
        }
    }

    fn parse_formal(&mut self) -> Result<Formal<Untyped>> {
        let name = self.parse_ident()?;
        self.consume(TokenKind::Colon)?;
        let ty = self.parse_type()?;
        Ok(Formal { name, ty })
    }

    fn parse_initializer(&mut self) -> Result<Option<Expr<Untyped>>> {
        if !self.take(TokenKind::Assign) {
            return Ok(None);
        }
        let expr = self.parse_expr()?;
        Ok(Some(expr))
    }

    fn parse_type(&mut self) -> Result<TypeName> {
        self.parse_ident().map(TypeName)
    }

    fn parse_ident(&mut self) -> Result<Ident> {
        let token = self.consume(TokenKind::Identifier)?;
        Ok(Ident {
            name: self.ident_interner.intern(extract::ident(token, self.src)),
            span: token.span(),
        })
    }

    fn parse_expr(&mut self) -> Result<Expr<Untyped>> {
        self.parse_expr_bp(0)
    }

    fn parse_expr_bp(&mut self, min_bp: u8) -> Result<Expr<Untyped>> {
        let lhs_token = self.advance();
        let mut lhs = self.parse_nud(lhs_token)?;

        loop {
            let op_token = self.peek();

            if let Some((lbp, rbp)) = Self::infix_binding_power(op_token.kind) {
                if lbp < min_bp {
                    // Operator binds less tightly than the minimum required
                    break;
                }

                self.advance(); // Operator
                lhs = self.parse_led(op_token, lhs, rbp)?;
            } else {
                // Not an infix operator or binds too loosely
                break;
            }
        }

        Ok(lhs)
    }

    /// nud: Parses tokens that start an expression
    /// (prefix operators, literals, grouping)
    fn parse_nud(&mut self, token: Token) -> Result<Expr<Untyped>> {
        let (kind, span) = match token.kind {
            TokenKind::Identifier => {
                let ident = Ident {
                    name: self.ident_interner.intern(extract::ident(token, self.src)),
                    span: token.span(),
                };
                (ExprKind::Id(ident, ()), token.span())
            }
            TokenKind::Number => {
                let Ok(parsed) = extract::int(token, self.src) else {
                    self.error(token.span().wrap(Error::ParseInt));
                    return Err(());
                };
                (ExprKind::Int(parsed), token.span())
            }
            TokenKind::String => (
                ExprKind::String(extract::string(token, self.src)),
                token.span(),
            ),
            TokenKind::EscapedString => (
                ExprKind::String(extract::escaped_string(token, self.src)),
                token.span(),
            ),
            TokenKind::True => (ExprKind::Bool(true), token.span()),
            TokenKind::False => (ExprKind::Bool(false), token.span()),

            // Grouping: ( expr )
            TokenKind::LParen => {
                let expr = self.parse_expr()?;
                let end = self.consume(TokenKind::RParen)?;
                (ExprKind::Paren(Box::new(expr)), token.span().to(end.span()))
            }

            // Block: { expr; expr; ... }
            TokenKind::LBrace => {
                let body = self.parse_list(
                    TokenKind::RBrace,
                    TokenKind::Semicolon,
                    Some(Error::EmptyBlockBody),
                    Parser::parse_expr,
                )?;
                let end = self.consume(TokenKind::RBrace)?;
                let span = token.span().to(end.span());
                if body.is_empty() {
                    self.error(span.wrap(Error::EmptyBlockBody));
                    return Err(());
                }
                (ExprKind::Block { body }, span)
            }

            // New: new ty
            TokenKind::New => {
                let ty = self.parse_type()?;
                let new = ExprKind::New { ty };
                let span = token.span().to(ty.span());
                (new, span)
            }

            // Prefix operators: ~, not, isvoid, new
            kind @ (TokenKind::Tilde | TokenKind::Not | TokenKind::IsVoid) => {
                let op = match kind {
                    TokenKind::Tilde => UnaryOperator::Inverse,
                    TokenKind::Not => UnaryOperator::Not,
                    TokenKind::IsVoid => UnaryOperator::IsVoid,
                    _ => unreachable!(),
                };
                // SAFETY: Should have prefix due to above match
                let ((), rbp) = Self::prefix_binding_power(kind).unwrap();

                let expr = self.parse_expr_bp(rbp)?;

                let span = token.span().to(expr.span);
                let unary = ExprKind::Unary {
                    op,
                    expr: Box::new(expr),
                };
                (unary, span)
            }

            // Conditional: if expr then expr else expr fi
            TokenKind::If => {
                let predicate = self.parse_expr()?;
                self.consume(TokenKind::Then)?;
                let then_arm = self.parse_expr()?;
                self.consume(TokenKind::Else)?;
                let else_arm = self.parse_expr()?;
                let end = self.consume(TokenKind::Fi)?;
                let cond = ExprKind::Conditional {
                    predicate: Box::new(predicate),
                    then_arm: Box::new(then_arm),
                    else_arm: Box::new(else_arm),
                };
                (cond, token.span().to(end.span()))
            }

            // Loop: while expr loop expr pool
            TokenKind::While => {
                let predicate = self.parse_expr()?;
                self.consume(TokenKind::Loop)?;
                let body = self.parse_expr()?;
                let end = self.consume(TokenKind::Pool)?;
                let w = ExprKind::While {
                    predicate: Box::new(predicate),
                    body: Box::new(body),
                };
                (w, token.span().to(end.span()))
            }

            // Let: let binding [, binding]* in expr
            TokenKind::Let => {
                let bindings = self.parse_list(
                    TokenKind::In,
                    TokenKind::Comma,
                    Some(Error::MissingLetBinding),
                    Parser::parse_let_binding,
                )?;
                self.consume(TokenKind::In)?;
                let body = self.parse_expr()?;

                let span = token.span().to(body.span);
                let l = ExprKind::Let {
                    bindings,
                    body: Box::new(body),
                };
                (l, span)
            }

            // Case: case expr of arm; [arm;]* esac
            TokenKind::Case => {
                let predicate = self.parse_expr()?;
                self.consume(TokenKind::Of)?;

                let arms = self.parse_list(
                    TokenKind::Esac,
                    TokenKind::Semicolon,
                    Some(Error::EmptyCase),
                    |p| {
                        let (arm, _) = p.parse_case_arm()?;
                        Ok(arm)
                    },
                )?;
                let esac = self.consume(TokenKind::Esac)?;

                let span = token.span().to(esac.span());
                let case = ExprKind::Case {
                    predicate: Box::new(predicate),
                    arms,
                };
                (case, span)
            }

            other => {
                let error = Error::UnexpectedTokenInExpr { token: other };
                self.error(token.span().wrap(error));
                return Err(());
            }
        };

        Ok(Expr {
            kind,
            span,
            info: (),
        })
    }

    /// led: Parses tokens that follow a left-hand-side expression
    /// (infix/postfix operators)
    fn parse_led(&mut self, op_token: Token, lhs: Expr<Untyped>, rbp: u8) -> Result<Expr<Untyped>> {
        let (kind, span) = match op_token.kind {
            // Binary Operators: +, -, *, /, <, <=, =
            kind @ (TokenKind::Plus
            | TokenKind::Minus
            | TokenKind::Star
            | TokenKind::Slash
            | TokenKind::Less
            | TokenKind::LessEq
            | TokenKind::Eq) => {
                let op = match kind {
                    TokenKind::Plus => BinaryOperator::Add,
                    TokenKind::Minus => BinaryOperator::Sub,
                    TokenKind::Star => BinaryOperator::Mul,
                    TokenKind::Slash => BinaryOperator::Div,
                    TokenKind::Less => BinaryOperator::Le,
                    TokenKind::LessEq => BinaryOperator::Leq,
                    TokenKind::Eq => BinaryOperator::Eq,
                    _ => unreachable!(),
                };
                // Parse right operand with correct precedence
                let rhs = self.parse_expr_bp(rbp)?;

                let span = lhs.span.to(rhs.span);
                let binary = ExprKind::Binary {
                    op,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                };
                (binary, span)
            }

            // Assignment: ID <- expr
            TokenKind::Assign => {
                // Check if lhs is a simple identifier
                let ExprKind::Id(target, ()) = lhs.kind else {
                    let error = Error::InvalidAssignmentTarget;
                    self.error(lhs.span.wrap(error));
                    return Err(());
                };

                let value = self.parse_expr_bp(rbp)?;
                let span = lhs.span.to(value.span);
                let assign = ExprKind::Assignment {
                    target,
                    value: Box::new(value),
                    info: (),
                };
                (assign, span)
            }

            // Dispatch: expr@TYPE.ID(args) or expr.ID(args) or ID(args)
            // Note: ID(args) is handled by nud(ID) followed by led(LParen)
            //
            // Static Dispatch: expr @ TYPE . ID ( [expr [, expr]*] )
            TokenKind::At => {
                let static_qualifier = self.parse_type()?;
                self.consume(TokenKind::Dot)?;
                let method = self.parse_ident()?;

                self.consume(TokenKind::LParen)?;
                let args = self.parse_list(TokenKind::RParen, TokenKind::Comma, None, |p| {
                    p.parse_expr()
                })?;
                let end = self.consume(TokenKind::RParen)?;

                let span = lhs.span.to(end.span());
                let dispatch = ExprKind::Dispatch {
                    qualifier: Some(DispatchQualifier {
                        expr: Box::new(lhs),
                        static_qualifier: Some(static_qualifier),
                    }),
                    method,
                    args,
                };
                (dispatch, span)
            }

            // Dynamic Dispatch: expr . ID ( [expr [, expr]*] )
            TokenKind::Dot => {
                let method = self.parse_ident()?;

                self.consume(TokenKind::LParen)?;
                let args = self.parse_list(TokenKind::RParen, TokenKind::Comma, None, |p| {
                    p.parse_expr()
                })?;
                let end = self.consume(TokenKind::RParen)?;

                let span = lhs.span.to(end.span());
                let dispatch = ExprKind::Dispatch {
                    qualifier: Some(DispatchQualifier {
                        expr: Box::new(lhs),
                        static_qualifier: None,
                    }),
                    method,
                    args,
                };
                (dispatch, span)
            }

            // Self Dispatch Call: ID ( [expr [, expr]*] ) (parsed as led for '(')
            TokenKind::LParen => {
                // Ensure the lhs was just a simple ID parsed by nud
                let ExprKind::Id(method, ()) = lhs.kind else {
                    self.error(lhs.span.wrap(Error::InvalidDispatch));
                    return Err(());
                };

                // LParen was already consumed above.
                let args = self.parse_list(TokenKind::RParen, TokenKind::Comma, None, |p| {
                    p.parse_expr()
                })?;
                let end = self.consume(TokenKind::RParen)?;

                let dispatch = ExprKind::Dispatch {
                    qualifier: None,
                    method,
                    args,
                };
                (dispatch, lhs.span.to(end.span()))
            }

            other => {
                let error = Error::UnexpectedOperator { actual: other };
                self.error(op_token.span().wrap(error));
                return Err(());
            }
        };

        Ok(Expr {
            kind,
            span,
            info: (),
        })
    }

    /// Parses `item (delim item)*` until `end_delim` is found. Does **NOT**
    /// consume the end delimiter.
    fn parse_list<T>(
        &mut self,
        end_delim: TokenKind,
        separator: TokenKind,
        require_one: Option<Error>,
        parse_item: impl Fn(&mut Self) -> Result<T>,
    ) -> Result<Vec<T>> {
        debug_assert_ne!(end_delim, separator);

        let mut items = Vec::new();
        while self.except([end_delim]) {
            let item = self.synchronize(&[separator], &[end_delim], |p| parse_item(p))?;
            items.push(item);

            // After consuming an item, we must consume the separator.
            if !self.take(separator) {
                if self.is(end_delim) {
                    // If, however, it is not present, then we check if the end
                    // delimiter is current. If so, we can stop.
                    break;
                }
                // However, if the current token is not the separator nor
                // the end delimiter, we must return an error.
                let c = self.peek();
                self.error(c.span().wrap(Error::UnexpectedAny {
                    actual: c.kind,
                    expected: Box::from([separator, end_delim]),
                }));
            }
        }

        let next = self.peek();
        assert!(next.kind == end_delim || next.kind == TokenKind::Eof);
        if let Some(error) = require_one {
            if items.is_empty() {
                self.error(next.span().wrap(error));
                return Err(());
            }
        }

        Ok(items)
    }

    fn infix_binding_power(kind: TokenKind) -> Option<(u8, u8)> {
        let bp = match kind {
            // Level 9: Assignment (right-associative)
            TokenKind::Assign => (2, 1),

            // Level 7: Comparisons (left-associative)
            TokenKind::Less | TokenKind::LessEq | TokenKind::Eq => (5, 6),

            // Level 6: Addition/Subtraction (left-associative)
            TokenKind::Plus | TokenKind::Minus => (7, 8),

            // Level 5: Multiplication/Division (left-associative)
            TokenKind::Star | TokenKind::Slash => (9, 10),

            // Level 2: Static Dispatch (left-associative)
            TokenKind::At => (15, 16),

            // Level 1: Dynamic Dispatch / Function Call (left-associative)
            TokenKind::Dot => (17, 18),
            // func(...) - Treat call '(' with same precedence as '.'
            TokenKind::LParen => (17, 18),

            _ => return None,
        };
        Some(bp)
    }

    // Prefix operators:
    fn prefix_binding_power(kind: TokenKind) -> Option<((), u8)> {
        let bp = match kind {
            // Level 8: Logical Not
            TokenKind::Not => ((), 4), // not expr

            // Level 4: Type check / Allocation
            TokenKind::IsVoid | TokenKind::New => ((), 12),

            // Level 3: Arithmetic Negation
            TokenKind::Tilde => ((), 14),

            // Other tokens are not prefix operators handled by binding power
            // (Keywords like if, while, let, case, new are handled directly in nud)
            // (Literals, IDs, (, { are handled directly in nud)
            _ => return None,
        };
        Some(bp)
    }

    fn parse_let_binding(&mut self) -> Result<Binding<Untyped>> {
        let name = self.parse_ident()?;
        self.consume(TokenKind::Colon)?;
        let ty = self.parse_type()?;
        let initializer = self.parse_initializer()?;

        Ok(Binding {
            name,
            ty,
            initializer,
        })
    }

    fn parse_case_arm(&mut self) -> Result<(CaseArm<Untyped>, Span)> {
        let name = self.parse_ident()?;
        let start_span = name.span;
        self.consume(TokenKind::Colon)?;
        let ty = self.parse_type()?;
        self.consume(TokenKind::FatArrow)?;
        let body = self.parse_expr()?;

        let span = start_span.to(body.span);
        let arm = CaseArm {
            name,
            ty,
            body: Box::new(body),
        };
        Ok((arm, span))
    }
}

impl Parser<'_, '_, '_> {
    pub fn new<'src, 'tok, 'ident>(
        src: &'src str,
        tokens: &'tok mut Vec<Token>,
        ident_interner: &'ident mut Interner<str>,
    ) -> Parser<'src, 'tok, 'ident> {
        let mut p = Parser {
            src,
            tokens,
            ident_interner,
            cursor: 0,
            errors: Vec::with_capacity(8),
        };
        p.setup();
        p
    }

    /// Adds an error and returns the error sentinel.
    fn error(&mut self, error: Spanned<Error>) {
        self.errors.push(error);
    }

    /// Setups the parser, skipping any trivia if necessary.
    fn setup(&mut self) {
        while self.peek().kind.is_trivia() {
            self.advance();
        }
    }

    /// Returns the current token.
    ///
    /// Advances if the current token is trivia.
    #[inline]
    fn peek(&self) -> Token {
        match self.tokens.get(self.cursor) {
            Some(token) => *token,
            None => Token::eof_for(self.src),
        }
    }

    /// Returns the current token and advances. Skips any trivia.
    fn advance(&mut self) -> Token {
        let c = self.peek(); // Before any advancement
        while {
            self.cursor += 1;
            self.peek().kind.is_trivia()
        } {}
        c
    }

    /// Checks whether the current token matches the given one.
    fn is(&self, expect: TokenKind) -> bool {
        self.peek().kind == expect
    }

    /// Advances if the current token matches the provided one, returning true.
    /// If not, returns false and doesn't advance.
    fn take(&mut self, expect: TokenKind) -> bool {
        if self.is(expect) {
            self.advance();
            true
        } else {
            false
        }
    }

    /// Advances if the current token matches the provided one, returning true.
    /// If not, records an error.
    fn consume(&mut self, expect: TokenKind) -> Result<Token> {
        let c = self.peek();
        if self.is(expect) {
            self.advance();
            Ok(c)
        } else {
            self.error(c.span().wrap(Error::Unexpected {
                actual: c.kind,
                expected: expect,
            }));
            Err(())
        }
    }

    /// Advances if the current token matches any of the provided tokens,
    /// returning true. If not, records an error.
    fn consume_any(&mut self, expect: &'static [TokenKind]) -> Result<Token> {
        for t in expect {
            if self.is(*t) {
                return Ok(self.advance());
            }
        }
        let c = self.peek();
        self.error(c.span().wrap(Error::UnexpectedAny {
            actual: c.kind,
            expected: Box::from(expect),
        }));
        Err(())
    }

    /// Returns true while the current token does *not* match one of the
    /// provided ones. [`TokenKind::Eof`] is implicitly included in the list.
    ///
    /// This won't advance the cursor.
    fn except(&mut self, except: impl IntoIterator<Item = TokenKind>) -> bool {
        let c = self.peek();
        for e in except {
            if c.kind == e {
                return false;
            }
        }
        if c.kind == TokenKind::Eof {
            return false;
        }
        true
    }

    fn synchronize<T>(
        &mut self,
        cont_cond: &[TokenKind],
        stop_cond: &[TokenKind],
        mut f: impl FnMut(&mut Self) -> Result<T>,
    ) -> Result<T> {
        'outer: loop {
            if let Ok(val) = f(self) {
                break Ok(val);
            }
            // In the case of an error, try to advance until find a token
            // specified in `cont_cond` (in which case we retry) or in
            // `stop_cond` (in which case we stop).
            loop {
                let c = self.peek().kind;
                // Check whether must stop
                if c == TokenKind::Eof || stop_cond.contains(&c) {
                    break 'outer Err(());
                }
                // The token advancement must be AFTER stopping. If we break
                // out, the caller should advance (to follow the convention).
                self.advance();
                // Check whether can retry
                if cont_cond.contains(&c) {
                    continue 'outer;
                }
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    InvalidAssignmentTarget,
    InvalidDispatch,
    UnexpectedTokenInExpr {
        token: TokenKind,
    },
    Unexpected {
        actual: TokenKind,
        expected: TokenKind,
    },
    UnexpectedAny {
        actual: TokenKind,
        expected: Box<[TokenKind]>,
    },
    UnexpectedOperator {
        actual: TokenKind,
    },
    EmptyProgram,
    EmptyBlockBody,
    EmptyCase,
    MissingLetBinding,
    ParseInt,
    /// A token kind which holds the [`TokenKind::is_error`] property.
    Lexer(TokenKind),
}

impl From<std::num::ParseIntError> for Error {
    fn from(_: std::num::ParseIntError) -> Self {
        Error::ParseInt
    }
}

#[cfg(test)]
pub(crate) mod test_utils {
    use super::*;

    pub fn parse_program(src: &str) -> (Interner<str>, Program<Untyped>) {
        let mut i = Interner::with_capacity(32);
        let prog = super::parse_program(src, &mut Vec::with_capacity(512), &mut i)
            .expect("failed to parse");
        (i, prog)
    }

    #[expect(dead_code)]
    pub fn parse_expr(src: &str) -> (Interner<str>, Expr<Untyped>) {
        let mut i = Interner::with_capacity(32);
        let prog =
            super::parse_expr(src, &mut Vec::with_capacity(512), &mut i).expect("failed to parse");
        (i, prog)
    }
}

#[cfg(test)]
mod tests {
    use crate::util::test_utils::tree_tests;

    tree_tests!(
        use parser;

        fn test_simple_expression() {
            let expr = "(1 * 2 + 3) - (1 + 2 * 3)";
            let tree_ok = "
                binary Sub (0..25)
                  paren (0..11)
                    binary Add (1..10)
                      binary Mul (1..6)
                        int 1 (1..2)
                        int 2 (5..6)
                      int 3 (9..10)
                  paren (14..25)
                    binary Add (15..24)
                      int 1 (15..16)
                      binary Mul (19..24)
                        int 2 (19..20)
                        int 3 (23..24)
            ";
        }

        fn test_identifier_expr() {
            let expr = "myVar";
            let tree_ok = "ident myVar (0..5)";
        }

        fn test_integer_literal_expr() {
            let expr = "12345";
            let tree_ok = "int 12345 (0..5)";
        }

        fn test_string_literal_expr() {
            let expr = r#""hello world""#;
            let tree_ok = r#"string "hello world" (0..13)"#;
        }

        fn test_escaped_string_literal_expr() {
            let expr = r#""hello\nworld""#;
            let tree_ok = r#"string "hello\nworld" (0..14)"#;
        }

        fn test_boolean_true_expr() {
            let expr = "true";
            let tree_ok = "bool true (0..4)";
        }

        fn test_boolean_false_expr() {
            let expr = "false";
            let tree_ok = "bool false (0..5)";
        }

        fn test_parenthesized_expr() {
            let expr = "(x)";
            let tree_ok = "
                paren (0..3)
                  ident x (1..2)
            ";
        }

        fn test_block_expr_simple() {
            let expr = "{ x; }";
            let tree_ok = "
                block (0..6)
                  ident x (2..3)
            ";
        }

        fn test_block_expr_multiple_statements() {
            let expr = "{ x; y; z; }";
            let tree_ok = "
                block (0..12)
                  ident x (2..3)
                  ident y (5..6)
                  ident z (8..9)
            ";
        }

        fn test_new_object_expr() {
            let expr = "new MyType";
            let tree_ok = "new MyType (0..10)";
        }

        fn test_unary_isvoid_expr() {
            let expr = "isvoid x";
            let tree_ok = "
                unary IsVoid (0..8)
                  ident x (7..8)
            ";
        }

        fn test_unary_integer_negation_expr() {
            let expr = "~x";
            let tree_ok = "
                unary Inverse (0..2)
                  ident x (1..2)
            ";
        }

        fn test_unary_boolean_negation_expr() {
            let expr = "not x";
            let tree_ok = "
                unary Not (0..5)
                  ident x (4..5)
            ";
        }

        fn test_binary_addition_expr() {
            let expr = "a + b";
            let tree_ok = "
                binary Add (0..5)
                  ident a (0..1)
                  ident b (4..5)
            ";
        }

        fn test_binary_subtraction_expr() {
            let expr = "a - b";
            let tree_ok = "
                binary Sub (0..5)
                  ident a (0..1)
                  ident b (4..5)
            ";
        }

        fn test_binary_multiplication_expr() {
            let expr = "a * b";
            let tree_ok = "
                binary Mul (0..5)
                  ident a (0..1)
                  ident b (4..5)
            ";
        }

        fn test_binary_division_expr() {
            let expr = "a / b";
            let tree_ok = "
                binary Div (0..5)
                  ident a (0..1)
                  ident b (4..5)
            ";
        }

        fn test_binary_less_than_expr() {
            let expr = "a < b";
            let tree_ok = "
                binary Le (0..5)
                  ident a (0..1)
                  ident b (4..5)
            ";
        }

        fn test_binary_less_than_or_equal_expr() {
            let expr = "a <= b";
            let tree_ok = "
                binary Leq (0..6)
                  ident a (0..1)
                  ident b (5..6)
            ";
        }

        fn test_binary_equals_expr() {
            let expr = "a = b";
            let tree_ok = "
                binary Eq (0..5)
                  ident a (0..1)
                  ident b (4..5)
            ";
        }

        fn test_assignment_expr() {
            let expr = "a <- b";
            let tree_ok = "
                assignment a (0..6)
                  ident b (5..6)
            ";
        }

        fn test_assignment_expr_complex_rhs() {
            let expr = "a <- b + c";
            let tree_ok = "
                assignment a (0..10)
                  binary Add (5..10)
                    ident b (5..6)
                    ident c (9..10)
            ";
        }

        fn test_conditional_expr() {
            let expr = "if p then x else y fi";
            let tree_ok = "
                conditional (0..21)
                  ident p (3..4)
                  ident x (10..11)
                  ident y (17..18)
            ";
        }

        fn test_while_loop_expr() {
            let expr = "while cond loop body pool";
            let tree_ok = "
                while (0..25)
                  ident cond (6..10)
                  ident body (16..20)
            ";
        }

        fn test_let_expr_single_binding_no_init() {
            let expr = "let x : Int in x";
            let tree_ok = "
                let (0..16)
                  binding x: Int
                  in
                    ident x (15..16)
            ";
        }

        fn test_let_expr_single_binding_with_init() {
            let expr = "let x : Int <- 1 in x";
            let tree_ok = "
                let (0..21)
                  binding x: Int (initialized)
                    int 1 (15..16)
                  in
                    ident x (20..21)
            ";
        }

        fn test_let_expr_multiple_bindings() {
            let expr = r#"let x : Int <- 1, y : String <- "s" in x"#;
            let tree_ok = r#"
                let (0..40)
                  binding x: Int (initialized)
                    int 1 (15..16)
                  binding y: String (initialized)
                    string "s" (32..35)
                  in
                    ident x (39..40)
            "#;
        }

        fn test_case_expr_single_branch() {
            let expr = "
                case e of
                    id1 : Type1 => expr1;
                esac
            ";
            let tree_ok = "
                case (17..89)
                  ident e (22..23)
                  arm id1: Type1 =>
                    ident expr1 (62..67)
            ";
        }

        fn test_case_expr_multiple_branches() {
            let expr = "
                case e of
                    id1 : T1 => e1;
                    id2 : T2 => e2;
                esac
            ";
            let tree_ok = "
                case (17..119)
                  ident e (22..23)
                  arm id1: T1 =>
                    ident e1 (59..61)
                  arm id2: T2 =>
                    ident e2 (95..97)
            ";
        }

        fn test_self_dispatch_expr_no_args() {
            let expr = "method()";
            let tree_ok = "
                dispatch method (0..8)
            ";
        }

        fn test_self_dispatch_expr_one_arg() {
            let expr = "method(arg1)";
            let tree_ok = "
                dispatch method (0..12)
                  arguments
                    ident arg1 (7..11)
            ";
        }

        fn test_self_dispatch_expr_multiple_args() {
            let expr = "method(arg1, arg2)";
            let tree_ok = "
                dispatch method (0..18)
                  arguments
                    ident arg1 (7..11)
                    ident arg2 (13..17)
            ";
        }

        fn test_dynamic_dispatch_expr_no_args() {
            let expr = "obj.method()";
            let tree_ok = "
                dispatch method (0..12)
                  receiver
                    ident obj (0..3)
            ";
        }

        fn test_dynamic_dispatch_expr_one_arg() {
            let expr = "obj.method(arg1)";
            let tree_ok = "
                dispatch method (0..16)
                  receiver
                    ident obj (0..3)
                  arguments
                    ident arg1 (11..15)
            ";
        }

        fn test_static_dispatch_expr_no_args() {
            let expr = "obj@Type.method()";
            let tree_ok = "
                dispatch method (0..17)
                  receiver @ Type
                    ident obj (0..3)
            ";
        }

        fn test_static_dispatch_expr_one_arg() {
            let expr = "obj@Type.method(arg1)";
            let tree_ok = "
                dispatch method (0..21)
                  receiver @ Type
                    ident obj (0..3)
                  arguments
                    ident arg1 (16..20)
            ";
        }

        fn test_precedence_mul_plus() {
            let expr = "1 + 2 * 3";
            let tree_ok = "
                binary Add (0..9)
                  int 1 (0..1)
                  binary Mul (4..9)
                    int 2 (4..5)
                    int 3 (8..9)
            ";
        }

        fn test_precedence_plus_mul() {
            let expr = "1 * 2 + 3";
            let tree_ok = "
                binary Add (0..9)
                  binary Mul (0..5)
                    int 1 (0..1)
                    int 2 (4..5)
                  int 3 (8..9)
            ";
        }

        fn test_precedence_assign() {
            let expr = "a <- b <- c + d"; // a <- (b <- (c + d))
            let tree_ok = "
                assignment a (0..15)
                  assignment b (5..15)
                    binary Add (10..15)
                      ident c (10..11)
                      ident d (14..15)
            ";
        }

        fn test_precedence_dispatch_arith() {
            let expr = "obj.meth(a + b)";
            let tree_ok = "
                dispatch meth (0..15)
                  receiver
                    ident obj (0..3)
                  arguments
                    binary Add (9..14)
                      ident a (9..10)
                      ident b (13..14)
            ";
        }

        fn test_precedence_arith_compare() {
            let expr = "a + b < c * d"; // (a + b) < (c * d)
            let tree_ok = "
                binary Le (0..13)
                  binary Add (0..5)
                    ident a (0..1)
                    ident b (4..5)
                  binary Mul (8..13)
                    ident c (8..9)
                    ident d (12..13)
            ";
        }

        fn test_attribute_no_init() {
            let program = "
                class C {
                    attr : Int;
                };
            ";
            let tree_ok = "
                class C
                  attribute attr: Int
            ";
        }

        fn test_attribute_with_init() {
            let program = "
                class C {
                    attr : Int <- 1;
                };
            ";
            let tree_ok = "
                class C
                  attribute attr: Int (initialized)
                    int 1 (61..62)
            ";
        }

        fn test_method_no_formals() {
            let program = "
                class C {
                    meth() : Bool { true };
                };
            ";
            let tree_ok = "
                class C
                  method meth() : Bool
                    bool true (63..67)
            ";
        }

        fn test_method_one_formal() {
            let program = "
                class C {
                    meth(f1: Int) : Bool { true };
                };
            ";
            let tree_ok = "
                class C
                  method meth(f1: Int) : Bool
                    bool true (70..74)
            ";
        }

        fn test_method_multiple_formals() {
            let program = "
                class C {
                    meth(f1: Int, f2: String) : Bool { true };
                };
            ";
            let tree_ok = "
                class C
                  method meth(f1: Int, f2: String) : Bool
                    bool true (82..86)
            ";
        }

        fn test_simple_class() {
            let program = "
                class Main {
                    main(): Int { 1 };
                };
            ";
            let tree_ok = "
                class Main
                  method main() : Int
                    int 1 (64..65)
            ";
        }

        fn test_class_with_inheritance() {
            let program = "
                class Sub inherits Super {};
            ";
            let tree_ok = "class Sub inherits Super";
        }

        fn test_class_with_multiple_features() {
            let program = "
                class Test {
                    attr1 : String;
                    meth1() : Int { 0 };
                    attr2 : Bool <- false;
                    meth2(p1: Type1, p2: Type2) : ReturnType { body_expr };
                };
            ";
            let tree_ok = "
                class Test
                  attribute attr1: String
                  method meth1() : Int
                    int 0 (102..103)
                  attribute attr2: Bool (initialized)
                    bool false (143..148)
                  method meth2(p1: Type1, p2: Type2) : ReturnType
                    ident body_expr (213..222)
            ";
        }

        fn test_program_single_class() {
            let program = "
                class OnlyClass {};
            ";
            let tree_ok = "
                class OnlyClass
            ";
        }

        fn test_program_multiple_classes() {
            let program = "
                class First {};
                class Second {
                    meth() : IO { self };
                };
            ";
            let tree_ok = "
                class First
                class Second
                  method meth() : IO
                    ident self (98..102)
            ";
        }

        fn test_error_empty_program() {
            let program = "";
            let expected_errors = &["0..0: empty program"];
        }

        fn test_error_program_only_whitespace() {
            let program = "   \n\t   ";
            let expected_errors = &["0..8: empty program"];
        }

        fn test_error_class_missing_semicolon() {
            let program = "
                class A { }
                class B { }
            ";
            let expected_errors = &[
                "45..50: expected token Semicolon, but got Class",
                "69..69: expected token Semicolon, but got Eof",
            ];
        }

        fn test_error_attribute_missing_type() {
            let program = "
                class A {
                    attr : ;
                };
            ";
            let expected_errors = &[
                "54..55: expected token Identifier, but got Semicolon",
                "72..73: expected token Identifier, but got RBrace",
            ];
        }

        fn test_error_method_missing_return_type() {
            let program = "
                class A {
                    meth() : { 1 };
                };
            ";
            let expected_errors = &["56..57: expected token Identifier, but got LBrace"];
        }

        fn test_error_method_formal_malformed() {
            let program = "
                class A {
                    meth(f1 Int) : Bool { true };
                };
            ";
            let expected_errors = &["55..58: expected token Colon, but got Identifier"];
        }

        fn test_error_expr_unexpected_token_in_expr() {
            let expr = "1 + ;";
            let expected_errors = &["4..5: unexpected token in expression"];
        }

        fn test_error_expr_unmatched_paren_open() {
            let expr = "(1 + 2";
            let expected_errors = &["6..6: expected token RParen, but got Eof"];
        }

        fn test_error_expr_unmatched_paren_close() {
            let expr = "1 + 2)";
            let expected_errors = &[];
        }

        fn test_error_empty_block_body() {
            let expr = "{}";
            // wtf?
            let expected_errors = &["1..2: empty block or sequence"];
        }

        fn test_error_empty_case_arms() {
            let expr = "case x of esac";
            let expected_errors = &["10..14: empty case"];
        }

        fn test_error_missing_let_binding() {
            let expr = "let in x";
            let expected_errors = &["4..6: let without binding"];
        }

        fn test_error_parse_int_too_large() {
            let expr = "999999999999999999999999999999"; // Exceeds i64
            let expected_errors = &["0..30: parse int error, out of bounds"];
        }

        fn test_error_invalid_assignment_target() {
            let expr = "1 <- 2";
            let expected_errors = &["0..1: invalid assignment target"];
        }

        fn test_error_invalid_dispatch_target_non_id() {
            let expr = "(1+2)()"; // (1+2) is not an ID for self-dispatch
            let expected_errors = &["0..5: invalid dispatch"];
        }

        fn test_error_lexer_unexpected_char() {
            let expr = "$";
            let expected_errors = &["0..1: unexpected token in expression"];
        }

        fn test_error_lexer_unclosed_comment() {
            let program = "class A { (* unclosed comment };";
            let expected_errors =
                &["10..32: expected token Identifier, but got ErrorUnclosedComment"];
        }

        fn test_error_lexer_unclosed_string() {
            let expr = "\"abc";
            let expected_errors = &["0..4: unexpected token in expression"];
        }

        fn test_error_lexer_unescaped_line_break_in_string() {
            let expr = "\"string\n\""; // \n is not escaped
            let expected_errors = &["7..8: unexpected token in expression"];
        }

        fn test_recovery_in_feature() {
            let program = "
                class Main {
                    feature1() : Int {
                        1 +
                    };

                    feature2() : Int {
                        1 + 2
                    };
                };
            ";
            let tree_error = "
                class Main
                  method feature2() : Int
                    binary Add (184..189)
                      int 1 (184..185)
                      int 2 (188..189)
            ";
            let expected_errors = &["117..118: unexpected token in expression"];
        }

        fn test_recovery_in_let_multiple_bindings() {
            let expr = "
                let x : Int <- 1 + 2,
                    y : Int <- (3+),
                    z : Int <- 5 + 6 in
                    x + y + z
            ";
            let tree_error = "
                let (17..145)
                  binding x: Int (initialized)
                    binary Add (32..37)
                      int 1 (32..33)
                      int 2 (36..37)
                  binding z: Int (initialized)
                    binary Add (107..112)
                      int 5 (107..108)
                      int 6 (111..112)
                  in
                    binary Add (136..145)
                      binary Add (136..141)
                        ident x (136..137)
                        ident y (140..141)
                      ident z (144..145)
            ";
            let expected_errors = &["73..74: unexpected token in expression"];
        }

        fn test_recovery_block_expr_error_continue() {
            let expr = "{ 1 + ; 2 * 3 ; }"; // Error in first, should parse second
            let tree_error = "dummy (17..17)";
            let expected_errors = &[
                "6..7: unexpected token in expression",
                "16..17: unexpected token in expression",
            ];
        }
    );
}
