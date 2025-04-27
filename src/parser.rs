use crate::{
    ast::{
        BinaryOperator, Binding, CaseArm, Class, DispatchQualifier, Expr, ExprKind, Feature,
        Formal, Ident, Program, Type, UnaryOperator,
    },
    lexer::{self, extract},
    token::{Span, Spanned, Token, TokenKind},
};

type Result<T, E = Spanned<Error>> = std::result::Result<T, E>;

pub struct Parser<'src, 'tok> {
    src: &'src str,
    tokens: &'tok mut Vec<Token>,
    cursor: usize,
}

impl Parser<'_, '_> {
    pub fn parse(mut self) -> Result<Program> {
        assert!(self.tokens.is_empty());
        assert_eq!(self.cursor, 0);

        lexer::lex(self.src, self.tokens);
        self.parse_program()
    }

    fn parse_program(&mut self) -> Result<Program> {
        let mut classes = Vec::with_capacity(4);
        while self.except([]) {
            classes.push(self.parse_class()?);
        }
        self.consume(TokenKind::Eof)?;
        if classes.is_empty() {
            let s = Span::new_of_length(0, u32::try_from(self.src.len()).unwrap());
            Err(s.wrap(Error::EmptyProgram))
        } else {
            Ok(Program { classes })
        }
    }

    fn parse_class(&mut self) -> Result<Class> {
        self.consume(TokenKind::Class)?;
        let name = self.parse_type()?;

        let inherits = if self.consume(TokenKind::Inherits).is_ok() {
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

    fn parse_feature(&mut self) -> Result<Feature> {
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
                Ok(Feature::Method {
                    name,
                    formals,
                    return_ty,
                    body,
                })
            }
            _ => unreachable!(),
        }
    }

    fn parse_formal(&mut self) -> Result<Formal> {
        let name = self.parse_ident()?;
        self.consume(TokenKind::Colon)?;
        let ty = self.parse_type()?;
        Ok(Formal { name, ty })
    }

    fn parse_initializer(&mut self) -> Result<Option<Expr>> {
        if self.consume(TokenKind::Assign).is_err() {
            return Ok(None);
        }
        let expr = self.parse_expr()?;
        Ok(Some(expr))
    }

    fn parse_type(&mut self) -> Result<Type> {
        self.parse_ident().map(Type)
    }

    fn parse_ident(&mut self) -> Result<Ident> {
        let tok = self.consume(TokenKind::Identifier)?;
        let ident = extract::ident(tok, self.src);
        Ok(Ident {
            ident,
            span: tok.span(),
        })
    }

    fn parse_expr(&mut self) -> Result<Expr> {
        self.parse_expr_bp(0)
    }

    fn parse_expr_bp(&mut self, min_bp: u8) -> Result<Expr> {
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
    fn parse_nud(&mut self, token: Token) -> Result<Expr> {
        let (kind, span) = match token.kind {
            TokenKind::Identifier => (
                ExprKind::Id(Ident {
                    ident: extract::ident(token, self.src),
                    span: token.span(),
                }),
                token.span(),
            ),
            TokenKind::Number => (
                match extract::int(token, self.src) {
                    Ok(parsed) => ExprKind::Int(parsed),
                    Err(_) => return Err(token.span().wrap(Error::ParseInt)),
                },
                token.span(),
            ),
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
                let mut body = Vec::new();
                while self.except([TokenKind::RBrace]) {
                    body.push(self.parse_expr()?);
                    self.consume(TokenKind::Semicolon)?;
                }
                let end = self.consume(TokenKind::RBrace)?;
                let block_span = token.span().to(end.span());
                if body.is_empty() {
                    return Err(block_span.wrap(Error::EmptyBlockBody));
                }
                (ExprKind::Block { body }, block_span)
            }

            // Prefix operators: ~, not, isvoid, new
            kind @ (TokenKind::Tilde | TokenKind::Not | TokenKind::IsVoid | TokenKind::New) => {
                let op = match kind {
                    TokenKind::Tilde => UnaryOperator::Inverse,
                    TokenKind::Not => UnaryOperator::Not,
                    TokenKind::IsVoid => UnaryOperator::IsVoid,
                    TokenKind::New => UnaryOperator::New,
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
                let mut bindings = Vec::with_capacity(1);
                // First binding (required)
                bindings.push(self.parse_let_binding()?);
                // Parse subsequent bindings prefixed by comma
                while self.consume(TokenKind::Comma).is_ok() {
                    bindings.push(self.parse_let_binding()?);
                }
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
                return Err(token.span().wrap(error));
            }
        };

        Ok(Expr { kind, span })
    }

    /// led: Parses tokens that follow a left-hand-side expression
    /// (infix/postfix operators)
    fn parse_led(&mut self, op_token: Token, lhs: Expr, rbp: u8) -> Result<Expr> {
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
                let ExprKind::Id(target) = lhs.kind else {
                    let error = Error::InvalidAssignmentTarget;
                    return Err(lhs.span.wrap(error));
                };

                let value = self.parse_expr_bp(rbp)?;
                let span = lhs.span.to(value.span);
                let assign = ExprKind::Assignment {
                    target,
                    value: Box::new(value),
                };
                (assign, span)
            }

            // Dispatch: expr@TYPE.ID(args) or expr.ID(args) or ID(args)
            // Note: ID(args) is handled by nud(ID) followed by led(LParen)
            //
            // Static Dispatch: expr @ TYPE . ID ( [expr [, expr]*] )
            TokenKind::At => {
                let ty = self.parse_type()?;
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
                        ty,
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

                // XX: Do we need try to parse the qualifier here?
                let dispatch = ExprKind::Dispatch {
                    qualifier: None,
                    method,
                    args,
                };
                (dispatch, lhs.span.to(end.span()))
            }

            // Self Dispatch Call: ID ( [expr [, expr]*] ) (parsed as led for '(')
            TokenKind::LParen => {
                // Ensure the lhs was just a simple ID parsed by nud
                let ExprKind::Id(method) = lhs.kind else {
                    return Err(lhs.span.wrap(Error::InvalidDispatch));
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
                let err = Error::UnexpectedOperator { got: other };
                return Err(op_token.span().wrap(err));
            }
        };

        Ok(Expr { kind, span })
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
            items.push(parse_item(self)?);

            // Last separator is optional
            let sep_result = self.consume(separator);
            if let Err(error) = sep_result {
                if self.peek().kind == end_delim {
                    break;
                }
                return Err(error);
            }
        }

        let next = self.peek();
        assert_eq!(next.kind, end_delim);
        if let Some(error) = require_one {
            if items.is_empty() {
                return Err(next.span().wrap(error));
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

    fn parse_let_binding(&mut self) -> Result<Binding> {
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

    fn parse_case_arm(&mut self) -> Result<(CaseArm, Span)> {
        let name = self.parse_ident()?;
        let start_span = name.span;
        self.consume(TokenKind::Colon)?;
        let ty = self.parse_type()?;
        self.consume(TokenKind::Assign)?;
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

impl Parser<'_, '_> {
    pub fn new<'src, 'tok>(src: &'src str, tokens: &'tok mut Vec<Token>) -> Parser<'src, 'tok> {
        Parser {
            src,
            tokens,
            cursor: 0,
        }
    }

    /// Checks whether the token can be skipped for parsing purposes.
    #[inline]
    fn is_trivia(kind: TokenKind) -> bool {
        matches!(
            kind,
            TokenKind::InlineComment | TokenKind::MultilineComment | TokenKind::Whitespace
        )
    }

    /// Returns the current token.
    ///
    /// Advances if the current token is trivia.
    #[inline]
    fn peek(&mut self) -> Token {
        loop {
            match self.tokens.get(self.cursor) {
                Some(token) if Self::is_trivia(token.kind) => {
                    self.cursor += 1;
                    continue;
                }
                Some(token) => return *token,
                None => return Token::eof_for(self.src),
            }
        }
    }

    /// Returns the current token and advances.
    fn advance(&mut self) -> Token {
        let c = self.peek();
        self.cursor += 1;
        c
    }

    /// Advances if the provided token matches the current token. Errors if not.
    fn consume(&mut self, expect: TokenKind) -> Result<Token> {
        let c = self.peek();
        if c.kind == expect {
            self.advance();
            Ok(c)
        } else {
            Err(c.span().wrap(Error::Unexpected {
                got: c.kind,
                want: expect,
            }))
        }
    }

    /// Advances if matches any of the provided tokens.
    fn consume_any(&mut self, expect: &'static [TokenKind]) -> Result<Token> {
        for t in expect {
            if let Ok(token) = self.consume(*t) {
                return Ok(token);
            }
        }
        let c = self.peek();
        Err(c.span().wrap(Error::UnexpectedAny {
            got: c.kind,
            want: expect,
        }))
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
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Error {
    InvalidAssignmentTarget,
    InvalidDispatch,
    UnexpectedTokenInExpr {
        token: TokenKind,
    },
    Unexpected {
        got: TokenKind,
        want: TokenKind,
    },
    UnexpectedAny {
        got: TokenKind,
        want: &'static [TokenKind],
    },
    UnexpectedOperator {
        got: TokenKind,
    },
    EmptyProgram,
    EmptyBlockBody,
    EmptyCase,
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
mod tests {
    use super::*;
    use pretty_assertions::assert_eq;

    #[test]
    fn test_empty_class() {
        let parsed = parse(
            r#"
class OperatorList inherits Sanity {
   isNil() : Bool { true };
   head() : Operator {{
      die("called head() on empty list");
      new Operator;
   }};

   tail() : OperatorList {{
      die("called tail() on empty list");
      self;
   }};

   cons(op: Operator) : OperatorList {
      (new OperatorCons).init(op, self)
   };
};
            "#,
        );
        assert_eq!(parsed, Program::default());
    }

    fn parse(src: &str) -> Program {
        let mut buf = Vec::with_capacity(1024);
        let p = Parser::new(src, &mut buf);
        p.parse().unwrap()
    }
}
