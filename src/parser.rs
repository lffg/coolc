use std::mem;

use crate::{
    ast::{Binding, Class, Expr, Feature, Formal, Ident, Program, Type},
    lexer::extract,
    token::{Spanned, Token, TokenKind},
};

type Result<T, E = Spanned<Error>> = std::result::Result<T, E>;

pub struct Parser<'src, 'tok> {
    src: &'src str,
    tokens: &'tok mut Vec<Token>,
    cursor: usize,
}

macro_rules! ctl {
    (match consume($parser:expr) {
        $(TokenKind::$pat:ident => $arm:expr $(,)?)+
    }) => {{
        match $parser.consume_any(&[$(TokenKind::$pat,)+])?.kind {
            $(TokenKind::$pat => $arm),+
            _ => unreachable!(),
        }
    }};
}

impl Parser<'_, '_> {
    pub fn parse(&mut self) -> Result<Program> {
        self.parse_program()
    }

    fn parse_program(&mut self) -> Result<Program> {
        let mut classes = Vec::with_capacity(4);
        while self.peek().kind != TokenKind::Eof {
            classes.push(self.parse_class()?);
        }
        Ok(Program { classes })
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

        let features = self.parse_block(|p| p.parse_feature())?;

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
                let mut formals = Vec::with_capacity(2);
                while self.peek().kind != TokenKind::RParen {
                    formals.push(self.parse_formal()?);
                }
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

    fn parse_block<T>(
        &mut self,
        mut parse_item: impl FnMut(&mut Parser) -> Result<T>,
    ) -> Result<Vec<T>> {
        self.consume(TokenKind::LBrace)?;
        let mut items = Vec::with_capacity(4);
        while self.peek().kind != TokenKind::RBrace {
            items.push(parse_item(self)?);
        }
        self.consume(TokenKind::RBrace)?;
        Ok(items)
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
        todo!()
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

    /// Returns the current token without advancing.
    #[inline]
    fn peek(&self) -> Token {
        match self.tokens.get(self.cursor) {
            Some(token) => *token,
            None => Token::eof_for(self.src),
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
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Error {
    Unexpected {
        got: TokenKind,
        want: TokenKind,
    },
    UnexpectedAny {
        got: TokenKind,
        want: &'static [TokenKind],
    },
    /// A token kind which holds the [`TokenKind::is_error`] property.
    Lexer(TokenKind),
}
