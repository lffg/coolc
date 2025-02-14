use std::{fmt, ops::Range};

#[derive(Clone)]
#[cfg_attr(test, derive(PartialEq, Eq))]
pub struct Token {
    pub kind: TokenKind,
    lo: usize,
    len: u32,
}

impl Token {
    pub fn new<'a>(kind: TokenKind, span: Span) -> Token {
        Token {
            kind,
            len: span.len,
            lo: span.lo,
        }
    }

    pub fn span(&self) -> Span {
        Span {
            len: self.len,
            lo: self.lo,
        }
    }

    pub fn is_eof(&self) -> bool {
        self.kind == TokenKind::Eof
    }
}

impl fmt::Debug for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Token({:?}, {})", self.kind, self.span())
    }
}

#[derive(Copy, Clone)]
pub struct Span {
    pub len: u32,
    pub lo: usize,
}

impl Span {
    pub fn new_of_bounds(Range { start: lo, end: hi }: Range<usize>) -> Span {
        debug_assert!(hi >= lo);
        Self::new_of_length(lo, (hi - lo) as u32)
    }

    pub fn new_of_length(lo: usize, len: u32) -> Span {
        Span { len, lo }
    }
}

impl fmt::Debug for Span {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Span({self}, len: {})", self.len)
    }
}

impl fmt::Display for Span {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let lo = self.lo;
        let hi = lo + self.len as usize;
        write!(f, "{lo}..{hi}")
    }
}

// This is not the most efficient way of representing a token kind, but it
// suffices for this simple compiler implementation.
#[derive(Clone, Debug, PartialEq, Eq)]
#[expect(dead_code)]
pub enum TokenKind {
    Class,
    Else,
    False,
    Fi,
    If,
    In,
    Inherits,
    IsVoid,
    Let,
    While,
    Loop,
    Pool,
    Then,
    Case,
    Esac,
    New,
    Of,
    Not,
    True,
    Plus,
    Minus,
    Star,
    Slash,
    Inverse,
    Less,
    LessEq,
    Eq,
    GreaterEq,
    Greater,
    Assign,
    Colon,
    Semicolon,
    Comma,
    Dot,
    LParen,
    RParen,
    LBrace,
    RBrace,
    At,
    Identifier,

    String(String),
    Number(i64),

    Whitespace,
    Eof,
    Error(String),
}
