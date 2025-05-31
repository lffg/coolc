use std::{cmp, fmt, ops::Range};

#[derive(Copy, Clone)]
#[cfg_attr(test, derive(PartialEq, Eq))]
pub struct Token {
    lo: u32,
    /// We assume that no *single* token can be more than 2^16 (65.536) bytes
    /// long. Notice that a [`Span`] must have a higher "capacity" since it may
    /// encompass entire regions of a program, which in reasonable cases can
    /// surpass 2^16 bytes.
    len: u16,
    pub kind: TokenKind,
}

impl Token {
    pub fn new(kind: TokenKind, span: Span) -> Token {
        Token {
            lo: span.lo,
            len: u16::try_from(span.hi - span.lo).unwrap(),
            kind,
        }
    }

    pub fn span(&self) -> Span {
        Span {
            lo: self.lo,
            hi: self.lo + u32::from(self.len),
        }
    }

    pub fn eof_for(src: &str) -> Token {
        Token {
            lo: u32::try_from(src.len()).unwrap(),
            len: 0,
            kind: TokenKind::Eof,
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

#[derive(Debug)]
pub struct Spanned<T> {
    pub span: Span,
    pub inner: T,
}

#[derive(Copy, Clone, PartialEq, Eq)]
pub struct Span {
    pub lo: u32,
    pub hi: u32,
}

impl Span {
    pub fn new_of_bounds(Range { start: lo, end: hi }: Range<usize>) -> Span {
        debug_assert!(hi >= lo);
        Span {
            lo: u32::try_from(lo).unwrap(),
            hi: u32::try_from(hi).unwrap(),
        }
    }

    pub const fn new_of_length(lo: u32, len: u32) -> Span {
        Span { lo, hi: lo + len }
    }

    #[must_use]
    pub fn to(self, other: Span) -> Span {
        let lo = cmp::min(self.lo, other.lo);
        let hi = cmp::max(self.hi, other.hi);
        Span { lo, hi }
    }

    #[must_use]
    pub fn offset(self, lo: i8, hi: i8) -> Span {
        let lo_64 = (i64::from(self.lo)).checked_add(i64::from(lo)).unwrap();
        let hi_64 = (i64::from(self.hi)).checked_add(i64::from(hi)).unwrap();
        Span {
            lo: u32::try_from(lo_64).unwrap(),
            hi: u32::try_from(hi_64).unwrap(),
        }
    }

    pub fn substr(self, src: &str) -> &str {
        let lo = usize::try_from(self.lo).unwrap();
        let hi = usize::try_from(self.hi).unwrap();
        &src[lo..hi]
    }

    pub fn wrap<T>(self, inner: T) -> Spanned<T> {
        Spanned { span: self, inner }
    }
}

impl fmt::Debug for Span {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Span({self}, len: {})", self.hi - self.lo)
    }
}

impl fmt::Display for Span {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let lo = self.lo;
        let hi = self.hi;
        write!(f, "{lo}..{hi}")
    }
}

// This is not the most efficient way of representing a token kind, but it
// suffices for this simple compiler implementation.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum TokenKind {
    Class,
    Else,
    If,
    Fi,
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
    False,

    Plus,
    Minus,
    Star,
    Slash,
    /// Also known as "inverse" (in the language).
    ///
    /// `~`
    Tilde,
    Eq,
    Less,
    LessEq,
    GreaterEq,
    Greater,
    /// `<-`
    Assign,
    /// `=>`
    FatArrow,
    Colon,
    Semicolon,
    Comma,
    Dot,
    /// (
    LParen,
    /// )
    RParen,
    /// {
    LBrace,
    /// }
    RBrace,
    At,

    Identifier,
    String,
    EscapedString,
    Number,

    InlineComment,
    MultilineComment,
    Whitespace,
    Eof,

    ErrorUnexpectedChar,
    ErrorUnclosedComment,
    ErrorUnclosedString,
    ErrorUnescapedLineBreak,
}

impl TokenKind {
    pub fn is_error(self) -> bool {
        matches!(
            self,
            TokenKind::ErrorUnexpectedChar
                | TokenKind::ErrorUnclosedComment
                | TokenKind::ErrorUnclosedString
                | TokenKind::ErrorUnescapedLineBreak
        )
    }
}

pub static KEYWORDS: phf::Map<&'static str, TokenKind> = phf::phf_map! {
    "class" => TokenKind::Class,
    "else" => TokenKind::Else,
    "if" => TokenKind::If,
    "fi" => TokenKind::Fi,
    "in" => TokenKind::In,
    "inherits" => TokenKind::Inherits,
    "isvoid" => TokenKind::IsVoid,
    "let" => TokenKind::Let,
    "while" => TokenKind::While,
    "loop" => TokenKind::Loop,
    "pool" => TokenKind::Pool,
    "then" => TokenKind::Then,
    "case" => TokenKind::Case,
    "esac" => TokenKind::Esac,
    "new" => TokenKind::New,
    "of" => TokenKind::Of,
    "not" => TokenKind::Not,
    "true" => TokenKind::True,
    "false" => TokenKind::False,
};
