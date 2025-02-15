use std::{iter::Peekable, ops::Range};

use crate::{
    lexer1 as l,
    token::{Span, Token, TokenKind, KEYWORDS},
};

pub struct Lexer<'src> {
    src: &'src str,
    iter: Peekable<std::str::Chars<'src>>,
    cursor: usize,
    current_lo: usize,
    tokens: Vec<Token>,
}

pub fn lex(src: &str) -> Vec<Token> {
    let mut lexer = Lexer::new(src);
    while lexer.cursor < src.len() {
        let next = lexer.scan_token_kind();
        lexer.tokens.push(lexer.produce(next));
    }
    lexer.tokens
}

impl Lexer<'_> {
    /// Tries to scan the current character.
    fn scan_token_kind(&mut self) -> TokenKind {
        use TokenKind::*;
        match self.mark_advance() {
            '\0' => Eof,
            '+' => Plus,
            '-' => Minus,
            '*' => Star,
            '/' => Slash,
            '(' => LParen,
            ')' => RParen,
            '"' => self.string(),
            c if c.is_ascii_alphabetic() => self.identifier_or_keyword(),
            c if c.is_ascii_digit() => self.number(),
            c if c.is_ascii_whitespace() => self.whitespace(),
            _ => TokenKind::Error(l::Error::UnexpectedChar),
        }
    }

    fn string(&mut self) -> TokenKind {
        let mut has_escaped = false;
        let mut escaped = false;
        loop {
            let (current, current_span) = self.advance_with_span();
            match (escaped, current) {
                // A NUL char marks the unclosed string error, in any context.
                (_, '\0') => return TokenKind::Error(l::Error::UnclosedString),
                // An unescaped quotation mark marks the end of the string.
                (false, '"') => {
                    let raw = self.substr_bounded(1, -1);
                    let string = if has_escaped {
                        perform_escape(raw)
                    } else {
                        raw.to_string()
                    };
                    return TokenKind::String(string);
                }
                // A string can only contain a line break if it is escaped. In
                // this case, an error token is emitted with a resume point to
                // continue lexing the current string.
                (false, '\n') => {
                    self.tokens.push(Token::new(
                        TokenKind::Error(l::Error::UnescapedLineBreak),
                        current_span,
                    ));
                }
                // Mark a new escape context.
                (false, '\\') => {
                    has_escaped = true;
                    escaped = true;
                }
                // For any other character, just advance. Also, reset the
                // previous escaping context, if any.
                (_, _) => {
                    escaped = false;
                }
            }
        }
    }

    fn identifier_or_keyword(&mut self) -> TokenKind {
        let valid_identifier_suffix = |c: char| c.is_ascii_alphanumeric() || c == '_';
        let valid_boolean = |substr: &str| substr.as_bytes()[0].is_ascii_lowercase();

        while valid_identifier_suffix(self.peek()) {
            self.advance();
        }
        let substr = self.substr();
        let lower = substr.to_ascii_lowercase();
        match KEYWORDS.get(&lower).cloned() {
            // Even though keywords are "totally" case insensitive, booleans are
            // case insensitive except for the first character, which must
            // always be in lowercase.
            Some(TokenKind::True | TokenKind::False) if !valid_boolean(substr) => {
                TokenKind::Identifier(self.substr().to_string())
            }
            Some(keyword) => keyword,
            None => TokenKind::Identifier(self.substr().to_string()),
        }
    }

    fn number(&mut self) -> TokenKind {
        while self.peek().is_ascii_digit() {
            self.advance();
        }
        match self.substr().parse() {
            Ok(number) => TokenKind::Number(number),
            Err(_) => TokenKind::Error(l::Error::ParseInt),
        }
    }

    fn whitespace(&mut self) -> TokenKind {
        while self.peek().is_ascii_whitespace() {
            self.advance();
        }
        TokenKind::Whitespace(self.substr().to_string())
    }
}

impl Lexer<'_> {
    pub fn new(src: &str) -> Lexer<'_> {
        Lexer {
            src,
            iter: src.chars().peekable(),
            cursor: 0,
            current_lo: 0,
            tokens: Vec::with_capacity(8_192),
        }
    }

    /// Starts a new token "mark" and advances the iterator.
    fn mark_advance(&mut self) -> char {
        self.current_lo = self.cursor;
        self.advance()
    }

    /// Returns the next byte and advances the iterator.
    fn advance(&mut self) -> char {
        self.iter
            .next()
            .inspect(|c| self.cursor += c.len_utf8())
            .unwrap_or('\0')
    }

    /// Returns the next byte (with its span) and advances the iterator.
    fn advance_with_span(&mut self) -> (char, Span) {
        let lo = self.cursor;
        let char = self.advance();
        let hi = lo + char.len_utf8();
        let span = Span::new_of_bounds(lo..hi);
        (char, span)
    }

    /// Returns the next token without advancing the iterator.
    fn peek(&mut self) -> char {
        self.iter.peek().copied().unwrap_or('\0')
    }

    /// Returns the current range.
    fn range(&self) -> Range<usize> {
        self.current_lo..self.cursor
    }

    /// Returns the current span.
    fn span(&self) -> Span {
        Span::new_of_bounds(self.range())
    }

    /// Returns the substring of the current marked bounds.
    fn substr(&self) -> &str {
        &self.src[self.range()]
    }

    /// Returns a substring with custom bounds increments.
    ///
    /// Callers should (a) ensure that the operation is semantically correct to
    /// the specific token; (b) ensure that no overflows may occur; and (c) that
    /// the access will be within the source string's bounds.
    fn substr_bounded(&self, lo: isize, hi: isize) -> &str {
        let Range { start, end } = self.range();
        let lo = start.checked_add_signed(lo).unwrap();
        let hi = end.checked_add_signed(hi).unwrap();
        &self.src[lo..hi]
    }

    /// Produces a token using the marked bounds.
    fn produce(&self, kind: TokenKind) -> Token {
        Token::new(kind, self.span())
    }
}

fn perform_escape(raw: &str) -> String {
    let mut buf = String::with_capacity(raw.len());
    let mut escaped = false;
    for char in raw.chars() {
        let char = match (escaped, char) {
            (true, 'b') => '\x08', // backspace
            (true, 't') => '\t',   // tab
            (true, 'n') => '\n',   // newline
            (true, 'f') => '\x0c', // form feed
            (false, '\\') => {
                escaped = true;
                continue;
            }
            (_, char) => char,
        };
        escaped = false;
        buf.push(char);
    }
    buf.shrink_to_fit();
    // This function is only called if the string token contains at least one
    // escape sequence
    debug_assert!(buf.len() < raw.len(), "original string MUST be greater");
    buf
}
