use std::{iter::Peekable, ops::Range};

use crate::token::{Span, Token, TokenKind};

pub struct Lexer<'src> {
    src: &'src str,
    iter: Peekable<std::str::Chars<'src>>,
    cursor: usize,
    current_lo: usize,
}

impl Iterator for Lexer<'_> {
    type Item = Token;

    fn next(&mut self) -> Option<Self::Item> {
        let kind = self.scan_token_kind();
        Some(self.produce(kind))
    }
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
            ' ' => Whitespace,
            '\n' => Whitespace,
            '\r' => Whitespace,
            '\t' => Whitespace,
            '"' => self.string(),
            d if d.is_ascii_digit() => self.number(),
            unexpected => todo!("todo: {unexpected:?}"),
        }
    }

    fn string(&mut self) -> TokenKind {
        while !matches!(self.peek(), '\0' | '"') {
            self.advance();
        }
        match self.advance() {
            '\0' => TokenKind::Error("unclosed string".to_string()),
            '"' => TokenKind::String(self.substr().to_string()),
            char => unreachable!("{char:?}"),
        }
    }

    fn number(&mut self) -> TokenKind {
        while self.peek().is_ascii_digit() {
            self.advance();
        }
        match self.substr().parse() {
            Ok(number) => TokenKind::Number(number),
            Err(error) => TokenKind::Error(format!("failed to parse number: {error}")),
        }
    }
}

impl Lexer<'_> {
    pub fn new<'src>(src: &'src str) -> Lexer<'src> {
        Lexer {
            src,
            iter: src.chars().peekable(),
            cursor: 0,
            current_lo: 0,
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

    /// Returns the next token without advancing the iterator.
    fn peek(&mut self) -> char {
        self.iter.peek().copied().unwrap_or('\0')
    }

    /// Returns the range of the current marked bounds.
    fn marked_range(&self) -> Range<usize> {
        self.current_lo..self.cursor
    }

    /// Returns the substring of the current marked bounds.
    fn substr(&self) -> &str {
        &self.src[self.marked_range()]
    }

    /// Produces a token using the marked bounds.
    fn produce(&self, kind: TokenKind) -> Token {
        Token::new(kind, Span::new_of_bounds(self.marked_range()))
    }
}

#[cfg(test)]
mod tests {
    use crate::util::BreakableIteratorExt;

    use super::*;
    use pretty_assertions::assert_eq;

    #[test]
    fn tests_with_span() {
        use TokenKind::*;
        let cases = cases![
            "+" => [
                (Plus, 0..1),
                (Eof, 1..1),
            ],
            "++" => [
                (Plus, 0..1),
                (Plus, 1..2),
                (Eof, 2..2),
            ],
            "+-*/" => [
                (Plus, 0..1),
                (Minus, 1..2),
                (Star, 2..3),
                (Slash, 3..4),
                (Eof, 4..4),
            ],
        ];

        for (input, tokens) in cases {
            let lexed: Vec<_> = Lexer::new(input)
                .up_to(|t| t.kind == TokenKind::Eof)
                .collect();
            assert_eq!(lexed, tokens.as_slice());
        }
    }

    macro_rules! cases {
        ($($str:expr => [$(($kind:expr, $range:expr)),* $(,)?]),* $(,)?) => {{
            &[$((
                $str,
                vec![
                    $(Token::new($kind, Span::new_of_bounds($range.start..$range.end))),*
                ],
            )),*]
        }};
    }
    use cases;
}
