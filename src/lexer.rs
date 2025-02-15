use std::{iter::Peekable, mem, ops::Range};

use crate::token::{Span, Token, TokenKind, KEYWORDS};

type Result<T, E = MidwayError> = std::result::Result<T, E>;

/// The Cool lexer.
///
/// ## Implementation Remarks
///
/// This type implements the [`Iterator`] trait to make the parser walk through
/// the tokens without allocating a collection to hold all of them at once.
///
/// Since tokens of type [`TokenKind::Eof`] already serve as an indication of
/// termination (with the addition of having span information), the [`Iterator`]
/// implementation is infinite: instead of returning None when the source stream
/// is exhausted, tokens of type [`TokenKind::Eof`] will be continuously
/// returned.
///
/// Consumers must follow this convention, or use the [`up_to`] helper.
///
/// [`up_to`]: crate::util::BreakableIteratorExt::up_to
pub struct Lexer<'src> {
    src: &'src str,
    iter: Peekable<std::str::Chars<'src>>,
    cursor: usize,
    current_lo: usize,
    resumer: Resumer,
}

impl Iterator for Lexer<'_> {
    type Item = Token;

    fn next(&mut self) -> Option<Self::Item> {
        Some(match self.scan_token_kind() {
            Ok(kind) => self.produce(kind),
            Err(MidwayError { error, span }) => Token::new(TokenKind::Error(error), span),
        })
    }
}

impl Lexer<'_> {
    /// Tries to scan the current character.
    fn scan_token_kind(&mut self) -> Result<TokenKind> {
        use TokenKind::*;
        let _: () = match mem::take(&mut self.resumer) {
            Resumer::None => (),
            Resumer::String(ctx) => return self.string(ctx),
        };
        Ok(match self.mark_advance() {
            '\0' => Eof,
            '+' => Plus,
            '-' => match self.peek() {
                '-' => self.inline_comment(),
                _ => Minus,
            },
            '*' => Star,
            '/' => Slash,
            '~' => Tilde,
            '=' => Eq,
            '<' => match self.peek() {
                '=' => self.advance_with(LessEq),
                '-' => self.advance_with(Assign),
                _ => Less,
            },
            '>' => match self.peek() {
                '=' => self.advance_with(GreaterEq),
                _ => Greater,
            },
            ':' => Colon,
            ';' => Semicolon,
            ',' => Comma,
            '.' => Dot,
            '(' => match self.peek() {
                '*' => self.multiline_comment(),
                _ => LParen,
            },
            ')' => RParen,
            '{' => LBrace,
            '}' => RBrace,
            '@' => At,
            '"' => self.string(StringCtx::default())?,
            c if c.is_ascii_alphabetic() => self.identifier_or_keyword(),
            c if c.is_ascii_digit() => self.number(),
            c if c.is_ascii_whitespace() => self.whitespace(),
            _ => return self::Error::UnexpectedChar.with_span(self.span()),
        })
    }

    fn string(&mut self, mut ctx: StringCtx) -> Result<TokenKind> {
        let mut escaped = false;
        loop {
            let (current, current_span) = self.advance_with_span();
            match (escaped, current) {
                // A NUL char marks the unclosed string error, in any context.
                (_, '\0') => {
                    return Error::UnclosedString.with_span(self.span());
                }
                // An unescaped quotation mark marks the end of the string.
                (false, '"') => {
                    let raw = self.substr_bounded(1, -1);
                    let string = if ctx.has_escaped {
                        perform_escape(raw)
                    } else {
                        raw.to_string()
                    };
                    return Ok(TokenKind::String(string));
                }
                // A string can only contain a line break if it is escaped. In
                // this case, an error token is emitted with a resume point to
                // continue lexing the current string.
                (false, '\n') => {
                    return self.suspend_with_error(
                        Resumer::String(ctx),
                        Error::UnescapedLineBreak,
                        current_span,
                    );
                }
                // Mark a new escape context.
                (false, '\\') => {
                    ctx.has_escaped = true;
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
            Err(_) => TokenKind::Error(Error::ParseInt),
        }
    }

    fn whitespace(&mut self) -> TokenKind {
        while self.peek().is_ascii_whitespace() {
            self.advance();
        }
        TokenKind::Whitespace(self.substr().to_string())
    }

    fn inline_comment(&mut self) -> TokenKind {
        assert_eq!(self.advance(), '-');
        while self.peek() != '\n' {
            self.advance();
        }
        TokenKind::Comment(self.substr_bounded(2, 0).to_string())
    }

    fn multiline_comment(&mut self) -> TokenKind {
        assert_eq!(self.advance(), '*');
        loop {
            if self.advance() == '*' && self.advance() == ')' {
                break;
            }
        }
        TokenKind::Comment(self.substr_bounded(2, -2).to_string())
    }
}

impl Lexer<'_> {
    pub fn new(src: &str) -> Lexer<'_> {
        Lexer {
            src,
            iter: src.chars().peekable(),
            cursor: 0,
            current_lo: 0,
            resumer: Resumer::default(),
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

    /// Advances and returns the provided value.
    fn advance_with<T>(&mut self, value: T) -> T {
        self.advance();
        value
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

    /// Declares a suspension.
    fn suspend_with_error<T>(
        &mut self,
        suspended_from: Resumer,
        error: Error,
        span: Span,
    ) -> Result<T, MidwayError> {
        self.resumer = suspended_from;
        Err(MidwayError { error, span })
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

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Error {
    UnexpectedChar,
    UnclosedString,
    UnescapedLineBreak,
    ParseInt,
}

impl Error {
    fn with_span<T>(self, span: Span) -> Result<T, MidwayError> {
        Err(MidwayError { error: self, span })
    }
}

struct MidwayError {
    error: Error,
    span: Span,
}

#[derive(Default)]
enum Resumer {
    #[default]
    None,
    String(StringCtx),
}

#[derive(Default)]
struct StringCtx {
    has_escaped: bool,
}

#[cfg(test)]
mod tests {
    use crate::util::BreakableIteratorExt;

    use super::*;
    use pretty_assertions::assert_eq;

    #[test]
    fn tests_with_span() {
        use super::Error as E;
        use TokenKind::*;
        let cases = cases!(match .. {
            "+-*/" => [
                (Plus, 0..1),
                (Minus, 1..2),
                (Star, 2..3),
                (Slash, 3..4),
                (Eof, 4..4),
            ],
            "class/Class/cLaSs/CLASS" => [
                (Class, 0..5),
                (Slash, 5..6),
                (Class, 6..11),
                (Slash, 11..12),
                (Class, 12..17),
                (Slash, 17..18),
                (Class, 18..23),
                (Eof, 23..23),
            ],
            "true/tRue/trUe/tRUE/True/TRUE" => [
                (True, 0..4),
                (Slash, 4..5),
                (True, 5..9),
                (Slash, 9..10),
                (True, 10..14),
                (Slash, 14..15),
                (True, 15..19),
                (Slash, 19..20),
                (Identifier("True".into()), 20..24),
                (Slash, 24..25),
                (Identifier("TRUE".into()), 25..29),
                (Eof, 29..29),
            ],
            "1/11/111/01/001/123456789" => [
                (Number(1), 0..1),
                (Slash, 1..2),
                (Number(11), 2..4),
                (Slash, 4..5),
                (Number(111), 5..8),
                (Slash, 8..9),
                (Number(1), 9..11),
                (Slash, 11..12),
                (Number(1), 12..15),
                (Slash, 15..16),
                (Number(123456789), 16..25),
                (Eof, 25..25),
            ],
            "f/fo/foo/B/BA/BAR/a123z" => [
                (Identifier("f".into()), 0..1),
                (Slash, 1..2),
                (Identifier("fo".into()), 2..4),
                (Slash, 4..5),
                (Identifier("foo".into()), 5..8),
                (Slash, 8..9),
                (Identifier("B".into()), 9..10),
                (Slash, 10..11),
                (Identifier("BA".into()), 11..13),
                (Slash, 13..14),
                (Identifier("BAR".into()), 14..17),
                (Slash, 17..18),
                (Identifier("a123z".into()), 18..23),
                (Eof, 23..23),
            ],
            r#"""/"oi como vai"/"oi"# => [
                (String("".into()), 0..2),
                (Slash, 2..3),
                (String("oi como vai".into()), 3..16),
                (Slash, 16..17),
                (Error(E::UnclosedString), 17..20),
                (Eof, 20..20),
            ],
            r#"("\"")("\\")("\\\\")("\\\"")"# => [
                (LParen, 0..1),
                (String(r#"""#.into()), 1..5),
                (RParen, 5..6),
                (LParen, 6..7),
                (String(r#"\"#.into()), 7..11),
                (RParen, 11..12),
                (LParen, 12..13),
                (String(r#"\\"#.into()), 13..19),
                (RParen, 19..20),
                (LParen, 20..21),
                (String(r#"\""#.into()), 21..27),
                (RParen, 27..28),
                (Eof, 28..28),
            ],
            r#""\a\b\c\d\e\f\g\h\i\j\k\l\m\n\o\p\q\r\s\t\u\v\w\x\y\z""# => [
                (String("a\x08cde\x0cghijklm\nopqrs\tuvwxyz".into()), 0..54),
                (Eof, 54..54),
            ],
            r#""oi\"# => [(Error(E::UnclosedString), 0..4), (Eof, 4..4),],
            "(\"hello\\\nworld!\") (\"won't\nwork\") (\"neither\nthis\none\")" => [
                (LParen, 0..1),
                (String("hello\nworld!".into()), 1..16),
                (RParen, 16..17),
                (Whitespace(" ".into()), 17..18),
                (LParen, 18..19),
                (Error(E::UnescapedLineBreak), 25..26),
                (String("won't\nwork".into()), 19..31),
                (RParen, 31..32),
                (Whitespace(" ".into()), 32..33),
                (LParen, 33..34),
                (Error(E::UnescapedLineBreak), 42..43),
                (Error(E::UnescapedLineBreak), 47..48),
                (String("neither\nthis\none".into()), 34..52),
                (RParen, 52..53),
                (Eof, 53..53),
            ],
            "hello (* world!\n this *) 1 (**) 2 -- is a\n\"comment!\"" => [
                (Identifier("hello".into()), 0..5),
                (Whitespace(" ".into()), 5..6),
                (Comment(" world!\n this ".into()), 6..24),
                (Whitespace(" ".into()), 24..25),
                (Number(1), 25..26),
                (Whitespace(" ".into()), 26..27),
                (Comment("".into()), 27..31),
                (Whitespace(" ".into()), 31..32),
                (Number(2), 32..33),
                (Whitespace(" ".into()), 33..34),
                (Comment(" is a".into()), 34..41),
                (Whitespace("\n".into()), 41..42),
                (String("comment!".into()), 42..52),
                (Eof, 52..52),
            ],
            "(< <= <- > >= -) (<<=<->>=-)" => [
                (LParen, 0..1),
                (Less, 1..2),
                (Whitespace(" ".into()), 2..3),
                (LessEq, 3..5),
                (Whitespace(" ".into()), 5..6),
                (Assign, 6..8),
                (Whitespace(" ".into()), 8..9),
                (Greater, 9..10),
                (Whitespace(" ".into()), 10..11),
                (GreaterEq, 11..13),
                (Whitespace(" ".into()), 13..14),
                (Minus, 14..15),
                (RParen, 15..16),
                (Whitespace(" ".into()), 16..17),
                (LParen, 17..18),
                (Less, 18..19),
                (LessEq, 19..21),
                (Assign, 21..23),
                (Greater, 23..24),
                (GreaterEq, 24..26),
                (Minus, 26..27),
                (RParen, 27..28),
                (Eof, 28..28),
            ],
        });

        for (input, tokens) in cases {
            let lexed: Vec<_> = Lexer::new(input)
                .up_to(|t| t.kind == TokenKind::Eof)
                .collect();
            assert_eq!(lexed, tokens.as_slice());
        }
    }

    macro_rules! cases {
        (match .. {
            $($str:expr => [$(($kind:expr, $range:expr)),* $(,)?]),* $(,)?
        }) => {{
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
