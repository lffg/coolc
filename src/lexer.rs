use std::{iter::Peekable, num::ParseIntError};

use crate::token::{Span, Token, TokenKind, KEYWORDS};

pub const SUGGESTED_TOKENS_CAPACITY: usize = 8_192;

/// Lexes the provided string, producing the tokens into the provided buffer.
pub fn lex(src: &str, tokens: &mut Vec<Token>) {
    Lexer::new(src, tokens).lex();
}

/// A convenience function that allocates a new buffer per lexed input and
/// returns it.
pub fn lex_in_new(src: &str) -> Vec<Token> {
    let mut tokens = Vec::with_capacity(SUGGESTED_TOKENS_CAPACITY);
    lex(src, &mut tokens);
    tokens
}

/// The Cool lexer
struct Lexer<'src, 'tok> {
    src: &'src str,
    iter: Peekable<std::str::Chars<'src>>,
    cursor: usize,
    current_lo: usize,
    tokens: &'tok mut Vec<Token>,
}

impl Lexer<'_, '_> {
    /// Scans the source string until the input is exhausted.
    ///
    /// Tokens are written into the provided tokens buffer.
    fn lex(mut self) {
        assert_eq!(self.tokens.len(), 0, "must pass clean tokens buffer");
        loop {
            let next = self.scan_token_kind();
            let is_eof = matches!(next, TokenKind::Eof);
            self.produce(next);
            if is_eof {
                break;
            }
        }
    }

    /// Tries to scan the current character.
    fn scan_token_kind(&mut self) -> TokenKind {
        use TokenKind::*;
        match self.mark_advance() {
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
            '"' => self.string(),
            c if c.is_ascii_alphabetic() => self.identifier_or_keyword(),
            c if c.is_ascii_digit() => self.number(),
            c if c.is_ascii_whitespace() => self.whitespace(),
            _ => TokenKind::ErrorUnexpectedChar,
        }
    }

    /// Tries to lex a string token. This is the most complicated token lexing
    /// routine since it has to detect character escape sequences, if any.
    ///
    /// Notice that the lexer doesn't escape the string while trying to lex the
    /// token itself. Instead, it only performs the escape *after* the entire
    /// token has been lexed (just before returning). This is an optimization to
    /// avoid the need of a growing buffer for all string tokens (which is
    /// necessary when performing escaping): we only pay the cost of escape when
    /// it's actually necessary.
    fn string(&mut self) -> TokenKind {
        // Whether any escaping did happen inside this string token
        let mut has_escaped = false;
        // Whether the current character is being escaped
        let mut is_escaping = false;
        loop {
            let (current, current_span) = self.advance_with_span();
            match (is_escaping, current) {
                // A NUL char marks the unclosed string error, in any context.
                // Since there's not else to be done (the input has exhausted),
                // the scanner exists here with a single error token.
                (_, '\0') => {
                    return TokenKind::ErrorUnclosedString;
                }
                // An unescaped quotation mark marks the end of the string.
                (false, '"') => {
                    return if has_escaped {
                        TokenKind::EscapedString
                    } else {
                        TokenKind::String
                    };
                }
                // A string can only contain a line break if it is escaped. In
                // this case, an error token is emitted. Notice that the lexer
                // keeps scanning the string.
                (false, '\n') => {
                    self.produce_spanned(TokenKind::ErrorUnescapedLineBreak, current_span);
                }
                // Mark a new escape context.
                (false, '\\') => {
                    has_escaped = true;
                    is_escaping = true;
                }
                // For any other character, just advance. Also, reset the
                // previous escaping context, if any.
                (_, _) => {
                    is_escaping = false;
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
        match KEYWORDS.get(&lower).copied() {
            // Even though keywords are "totally" case insensitive, booleans are
            // case insensitive except for the first character, which must
            // always be in lowercase.
            Some(TokenKind::True | TokenKind::False) if !valid_boolean(substr) => {
                TokenKind::Identifier
            }
            Some(keyword) => keyword,
            None => TokenKind::Identifier,
        }
    }

    fn number(&mut self) -> TokenKind {
        while self.peek().is_ascii_digit() {
            self.advance();
        }
        TokenKind::Number
    }

    fn whitespace(&mut self) -> TokenKind {
        while self.peek().is_ascii_whitespace() {
            self.advance();
        }
        TokenKind::Whitespace
    }

    fn inline_comment(&mut self) -> TokenKind {
        assert_eq!(self.advance(), '-');
        while !matches!(self.peek(), '\n' | '\0') {
            self.advance();
        }
        TokenKind::InlineComment
    }

    fn multiline_comment(&mut self) -> TokenKind {
        assert_eq!(self.advance(), '*');
        loop {
            match self.advance() {
                '*' => (), // start closing comment
                '\0' => return TokenKind::ErrorUnclosedComment,
                _ => continue, // keep scanning comment...
            }
            match self.advance() {
                ')' => break, // finished closing comment
                '\0' => return TokenKind::ErrorUnclosedComment,
                _ => continue, // sadly couldn't close it! keep scanning...
            }
        }
        TokenKind::MultilineComment
    }
}

impl Lexer<'_, '_> {
    /// Constructs a new lexer with the default state.
    fn new<'src, 'tok>(src: &'src str, tokens: &'tok mut Vec<Token>) -> Lexer<'src, 'tok> {
        Lexer {
            src,
            iter: src.chars().peekable(),
            cursor: 0,
            current_lo: 0,
            tokens,
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

    /// Returns the current span.
    fn span(&self) -> Span {
        Span::new_of_bounds(self.current_lo..self.cursor)
    }

    /// Returns the substring of the current marked bounds.
    fn substr(&self) -> &str {
        self.span().substr(self.src)
    }

    /// Produces a token using the marked bounds.
    fn produce(&mut self, kind: TokenKind) {
        self.produce_spanned(kind, self.span());
    }

    /// Produces a token with the provided span.
    fn produce_spanned(&mut self, kind: TokenKind, span: Span) {
        self.tokens.push(Token::new(kind, span));
    }
}

pub mod extract {
    use super::*;

    pub fn int(token: Token, src: &str) -> Result<i64, ParseIntError> {
        debug_assert_eq!(token.kind, TokenKind::Number);
        token.span().substr(src).parse()
    }

    pub fn ident(token: Token, src: &str) -> Box<str> {
        debug_assert_eq!(token.kind, TokenKind::Identifier);
        token.span().substr(src).to_string().into_boxed_str()
    }

    pub fn string(token: Token, src: &str) -> Box<str> {
        debug_assert_eq!(token.kind, TokenKind::String);
        let s = token.span().offset(1, -1).substr(src);
        s.to_string().into_boxed_str()
    }

    pub fn escaped_string(token: Token, src: &str) -> Box<str> {
        debug_assert_eq!(token.kind, TokenKind::EscapedString);
        let s = token.span().offset(1, -1).substr(src);
        perform_escape(s).into_boxed_str()
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

#[cfg(test)]
mod tests {
    use super::*;
    use pretty_assertions::assert_eq;

    #[test]
    fn test_stack_machine_no_errors() {
        let input = include_str!("../examples/stack-machine.cool");
        let has_errors = lex_in_new(input).into_iter().any(|t| t.kind.is_error());
        assert!(!has_errors);
    }

    #[test]
    fn tests_with_span() {
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
                (Identifier, 20..24),
                (Slash, 24..25),
                (Identifier, 25..29),
                (Eof, 29..29),
            ],
            "1/11/111/01/001/123456789" => [
                (Number, 0..1),
                (Slash, 1..2),
                (Number, 2..4),
                (Slash, 4..5),
                (Number, 5..8),
                (Slash, 8..9),
                (Number, 9..11),
                (Slash, 11..12),
                (Number, 12..15),
                (Slash, 15..16),
                (Number, 16..25),
                (Eof, 25..25),
            ],
            "f/fo/foo/B/BA/BAR/a123z" => [
                (Identifier, 0..1),
                (Slash, 1..2),
                (Identifier, 2..4),
                (Slash, 4..5),
                (Identifier, 5..8),
                (Slash, 8..9),
                (Identifier, 9..10),
                (Slash, 10..11),
                (Identifier, 11..13),
                (Slash, 13..14),
                (Identifier, 14..17),
                (Slash, 17..18),
                (Identifier, 18..23),
                (Eof, 23..23),
            ],
            r#"""/"oi como vai"/"oi"# => [
                (String, 0..2),
                (Slash, 2..3),
                (String, 3..16),
                (Slash, 16..17),
                (ErrorUnclosedString, 17..20),
                (Eof, 20..20),
            ],
            r#"("\"")("\\")("\\\\")("\\\"")"# => [
                (LParen, 0..1),
                (EscapedString, 1..5),
                (RParen, 5..6),
                (LParen, 6..7),
                (EscapedString, 7..11),
                (RParen, 11..12),
                (LParen, 12..13),
                (EscapedString, 13..19),
                (RParen, 19..20),
                (LParen, 20..21),
                (EscapedString, 21..27),
                (RParen, 27..28),
                (Eof, 28..28),
            ],
            r#""\a\b\c\d\e\f\g\h\i\j\k\l\m\n\o\p\q\r\s\t\u\v\w\x\y\z""# =>
                [(EscapedString, 0..54), (Eof, 54..54),],
            r#""oi\"# => [(ErrorUnclosedString, 0..4), (Eof, 4..4),],
            "(\"hello\\\nworld!\") (\"won't\nwork\") (\"neither\nthis\none\")" => [
                (LParen, 0..1),
                (EscapedString, 1..16),
                (RParen, 16..17),
                (Whitespace, 17..18),
                (LParen, 18..19),
                (ErrorUnescapedLineBreak, 25..26),
                (String, 19..31),
                (RParen, 31..32),
                (Whitespace, 32..33),
                (LParen, 33..34),
                (ErrorUnescapedLineBreak, 42..43),
                (ErrorUnescapedLineBreak, 47..48),
                (String, 34..52),
                (RParen, 52..53),
                (Eof, 53..53),
            ],
            "hello (* world!\n this *) 1 (**) 2 -- is a\n\"comment!\"" => [
                (Identifier, 0..5),
                (Whitespace, 5..6),
                (MultilineComment, 6..24),
                (Whitespace, 24..25),
                (Number, 25..26),
                (Whitespace, 26..27),
                (MultilineComment, 27..31),
                (Whitespace, 31..32),
                (Number, 32..33),
                (Whitespace, 33..34),
                (InlineComment, 34..41),
                (Whitespace, 41..42),
                (String, 42..52),
                (Eof, 52..52),
            ],
            "-- line comment without line break" => [(InlineComment, 0..34), (Eof, 34..34),],
            "(* unclosed" => [
                //
                (ErrorUnclosedComment, 0..11),
                (Eof, 11..11),
            ],
            "(< <= <- > >= -) (<<=<->>=-)" => [
                (LParen, 0..1),
                (Less, 1..2),
                (Whitespace, 2..3),
                (LessEq, 3..5),
                (Whitespace, 5..6),
                (Assign, 6..8),
                (Whitespace, 8..9),
                (Greater, 9..10),
                (Whitespace, 10..11),
                (GreaterEq, 11..13),
                (Whitespace, 13..14),
                (Minus, 14..15),
                (RParen, 15..16),
                (Whitespace, 16..17),
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
            let lexed = lex_in_new(input);
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
