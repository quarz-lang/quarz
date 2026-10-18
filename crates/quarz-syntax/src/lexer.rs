//! The lexer.
//!
//! Tokens are pulled one at a time with [`Lexer::next_token`]. String-like
//! literals are not single tokens: the lexer keeps a stack of modes so that
//! `"a#{b}c"` comes out as `StringBegin StringContent("a") EmbExprBegin
//! Ident(b) EmbExprEnd StringContent("c") StringEnd`, with the code inside
//! the interpolation lexed by the ordinary rules. Heredocs use the same
//! mechanism: on `<<~EOS` the lexer jumps to the body on the following line,
//! emits it, and then returns to the rest of the tag's line.
//!
//! Like CRuby, a little state is kept to resolve the classic ambiguities:
//! whether the previous token ended a value (`a / b` vs. `if /re/`) and,
//! for `foo /re/` style command calls, whether `foo` is a known local
//! variable. The parser tells the lexer about locals through [`LocalTable`].
//! Labels (`name:`) are not lexed specially; the parser recognizes an
//! identifier immediately followed by `:`.

use std::collections::{HashSet, VecDeque};

use crate::diagnostic::Diagnostic;
use crate::source::Span;
use crate::token::{Keyword, OpAssign, StringKind, Token, TokenKind};

/// Local variables currently in scope, maintained by the parser.
///
/// A *hard* scope (method body, class body) hides the variables of enclosing
/// scopes; a soft one (block) does not.
#[derive(Debug, Default)]
pub struct LocalTable {
    scopes: Vec<Scope>,
}

#[derive(Debug, Default)]
struct Scope {
    hard: bool,
    names: HashSet<String>,
}

impl LocalTable {
    pub fn push_scope(&mut self, hard: bool) {
        self.scopes.push(Scope {
            hard,
            names: HashSet::new(),
        });
    }

    pub fn pop_scope(&mut self) {
        self.scopes.pop();
    }

    pub fn declare(&mut self, name: &str) {
        if self.scopes.is_empty() {
            self.push_scope(true);
        }
        self.scopes
            .last_mut()
            .unwrap()
            .names
            .insert(name.to_string());
    }

    pub fn is_declared(&self, name: &str) -> bool {
        for scope in self.scopes.iter().rev() {
            if scope.names.contains(name) {
                return true;
            }
            if scope.hard {
                return false;
            }
        }
        false
    }
}

#[derive(Debug)]
enum Mode {
    /// Ordinary code. `depth` counts unbalanced `{` so that the `}` closing
    /// an interpolation can be told apart from one closing a block or hash.
    Normal {
        depth: u32,
    },
    Str(StrState),
}

#[derive(Debug)]
struct StrState {
    kind: StringKind,
    /// The opening delimiter when it differs from the closing one (`%q(`),
    /// so that balanced pairs are allowed inside.
    open: Option<u8>,
    close: u8,
    interpolate: bool,
    nesting: u32,
    heredoc: Option<Heredoc>,
}

#[derive(Debug)]
struct Heredoc {
    term: String,
    /// `<<-` / `<<~`: the terminator may be indented.
    indented_term: bool,
    /// `<<~`: strip the common indentation.
    squiggly: bool,
    indent: usize,
    at_line_start: bool,
    /// Where to continue on the tag's line once the body has been lexed.
    resume: usize,
}

/// The pieces of a heredoc tag, found by lookahead.
struct HeredocTag {
    term: String,
    interpolate: bool,
    squiggly: bool,
    dash: bool,
    /// Position just past the tag.
    end: usize,
}

pub struct Lexer<'src> {
    src: &'src str,
    bytes: &'src [u8],
    pos: usize,
    modes: Vec<Mode>,
    pending: VecDeque<Token>,
    /// Whether the previous token ended a value.
    prev_value: bool,
    /// The previous token if it was a plain identifier (a possible command
    /// call).
    prev_ident: Option<String>,
    /// Whether the previous token could be the name of a label (`name:`),
    /// in which case an adjacent `:` is a plain colon rather than the start
    /// of a symbol.
    prev_label_ok: bool,
    /// Tracks `def` / `def self.` so that the following token is lexed as a
    /// method name (`def /`, `def %`, `def <<`): 3 after `def`, 2 after
    /// `def self`, 1 after `def self.`, 0 otherwise.
    fname_state: u8,
    /// After lexing a heredoc body, the position just past its terminator;
    /// the newline that ends the tag's line jumps there.
    after_heredoc: Option<usize>,
    /// Where the body of the next heredoc on the current line starts.
    next_heredoc_body: Option<usize>,
    pub locals: LocalTable,
    diagnostics: Vec<Diagnostic>,
    comments: Vec<Span>,
    data_offset: Option<usize>,
}

/// Everything the lexer produced for a source text.
#[derive(Debug)]
pub struct Lexed {
    pub tokens: Vec<Token>,
    pub diagnostics: Vec<Diagnostic>,
    pub comments: Vec<Span>,
    /// Byte offset of the text after a `__END__` line, if any.
    pub data_offset: Option<usize>,
}

/// Lex a whole source text at once (with no local variable information).
pub fn tokenize(src: &str) -> Lexed {
    let mut lexer = Lexer::new(src);
    let mut tokens = Vec::new();
    loop {
        let tok = lexer.next_token();
        let eof = tok.kind.is_eof();
        tokens.push(tok);
        if eof {
            break;
        }
    }
    Lexed {
        tokens,
        diagnostics: lexer.diagnostics,
        comments: lexer.comments,
        data_offset: lexer.data_offset,
    }
}

fn is_ident_start(b: u8) -> bool {
    b == b'_' || b.is_ascii_alphabetic() || b >= 0x80
}

fn is_ident_char(b: u8) -> bool {
    b == b'_' || b.is_ascii_alphanumeric() || b >= 0x80
}

fn is_space(b: u8) -> bool {
    matches!(b, b' ' | b'\t' | b'\r' | b'\n')
}

fn is_percent_delim(b: u8) -> bool {
    !is_ident_char(b) && !is_space(b)
}

fn paired_delims(delim: u8) -> (Option<u8>, u8) {
    match delim {
        b'(' => (Some(b'('), b')'),
        b'[' => (Some(b'['), b']'),
        b'{' => (Some(b'{'), b'}'),
        b'<' => (Some(b'<'), b'>'),
        d => (None, d),
    }
}

/// Operator method names that may follow `:` to form a symbol, longest
/// first.
const OPERATOR_SYMBOLS: &[&str] = &[
    "[]=", "[]", "<=>", "===", "==", "=~", "!=", "!~", "**", "<<", ">>", "<=", ">=", "+@", "-@",
    "+", "-", "*", "/", "%", "<", ">", "&", "|", "^", "~", "!",
];

impl<'src> Lexer<'src> {
    pub fn new(src: &'src str) -> Lexer<'src> {
        Lexer {
            src,
            bytes: src.as_bytes(),
            pos: 0,
            modes: vec![Mode::Normal { depth: 0 }],
            pending: VecDeque::new(),
            prev_value: false,
            prev_ident: None,
            prev_label_ok: false,
            fname_state: 0,
            after_heredoc: None,
            next_heredoc_body: None,
            locals: LocalTable::default(),
            diagnostics: Vec::new(),
            comments: Vec::new(),
            data_offset: None,
        }
    }

    pub fn diagnostics(&self) -> &[Diagnostic] {
        &self.diagnostics
    }

    pub fn take_diagnostics(&mut self) -> Vec<Diagnostic> {
        std::mem::take(&mut self.diagnostics)
    }

    /// Spans of all comments seen so far.
    pub fn comments(&self) -> &[Span] {
        &self.comments
    }

    /// Byte offset of the text after a `__END__` line, once it has been
    /// reached.
    pub fn data_offset(&self) -> Option<usize> {
        self.data_offset
    }

    pub fn next_token(&mut self) -> Token {
        let tok = match self.pending.pop_front() {
            Some(tok) => tok,
            None => match self.modes.last() {
                Some(Mode::Str(_)) => self.lex_string(),
                _ => self.lex_normal(),
            },
        };
        self.prev_ident = match &tok.kind {
            TokenKind::Ident(name) => Some(name.clone()),
            _ => None,
        };
        self.prev_value = tok.kind.ends_value();
        self.prev_label_ok = matches!(
            tok.kind,
            TokenKind::Ident(_)
                | TokenKind::Const(_)
                | TokenKind::Keyword(_)
                | TokenKind::StringEnd { .. }
        );
        self.fname_state = match (&tok.kind, self.fname_state) {
            (TokenKind::Keyword(Keyword::Def), _) => 3,
            (TokenKind::Keyword(Keyword::SelfKw), 3) => 2,
            (TokenKind::Dot, 2) => 1,
            _ => 0,
        };
        tok
    }

    /// Whether the next token is in method-name position (`def` here).
    fn in_fname_position(&self) -> bool {
        matches!(self.fname_state, 3 | 1)
    }

    // ----- helpers ---------------------------------------------------------

    fn peek(&self) -> Option<u8> {
        self.bytes.get(self.pos).copied()
    }

    fn peek_at(&self, n: usize) -> Option<u8> {
        self.bytes.get(self.pos + n).copied()
    }

    fn at_eof(&self) -> bool {
        self.pos >= self.bytes.len()
    }

    fn error(&mut self, message: impl Into<String>, span: Span) {
        self.diagnostics.push(Diagnostic::error(message, span));
    }

    fn warning(&mut self, message: impl Into<String>, span: Span) {
        self.diagnostics.push(Diagnostic::warning(message, span));
    }

    fn in_interpolation(&self) -> bool {
        self.modes.len() > 1
    }

    fn str_state(&mut self) -> &mut StrState {
        match self.modes.last_mut() {
            Some(Mode::Str(st)) => st,
            _ => unreachable!("not in string mode"),
        }
    }

    /// Byte offset just past the end of the line containing `from`.
    fn line_end_after(&self, from: usize) -> usize {
        match self.bytes[from..].iter().position(|&b| b == b'\n') {
            Some(i) => from + i + 1,
            None => self.bytes.len(),
        }
    }

    /// Take the next character (UTF-8 aware) and append it to `buf`.
    fn take_char(&mut self, buf: &mut String) {
        let ch = self.src[self.pos..].chars().next().unwrap();
        buf.push(ch);
        self.pos += ch.len_utf8();
    }

    /// Whether `/`, `%` or `<<` at the current position starts a literal.
    /// `space_before` is whether whitespace precedes it; `op_len` is the
    /// length of the operator form.
    fn literal_allowed(&mut self, space_before: bool, op_len: usize) -> bool {
        if self.in_fname_position() {
            return false;
        }
        if !self.prev_value {
            return true;
        }
        self.command_argument_position(space_before, op_len)
    }

    /// `foo /re/`: an identifier that is not a known local variable,
    /// followed by a space, followed by an operator with no space after it,
    /// is read as a command call with an argument (with a warning, as in
    /// Ruby).
    fn command_argument_position(&mut self, space_before: bool, op_len: usize) -> bool {
        let Some(name) = &self.prev_ident else {
            return false;
        };
        if !space_before || self.locals.is_declared(name) {
            return false;
        }
        match self.peek_at(op_len) {
            Some(b) if !is_space(b) => {
                let span = Span::new(self.pos, self.pos + op_len);
                self.warning(
                    "ambiguous first argument; put parentheses or a space after the operator",
                    span,
                );
                true
            }
            _ => false,
        }
    }

    // ----- normal mode -----------------------------------------------------

    fn lex_normal(&mut self) -> Token {
        let mut space_before = false;
        let mut newline_at: Option<usize> = None;

        while let Some(b) = self.peek() {
            match b {
                b' ' | b'\t' | b'\r' => {
                    self.pos += 1;
                    space_before = true;
                }
                b'\\' if self.peek_at(1) == Some(b'\n') => {
                    self.pos += 2;
                    space_before = true;
                }
                b'\\' if self.peek_at(1) == Some(b'\r') && self.peek_at(2) == Some(b'\n') => {
                    self.pos += 3;
                    space_before = true;
                }
                b'#' => {
                    let start = self.pos;
                    let mut end = self.line_end_after(self.pos);
                    if end > start && self.bytes[end - 1] == b'\n' {
                        end -= 1;
                    }
                    self.comments.push(Span::new(start, end));
                    // Leave the newline for the arm below.
                    self.pos = end;
                }
                b'\n' => {
                    if newline_at.is_none() {
                        newline_at = Some(self.pos);
                    }
                    self.pos += 1;
                    space_before = true;
                    if !self.in_interpolation() {
                        if let Some(p) = self.after_heredoc.take() {
                            self.pos = p;
                        }
                        self.next_heredoc_body = None;
                    }
                }
                b';' => {
                    if newline_at.is_none() {
                        newline_at = Some(self.pos);
                    }
                    self.pos += 1;
                    space_before = true;
                }
                _ => break,
            }
        }

        if !self.in_interpolation() && self.at_line_start() && self.at_data_marker() {
            self.data_offset = Some(self.line_end_after(self.pos));
            self.pos = self.bytes.len();
        }

        if let Some(at) = newline_at {
            if !self.leading_dot_ahead() {
                return Token::new(TokenKind::Newline, Span::new(at, at + 1), false);
            }
        }

        if self.at_eof() {
            return Token::new(TokenKind::Eof, Span::empty(self.pos), space_before);
        }

        let start = self.pos;
        let b = self.bytes[start];
        let kind = match b {
            b'0'..=b'9' => self.lex_number(),
            b'"' => {
                self.pos += 1;
                self.push_str(StringKind::String, None, b'"', true)
            }
            b'\'' => {
                self.pos += 1;
                self.push_str(StringKind::String, None, b'\'', false)
            }
            b'`' => {
                self.pos += 1;
                self.error(
                    "backquote literals are not supported; use Process.run",
                    Span::new(start, self.pos),
                );
                TokenKind::Error
            }
            b'@' => self.lex_ivar(),
            b'$' => {
                self.pos += 1;
                while self.peek().is_some_and(is_ident_char) {
                    self.pos += 1;
                }
                self.error(
                    "global variables are not supported; use a constant holding an Atom",
                    Span::new(start, self.pos),
                );
                TokenKind::Error
            }
            b':' => self.lex_colon(space_before),
            b'%' => self.lex_percent(space_before),
            b'/' => {
                if self.literal_allowed(space_before, 1) {
                    self.pos += 1;
                    self.push_str(StringKind::Regexp, None, b'/', true)
                } else if self.peek_at(1) == Some(b'=') {
                    self.pos += 2;
                    TokenKind::OpAssign(OpAssign::Slash)
                } else {
                    self.pos += 1;
                    TokenKind::Slash
                }
            }
            b'<' => {
                if self.peek_at(1) == Some(b'<') {
                    if let Some(tag) = self.heredoc_tag_ahead() {
                        if self.literal_allowed(space_before, 2) {
                            return self.begin_heredoc(tag, space_before);
                        }
                    }
                }
                self.lex_lt()
            }
            b'{' => {
                if let Some(Mode::Normal { depth }) = self.modes.last_mut() {
                    *depth += 1;
                }
                self.pos += 1;
                TokenKind::LBrace
            }
            b'}' => {
                self.pos += 1;
                let nested = self.modes.len() > 1;
                match self.modes.last_mut() {
                    Some(Mode::Normal { depth }) if *depth > 0 => {
                        *depth -= 1;
                        TokenKind::RBrace
                    }
                    Some(Mode::Normal { .. }) if nested => {
                        self.modes.pop();
                        TokenKind::EmbExprEnd
                    }
                    _ => TokenKind::RBrace,
                }
            }
            _ if is_ident_start(b) => self.lex_ident(),
            _ => self.lex_operator(),
        };
        Token::new(kind, Span::new(start, self.pos), space_before)
    }

    fn at_line_start(&self) -> bool {
        self.pos == 0 || self.bytes[self.pos - 1] == b'\n'
    }

    fn at_data_marker(&self) -> bool {
        let rest = &self.bytes[self.pos..];
        rest.starts_with(b"__END__") && matches!(rest.get(7), None | Some(b'\n') | Some(b'\r'))
    }

    /// After a newline, a line starting with `.foo` or `&.foo` continues the
    /// previous expression (leading-dot method chain).
    fn leading_dot_ahead(&self) -> bool {
        match self.peek() {
            Some(b'.') => self.peek_at(1) != Some(b'.'),
            Some(b'&') => self.peek_at(1) == Some(b'.'),
            _ => false,
        }
    }

    fn lex_number(&mut self) -> TokenKind {
        let start = self.pos;
        let mut digits = String::new();
        let mut base = 10u8;
        let mut is_float = false;

        let prefix = if self.peek() == Some(b'0') {
            match self.peek_at(1) {
                Some(b'x' | b'X') => Some((16, 2)),
                Some(b'b' | b'B') => Some((2, 2)),
                Some(b'o' | b'O') => Some((8, 2)),
                Some(b'd' | b'D') => Some((10, 2)),
                Some(b'0'..=b'7' | b'_') => Some((8, 1)),
                _ => None,
            }
        } else {
            None
        };

        if let Some((b, skip)) = prefix {
            base = b;
            self.pos += skip;
            self.take_digits(&mut digits, base);
        } else {
            self.take_digits(&mut digits, 10);
            if self.peek() == Some(b'.') && self.peek_at(1).is_some_and(|c| c.is_ascii_digit()) {
                is_float = true;
                digits.push('.');
                self.pos += 1;
                self.take_digits(&mut digits, 10);
            }
            if matches!(self.peek(), Some(b'e' | b'E')) {
                let save = self.pos;
                let mut exp = String::from("e");
                self.pos += 1;
                if matches!(self.peek(), Some(b'+' | b'-')) {
                    exp.push(self.bytes[self.pos] as char);
                    self.pos += 1;
                }
                if self.peek().is_some_and(|c| c.is_ascii_digit()) {
                    self.take_digits(&mut exp, 10);
                    digits.push_str(&exp);
                    is_float = true;
                } else {
                    self.pos = save;
                }
            }
        }

        if digits.is_empty() {
            self.error("malformed numeric literal", Span::new(start, self.pos));
        }
        if self.peek().is_some_and(is_ident_char) {
            let bad_start = self.pos;
            while self.peek().is_some_and(is_ident_char) {
                self.pos += 1;
            }
            self.error(
                "trailing characters after numeric literal",
                Span::new(bad_start, self.pos),
            );
        }

        if is_float {
            TokenKind::Float(digits)
        } else {
            TokenKind::Int { digits, base }
        }
    }

    /// Consume digits of `base` (with `_` separators), appending them to
    /// `out` without the underscores.
    fn take_digits(&mut self, out: &mut String, base: u8) {
        let start = self.pos;
        while let Some(b) = self.peek() {
            if b == b'_' {
                let next_is_digit = self
                    .peek_at(1)
                    .is_some_and(|c| (c as char).is_digit(base as u32));
                if self.pos == start || !next_is_digit {
                    self.error(
                        "misplaced underscore in numeric literal",
                        Span::new(self.pos, self.pos + 1),
                    );
                }
                self.pos += 1;
            } else if (b as char).is_digit(base as u32) {
                out.push(b as char);
                self.pos += 1;
            } else if b.is_ascii_digit() {
                // e.g. `0b102`, `0o9`
                self.error(
                    format!("invalid digit '{}' for base {base} literal", b as char),
                    Span::new(self.pos, self.pos + 1),
                );
                self.pos += 1;
            } else {
                break;
            }
        }
    }

    fn lex_ivar(&mut self) -> TokenKind {
        let start = self.pos;
        self.pos += 1;
        if self.peek() == Some(b'@') {
            self.pos += 1;
            while self.peek().is_some_and(is_ident_char) {
                self.pos += 1;
            }
            self.error(
                "class variables are not supported; use a constant holding an Atom",
                Span::new(start, self.pos),
            );
            return TokenKind::Error;
        }
        if !self.peek().is_some_and(is_ident_start) {
            self.error(
                "expected an identifier after '@'",
                Span::new(start, self.pos),
            );
            return TokenKind::Error;
        }
        let name_start = self.pos;
        while self.peek().is_some_and(is_ident_char) {
            self.pos += 1;
        }
        TokenKind::IVar(self.src[name_start..self.pos].to_string())
    }

    /// Consume an identifier, including a trailing `?` or `!` when it is not
    /// the start of `!=` (so `foo!=bar` is `foo != bar`). With
    /// `allow_setter`, a trailing `=` is included too (`:name=`).
    fn take_ident(&mut self, allow_setter: bool) -> &'src str {
        let start = self.pos;
        let is_const = self.peek().is_some_and(|b| b.is_ascii_uppercase());
        while self.peek().is_some_and(is_ident_char) {
            self.pos += 1;
        }
        match self.peek() {
            // Constants never end in `?`/`!` (`String?` is a nilable type).
            Some(b'?' | b'!') if !is_const && self.peek_at(1) != Some(b'=') => self.pos += 1,
            Some(b'=') if allow_setter && !matches!(self.peek_at(1), Some(b'=' | b'~' | b'>')) => {
                self.pos += 1
            }
            _ => {}
        }
        &self.src[start..self.pos]
    }

    fn lex_ident(&mut self) -> TokenKind {
        let name = self.take_ident(false);
        if name.as_bytes()[0].is_ascii_uppercase() {
            return TokenKind::Const(name.to_string());
        }
        match Keyword::from_ident(name) {
            Some(kw) => TokenKind::Keyword(kw),
            None => TokenKind::Ident(name.to_string()),
        }
    }

    fn lex_colon(&mut self, space_before: bool) -> TokenKind {
        self.pos += 1;
        if self.peek() == Some(b':') {
            self.pos += 1;
            return TokenKind::ColonColon;
        }
        // `name:` / `"name":` is a label (decided by the parser), so the
        // colon must not swallow what follows as a symbol.
        if !space_before && self.prev_label_ok {
            return TokenKind::Colon;
        }
        match self.peek() {
            Some(b'"') => {
                self.pos += 1;
                self.push_str(StringKind::Symbol, None, b'"', true)
            }
            Some(b'\'') => {
                self.pos += 1;
                self.push_str(StringKind::Symbol, None, b'\'', false)
            }
            Some(b) if is_ident_start(b) => {
                let name = self.take_ident(true);
                TokenKind::Symbol(name.to_string())
            }
            _ => {
                let rest = &self.src[self.pos..];
                for op in OPERATOR_SYMBOLS {
                    if rest.starts_with(op) {
                        self.pos += op.len();
                        return TokenKind::Symbol(op.to_string());
                    }
                }
                TokenKind::Colon
            }
        }
    }

    fn lex_percent(&mut self, space_before: bool) -> TokenKind {
        if let Some((letter, delim)) = self.percent_literal_ahead() {
            if self.literal_allowed(space_before, 1) {
                return self.lex_percent_literal(letter, delim);
            }
        }
        self.pos += 1;
        if self.peek() == Some(b'=') {
            self.pos += 1;
            TokenKind::OpAssign(OpAssign::Percent)
        } else {
            TokenKind::Percent
        }
    }

    /// At `%`: the type letter (if any) and the delimiter of a percent
    /// literal, if the following text has that shape.
    fn percent_literal_ahead(&self) -> Option<(Option<u8>, u8)> {
        match (self.peek_at(1), self.peek_at(2)) {
            (Some(l @ (b'q' | b'Q' | b'w' | b'i' | b'r')), Some(d)) if is_percent_delim(d) => {
                Some((Some(l), d))
            }
            (Some(d), _) if is_percent_delim(d) && d != b'=' => Some((None, d)),
            _ => None,
        }
    }

    /// `%q(...)`, `%Q(...)`, `%(...)`, `%w[...]`, `%i[...]`, `%r{...}`.
    fn lex_percent_literal(&mut self, letter: Option<u8>, delim: u8) -> TokenKind {
        let start = self.pos;
        let (open, close) = paired_delims(delim);
        self.pos = start + if letter.is_some() { 3 } else { 2 };
        match letter {
            Some(b'w') => TokenKind::Words(self.lex_words(start, open, close)),
            Some(b'i') => TokenKind::Symbols(self.lex_words(start, open, close)),
            Some(b'q') => self.push_str(StringKind::String, open, close, false),
            Some(b'r') => self.push_str(StringKind::Regexp, open, close, true),
            _ => self.push_str(StringKind::String, open, close, true),
        }
    }

    fn lex_words(&mut self, start: usize, open: Option<u8>, close: u8) -> Vec<String> {
        let mut words = Vec::new();
        let mut word = String::new();
        let mut nesting = 0u32;
        loop {
            let Some(b) = self.peek() else {
                self.error("unterminated %w literal", Span::new(start, self.pos));
                break;
            };
            if is_space(b) {
                if !word.is_empty() {
                    words.push(std::mem::take(&mut word));
                }
                self.pos += 1;
            } else if b == close && nesting == 0 {
                self.pos += 1;
                break;
            } else if b == b'\\' {
                self.pos += 1;
                match self.peek() {
                    Some(c) if is_space(c) || c == b'\\' || c == close || Some(c) == open => {
                        word.push(c as char);
                        self.pos += 1;
                    }
                    _ => word.push('\\'),
                }
            } else {
                if b == close {
                    nesting -= 1;
                } else if Some(b) == open {
                    nesting += 1;
                }
                self.take_char(&mut word);
            }
        }
        if !word.is_empty() {
            words.push(word);
        }
        words
    }

    fn lex_lt(&mut self) -> TokenKind {
        match (self.peek_at(1), self.peek_at(2)) {
            (Some(b'<'), Some(b'=')) => {
                self.pos += 3;
                TokenKind::OpAssign(OpAssign::Shl)
            }
            (Some(b'<'), _) => {
                self.pos += 2;
                TokenKind::Shl
            }
            (Some(b'='), Some(b'>')) => {
                self.pos += 3;
                TokenKind::Cmp
            }
            (Some(b'='), _) => {
                self.pos += 2;
                TokenKind::LtEq
            }
            _ => {
                self.pos += 1;
                TokenKind::Lt
            }
        }
    }

    /// At `<<`: parse a heredoc tag (`<<~EOS`, `<<-'EOS'`, `<<"EOS"`,
    /// `<<EOS`) by lookahead, without consuming it.
    fn heredoc_tag_ahead(&self) -> Option<HeredocTag> {
        let mut p = self.pos + 2;
        let (mut squiggly, mut dash) = (false, false);
        match self.bytes.get(p) {
            Some(b'~') => {
                squiggly = true;
                p += 1;
            }
            Some(b'-') => {
                dash = true;
                p += 1;
            }
            _ => {}
        }
        let (term, interpolate) = match self.bytes.get(p) {
            Some(&q @ (b'"' | b'\'')) => {
                let name_start = p + 1;
                let mut e = name_start;
                while self.bytes.get(e).is_some_and(|&b| b != q && b != b'\n') {
                    e += 1;
                }
                if self.bytes.get(e) != Some(&q) || e == name_start {
                    return None;
                }
                p = e + 1;
                (self.src[name_start..e].to_string(), q == b'"')
            }
            Some(&b) if is_ident_start(b) => {
                let name_start = p;
                while self.bytes.get(p).is_some_and(|&b| is_ident_char(b)) {
                    p += 1;
                }
                (self.src[name_start..p].to_string(), true)
            }
            _ => return None,
        };
        Some(HeredocTag {
            term,
            interpolate,
            squiggly,
            dash,
            end: p,
        })
    }

    /// Set up the heredoc body as the current string mode and return the
    /// `StringBegin` token spanning the tag.
    fn begin_heredoc(&mut self, tag: HeredocTag, space_before: bool) -> Token {
        let start = self.pos;
        let tag_span = Span::new(start, tag.end);

        let inside_heredoc = self
            .modes
            .iter()
            .any(|m| matches!(m, Mode::Str(s) if s.heredoc.is_some()));
        if inside_heredoc {
            self.pos = tag.end;
            self.error(
                "a heredoc cannot start inside another heredoc's interpolation",
                tag_span,
            );
            return Token::new(TokenKind::Error, tag_span, space_before);
        }

        let body_start = self
            .next_heredoc_body
            .unwrap_or_else(|| self.line_end_after(tag.end));

        // Find the terminator and, for `<<~`, the common indentation.
        let indented_term = tag.squiggly || tag.dash;
        let mut line_start = body_start;
        let mut indent = usize::MAX;
        let mut body_end = None;
        while line_start < self.bytes.len() {
            let next = self.line_end_after(line_start);
            let line = self.src[line_start..next].trim_end_matches(['\n', '\r']);
            let candidate = if indented_term {
                line.trim_start()
            } else {
                line
            };
            if candidate == tag.term {
                body_end = Some(next);
                break;
            }
            if tag.squiggly && !line.trim().is_empty() {
                let ws = line.len() - line.trim_start_matches([' ', '\t']).len();
                indent = indent.min(ws);
            }
            line_start = next;
        }
        let Some(body_end) = body_end else {
            self.pos = tag.end;
            self.error(
                format!("unterminated heredoc; missing terminator \"{}\"", tag.term),
                tag_span,
            );
            return Token::new(TokenKind::Error, tag_span, space_before);
        };
        if indent == usize::MAX {
            indent = 0;
        }

        self.after_heredoc = Some(body_end);
        self.next_heredoc_body = Some(body_end);
        self.pos = body_start;
        self.modes.push(Mode::Str(StrState {
            kind: StringKind::String,
            open: None,
            close: 0,
            interpolate: tag.interpolate,
            nesting: 0,
            heredoc: Some(Heredoc {
                term: tag.term,
                indented_term,
                squiggly: tag.squiggly,
                indent,
                at_line_start: true,
                resume: tag.end,
            }),
        }));
        Token::new(
            TokenKind::StringBegin(StringKind::String),
            tag_span,
            space_before,
        )
    }

    fn push_str(
        &mut self,
        kind: StringKind,
        open: Option<u8>,
        close: u8,
        interpolate: bool,
    ) -> TokenKind {
        self.modes.push(Mode::Str(StrState {
            kind,
            open,
            close,
            interpolate,
            nesting: 0,
            heredoc: None,
        }));
        TokenKind::StringBegin(kind)
    }

    fn lex_operator(&mut self) -> TokenKind {
        use TokenKind::*;
        let b = self.bytes[self.pos];
        let n1 = self.peek_at(1);
        let n2 = self.peek_at(2);
        // Unary operator method names: `def -@`, `def +@`.
        if matches!(b, b'+' | b'-' | b'!' | b'~')
            && n1 == Some(b'@')
            && !n2.is_some_and(is_ident_char)
        {
            self.pos += 2;
            return Ident(format!("{}@", b as char));
        }
        let (kind, len) = match (b, n1, n2) {
            (b'+', Some(b'='), _) => (OpAssign(self::OpAssign::Plus), 2),
            (b'+', _, _) => (Plus, 1),
            (b'-', Some(b'='), _) => (OpAssign(self::OpAssign::Minus), 2),
            (b'-', Some(b'>'), _) => (Arrow, 2),
            (b'-', _, _) => (Minus, 1),
            (b'*', Some(b'*'), Some(b'=')) => (OpAssign(self::OpAssign::StarStar), 3),
            (b'*', Some(b'*'), _) => (StarStar, 2),
            (b'*', Some(b'='), _) => (OpAssign(self::OpAssign::Star), 2),
            (b'*', _, _) => (Star, 1),
            (b'=', Some(b'='), Some(b'=')) => (Eqq, 3),
            (b'=', Some(b'='), _) => (Eq, 2),
            (b'=', Some(b'~'), _) => (Match, 2),
            (b'=', Some(b'>'), _) => (FatArrow, 2),
            (b'=', _, _) => (Assign, 1),
            (b'!', Some(b'='), _) => (NotEq, 2),
            (b'!', Some(b'~'), _) => (NotMatch, 2),
            (b'!', _, _) => (Bang, 1),
            (b'>', Some(b'='), _) => (GtEq, 2),
            (b'>', Some(b'>'), Some(b'=')) => (OpAssign(self::OpAssign::Shr), 3),
            (b'>', Some(b'>'), _) => (Shr, 2),
            (b'>', _, _) => (Gt, 1),
            (b'&', Some(b'&'), Some(b'=')) => (OpAssign(self::OpAssign::AndAnd), 3),
            (b'&', Some(b'&'), _) => (AndAnd, 2),
            (b'&', Some(b'='), _) => (OpAssign(self::OpAssign::Amp), 2),
            (b'&', Some(b'.'), _) => (SafeNav, 2),
            (b'&', _, _) => (Amp, 1),
            (b'|', Some(b'|'), Some(b'=')) => (OpAssign(self::OpAssign::OrOr), 3),
            (b'|', Some(b'|'), _) => (OrOr, 2),
            (b'|', Some(b'='), _) => (OpAssign(self::OpAssign::Pipe), 2),
            (b'|', _, _) => (Pipe, 1),
            (b'^', Some(b'='), _) => (OpAssign(self::OpAssign::Caret), 2),
            (b'^', _, _) => (Caret, 1),
            (b'~', _, _) => (Tilde, 1),
            (b'.', Some(b'.'), Some(b'.')) => (DotDotDot, 3),
            (b'.', Some(b'.'), _) => (DotDot, 2),
            (b'.', Some(b':'), _) => (DotColon, 2),
            (b'.', _, _) => (Dot, 1),
            (b',', _, _) => (Comma, 1),
            (b'(', _, _) => (LParen, 1),
            (b')', _, _) => (RParen, 1),
            (b'[', _, _) => (LBracket, 1),
            (b']', _, _) => (RBracket, 1),
            (b'?', _, _) => (Question, 1),
            _ => {
                let ch = self.src[self.pos..].chars().next().unwrap();
                let span = Span::new(self.pos, self.pos + ch.len_utf8());
                self.error(format!("unexpected character {ch:?}"), span);
                (Error, ch.len_utf8())
            }
        };
        self.pos += len;
        kind
    }

    // ----- string mode -----------------------------------------------------

    fn lex_string(&mut self) -> Token {
        let st = self.str_state();
        let kind = st.kind;
        let open = st.open;
        let close = st.close;
        let interpolate = st.interpolate;
        let is_heredoc = st.heredoc.is_some();

        if is_heredoc {
            if let Some(tok) = self.heredoc_line_start() {
                return tok;
            }
        }

        let start = self.pos;
        let mut buf = String::new();
        loop {
            let Some(b) = self.peek() else {
                self.error("unterminated string literal", Span::empty(self.pos));
                self.modes.pop();
                let end = Token::new(
                    TokenKind::StringEnd {
                        flags: String::new(),
                    },
                    Span::empty(self.pos),
                    false,
                );
                if buf.is_empty() {
                    return end;
                }
                self.pending.push_back(end);
                return Token::new(
                    TokenKind::StringContent(buf),
                    Span::new(start, self.pos),
                    false,
                );
            };

            if is_heredoc && b == b'\n' {
                buf.push('\n');
                self.pos += 1;
                self.str_state().heredoc.as_mut().unwrap().at_line_start = true;
                return Token::new(
                    TokenKind::StringContent(buf),
                    Span::new(start, self.pos),
                    false,
                );
            }

            if !is_heredoc {
                if b == close {
                    if self.str_state().nesting > 0 {
                        self.str_state().nesting -= 1;
                        buf.push(b as char);
                        self.pos += 1;
                        continue;
                    }
                    if !buf.is_empty() {
                        // Return the content now; the next call sees the
                        // delimiter with an empty buffer and closes.
                        return Token::new(
                            TokenKind::StringContent(buf),
                            Span::new(start, self.pos),
                            false,
                        );
                    }
                    let close_start = self.pos;
                    self.pos += 1;
                    let mut flags = String::new();
                    if kind == StringKind::Regexp {
                        while self.peek().is_some_and(|c| c.is_ascii_alphabetic()) {
                            flags.push(self.bytes[self.pos] as char);
                            self.pos += 1;
                        }
                    }
                    self.modes.pop();
                    return Token::new(
                        TokenKind::StringEnd { flags },
                        Span::new(close_start, self.pos),
                        false,
                    );
                }
                if Some(b) == open {
                    self.str_state().nesting += 1;
                    buf.push(b as char);
                    self.pos += 1;
                    continue;
                }
            }

            if b == b'#' && interpolate && self.peek_at(1) == Some(b'{') {
                if !buf.is_empty() {
                    return Token::new(
                        TokenKind::StringContent(buf),
                        Span::new(start, self.pos),
                        false,
                    );
                }
                let begin = self.pos;
                self.pos += 2;
                self.modes.push(Mode::Normal { depth: 0 });
                return Token::new(TokenKind::EmbExprBegin, Span::new(begin, self.pos), false);
            }

            if b == b'\\' {
                self.lex_escape(&mut buf, kind, interpolate, is_heredoc, open, close);
                continue;
            }

            self.take_char(&mut buf);
        }
    }

    /// In heredoc mode at the start of a line: close the heredoc if this is
    /// the terminator line, otherwise strip the `<<~` indentation.
    fn heredoc_line_start(&mut self) -> Option<Token> {
        let line_end = self.line_end_after(self.pos);
        let line = &self.src[self.pos..line_end];
        let line = line.trim_end_matches(['\n', '\r']);
        let line_len = line.len();

        let h = self.str_state().heredoc.as_mut().unwrap();
        if !h.at_line_start {
            return None;
        }
        h.at_line_start = false;
        let candidate = if h.indented_term {
            line.trim_start()
        } else {
            line
        };
        if candidate == h.term {
            let resume = h.resume;
            let span = Span::new(self.pos, self.pos + line_len);
            self.modes.pop();
            self.pos = resume;
            return Some(Token::new(
                TokenKind::StringEnd {
                    flags: String::new(),
                },
                span,
                false,
            ));
        }
        if h.squiggly {
            let indent = h.indent;
            let mut stripped = 0;
            while stripped < indent && matches!(self.peek(), Some(b' ' | b'\t')) {
                self.pos += 1;
                stripped += 1;
            }
        }
        None
    }

    /// At a backslash inside a string literal.
    fn lex_escape(
        &mut self,
        buf: &mut String,
        kind: StringKind,
        interpolate: bool,
        is_heredoc: bool,
        open: Option<u8>,
        close: u8,
    ) {
        let start = self.pos;
        let Some(n) = self.peek_at(1) else {
            buf.push('\\');
            self.pos += 1;
            return;
        };

        // Regexps keep their escapes for the regexp engine, except for the
        // delimiter itself.
        if kind == StringKind::Regexp {
            if n == close || Some(n) == open {
                buf.push(n as char);
                self.pos += 2;
            } else {
                buf.push('\\');
                self.pos += 1;
                self.take_char(buf);
            }
            return;
        }

        if !interpolate {
            if !is_heredoc && (n == b'\\' || n == close || Some(n) == open) {
                buf.push(n as char);
                self.pos += 2;
            } else {
                buf.push('\\');
                self.pos += 1;
            }
            return;
        }

        self.pos += 2;
        match n {
            b'n' => buf.push('\n'),
            b't' => buf.push('\t'),
            b'r' => buf.push('\r'),
            b's' => buf.push(' '),
            b'a' => buf.push('\x07'),
            b'b' => buf.push('\x08'),
            b'e' => buf.push('\x1b'),
            b'f' => buf.push('\x0c'),
            b'v' => buf.push('\x0b'),
            b'\n' => {}
            b'\r' if self.peek() == Some(b'\n') => self.pos += 1,
            b'x' => {
                let value = self.take_hex(2);
                self.push_byte_escape(buf, value, start);
            }
            b'0'..=b'7' => {
                self.pos -= 1;
                let mut value = 0u32;
                let mut count = 0;
                while count < 3 && matches!(self.peek(), Some(b'0'..=b'7')) {
                    value = value * 8 + (self.bytes[self.pos] - b'0') as u32;
                    self.pos += 1;
                    count += 1;
                }
                self.push_byte_escape(buf, Some(value), start);
            }
            b'u' => self.lex_unicode_escape(buf, start, close),
            _ => {
                // `\"`, `\\`, `\#`, `\'` and any other character stand for
                // themselves.
                self.pos -= 1;
                self.take_char(buf);
            }
        }
    }

    fn lex_unicode_escape(&mut self, buf: &mut String, start: usize, close: u8) {
        if self.peek() != Some(b'{') {
            match self.take_hex_exact(4).and_then(char::from_u32) {
                Some(c) => buf.push(c),
                None => {
                    self.error("invalid Unicode escape", Span::new(start, self.pos));
                    buf.push('\u{FFFD}');
                }
            }
            return;
        }
        self.pos += 1;
        loop {
            while self.peek() == Some(b' ') {
                self.pos += 1;
            }
            if self.peek() == Some(b'}') {
                self.pos += 1;
                return;
            }
            match self.take_hex(6).and_then(char::from_u32) {
                Some(c) => buf.push(c),
                None => {
                    self.error("invalid Unicode escape", Span::new(start, self.pos));
                    buf.push('\u{FFFD}');
                    while self
                        .peek()
                        .is_some_and(|c| c != b'}' && c != close && c != b'\n')
                    {
                        self.pos += 1;
                    }
                    if self.peek() == Some(b'}') {
                        self.pos += 1;
                    }
                    return;
                }
            }
        }
    }

    fn push_byte_escape(&mut self, buf: &mut String, value: Option<u32>, start: usize) {
        match value {
            Some(v) if v < 0x80 => buf.push(v as u8 as char),
            Some(_) => {
                self.error(
                    "byte escapes above \\x7f are not allowed in strings; use \\u for characters or a Bytes literal",
                    Span::new(start, self.pos),
                );
                buf.push('\u{FFFD}');
            }
            None => {
                self.error("invalid escape sequence", Span::new(start, self.pos));
                buf.push('\u{FFFD}');
            }
        }
    }

    /// Up to `max` hex digits (at least one).
    fn take_hex(&mut self, max: usize) -> Option<u32> {
        let mut value = 0u32;
        let mut count = 0;
        while count < max && self.peek().is_some_and(|c| c.is_ascii_hexdigit()) {
            value = value * 16 + (self.bytes[self.pos] as char).to_digit(16).unwrap();
            self.pos += 1;
            count += 1;
        }
        (count > 0).then_some(value)
    }

    fn take_hex_exact(&mut self, n: usize) -> Option<u32> {
        let save = self.pos;
        let mut value = 0u32;
        for _ in 0..n {
            match self.peek() {
                Some(c) if c.is_ascii_hexdigit() => {
                    value = value * 16 + (c as char).to_digit(16).unwrap();
                    self.pos += 1;
                }
                _ => {
                    self.pos = save;
                    return None;
                }
            }
        }
        Some(value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::token::Keyword as K;
    use crate::token::OpAssign as Op;
    use crate::token::TokenKind::*;

    fn kinds(src: &str) -> Vec<TokenKind> {
        let lexed = tokenize(src);
        let errors: Vec<_> = lexed.diagnostics.iter().filter(|d| d.is_error()).collect();
        assert!(
            errors.is_empty(),
            "unexpected errors for {src:?}: {errors:?}"
        );
        lexed.tokens.into_iter().map(|t| t.kind).collect()
    }

    fn errors(src: &str) -> Vec<String> {
        tokenize(src)
            .diagnostics
            .into_iter()
            .filter(|d| d.is_error())
            .map(|d| d.message)
            .collect()
    }

    fn ident(s: &str) -> TokenKind {
        Ident(s.to_string())
    }

    fn int(s: &str) -> TokenKind {
        Int {
            digits: s.to_string(),
            base: 10,
        }
    }

    fn content(s: &str) -> TokenKind {
        StringContent(s.to_string())
    }

    fn str_end() -> TokenKind {
        StringEnd {
            flags: String::new(),
        }
    }

    #[test]
    fn simple_expression() {
        assert_eq!(
            kinds("x = 1 + 2.5"),
            vec![ident("x"), Assign, int("1"), Plus, Float("2.5".into()), Eof]
        );
    }

    #[test]
    fn identifiers_keywords_constants() {
        assert_eq!(
            kinds("def empty? self.foo! Foo::Bar @ivar nil data"),
            vec![
                Keyword(K::Def),
                ident("empty?"),
                Keyword(K::SelfKw),
                Dot,
                ident("foo!"),
                Const("Foo".into()),
                ColonColon,
                Const("Bar".into()),
                IVar("ivar".into()),
                Keyword(K::Nil),
                ident("data"),
                Eof
            ]
        );
        assert_eq!(kinds("a!=b"), vec![ident("a"), NotEq, ident("b"), Eof]);
        assert_eq!(kinds("__FILE__"), vec![Keyword(K::File), Eof]);
    }

    #[test]
    fn numbers() {
        assert_eq!(
            kinds("1_000 0xff 0b1010 0o755 0755 1e3 1.5e-3 1.times 1..2"),
            vec![
                int("1000"),
                Int {
                    digits: "ff".into(),
                    base: 16
                },
                Int {
                    digits: "1010".into(),
                    base: 2
                },
                Int {
                    digits: "755".into(),
                    base: 8
                },
                Int {
                    digits: "755".into(),
                    base: 8
                },
                Float("1e3".into()),
                Float("1.5e-3".into()),
                int("1"),
                Dot,
                ident("times"),
                int("1"),
                DotDot,
                int("2"),
                Eof
            ]
        );
        assert!(!errors("1abc").is_empty());
        assert!(!errors("0b102").is_empty());
        assert!(!errors("1__0").is_empty());
    }

    #[test]
    fn strings_and_escapes() {
        assert_eq!(
            kinds(r##""a\tb\u00e9\u{1F600 41}" 'it\'s \n' "" "##),
            vec![
                StringBegin(StringKind::String),
                content("a\tb\u{e9}\u{1F600}A"),
                str_end(),
                StringBegin(StringKind::String),
                content("it's \\n"),
                str_end(),
                StringBegin(StringKind::String),
                str_end(),
                Eof
            ]
        );
    }

    #[test]
    fn interpolation() {
        assert_eq!(
            kinds(r##""a#{b}c#{ "x#{y}" }""##),
            vec![
                StringBegin(StringKind::String),
                content("a"),
                EmbExprBegin,
                ident("b"),
                EmbExprEnd,
                content("c"),
                EmbExprBegin,
                StringBegin(StringKind::String),
                content("x"),
                EmbExprBegin,
                ident("y"),
                EmbExprEnd,
                str_end(),
                EmbExprEnd,
                str_end(),
                Eof
            ]
        );
        // Braces inside an interpolation do not end it.
        assert_eq!(
            kinds(r##""#{ {a: 1}[:a] } #{ xs.map { |x| x } }""##),
            vec![
                StringBegin(StringKind::String),
                EmbExprBegin,
                LBrace,
                ident("a"),
                Colon,
                int("1"),
                RBrace,
                LBracket,
                Symbol("a".into()),
                RBracket,
                EmbExprEnd,
                content(" "),
                EmbExprBegin,
                ident("xs"),
                Dot,
                ident("map"),
                LBrace,
                Pipe,
                ident("x"),
                Pipe,
                ident("x"),
                RBrace,
                EmbExprEnd,
                str_end(),
                Eof
            ]
        );
    }

    #[test]
    fn symbols() {
        assert_eq!(
            kinds(r##":foo :bar? :baz= :[]= :<=> :+ :"a b" :'c' a ? b : c"##),
            vec![
                Symbol("foo".into()),
                Symbol("bar?".into()),
                Symbol("baz=".into()),
                Symbol("[]=".into()),
                Symbol("<=>".into()),
                Symbol("+".into()),
                StringBegin(StringKind::Symbol),
                content("a b"),
                str_end(),
                StringBegin(StringKind::Symbol),
                content("c"),
                str_end(),
                ident("a"),
                Question,
                ident("b"),
                Colon,
                ident("c"),
                Eof
            ]
        );
    }

    #[test]
    fn labels_are_adjacent_ident_and_colon() {
        let lexed = tokenize("f(a: 1, b:c)");
        let t = &lexed.tokens;
        assert_eq!(t[2].kind, ident("a"));
        assert_eq!(t[3].kind, Colon);
        assert_eq!(t[2].span.end, t[3].span.start);
        assert!(!t[3].space_before);
        assert_eq!(t[6].kind, ident("b"));
        assert_eq!(t[7].kind, Colon);
        assert_eq!(t[8].kind, ident("c"));
        assert_eq!(
            kinds("{ if: 1, \"s\": 2 }"),
            vec![
                LBrace,
                Keyword(K::If),
                Colon,
                int("1"),
                Comma,
                StringBegin(StringKind::String),
                content("s"),
                str_end(),
                Colon,
                int("2"),
                RBrace,
                Eof
            ]
        );
        // With a space it is a symbol, as in Ruby.
        assert_eq!(
            kinds("a ? b :c"),
            vec![ident("a"), Question, ident("b"), Symbol("c".into()), Eof]
        );
    }

    #[test]
    fn regexp_versus_division() {
        assert_eq!(
            kinds("x = /a\\/b/i"),
            vec![
                ident("x"),
                Assign,
                StringBegin(StringKind::Regexp),
                content("a/b"),
                StringEnd { flags: "i".into() },
                Eof
            ]
        );
        assert_eq!(kinds("a / b"), vec![ident("a"), Slash, ident("b"), Eof]);
        assert_eq!(
            kinds("(a) /b/"),
            vec![LParen, ident("a"), RParen, Slash, ident("b"), Slash, Eof]
        );
        let mut lexer = Lexer::new("a /= 2");
        lexer.locals.declare("a");
        assert_eq!(lexer.next_token().kind, ident("a"));
        assert_eq!(lexer.next_token().kind, TokenKind::OpAssign(Op::Slash));
        assert_eq!(
            kinds("if /re/ then end"),
            vec![
                Keyword(K::If),
                StringBegin(StringKind::Regexp),
                content("re"),
                str_end(),
                Keyword(K::Then),
                Keyword(K::End),
                Eof
            ]
        );
        // Command call with a regexp argument: a warning, but a regexp.
        let lexed = tokenize("puts /re/");
        assert_eq!(lexed.tokens[1].kind, StringBegin(StringKind::Regexp));
        assert_eq!(lexed.diagnostics.len(), 1);
        assert!(!lexed.diagnostics[0].is_error());

        // ...unless the identifier is a known local variable.
        let mut lexer = Lexer::new("x /2");
        lexer.locals.declare("x");
        assert_eq!(lexer.next_token().kind, ident("x"));
        assert_eq!(lexer.next_token().kind, Slash);
        assert_eq!(lexer.next_token().kind, int("2"));
    }

    #[test]
    fn percent_literals() {
        assert_eq!(
            kinds("%w[a b\\ c (d)]\n%i(x y)"),
            vec![
                Words(vec!["a".into(), "b c".into(), "(d)".into()]),
                Newline,
                Symbols(vec!["x".into(), "y".into()]),
                Eof
            ]
        );
        assert_eq!(
            kinds("%q(a(b)c)\n%(x#{y})\n%r{a/b}m"),
            vec![
                StringBegin(StringKind::String),
                content("a(b)c"),
                str_end(),
                Newline,
                StringBegin(StringKind::String),
                content("x"),
                EmbExprBegin,
                ident("y"),
                EmbExprEnd,
                str_end(),
                Newline,
                StringBegin(StringKind::Regexp),
                content("a/b"),
                StringEnd { flags: "m".into() },
                Eof
            ]
        );
        assert_eq!(kinds("x % 3"), vec![ident("x"), Percent, int("3"), Eof]);
        assert_eq!(
            kinds("x %= 3"),
            vec![ident("x"), TokenKind::OpAssign(Op::Percent), int("3"), Eof]
        );
        assert_eq!(kinds("x%w"), vec![ident("x"), Percent, ident("w"), Eof]);
    }

    #[test]
    fn heredocs() {
        let src = "x = <<~EOS.upcase\n    a #{b}\n      c\n  EOS\ny\n";
        assert_eq!(
            kinds(src),
            vec![
                ident("x"),
                Assign,
                StringBegin(StringKind::String),
                content("a "),
                EmbExprBegin,
                ident("b"),
                EmbExprEnd,
                content("\n"),
                content("  c\n"),
                str_end(),
                Dot,
                ident("upcase"),
                Newline,
                ident("y"),
                Newline,
                Eof
            ]
        );
        // Two heredocs on one line, one of them single-quoted.
        let src = "f(<<-A, <<~'B')\n  one\\n\n  A\n  two #{x}\nB\nz\n";
        assert_eq!(
            kinds(src),
            vec![
                ident("f"),
                LParen,
                StringBegin(StringKind::String),
                content("  one\n\n"),
                str_end(),
                Comma,
                StringBegin(StringKind::String),
                content("two #{x}\n"),
                str_end(),
                RParen,
                Newline,
                ident("z"),
                Newline,
                Eof
            ]
        );
        assert!(!errors("x = <<~EOS\nnever closed\n").is_empty());
        // `<<` after a value is a shift.
        assert_eq!(kinds("a << b"), vec![ident("a"), Shl, ident("b"), Eof]);
        assert_eq!(
            kinds("a <<= 1"),
            vec![ident("a"), TokenKind::OpAssign(Op::Shl), int("1"), Eof]
        );
    }

    #[test]
    fn newlines_comments_and_continuations() {
        let src = "a # comment\n\n  # another\nb\n  .c\n  &.d;e \\\n f\n";
        let lexed = tokenize(src);
        let kinds: Vec<_> = lexed.tokens.iter().map(|t| t.kind.clone()).collect();
        assert_eq!(
            kinds,
            vec![
                ident("a"),
                Newline,
                ident("b"),
                Dot,
                ident("c"),
                SafeNav,
                ident("d"),
                Newline,
                ident("e"),
                ident("f"),
                Newline,
                Eof
            ]
        );
        assert_eq!(lexed.comments.len(), 2);
        assert_eq!(
            &src[lexed.comments[0].start as usize..lexed.comments[0].end as usize],
            "# comment"
        );
        // A range at the start of a line is not a leading dot.
        assert_eq!(
            kinds_of("a\n..b"),
            vec![ident("a"), Newline, DotDot, ident("b"), Eof]
        );
    }

    fn kinds_of(src: &str) -> Vec<TokenKind> {
        kinds(src)
    }

    #[test]
    fn operators() {
        assert_eq!(
            kinds("a ** b <=> c === d =~ e !~ f &&= g ||= h -> i => j .: k &. l ... m"),
            vec![
                ident("a"),
                StarStar,
                ident("b"),
                Cmp,
                ident("c"),
                Eqq,
                ident("d"),
                Match,
                ident("e"),
                NotMatch,
                ident("f"),
                TokenKind::OpAssign(Op::AndAnd),
                ident("g"),
                TokenKind::OpAssign(Op::OrOr),
                ident("h"),
                Arrow,
                ident("i"),
                FatArrow,
                ident("j"),
                DotColon,
                ident("k"),
                SafeNav,
                ident("l"),
                DotDotDot,
                ident("m"),
                Eof
            ]
        );
    }

    #[test]
    fn space_before_is_recorded() {
        let lexed = tokenize("foo -x\nfoo - x\nfoo-x");
        let t = &lexed.tokens;
        assert!(t[1].space_before && !t[2].space_before); // foo -x
        assert!(t[5].space_before && t[6].space_before); // foo - x
        assert!(!t[9].space_before && !t[10].space_before); // foo-x
    }

    #[test]
    fn data_section() {
        let lexed = tokenize("a\n__END__\nraw data\n");
        let kinds: Vec<_> = lexed.tokens.iter().map(|t| t.kind.clone()).collect();
        assert_eq!(kinds, vec![ident("a"), Newline, Eof]);
        assert_eq!(lexed.data_offset, Some(10));
    }

    #[test]
    fn unsupported_syntax_is_reported() {
        assert_eq!(errors("$stdout").len(), 1);
        assert_eq!(errors("@@count").len(), 1);
        assert_eq!(errors("`ls`").len(), 2);
        assert_eq!(errors("\"unterminated").len(), 1);
        assert_eq!(errors("\"\\xff\"").len(), 1);
        assert_eq!(errors("\u{1}").len(), 1);
    }

    #[test]
    fn unicode_identifiers() {
        assert_eq!(
            kinds("名前 = 1"),
            vec![ident("名前"), Assign, int("1"), Eof]
        );
        assert_eq!(kinds("§"), vec![ident("§"), Eof]);
    }
}
