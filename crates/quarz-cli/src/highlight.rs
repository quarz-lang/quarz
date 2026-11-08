//! Syntax highlighting: the text's tokens, from the lexer, classed
//! (`Class`), in ANSI colors for the REPL (an unfinished input, an open
//! string or a missing `end`, is highlighted as far as it goes) and in
//! HTML spans for `quarz doc` (`html`).

use quarz_syntax::{tokenize, Keyword, StringKind, TokenKind};

/// What a token is, for its color.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Class {
    Keyword,
    /// `nil`, `true`, `false`, `self` and the like.
    Literal,
    Number,
    /// A string, with its interpolations' delimiters.
    String,
    Regexp,
    Symbol,
    /// A constant: a class, module or type name.
    Constant,
    /// An `@field`.
    IVar,
    Comment,
    /// A local name or a method's (HTML only).
    Ident,
    /// An operator or punctuation (HTML only).
    Op,
}

impl Class {
    /// Its ANSI color, if the REPL colors it.
    fn ansi(self) -> Option<&'static str> {
        Some(match self {
            Class::Keyword => "35",
            Class::Literal => "1;36",
            Class::Number => "36",
            Class::String => "32",
            Class::Regexp => "31",
            Class::Symbol => "33",
            Class::Constant => "1;34",
            Class::IVar => "34",
            Class::Comment => "90",
            Class::Ident | Class::Op => return None,
        })
    }

    /// Its HTML class (`quarz doc`'s style sheet).
    pub fn css(self) -> &'static str {
        match self {
            Class::Keyword => "k",
            Class::Literal => "l",
            Class::Number => "n",
            Class::String => "s",
            Class::Regexp => "r",
            Class::Symbol => "y",
            Class::Constant => "t",
            Class::IVar => "v",
            Class::Comment => "c",
            Class::Ident => "i",
            Class::Op => "o",
        }
    }
}

fn string_class(kind: StringKind) -> Class {
    match kind {
        StringKind::String | StringKind::Bytes => Class::String,
        StringKind::Symbol => Class::Symbol,
        StringKind::Regexp => Class::Regexp,
    }
}

/// `src` with ANSI color escapes around its tokens.
pub fn highlight(src: &str) -> String {
    let mut out = String::with_capacity(src.len() * 2);
    let mut at = 0;
    for (start, end, class) in spans(&tokenize(src), src) {
        let Some(color) = class.ansi() else {
            continue;
        };
        out.push_str(&src[at..start]);
        out.push_str("\x1b[");
        out.push_str(color);
        out.push('m');
        out.push_str(&src[start..end]);
        out.push_str("\x1b[0m");
        at = end;
    }
    out.push_str(&src[at..]);
    out
}

/// `src` as HTML (escaped), each token in a `<span class="...">`
/// (`Class::css`); `None` when the lexer reports an error (a fragment,
/// an example of an error), to show as plain text.
pub fn html(src: &str) -> Option<String> {
    let lexed = tokenize(src);
    if !lexed.diagnostics.is_empty() {
        return None;
    }
    let mut out = String::with_capacity(src.len() * 3);
    let mut at = 0;
    for (start, end, class) in spans(&lexed, src) {
        escape_into(&mut out, &src[at..start]);
        out.push_str("<span class=\"");
        out.push_str(class.css());
        out.push_str("\">");
        escape_into(&mut out, &src[start..end]);
        out.push_str("</span>");
        at = end;
    }
    escape_into(&mut out, &src[at..]);
    Some(out)
}

fn escape_into(out: &mut String, s: &str) {
    for c in s.chars() {
        match c {
            '&' => out.push_str("&amp;"),
            '<' => out.push_str("&lt;"),
            '>' => out.push_str("&gt;"),
            '"' => out.push_str("&quot;"),
            c => out.push(c),
        }
    }
}

/// The classed ranges of `src`, in order, not overlapping, on character
/// boundaries; neighbours of one class merged.
fn spans(lexed: &quarz_syntax::Lexed, src: &str) -> Vec<(usize, usize, Class)> {
    // The colored ranges, in order: tokens and comments do not overlap.
    let mut spans: Vec<(usize, usize, Class)> = Vec::new();
    // The colors of the string literals being read (an interpolation's
    // tokens get their own colors, the literal's go on after it).
    let mut strings: Vec<Class> = Vec::new();
    // For each open `[`, whether it may be a type parameter list (right
    // after a name), where `T<:Shape` is `<:` and a constant, not `<`
    // and a symbol.
    let mut brackets: Vec<bool> = Vec::new();
    let toks = &lexed.tokens;
    for (i, tok) in toks.iter().enumerate() {
        let prev = |n: usize| i.checked_sub(n).map(|j| &toks[j]);
        match &tok.kind {
            TokenKind::LBracket => brackets.push(
                !tok.space_before
                    && prev(1).is_some_and(|p| {
                        matches!(p.kind, TokenKind::Const(_) | TokenKind::Ident(_))
                    }),
            ),
            TokenKind::RBracket => {
                brackets.pop();
            }
            TokenKind::Symbol(name)
                if brackets.last() == Some(&true)
                    && !tok.space_before
                    && name.starts_with(|c: char| c.is_ascii_uppercase())
                    && prev(1).is_some_and(|p| matches!(p.kind, TokenKind::Lt | TokenKind::Gt))
                    && prev(2).is_some_and(|p| matches!(p.kind, TokenKind::Const(_))) =>
            {
                spans.push((
                    tok.span.start as usize,
                    tok.span.start as usize + 1,
                    Class::Op,
                ));
                spans.push((
                    tok.span.start as usize + 1,
                    tok.span.end as usize,
                    Class::Constant,
                ));
                continue;
            }
            _ => {}
        }
        let class = match &tok.kind {
            TokenKind::Keyword(k) => match k {
                Keyword::Nil
                | Keyword::True
                | Keyword::False
                | Keyword::SelfKw
                | Keyword::File
                | Keyword::Line
                | Keyword::Method => Some(Class::Literal),
                _ => Some(Class::Keyword),
            },
            TokenKind::Int { .. } | TokenKind::Float(_) => Some(Class::Number),
            TokenKind::Symbol(_) | TokenKind::Symbols(_) => Some(Class::Symbol),
            TokenKind::Words(_) => Some(Class::String),
            TokenKind::Const(_) => Some(Class::Constant),
            TokenKind::IVar(_) => Some(Class::IVar),
            TokenKind::Ident(_) => Some(Class::Ident),
            TokenKind::StringBegin(kind) => {
                strings.push(string_class(*kind));
                strings.last().copied()
            }
            TokenKind::StringContent(_) | TokenKind::EmbExprBegin | TokenKind::EmbExprEnd => {
                strings.last().copied()
            }
            TokenKind::StringEnd { .. } => strings.pop(),
            TokenKind::Newline | TokenKind::Eof => None,
            _ => Some(Class::Op),
        };
        if let Some(class) = class {
            spans.push((tok.span.start as usize, tok.span.end as usize, class));
        }
    }
    for c in &lexed.comments {
        spans.push((c.start as usize, c.end as usize, Class::Comment));
    }
    spans.sort_by_key(|s| s.0);
    // One span for neighbours of one class (`"`, `n=`, `"`).
    let mut merged: Vec<(usize, usize, Class)> = Vec::new();
    let mut at = 0;
    for (start, end, class) in spans {
        let (start, end) = (start.max(at).min(src.len()), end.min(src.len()));
        if start >= end || !src.is_char_boundary(start) || !src.is_char_boundary(end) {
            continue;
        }
        match merged.last_mut() {
            Some(last) if last.1 == start && last.2 == class => last.1 = end,
            _ => merged.push((start, end, class)),
        }
        at = end;
    }
    merged
}
