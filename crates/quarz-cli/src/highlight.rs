//! Syntax highlighting for the REPL: the text's tokens, from the lexer,
//! in ANSI colors. An unfinished input (an open string, a missing `end`)
//! is highlighted as far as it goes.

use quarz_syntax::{tokenize, Keyword, StringKind, TokenKind};

const KEYWORD: &str = "35";
/// `nil`, `true`, `false`, `self` and the like.
const LITERAL: &str = "1;36";
const NUMBER: &str = "36";
const STRING: &str = "32";
const REGEXP: &str = "31";
const SYMBOL: &str = "33";
const CONSTANT: &str = "1;34";
const IVAR: &str = "34";
const COMMENT: &str = "90";

fn string_color(kind: StringKind) -> &'static str {
    match kind {
        StringKind::String | StringKind::Bytes => STRING,
        StringKind::Symbol => SYMBOL,
        StringKind::Regexp => REGEXP,
    }
}

/// `src` with ANSI color escapes around its tokens.
pub fn highlight(src: &str) -> String {
    let lexed = tokenize(src);
    // The colored ranges, in order: tokens and comments do not overlap.
    let mut spans: Vec<(usize, usize, &str)> = Vec::new();
    // The colors of the string literals being read (an interpolation's
    // tokens get their own colors, the literal's go on after it).
    let mut strings: Vec<&str> = Vec::new();
    for tok in &lexed.tokens {
        let color = match &tok.kind {
            TokenKind::Keyword(k) => match k {
                Keyword::Nil
                | Keyword::True
                | Keyword::False
                | Keyword::SelfKw
                | Keyword::File
                | Keyword::Line
                | Keyword::Method => Some(LITERAL),
                _ => Some(KEYWORD),
            },
            TokenKind::Int { .. } | TokenKind::Float(_) => Some(NUMBER),
            TokenKind::Symbol(_) | TokenKind::Symbols(_) => Some(SYMBOL),
            TokenKind::Words(_) => Some(STRING),
            TokenKind::Const(_) => Some(CONSTANT),
            TokenKind::IVar(_) => Some(IVAR),
            TokenKind::StringBegin(kind) => {
                strings.push(string_color(*kind));
                strings.last().copied()
            }
            TokenKind::StringContent(_) | TokenKind::EmbExprBegin | TokenKind::EmbExprEnd => {
                strings.last().copied()
            }
            TokenKind::StringEnd { .. } => strings.pop(),
            _ => None,
        };
        if let Some(color) = color {
            spans.push((tok.span.start as usize, tok.span.end as usize, color));
        }
    }
    for c in &lexed.comments {
        spans.push((c.start as usize, c.end as usize, COMMENT));
    }
    spans.sort_by_key(|s| s.0);
    // One escape for neighbours of one color (`"`, `n=`, `"`).
    let mut merged: Vec<(usize, usize, &str)> = Vec::new();
    for s in spans {
        match merged.last_mut() {
            Some(last) if last.1 == s.0 && last.2 == s.2 => last.1 = s.1,
            _ => merged.push(s),
        }
    }
    let mut out = String::with_capacity(src.len() * 2);
    let mut at = 0;
    for (start, end, color) in merged {
        let (start, end) = (start.max(at).min(src.len()), end.min(src.len()));
        if start >= end || !src.is_char_boundary(start) || !src.is_char_boundary(end) {
            continue;
        }
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
