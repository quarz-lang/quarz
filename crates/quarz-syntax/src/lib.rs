//! Syntax front end for Quarz: source files, tokens and the lexer. The parser
//! and the AST will live here too.

pub mod ast;
pub mod diagnostic;
pub mod doc;
pub mod lexer;
pub mod parser;
pub mod sexp;
pub mod source;
pub mod token;

pub use diagnostic::{Diagnostic, Severity};
pub use lexer::{tokenize, Lexed, Lexer, LocalTable};
pub use parser::{parse, parse_repl, parse_with_bases, Parsed, Parser};
pub use source::{LineCol, SourceFile, Span};
pub use token::{Keyword, OpAssign, StringKind, Token, TokenKind};

#[cfg(test)]
mod parser_tests;

/// Why `name` cannot name a declared type (a class, module, data, enum,
/// type alias, type parameter): the type syntax gives it its own meaning.
pub fn reserved_type_name(name: &str) -> Option<&'static str> {
    match name {
        "Self" => Some("`Self` is reserved: it is the type of the receiver"),
        "Void" => Some("`Void` is reserved: it is the result of a method or procedure whose value is discarded"),
        "Nothing" => Some("`Nothing` is reserved: it is the type of what never gives a value (`raise`, `exit`)"),
        _ => None,
    }
}
