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
