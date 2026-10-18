//! Syntax front end for Quarz: source files, tokens and the lexer. The parser
//! and the AST will live here too.

pub mod diagnostic;
pub mod lexer;
pub mod source;
pub mod token;

pub use diagnostic::{Diagnostic, Severity};
pub use lexer::{tokenize, Lexed, Lexer, LocalTable};
pub use source::{LineCol, SourceFile, Span};
pub use token::{Keyword, OpAssign, StringKind, Token, TokenKind};
