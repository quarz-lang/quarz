//! Errors and warnings reported by the front end.

use crate::source::{SourceFile, Span};
use std::fmt::Write as _;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Severity {
    Error,
    Warning,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Diagnostic {
    pub severity: Severity,
    pub message: String,
    pub span: Span,
}

impl Diagnostic {
    pub fn error(message: impl Into<String>, span: Span) -> Diagnostic {
        Diagnostic {
            severity: Severity::Error,
            message: message.into(),
            span,
        }
    }

    pub fn warning(message: impl Into<String>, span: Span) -> Diagnostic {
        Diagnostic {
            severity: Severity::Warning,
            message: message.into(),
            span,
        }
    }

    pub fn is_error(&self) -> bool {
        self.severity == Severity::Error
    }

    /// Render as `file:line:col: error: message`, followed by the offending
    /// line and a caret under the span.
    pub fn render(&self, file: &SourceFile) -> String {
        let lc = file.line_col(self.span.start);
        let label = match self.severity {
            Severity::Error => "error",
            Severity::Warning => "warning",
        };
        let mut out = String::new();
        let _ = writeln!(
            out,
            "{}:{}:{}: {}: {}",
            file.name, lc.line, lc.col, label, self.message
        );
        let line = file.line_text(lc.line);
        let _ = writeln!(out, "  {}", line);
        let width = file
            .text
            .get(self.span.start as usize..self.span.end as usize)
            .map(|s| s.lines().next().unwrap_or("").chars().count())
            .unwrap_or(0)
            .max(1);
        let _ = writeln!(out, "  {}{}", " ".repeat(lc.col - 1), "^".repeat(width));
        out
    }
}
