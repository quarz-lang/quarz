//! Source text and byte-offset spans.

use std::fmt;

/// A half-open byte range `[start, end)` into a source file.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct Span {
    pub start: u32,
    pub end: u32,
}

impl Span {
    pub fn new(start: usize, end: usize) -> Span {
        debug_assert!(start <= end);
        Span {
            start: start as u32,
            end: end as u32,
        }
    }

    pub fn empty(at: usize) -> Span {
        Span::new(at, at)
    }

    pub fn len(self) -> usize {
        (self.end - self.start) as usize
    }

    pub fn is_empty(self) -> bool {
        self.start == self.end
    }

    /// The smallest span covering both `self` and `other`.
    pub fn to(self, other: Span) -> Span {
        Span {
            start: self.start.min(other.start),
            end: self.end.max(other.end),
        }
    }
}

impl fmt::Display for Span {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}..{}", self.start, self.end)
    }
}

/// A 1-based line and column. The column counts characters, not bytes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LineCol {
    pub line: usize,
    pub col: usize,
}

/// A source file with precomputed line starts for offset → line/column
/// conversion.
#[derive(Clone, Debug)]
pub struct SourceFile {
    pub name: String,
    pub text: String,
    /// Offset added to every span of this file, so that spans of different
    /// files never collide.
    pub base: u32,
    line_starts: Vec<u32>,
}

impl SourceFile {
    pub fn new(name: impl Into<String>, text: impl Into<String>) -> SourceFile {
        SourceFile::with_base(name, text, 0)
    }

    /// A file whose spans start at `base` rather than 0.
    pub fn with_base(name: impl Into<String>, text: impl Into<String>, base: u32) -> SourceFile {
        let text = text.into();
        let mut line_starts = vec![0];
        for (i, b) in text.bytes().enumerate() {
            if b == b'\n' {
                line_starts.push(i as u32 + 1);
            }
        }
        SourceFile {
            name: name.into(),
            text,
            base,
            line_starts,
        }
    }

    pub fn slice(&self, span: Span) -> &str {
        let start = span.start.saturating_sub(self.base) as usize;
        let end = span.end.saturating_sub(self.base) as usize;
        self.text.get(start..end).unwrap_or("")
    }

    pub fn line_count(&self) -> usize {
        self.line_starts.len()
    }

    pub fn line_col(&self, offset: u32) -> LineCol {
        let offset = offset.saturating_sub(self.base).min(self.text.len() as u32);
        let line = match self.line_starts.binary_search(&offset) {
            Ok(i) => i,
            Err(i) => i - 1,
        };
        let line_start = self.line_starts[line] as usize;
        let col = self.text[line_start..offset as usize].chars().count();
        LineCol {
            line: line + 1,
            col: col + 1,
        }
    }

    /// The text of the 1-based line `line`, without its newline.
    pub fn line_text(&self, line: usize) -> &str {
        let start = self.line_starts[line - 1] as usize;
        let end = self
            .line_starts
            .get(line)
            .map(|&s| s as usize)
            .unwrap_or(self.text.len());
        self.text[start..end].trim_end_matches(['\n', '\r'])
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn line_col_conversion() {
        let f = SourceFile::new("t", "ab\ncd\n\nあい");
        assert_eq!(f.line_col(0), LineCol { line: 1, col: 1 });
        assert_eq!(f.line_col(2), LineCol { line: 1, col: 3 });
        assert_eq!(f.line_col(3), LineCol { line: 2, col: 1 });
        assert_eq!(f.line_col(6), LineCol { line: 3, col: 1 });
        assert_eq!(f.line_col(10), LineCol { line: 4, col: 2 });
        assert_eq!(f.line_text(2), "cd");
        assert_eq!(f.line_text(4), "あい");
        assert_eq!(f.line_count(), 4);
    }
}
