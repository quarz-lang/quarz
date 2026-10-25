//! Documentation comments (docs/13-doc-comments.md): the run of
//! whole-line comments directly above a line documents what that line
//! declares.

use crate::source::Span;

/// A documentation comment: its text (the comment lines without `#` and
/// one space), where the comment is, and the line it documents.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct Doc {
    pub text: String,
    /// The comment run, first `#` to the end of its last line.
    pub span: Span,
    /// The documented line: what a declaration starting in it gets.
    pub line: Span,
}

impl Doc {
    /// The first paragraph.
    pub fn summary(&self) -> &str {
        let t = self.text.trim_start();
        match t.find("\n\n") {
            Some(i) => t[..i].trim_end(),
            None => t.trim_end(),
        }
    }

    /// The text's lines, numbered: the source line of each (1-based,
    /// relative to the file), for an example's diagnostics.
    pub fn first_line(&self, src: &str, base: u32) -> usize {
        let at = (self.span.start - base) as usize;
        src[..at.min(src.len())].matches('\n').count() + 1
    }
}

/// The documentation comments of `src` (whose offsets start at `base`),
/// given the spans of its comments, in order.
pub fn extract(src: &str, base: u32, comments: &[Span]) -> Vec<Doc> {
    let at = |s: u32| (s - base) as usize;
    let line_start = |i: usize| src[..i].rfind('\n').map_or(0, |n| n + 1);
    let line_end = |i: usize| src[i..].find('\n').map_or(src.len(), |n| i + n);
    let mut docs = Vec::new();
    let mut i = 0;
    while i < comments.len() {
        // A run of whole-line comments on consecutive lines.
        let mut lines: Vec<Span> = Vec::new();
        while i < comments.len() {
            let c = comments[i];
            let s = at(c.start);
            let ls = line_start(s);
            // A `#!` line at the start of the file is not a comment.
            let whole = src[ls..s].chars().all(|ch| ch == ' ' || ch == '\t')
                && !(s == 0 && src.starts_with("#!"));
            let next_line = lines
                .last()
                .is_none_or(|prev| line_end(at(prev.start)) + 1 == ls);
            if !whole || !next_line {
                break;
            }
            lines.push(c);
            i += 1;
        }
        if lines.is_empty() {
            i += 1;
            continue;
        }
        // The line after the run: not blank, not a comment.
        let last = *lines.last().unwrap();
        let after = line_end(at(last.start)) + 1;
        if after < src.len() {
            let end = line_end(after);
            let code = &src[after..end];
            let trimmed = code.trim_start();
            if !trimmed.is_empty() && !trimmed.starts_with('#') {
                let text = lines
                    .iter()
                    .map(|c| {
                        let raw = &src[at(c.start)..at(c.end)];
                        let body = raw.strip_prefix('#').unwrap_or(raw);
                        body.strip_prefix(' ').unwrap_or(body).trim_end()
                    })
                    .collect::<Vec<_>>()
                    .join("\n");
                let first = lines[0];
                docs.push(Doc {
                    text,
                    span: Span::new(
                        at(first.start) + base as usize,
                        at(last.end) + base as usize,
                    ),
                    line: Span::new(after + base as usize, end + base as usize),
                });
            }
        }
    }
    docs
}

/// The doc of the declaration starting at `pos`, from `docs` sorted by
/// line.
pub fn doc_at(docs: &[Doc], pos: u32) -> Option<&Doc> {
    let i = docs.partition_point(|d| d.line.start <= pos);
    let d = docs.get(i.checked_sub(1)?)?;
    (pos < d.line.end || (d.line.start == d.line.end && pos == d.line.start)).then_some(d)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::parse;

    fn docs(src: &str) -> Vec<(String, String)> {
        let parsed = parse(src);
        parsed
            .program
            .docs
            .iter()
            .map(|d| {
                let line = &src[d.line.start as usize..d.line.end as usize];
                (d.text.clone(), line.trim().to_string())
            })
            .collect()
    }

    #[test]
    fn the_run_directly_above_a_line_documents_it() {
        let src = "# A stack.\n#\n#   indented\nclass S\n  # note\n\n  def a = 1\n  @x: Int # trailing\n  @y: Int\n  # b\n  def b = 2\nend\n# at the end\n";
        assert_eq!(
            docs(src),
            vec![
                ("A stack.\n\n  indented".to_string(), "class S".to_string()),
                ("b".to_string(), "def b = 2".to_string()),
            ]
        );
    }

    #[test]
    fn summary_and_lookup() {
        let src = "# One\n# two.\n#\n# More.\ndef f = 1\n";
        let parsed = parse(src);
        let d = &parsed.program.docs[0];
        assert_eq!(d.summary(), "One\ntwo.");
        assert_eq!(
            doc_at(&parsed.program.docs, 30).map(|d| d.summary()),
            Some("One\ntwo.")
        );
        assert!(doc_at(&parsed.program.docs, 0).is_none());
    }
}
