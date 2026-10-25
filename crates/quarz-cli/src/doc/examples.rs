//! The examples in documentation comments, as tests (docs/13 §4): each
//! fenced block of Quarz becomes a unit of its own, its declarations at
//! the top level and its statements the one test method of a class that
//! inherits `Test::DocCase`, with `# => text` and `# raises K` rewritten
//! to checks. The unit maps its lines back to the comment's.

use quarz_syntax::ast::ExprKind;
use quarz_syntax::{parse, SourceFile};
use quarz_types::World;

use super::{fence_kind, fences, Api};
use crate::test::literal;

/// An example to run.
pub(crate) struct Example {
    /// The declaration it documents: `Stack#pop`.
    pub decl: String,
    /// Its number among that declaration's examples, from 1.
    pub index: usize,
    /// The source file and the line of the example's first line of code.
    pub file: String,
    pub line: usize,
    pub code: String,
    /// `quarz no_run`: compiled, not run.
    pub run: bool,
}

/// The examples in the docs of the files `own`.
pub(crate) fn gather(world: &World, files: &[SourceFile], own: &[u32]) -> Vec<Example> {
    let api = Api::of(world, own, true);
    let file_of = |offset: u32| {
        files
            .iter()
            .filter(|f| f.base <= offset && offset <= f.base + f.text.len() as u32)
            .max_by_key(|f| f.base)
    };
    let mut out = Vec::new();
    let mut seen: Vec<u32> = Vec::new();
    let mut decls: Vec<(String, &quarz_syntax::doc::Doc)> = Vec::new();
    for k in &api.constants {
        if let Some(d) = &k.doc {
            decls.push((k.path.clone(), d));
        }
    }
    for p in &api.pages {
        if let Some(d) = &p.doc {
            decls.push((p.name.clone(), d));
        }
        for m in &p.members {
            if let (Some(d), None) = (&m.doc, &m.from) {
                decls.push((m.path.clone(), d));
            }
        }
    }
    for (decl, doc) in decls {
        // A doc shared by `:ditto:` or by overloads is run once.
        if seen.contains(&doc.span.start) {
            continue;
        }
        seen.push(doc.span.start);
        let Some(file) = file_of(doc.span.start) else {
            continue;
        };
        let first = file.line_col(doc.span.start).line;
        let mut index = 0;
        for (info, code, offset) in fences(&doc.text) {
            let Some(run) = fence_kind(&info) else {
                continue;
            };
            index += 1;
            // The fence's line in the text, then its code's first line.
            let text_line = doc.text[..offset].matches('\n').count();
            out.push(Example {
                decl: decl.clone(),
                index,
                file: file.name.clone(),
                line: first + text_line + 1,
                code,
                run,
            });
        }
    }
    out
}

/// An example as a unit: its source, the class holding its test, and the
/// source line of each of its lines (0 for a line it adds).
pub(crate) struct ExampleUnit {
    pub text: String,
    pub class: String,
    pub lines: Vec<usize>,
    /// Checks that apply to nothing: the source line and why.
    pub errors: Vec<(usize, String)>,
}

/// A check written as a comment: `# => text` or `# raises K`.
enum Check {
    Expect(String),
    Raises(String),
}

/// Whether a top-level expression of an example is a declaration, which
/// goes to the unit's top level.
fn declaration(kind: &ExprKind) -> bool {
    matches!(
        kind,
        ExprKind::ClassDef(_)
            | ExprKind::ModuleDef(_)
            | ExprKind::DataDef(_)
            | ExprKind::EnumDef(_)
            | ExprKind::ExtensionDef(_)
            | ExprKind::MethodDef(_)
            | ExprKind::TypeAlias { .. }
            | ExprKind::ConstAssign { .. }
    )
}

pub(crate) fn unit(ex: &Example, k: usize) -> ExampleUnit {
    let class = format!("QuarzDocExample{k}");
    let src = if ex.code.ends_with('\n') {
        ex.code.clone()
    } else {
        format!("{}\n", ex.code)
    };
    let parsed = parse(&src);
    let starts: Vec<usize> = std::iter::once(0)
        .chain(src.match_indices('\n').map(|(i, _)| i + 1))
        .collect();
    let line_of = |offset: usize| starts.partition_point(|s| *s <= offset) - 1;
    let loc = |line: usize| literal(&format!("{}:{}", ex.file, ex.line + line));
    // Statements (top-level expressions) with their first and last lines.
    let body = &parsed.program.body;
    let ranges: Vec<(usize, usize)> = body
        .iter()
        .map(|e| {
            let (a, b) = (e.span.start as usize, e.span.end as usize);
            (line_of(a), line_of(b.saturating_sub(1).max(a)))
        })
        .collect();
    // The checks, from the comments (which the lexer told from strings),
    // each on the statement that ends on its line, or, alone on a line,
    // on the statement before it.
    let mut checks: Vec<Option<(Check, usize, usize)>> = (0..body.len()).map(|_| None).collect();
    let mut errors: Vec<(usize, String)> = Vec::new();
    for c in &parsed.comments {
        let (cs, ce) = (c.start as usize, c.end as usize);
        let text = &src[cs..ce];
        let check = if let Some(t) = text.strip_prefix("# =>") {
            Check::Expect(t.trim().to_string())
        } else if let Some(k) = text.strip_prefix("# raises ") {
            let k = k.trim();
            if !k.chars().next().is_some_and(|c| c.is_ascii_uppercase()) {
                continue;
            }
            Check::Raises(k.to_string())
        } else {
            continue;
        };
        let line = line_of(cs);
        let alone = src[starts[line]..cs].trim().is_empty();
        // The statement that ends on the line, before the comment.
        let ending = (0..body.len())
            .rev()
            .find(|&i| ranges[i].1 == line && (body[i].span.end as usize) <= cs);
        // One that goes on past the line: a heredoc's (`s = <<~EOS # => ...`)
        // is checked; anything else is inside a statement (a block's
        // body), where there is no statement to check.
        let spanning = (0..body.len()).find(|&i| ranges[i].0 <= line && line < ranges[i].1);
        let target = match (alone, ending, spanning) {
            (_, _, Some(i)) if ranges[i].0 < line => None,
            (false, None, Some(i))
                if text_starts_heredoc(&src[body[i].span.start as usize..cs]) =>
            {
                Some(i)
            }
            (false, Some(i), _) => Some(i),
            (false, None, _) => None,
            (true, _, _) => ranges.iter().rposition(|(_, b)| *b < line),
        };
        let Some(i) = target else {
            errors.push((
                ex.line + line,
                "a check (`# =>`, `# raises`) goes at the end of a statement's last line, or alone on the line after it".to_string(),
            ));
            continue;
        };
        if matches!(check, Check::Raises(_)) && declaration(&body[i].kind) {
            errors.push((
                ex.line + line,
                "`# raises` goes after a statement, not a declaration".to_string(),
            ));
            continue;
        }
        {
            if checks[i].is_none() {
                checks[i] = Some((check, line, cs));
            }
        }
    }
    let mut top = String::new();
    let mut top_map: Vec<usize> = Vec::new();
    let mut stmts = String::new();
    let mut stmt_map: Vec<usize> = Vec::new();
    let failed = parsed.diagnostics.iter().any(|d| d.is_error());
    if failed {
        // As written: the compiler reports the errors at their lines.
        stmts.push_str(&src);
        stmt_map.extend((0..src.lines().count()).map(|l| ex.line + l));
    }
    // Each statement on lines of its own (statements sharing a line are
    // split), declarations to the top level.
    for (i, e) in body.iter().enumerate().filter(|_| !failed) {
        let code = &src[e.span.start as usize..e.span.end as usize];
        let mut text = code.to_string();
        let mut after: Option<(String, usize)> = None;
        if let Some((check, line, cs)) = &checks[i] {
            match (check, &e.kind) {
                (Check::Expect(t), ExprKind::ConstAssign { name, .. }) => {
                    after = Some((
                        format!("doc_expect({name}, {}, {})\n", literal(t), loc(*line)),
                        *line,
                    ))
                }
                (Check::Expect(t), _) => {
                    let close = format!("), {}, {})", literal(t), loc(*line));
                    // A heredoc's body follows its first line: the call
                    // closes there.
                    let start = e.span.start as usize;
                    text = if ranges[i].0 == *line && ranges[i].1 > *line {
                        // A heredoc's check is on its first line, the
                        // body after it: the call closes before the
                        // comment.
                        let nl = src[*cs..].find('\n').map_or(src.len(), |n| cs + n);
                        let head = src[start..*cs].trim_end();
                        let rest = &src[nl..e.span.end as usize];
                        format!("doc_expect(({head}{close}{rest}")
                    } else {
                        format!("doc_expect(({code}{close}")
                    };
                }
                (Check::Raises(klass), _) => {
                    text = format!("doc_raises({klass}, {}) {{ {code} }}", loc(*line))
                }
            }
        }
        let (out, map) = if declaration(&e.kind) {
            (&mut top, &mut top_map)
        } else {
            (&mut stmts, &mut stmt_map)
        };
        let first = ranges[i].0;
        out.push_str(&text);
        out.push('\n');
        map.extend((0..=text.matches('\n').count()).map(|l| ex.line + first + l));
        if let Some((t, line)) = after {
            stmts.push_str(&t);
            stmt_map.push(ex.line + line);
        }
    }
    // Lines the unit adds map to 0.
    let mut out = top;
    let mut map = top_map;
    out.push_str(&format!(
        "class {class} < Test::DocCase\n  def test_example\n"
    ));
    map.extend([0, 0]);
    if !ex.run {
        // Compiled, not run: behind a condition the checker cannot see.
        out.push_str("    if Test::DocCase.never\n");
        map.push(0);
    }
    out.push_str(&stmts);
    map.extend(stmt_map);
    if !ex.run {
        out.push_str("    end\n");
        map.push(0);
    }
    out.push_str("    nil\n  end\nend\n");
    map.extend([0, 0, 0]);
    ExampleUnit {
        text: out,
        class,
        lines: map,
        errors,
    }
}

/// Whether the code before a comment on a statement's first line opens
/// a heredoc (whose check is on that line).
fn text_starts_heredoc(code: &str) -> bool {
    code.contains("<<~") || code.contains("<<-")
}
