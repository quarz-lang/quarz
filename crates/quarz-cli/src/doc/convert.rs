//! `quarz doc --convert-links` (#881): the code spans of the documented
//! files' comments (and of the front page's Markdown) that link today
//! become bracket links, `` `Array#push` `` → `[Array#push]`, so that the
//! generated pages keep their links once a code span is plain code
//! (docs/13 §3). Every other span stays as it is. A span the conversion
//! would change the meaning of is left and listed, and so is a converted
//! bracket that does not link when the converted text is read back (with
//! the declarations as loaded: only comments change).

use std::ops::Range;
use std::path::PathBuf;
use std::process::ExitCode;

use pulldown_cmark::{Event, Options, Parser, Tag, TagEnd};
use quarz_types::ClassId;

use super::{brackets, documented, links, name_shaped, Api, Loaded, Target};

/// A text's edits: a byte range and its bracket.
type Edits = Vec<(Range<usize>, String)>;
/// The spans left: a byte offset and why.
type Left = Vec<(usize, String)>;

/// Whether code span `code` links as it did before #881: a name's shape
/// resolved in `scope`, else a bare public method of `scope`, with a page
/// to link to.
fn span_linked(loaded: &Loaded, api: &Api, scope: Option<ClassId>, code: &str) -> bool {
    span_target(loaded, api, scope, code).is_some()
}

/// What code span `code` linked to before #881, as `span_linked` says.
fn span_target(loaded: &Loaded, api: &Api, scope: Option<ClassId>, code: &str) -> Option<Target> {
    let world = &loaded.world;
    let target = if name_shaped(code) {
        api.resolve(world, scope, code)
    } else {
        scope.and_then(|s| api.resolve_bare(world, s, code))
    };
    target.filter(|t| super::html::href(loaded, api, t).is_some())
}

/// The code spans of Markdown text `md` that link on another page
/// showing it (`there`) but not where it is converted (`here`), outside
/// a link's text: at their offset, with their code. Converted for
/// `here`, such a span stays code and its link on the other page is lost
/// (#920).
pub(crate) fn linked_elsewhere(
    md: &str,
    here: impl Fn(&str) -> bool,
    there: impl Fn(&str) -> bool,
) -> Vec<(usize, String)> {
    let mut out = Vec::new();
    let mut in_link = 0usize;
    for (event, range) in Parser::new_ext(md, Options::ENABLE_TABLES).into_offset_iter() {
        match event {
            Event::Start(Tag::Link { .. }) | Event::Start(Tag::Image { .. }) => in_link += 1,
            Event::End(TagEnd::Link) | Event::End(TagEnd::Image) => {
                in_link = in_link.saturating_sub(1)
            }
            Event::Code(code) if in_link == 0 && !here(&code) && there(&code) => {
                out.push((range.start, code.to_string()))
            }
            _ => {}
        }
    }
    out
}

/// The edits of Markdown text `md`: each code span `linked` says links,
/// its range and its bracket; and the spans left, at their offset, with
/// why.
pub(crate) fn span_edits(md: &str, linked: impl Fn(&str) -> bool) -> (Edits, Left) {
    let mut edits = Vec::new();
    let mut left = Vec::new();
    let mut in_link = 0usize;
    for (event, range) in Parser::new_ext(md, Options::ENABLE_TABLES).into_offset_iter() {
        match event {
            Event::Start(Tag::Link { .. }) | Event::Start(Tag::Image { .. }) => in_link += 1,
            Event::End(TagEnd::Link) | Event::End(TagEnd::Image) => {
                in_link = in_link.saturating_sub(1)
            }
            Event::Code(code) if linked(&code) => {
                let before = md[..range.start].chars().next_back();
                let after = md[range.end..].chars().next();
                let why = if md[range.clone()].contains('\n') {
                    Some("spans two lines")
                } else if in_link > 0 {
                    Some("is in a link's text")
                } else if !brackets::link_at(md, range.start) {
                    Some("follows a word character, after which a bracket is no link")
                } else if before == Some('!') {
                    Some("follows `!`, which would make the bracket an image")
                } else if matches!(after, Some('(' | '[')) {
                    Some("is followed by a parenthesis or a bracket, which would make it another link")
                } else {
                    None
                };
                match why {
                    Some(why) => left.push((range.start, format!("`{code}` {why}"))),
                    None => edits.push((range, format!("[{}]", brackets::label_of(&code)))),
                }
            }
            _ => {}
        }
    }
    (edits, left)
}

/// `span_edits`, less those whose bracket would not link once the text
/// is converted (one read as a link definition, `[Name]: text`, say):
/// each is left and listed, and the rest read back again.
pub(crate) fn conversions(md: &str, linked: impl Fn(&str) -> bool) -> (Edits, Left) {
    let (mut edits, mut left) = span_edits(md, &linked);
    loop {
        let failed = read_back(md, &edits, &linked);
        if failed.is_empty() {
            return (edits, left);
        }
        for (at, with) in failed {
            left.push((at, format!("{with} would not link there as a bracket")));
            edits.retain(|(r, _)| r.start != at);
        }
    }
}

/// The text `md` with `edits` applied (sorted by offset), and the
/// converted brackets of it that do not link (`linked`): read back as
/// the pages will read it, the declarations unchanged.
fn read_back(
    md: &str,
    edits: &[(Range<usize>, String)],
    linked: impl Fn(&str) -> bool,
) -> Vec<(usize, String)> {
    let mut text = String::with_capacity(md.len());
    let mut starts: Vec<(usize, usize)> = Vec::new();
    let mut last = 0;
    for (range, with) in edits {
        text.push_str(&md[last..range.start]);
        starts.push((text.len(), range.start));
        text.push_str(with);
        last = range.end;
    }
    text.push_str(&md[last..]);
    let mut found: Vec<usize> = Vec::new();
    brackets::events(&text, Options::ENABLE_TABLES, |name, range| {
        if linked(name) {
            found.push(range.start);
        }
        None
    })
    .for_each(drop);
    starts
        .iter()
        .zip(edits)
        .filter(|((new, _), _)| !found.contains(new))
        .map(|((_, old), (_, with))| (*old, with.clone()))
        .collect()
}

/// Where each line of a doc comment's text starts in its source: the
/// offset after its `#` and the one space that follows it.
fn comment_lines(src: &str, start: usize, end: usize) -> Vec<usize> {
    let mut out = Vec::new();
    let mut at = start;
    for line in src[start..end].split('\n') {
        let hash = line.find('#').map_or(0, |i| i + 1);
        let body = hash + usize::from(line[hash..].starts_with(' '));
        out.push(at + body);
        at += line.len() + 1;
    }
    out
}

/// A text offset of a doc comment as an offset of its source, given its
/// lines' starts (`comment_lines`).
fn source_offset(text: &str, lines: &[usize], offset: usize) -> usize {
    let line = text[..offset].matches('\n').count();
    let col = offset - text[..offset].rfind('\n').map_or(0, |i| i + 1);
    lines[line] + col
}

/// A file to write: its path, its text, and the edits (offsets in the
/// text) with the name each converted.
struct FileEdits {
    path: PathBuf,
    text: String,
    edits: Vec<(Range<usize>, String)>,
}

/// The path a loaded file is written back to: a standard library file
/// under `std/` of the current directory (the repository's root), which
/// must hold what the binary was built with.
fn path_of(name: &str, text: &str) -> Result<PathBuf, String> {
    let Some(rel) = links::std_path(name) else {
        return Ok(PathBuf::from(name));
    };
    let path = PathBuf::from("std").join(rel);
    match std::fs::read_to_string(&path) {
        Ok(on_disk) if on_disk == text => Ok(path),
        Ok(_) => Err(format!(
            "{}: differs from the standard library this `quarz` was built with: run the conversion with a build of this checkout",
            path.display()
        )),
        Err(e) => Err(format!(
            "{}: {e} (convert the standard library from the repository's root)",
            path.display()
        )),
    }
}

pub(crate) fn command(loaded: &Loaded, api: &Api) -> ExitCode {
    let mut files: Vec<FileEdits> = Vec::new();
    let mut left: Vec<String> = Vec::new();
    let mut unlinked: Vec<String> = Vec::new();
    let mut seen: Vec<u32> = Vec::new();
    for (scope, _, doc, _) in documented(&loaded.world, api) {
        let Some(doc) = doc else { continue };
        if seen.contains(&doc.span.start) {
            continue;
        }
        seen.push(doc.span.start);
        let Some(file) = loaded.file_of(doc.span.start) else {
            continue;
        };
        let index = loaded.files.iter().position(|f| f.base == file.base);
        if !index.is_some_and(|i| loaded.own.contains(&(i as u32))) {
            continue;
        }
        let link = super::linker(loaded, api, Some(scope));
        let (edits, spans_left) = conversions(&doc.text, |code| {
            span_linked(loaded, api, Some(scope), code) && link(code)
        });
        let start = (doc.span.start - file.base) as usize;
        let end = (doc.span.end - file.base) as usize;
        let lines = comment_lines(&file.text, start, end);
        for (at, why) in spans_left {
            let o = source_offset(&doc.text, &lines, at) as u32 + file.base;
            left.push(format!("{}: {why}", loaded.location(o)));
        }
        if edits.is_empty() {
            continue;
        }
        for (at, with) in read_back(&doc.text, &edits, &link) {
            let o = source_offset(&doc.text, &lines, at) as u32 + file.base;
            unlinked.push(format!("{}: {with}", loaded.location(o)));
        }
        let path = match path_of(&file.name, &file.text) {
            Ok(p) => p,
            Err(e) => {
                eprintln!("quarz doc: {e}");
                return ExitCode::FAILURE;
            }
        };
        let at = match files.iter().position(|f| f.path == path) {
            Some(i) => i,
            None => {
                files.push(FileEdits {
                    path,
                    text: file.text.clone(),
                    edits: Vec::new(),
                });
                files.len() - 1
            }
        };
        for (range, with) in edits {
            let s = source_offset(&doc.text, &lines, range.start);
            let e = source_offset(&doc.text, &lines, range.end);
            files[at].edits.push((s..e, with));
        }
    }
    // The front page's Markdown, linked from no class.
    if let (Some(text), Some(path)) = (&loaded.readme, &loaded.readme_path) {
        let link = super::linker(loaded, api, None);
        let (edits, spans_left) = conversions(text, |code| {
            span_linked(loaded, api, None, code) && link(code)
        });
        for (at, why) in spans_left {
            let line = text[..at].matches('\n').count() + 1;
            left.push(format!("{}:{line}: {why}", path.display()));
        }
        for (at, with) in read_back(text, &edits, &link) {
            let line = text[..at].matches('\n').count() + 1;
            unlinked.push(format!("{}:{line}: {with}", path.display()));
        }
        // The root module's page shows it too, with names resolved in the
        // module: a span that linked there only stays code, and is listed
        // with that page and, when one links here, the full name to write
        // (#920).
        for page in api.pages.iter().filter(|p| super::html::shows_readme(p)) {
            let scope = Some(page.id);
            let there = super::linker(loaded, api, scope);
            let spans = linked_elsewhere(
                text,
                |code| span_linked(loaded, api, None, code) && link(code),
                |code| span_linked(loaded, api, scope, code) && there(code),
            );
            for (at, code) in spans {
                let line = text[..at].matches('\n').count() + 1;
                let full = match span_target(loaded, api, scope, &code) {
                    Some(Target::Page(p, member)) => Some(member.unwrap_or(p)),
                    _ => None,
                }
                .filter(|full| link(full));
                let write = match full {
                    Some(full) => format!("write [{}]", brackets::label_of(&full)),
                    None => "write its full name".to_string(),
                };
                left.push(format!(
                    "{}:{line}: `{code}` links on the page of `{}` only, not on the front page: {write}",
                    path.display(),
                    page.name
                ));
            }
        }
        if !edits.is_empty() {
            files.push(FileEdits {
                path: path.clone(),
                text: text.clone(),
                edits,
            });
        }
    }
    let mut converted = 0usize;
    for f in &mut files {
        f.edits.sort_by_key(|(r, _)| std::cmp::Reverse(r.start));
        let mut text = f.text.clone();
        for (range, with) in &f.edits {
            text.replace_range(range.clone(), with);
            converted += 1;
        }
        if let Err(e) = std::fs::write(&f.path, text) {
            eprintln!("quarz doc: {}: {e}", f.path.display());
            return ExitCode::FAILURE;
        }
    }
    eprintln!(
        "quarz doc: converted {converted} code span(s) in {} file(s)",
        files.len()
    );
    for l in &left {
        eprintln!("quarz doc: left: {l}");
    }
    for u in &unlinked {
        eprintln!("quarz doc: converted, but does not link: {u}");
    }
    if unlinked.is_empty() {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn convert(md: &str) -> (String, Vec<String>) {
        let (mut edits, left) = conversions(md, |c| c != "x");
        edits.sort_by_key(|(r, _)| std::cmp::Reverse(r.start));
        let mut s = md.to_string();
        for (r, w) in edits {
            s.replace_range(r, &w);
        }
        (s, left.into_iter().map(|(_, w)| w).collect())
    }

    #[test]
    fn the_spans_that_link_become_brackets() {
        assert_eq!(
            convert("See `Foo` and `x`, `Array#[]`.").0,
            "See [Foo] and `x`, [Array#\\[\\]]."
        );
        let (s, left) = convert("a`Foo` `Bar`(1) !`Baz` [`Q`](u)\n`K`: v\n`Two\nlines`");
        // (`[K]: v` inside a paragraph is a link: a definition cannot
        // interrupt one.)
        assert_eq!(s, "a`Foo` `Bar`(1) !`Baz` [`Q`](u)\n[K]: v\n`Two\nlines`");
        assert_eq!(left.len(), 5, "{left:?}");
        // At a paragraph's start it would be a definition: read back,
        // left.
        let (s, left) = convert("One.\n\n`K`: v");
        assert_eq!(s, "One.\n\n`K`: v");
        assert_eq!(left, ["[K] would not link there as a bracket"]);
    }

    #[test]
    fn spans_that_link_on_the_other_page_only() {
        let md = "`A` and `B`, `C`; [`B`](u) ``B``.";
        let here = |c: &str| c == "A";
        let there = |c: &str| c == "A" || c == "B";
        // (Not the one in a link's text: it links already.)
        let found = linked_elsewhere(md, here, there);
        assert_eq!(
            found,
            [
                (md.find("`B`").unwrap(), "B".to_string()),
                (md.find("``B``").unwrap(), "B".to_string())
            ]
        );
    }

    #[test]
    fn comment_offsets() {
        let src = "x\n  # One `A`.\n  #\n  # Two.\nclass A";
        let start = src.find('#').unwrap();
        let end = src.find("Two.").unwrap() + 4;
        let lines = comment_lines(src, start, end);
        let text = "One `A`.\n\nTwo.";
        let o = source_offset(text, &lines, text.find('`').unwrap());
        assert_eq!(&src[o..o + 3], "`A`");
        let o = source_offset(text, &lines, text.find("Two").unwrap());
        assert_eq!(&src[o..o + 3], "Two");
    }
}
