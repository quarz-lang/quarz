//! `quarz doc --html`: a static site, one page per class and module, the
//! README as the front page, and a search index loaded as a script (so
//! that the site works from `file://`).

use std::fmt::Write as _;
use std::path::Path;

use pulldown_cmark::{
    html, CodeBlockKind, CowStr, Event, HeadingLevel, Options, Parser, Tag, TagEnd,
};

use super::{first_line, Api, Item, Kind, Loaded, Page, Target};
use quarz_types::ClassId;

/// The file of a page: `Stack::Empty` → `Stack--Empty.html`.
fn page_file(name: &str) -> String {
    format!("{}.html", name.replace("::", "--"))
}

/// The anchor of a member in its page.
fn anchor(item: &Item) -> String {
    super::anchor_of(item.kind, &item.name)
}

fn escape(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '&' => out.push_str("&amp;"),
            '<' => out.push_str("&lt;"),
            '>' => out.push_str("&gt;"),
            '"' => out.push_str("&quot;"),
            c => out.push(c),
        }
    }
    out
}

/// The href of a link target, from a page in the same directory; one of
/// another site, when its API is published (#448).
fn href(loaded: &Loaded, api: &Api, target: &Target) -> Option<String> {
    match target {
        Target::Page(p, None) => Some(page_file(p)),
        Target::Page(p, Some(member)) => {
            let page = api.page(p)?;
            let item = page.members.iter().find(|m| &m.path == member)?;
            Some(format!("{}#{}", page_file(p), anchor(item)))
        }
        Target::Elsewhere { .. } => None,
        Target::Foreign {
            class,
            page,
            anchor,
        } => {
            let base = loaded.docs_of(&loaded.world, *class)?;
            Some(match anchor {
                Some(a) => format!("{base}/{}#{a}", page_file(page)),
                None => format!("{base}/{}", page_file(page)),
            })
        }
    }
}

/// `url`, or `#` for a scheme other than http, https and mailto (a
/// `:` before any `/`, `?` or `#` makes a scheme, whatever else is in
/// it: browsers drop tabs and newlines from `java\tscript:`).
fn safe_url(url: CowStr) -> CowStr {
    let Some(end) = url.find([':', '/', '?', '#']) else {
        return url;
    };
    if !url[end..].starts_with(':') {
        return url;
    }
    let scheme: String = url[..end]
        .chars()
        .filter(|c| !c.is_ascii_whitespace() && !c.is_control())
        .collect::<String>()
        .to_ascii_lowercase();
    if ["http", "https", "mailto"].contains(&scheme.as_str()) {
        url
    } else {
        CowStr::from("#")
    }
}

/// A doc's Markdown as HTML: raw HTML shown as text, code spans that name
/// a documented declaration linked, `NOTE:`-style paragraphs set off, and
/// headings `shift` levels down (`##` is an `<h4>` in a member's doc,
/// which sits under the member's `<h3>`).
fn markdown_html(
    loaded: &Loaded,
    api: &Api,
    scope: Option<ClassId>,
    md: &str,
    shift: usize,
) -> String {
    let world = &loaded.world;
    let events: Vec<Event> = Parser::new_ext(md, Options::ENABLE_TABLES).collect();
    let mut out: Vec<Event> = Vec::with_capacity(events.len());
    // A Quarz code block being read: its text, colored at its end.
    let mut quarz_block: Option<String> = None;
    for (i, e) in events.iter().enumerate() {
        if let Some(code) = quarz_block.as_mut() {
            match e {
                Event::Text(t) => {
                    code.push_str(t);
                    continue;
                }
                Event::End(TagEnd::CodeBlock) => {
                    let code = quarz_block.take().unwrap_or_default();
                    let body = quarz_cli::highlight::html(&code).unwrap_or_else(|| escape(&code));
                    out.push(Event::Html(CowStr::from(format!(
                        "<pre><code class=\"quarz\">{body}</code></pre>\n"
                    ))));
                    continue;
                }
                _ => {}
            }
        }
        match e.clone() {
            Event::Start(Tag::CodeBlock(kind)) if quarz_fence(&kind) => {
                quarz_block = Some(String::new());
            }
            Event::Html(t) | Event::InlineHtml(t) => out.push(Event::Text(t)),
            Event::Start(Tag::Heading {
                level,
                id,
                classes,
                attrs,
            }) => out.push(Event::Start(Tag::Heading {
                level: shifted(level, shift),
                id,
                classes,
                attrs,
            })),
            Event::End(TagEnd::Heading(level)) => {
                out.push(Event::End(TagEnd::Heading(shifted(level, shift))))
            }
            Event::Code(code) => {
                let target = if super::name_shaped(&code) {
                    api.resolve(world, scope, &code)
                } else {
                    scope.and_then(|s| api.resolve_bare(world, s, &code))
                };
                match target.as_ref().and_then(|t| href(loaded, api, t)) {
                    Some(h) => out.push(Event::Html(CowStr::from(format!(
                        "<a href=\"{}\"><code>{}</code></a>",
                        escape(&h),
                        escape(&code)
                    )))),
                    None => out.push(Event::Code(code)),
                }
            }
            Event::Start(Tag::Paragraph) => {
                let note = match events.get(i + 1) {
                    Some(Event::Text(t)) => ["NOTE:", "WARNING:", "DEPRECATED:", "EXPERIMENTAL:"]
                        .iter()
                        .find(|k| t.starts_with(**k))
                        .map(|k| k.trim_end_matches(':').to_ascii_lowercase()),
                    _ => None,
                };
                match note {
                    // Closed by the paragraph's own end, `</p>`.
                    Some(class) => out.push(Event::Html(CowStr::from(format!(
                        "<p class=\"admonition {class}\">"
                    )))),
                    None => out.push(Event::Start(Tag::Paragraph)),
                }
            }
            // A link or an image goes only where a page may: the web
            // (http, https), mail, or a relative path.
            Event::Start(Tag::Link {
                link_type,
                dest_url,
                title,
                id,
            }) => out.push(Event::Start(Tag::Link {
                link_type,
                dest_url: safe_url(dest_url),
                title,
                id,
            })),
            Event::Start(Tag::Image {
                link_type,
                dest_url,
                title,
                id,
            }) => out.push(Event::Start(Tag::Image {
                link_type,
                dest_url: safe_url(dest_url),
                title,
                id,
            })),
            other => out.push(other),
        }
    }
    let mut s = String::new();
    html::push_html(&mut s, out.into_iter());
    s
}

/// Whether a code block holds Quarz code, colored (#446): one with no
/// info string (the doc comments' convention), `quarz` with or without
/// options (`quarz no_run`), or `crystal` (the READMEs' fences, for
/// GitHub's colors); any other language is shown plain.
fn quarz_fence(kind: &CodeBlockKind) -> bool {
    match kind {
        CodeBlockKind::Indented => true,
        CodeBlockKind::Fenced(info) => {
            // (A language's name in any case, as GitHub reads it.)
            let lang = info
                .split(|c: char| c.is_whitespace() || c == ',')
                .next()
                .unwrap_or("");
            lang.is_empty()
                || lang.eq_ignore_ascii_case("quarz")
                || lang.eq_ignore_ascii_case("crystal")
        }
    }
}

/// A heading `shift` levels down, at most `<h6>`, and when shifted below
/// what it is in (a `#` in a member's doc is still an `<h4>`).
fn shifted(level: HeadingLevel, shift: usize) -> HeadingLevel {
    let floor = if shift > 0 { shift + 2 } else { 1 };
    let n = (level as usize + shift).max(floor).min(6);
    HeadingLevel::try_from(n).unwrap_or(HeadingLevel::H6)
}

const STYLE: &str = r#":root { --fg: #1d1f21; --bg: #ffffff; --muted: #5f6368; --rule: #e0e0e0; --code-bg: #f4f4f5; --link: #0b57d0; --note: #fff8e1; --warn: #fdecea; }
@media (prefers-color-scheme: dark) { :root { --fg: #e6e6e6; --bg: #17181a; --muted: #a0a4a8; --rule: #33363a; --code-bg: #24262a; --link: #8ab4f8; --note: #3a3320; --warn: #3d2422; } }
body { margin: 0; background: var(--bg); color: var(--fg); font: 16px/1.55 system-ui, -apple-system, "Segoe UI", sans-serif; }
.wrap { display: flex; max-width: 72rem; margin: 0 auto; }
nav { width: 15rem; flex: none; padding: 1rem; border-right: 1px solid var(--rule); font-size: 0.9rem; position: sticky; top: 0; height: 100vh; overflow-y: auto; box-sizing: border-box; }
nav ul { list-style: none; padding: 0; margin: 0.5rem 0; }
nav li { margin: 0.15rem 0; overflow-wrap: anywhere; }
nav [aria-current] { font-weight: 600; }
nav summary { margin: 0.75rem 0 0; color: var(--muted); cursor: pointer; }
main { flex: 1; min-width: 0; padding: 1rem 2rem 4rem; }
a { color: var(--link); text-decoration: none; }
a:hover { text-decoration: underline; }
code, pre { font-family: ui-monospace, "SF Mono", Menlo, Consolas, monospace; font-size: 0.9em; }
code { background: var(--code-bg); padding: 0.1em 0.3em; border-radius: 4px; }
pre { background: var(--code-bg); padding: 0.8rem 1rem; border-radius: 6px; overflow-x: auto; }
pre code, h1 code, h3 code { background: none; padding: 0; }
pre code .k { color: #cf222e; } pre code .l { color: #0550ae; } pre code .n { color: #0550ae; } pre code .s { color: #0a3069; } pre code .r { color: #116329; } pre code .y { color: #8250df; } pre code .t { color: #953800; } pre code .v { color: #0550ae; } pre code .c { color: #59636e; font-style: italic; } pre code .i { color: inherit; } pre code .o { color: #57606a; }
@media (prefers-color-scheme: dark) { pre code .k { color: #ff7b72; } pre code .l, pre code .n, pre code .v { color: #79c0ff; } pre code .s { color: #a5d6ff; } pre code .r { color: #7ee787; } pre code .y { color: #d2a8ff; } pre code .t { color: #ffa657; } pre code .c { color: #8b949e; } pre code .o { color: #b1bac4; } }
h1 { overflow-wrap: anywhere; }
.member { border-top: 1px solid var(--rule); padding-top: 0.5rem; margin-top: 1.2rem; }
.member h3 { font-size: 1rem; margin: 0.3rem 0; overflow-wrap: anywhere; }
.member h4 { font-size: 0.95rem; color: var(--muted); }
.member h5, .member h6 { font-size: 0.9rem; color: var(--muted); }
.loc, .from { color: var(--muted); font-size: 0.85rem; }
.summary { color: var(--muted); }
.admonition { padding: 0.5rem 0.8rem; border-radius: 6px; background: var(--note); }
.admonition.warning, .admonition.deprecated { background: var(--warn); }
#search { width: 100%; box-sizing: border-box; padding: 0.35rem 0.5rem; border: 1px solid var(--rule); border-radius: 4px; background: var(--bg); color: var(--fg); }
/* The narrow layout; `layout`'s script folds the list of pages at the same width. */
@media (max-width: 48rem) { .wrap { display: block; } nav { width: auto; height: auto; position: static; border-right: none; border-bottom: 1px solid var(--rule); } main { padding: 1rem; } }
"#;

const SEARCH: &str = r#"(function () {
  var box = document.getElementById("search"), list = document.getElementById("results");
  if (!box || !window.QUARZ_DOC_INDEX) return;
  box.addEventListener("input", function () {
    var q = box.value.trim().toLowerCase();
    list.innerHTML = "";
    if (!q) return;
    window.QUARZ_DOC_INDEX.filter(function (e) { return e[0].toLowerCase().indexOf(q) >= 0; })
      .slice(0, 50).forEach(function (e) {
        var li = document.createElement("li"), a = document.createElement("a");
        a.href = e[1]; a.textContent = e[0]; li.appendChild(a); list.appendChild(li);
      });
  });
})();
"#;

fn layout(title: &str, api: &Api, current: Option<&str>, body: &str) -> String {
    let mut nav = String::new();
    nav.push_str("<p><a href=\"index.html\"><strong>Index</strong></a></p>\n");
    nav.push_str("<input id=\"search\" type=\"search\" placeholder=\"Search\" aria-label=\"Search\">\n<ul id=\"results\"></ul>\n");
    // The list of pages folds: closed at first on a narrow screen, where
    // it would stand between the top and the page's text (the script
    // runs as soon as the list is read, before it is shown), and closed or
    // opened again when the width crosses the stylesheet's breakpoint for
    // the narrow layout (48rem, in `STYLE`).
    nav.push_str("<details id=\"pages\" open>\n<summary>Classes and modules</summary>\n<ul>\n");
    for p in &api.pages {
        let cur = if Some(p.name.as_str()) == current {
            " aria-current=\"page\""
        } else {
            ""
        };
        let _ = writeln!(
            nav,
            "<li><a href=\"{}\"{cur}>{}</a></li>",
            escape(&page_file(&p.name)),
            escape(&p.name)
        );
    }
    nav.push_str("</ul>\n</details>\n");
    nav.push_str("<script>(function () { var narrow = window.matchMedia(\"(max-width: 48rem)\"), pages = document.getElementById(\"pages\"); pages.open = !narrow.matches; narrow.addEventListener(\"change\", function (e) { pages.open = !e.matches; }); })();</script>\n");
    format!(
        "<!doctype html>\n<html lang=\"en\">\n<head>\n<meta charset=\"utf-8\">\n<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n<title>{}</title>\n<link rel=\"stylesheet\" href=\"style.css\">\n</head>\n<body>\n<div class=\"wrap\">\n<nav>\n{nav}</nav>\n<main>\n{body}</main>\n</div>\n<script src=\"search-index.js\"></script>\n<script src=\"search.js\"></script>\n</body>\n</html>\n",
        escape(title)
    )
}

/// A signature, its names of classes linked where they have a page, here
/// or on another site (#448). A signature names classes by their declared
/// names (`Dep::Thing`, `Time`), whatever the page's scope.
fn signature_html(loaded: &Loaded, api: &Api, current: Option<ClassId>, sig: &str) -> String {
    let mut out = String::with_capacity(sig.len() * 2);
    let mut prev: Option<char> = None;
    let mut rest = sig;
    while let Some(c) = rest.chars().next() {
        let starts_name = c.is_ascii_uppercase()
            && !prev.is_some_and(|p| p.is_alphanumeric() || p == '_' || p == '@');
        if !starts_name {
            out.push_str(&escape(&c.to_string()));
            prev = Some(c);
            rest = &rest[c.len_utf8()..];
            continue;
        }
        // `A`, `A::B`.
        let bytes = rest.as_bytes();
        let mut end = 0;
        loop {
            while end < rest.len() && (bytes[end].is_ascii_alphanumeric() || bytes[end] == b'_') {
                end += 1;
            }
            if rest[end..].starts_with("::")
                && rest[end + 2..].starts_with(|c: char| c.is_ascii_uppercase())
            {
                end += 2;
            } else {
                break;
            }
        }
        // (A name running into a non-ASCII letter is no name.)
        let name = &rest[..end];
        let whole = !rest[end..].starts_with(|c: char| c.is_alphanumeric());
        let link = whole
            .then(|| api.class_target(&loaded.world, name))
            .flatten()
            // (Not the page the signature is on.)
            .filter(|t| {
                !matches!(t, Target::Page(p, None)
                    if current.is_some_and(|c| loaded.world.class(c).name == *p))
            })
            .and_then(|t| href(loaded, api, &t));
        match link {
            Some(h) => {
                let _ = write!(out, "<a href=\"{}\">{}</a>", escape(&h), escape(name));
            }
            None => out.push_str(&escape(name)),
        }
        prev = name.chars().last();
        rest = &rest[end..];
    }
    out
}

/// A location, `file:line`, linked to its line on GitHub when known
/// (#449).
fn location_html(loaded: &Loaded, offset: u32) -> String {
    let at = loaded.location(offset);
    match loaded.source_url(offset) {
        Some(url) => format!("<a href=\"{}\">{}</a>", escape(&url), escape(&at)),
        None => escape(&at),
    }
}

/// A class's name, linked to its page here or on another site.
fn class_link(loaded: &Loaded, api: &Api, name: &str, shown: &str) -> String {
    match api
        .class_target(&loaded.world, name)
        .and_then(|t| href(loaded, api, &t))
    {
        Some(h) => format!(
            "<a href=\"{}\"><code>{}</code></a>",
            escape(&h),
            escape(shown)
        ),
        None => format!("<code>{}</code>", escape(shown)),
    }
}

fn member_html(loaded: &Loaded, api: &Api, page: &Page, m: &Item) -> String {
    let mut s = String::new();
    let _ = writeln!(s, "<section class=\"member\" id=\"{}\">", anchor(m));
    let _ = writeln!(
        s,
        "<h3><code>{}</code></h3>",
        signature_html(loaded, api, Some(page.id), &m.signature)
    );
    if let Some(ext) = &m.extension {
        let _ = writeln!(s, "<p class=\"from\">in <code>{}</code></p>", escape(ext));
    }
    if let Some(d) = &m.doc {
        s.push_str(&markdown_html(loaded, api, Some(page.id), &d.text, 2));
    }
    if let Some(f) = &m.from {
        let link = api
            .class_target(&loaded.world, f)
            .and_then(|t| href(loaded, api, &t));
        let from = match link {
            Some(h) => format!("<a href=\"{}\">{}</a>", escape(&h), escape(f)),
            None => escape(f),
        };
        let _ = writeln!(s, "<p class=\"from\">from {from}</p>");
    }
    if let Some(by) = m.generated_by {
        let _ = writeln!(
            s,
            "<p class=\"from\">generated by <code>{}</code></p>",
            escape(&loaded.source_line(by))
        );
    }
    let _ = writeln!(
        s,
        "<p class=\"loc\">{}</p>\n</section>",
        location_html(loaded, m.span.start)
    );
    s
}

fn summary_list(api: &Api, pages: &[&Page]) -> String {
    let mut s = String::from("<ul>\n");
    for p in pages {
        let summary = p
            .doc
            .as_ref()
            .map(|d| first_line(d.summary()))
            .unwrap_or_default();
        let _ = writeln!(
            s,
            "<li><a href=\"{}\"><code>{}</code></a> <span class=\"summary\">{}</span></li>",
            escape(&page_file(&p.name)),
            escape(&p.name),
            escape(&summary)
        );
    }
    let _ = api;
    s.push_str("</ul>\n");
    s
}

fn page_html(loaded: &Loaded, api: &Api, page: &Page) -> String {
    let mut s = String::new();
    let _ = writeln!(
        s,
        "<h1><code>{}</code></h1>",
        signature_html(loaded, api, Some(page.id), &page.signature)
    );
    if !page.includes.is_empty() {
        let names: Vec<String> = page
            .includes
            .iter()
            .map(|n| {
                let base = n.split('[').next().unwrap_or(n);
                class_link(loaded, api, base, n)
            })
            .collect();
        let _ = writeln!(s, "<p>include {}</p>", names.join(", "));
    }
    match (&page.doc, &loaded.readme) {
        (Some(d), _) => s.push_str(&markdown_html(loaded, api, Some(page.id), &d.text, 1)),
        // A library's root module: its README.
        (None, Some(readme)) if page.span.start == 0 => {
            s.push_str(&markdown_html(loaded, api, Some(page.id), readme, 1))
        }
        _ => {}
    }
    if !loaded.location(page.span.start).is_empty() {
        let _ = writeln!(
            s,
            "<p class=\"loc\">{}</p>",
            location_html(loaded, page.span.start)
        );
    }
    let prefix = format!("{}::", page.name);
    let nested: Vec<&Page> = api
        .pages
        .iter()
        .filter(|p| {
            p.name
                .strip_prefix(&prefix)
                .is_some_and(|rest| !rest.contains("::"))
        })
        .collect();
    // A cog's public functions first, before its classes.
    let functions: Vec<&Item> = page
        .members
        .iter()
        .filter(|m| m.kind == Kind::Function)
        .collect();
    if !functions.is_empty() {
        s.push_str("<h2>Functions</h2>\n");
        for m in functions {
            s.push_str(&member_html(loaded, api, page, m));
        }
    }
    if !nested.is_empty() {
        s.push_str("<h2>Classes and modules</h2>\n");
        s.push_str(&summary_list(api, &nested));
    }
    for (title, kind) in [
        ("Variants", Kind::Variant),
        ("Constants", Kind::Const),
        ("Class methods", Kind::ClassMethod),
        ("Methods", Kind::Method),
    ] {
        let ms: Vec<&Item> = page
            .members
            .iter()
            .filter(|m| m.kind == kind && m.extension.is_none())
            .collect();
        if ms.is_empty() {
            continue;
        }
        let _ = writeln!(s, "<h2>{title}</h2>");
        for m in ms {
            s.push_str(&member_html(loaded, api, page, m));
        }
    }
    let ext: Vec<&Item> = page
        .members
        .iter()
        .filter(|m| m.extension.is_some())
        .collect();
    if !ext.is_empty() {
        s.push_str("<h2>Extensions</h2>\n");
        for m in ext {
            s.push_str(&member_html(loaded, api, page, m));
        }
    }
    s
}

fn index_html(loaded: &Loaded, api: &Api) -> String {
    let mut s = String::new();
    match &loaded.readme {
        Some(md) => s.push_str(&markdown_html(loaded, api, None, md, 0)),
        None => {
            let _ = writeln!(s, "<h1>{}</h1>", escape(&loaded.title));
        }
    }
    s.push_str("<h2>Classes and modules</h2>\n");
    let all: Vec<&Page> = api.pages.iter().collect();
    s.push_str(&summary_list(api, &all));
    for (title, items) in [("Constants", &api.constants), ("Functions", &api.functions)] {
        if items.is_empty() {
            continue;
        }
        let _ = writeln!(s, "<h2>{title}</h2>");
        for k in items {
            let _ = writeln!(s, "<section class=\"member\" id=\"{}\">", anchor(k));
            let _ = writeln!(
                s,
                "<h3><code>{}</code></h3>",
                signature_html(loaded, api, None, &k.signature)
            );
            if let Some(d) = &k.doc {
                s.push_str(&markdown_html(loaded, api, None, &d.text, 2));
            }
            let _ = writeln!(
                s,
                "<p class=\"loc\">{}</p>\n</section>",
                location_html(loaded, k.span.start)
            );
        }
    }
    s
}

fn search_index(api: &Api) -> String {
    let mut entries: Vec<String> = Vec::new();
    // A script's functions, on the index page.
    for f in &api.functions {
        entries.push(format!(
            "[{},{}]",
            super::json_string(&f.path),
            super::json_string(&format!("index.html#{}", anchor(f)))
        ));
    }
    for p in &api.pages {
        entries.push(format!(
            "[{},{}]",
            super::json_string(&p.name),
            super::json_string(&page_file(&p.name))
        ));
        for m in &p.members {
            let h = format!("{}#{}", page_file(&p.name), anchor(m));
            entries.push(format!(
                "[{},{}]",
                super::json_string(&m.path),
                super::json_string(&h)
            ));
        }
    }
    format!("window.QUARZ_DOC_INDEX = [\n{}\n];\n", entries.join(",\n"))
}

/// Write the site into `out`; the number of pages.
pub(crate) fn write(loaded: &Loaded, api: &Api, out: &Path) -> std::io::Result<usize> {
    std::fs::create_dir_all(out)?;
    std::fs::write(out.join("style.css"), STYLE)?;
    std::fs::write(out.join("search.js"), SEARCH)?;
    std::fs::write(out.join("search-index.js"), search_index(api))?;
    std::fs::write(
        out.join("index.html"),
        layout(&loaded.title, api, None, &index_html(loaded, api)),
    )?;
    for p in &api.pages {
        let body = page_html(loaded, api, p);
        let title = format!("{} — {}", p.name, loaded.title);
        std::fs::write(
            out.join(page_file(&p.name)),
            layout(&title, api, Some(&p.name), &body),
        )?;
    }
    Ok(api.pages.len() + 1)
}
