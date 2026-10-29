//! `quarz doc --html`: a static site, one page per class and module, the
//! README as the front page, and a search index loaded as a script (so
//! that the site works from `file://`).

use std::fmt::Write as _;
use std::path::Path;

use pulldown_cmark::{html, CowStr, Event, Options, Parser, Tag};

use super::{first_line, Api, Item, Kind, Loaded, Page, Target};
use quarz_types::ClassId;

/// The file of a page: `Stack::Empty` → `Stack--Empty.html`.
fn page_file(name: &str) -> String {
    format!("{}.html", name.replace("::", "--"))
}

/// The anchor of a member in its page.
fn anchor(item: &Item) -> String {
    let prefix = match item.kind {
        Kind::Method => "method",
        Kind::ClassMethod => "class-method",
        Kind::Const => "const",
        Kind::Variant => "variant",
        _ => "item",
    };
    let name: String = item
        .name
        .chars()
        .map(|c| {
            if c.is_ascii_alphanumeric() || c == '_' {
                c.to_string()
            } else {
                format!("-{:x}", c as u32)
            }
        })
        .collect();
    format!("{prefix}-{name}")
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

/// The href of a link target, from a page in the same directory.
fn href(api: &Api, target: &Target) -> Option<String> {
    match target {
        Target::Page(p, None) => Some(page_file(p)),
        Target::Page(p, Some(member)) => {
            let page = api.page(p)?;
            let item = page.members.iter().find(|m| &m.path == member)?;
            Some(format!("{}#{}", page_file(p), anchor(item)))
        }
        Target::Elsewhere { .. } => None,
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
/// a documented declaration linked, `NOTE:`-style paragraphs set off.
fn markdown_html(loaded: &Loaded, api: &Api, scope: Option<ClassId>, md: &str) -> String {
    let world = &loaded.world;
    let events: Vec<Event> = Parser::new_ext(md, Options::ENABLE_TABLES).collect();
    let mut out: Vec<Event> = Vec::with_capacity(events.len());
    for (i, e) in events.iter().enumerate() {
        match e.clone() {
            Event::Html(t) | Event::InlineHtml(t) => out.push(Event::Text(t)),
            Event::Code(code) => {
                let target = if super::name_shaped(&code) {
                    api.resolve(world, scope, &code)
                } else {
                    scope.and_then(|s| api.resolve_bare(world, s, &code))
                };
                match target.as_ref().and_then(|t| href(api, t)) {
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
h1 { overflow-wrap: anywhere; }
.member { border-top: 1px solid var(--rule); padding-top: 0.5rem; margin-top: 1.2rem; }
.member h3 { font-size: 1rem; margin: 0.3rem 0; overflow-wrap: anywhere; }
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

fn member_html(loaded: &Loaded, api: &Api, page: &Page, m: &Item) -> String {
    let mut s = String::new();
    let _ = writeln!(s, "<section class=\"member\" id=\"{}\">", anchor(m));
    let _ = writeln!(s, "<h3><code>{}</code></h3>", escape(&m.signature));
    if let Some(ext) = &m.extension {
        let _ = writeln!(s, "<p class=\"from\">in <code>{}</code></p>", escape(ext));
    }
    if let Some(d) = &m.doc {
        s.push_str(&markdown_html(loaded, api, Some(page.id), &d.text));
    }
    if let Some(f) = &m.from {
        let from = match api.page(f) {
            Some(_) => format!("<a href=\"{}\">{}</a>", escape(&page_file(f)), escape(f)),
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
        escape(&loaded.location(m.span.start))
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
    let _ = writeln!(s, "<h1><code>{}</code></h1>", escape(&page.signature));
    if !page.includes.is_empty() {
        let names: Vec<String> = page
            .includes
            .iter()
            .map(|n| {
                let base = n.split('[').next().unwrap_or(n);
                match api.page(base) {
                    Some(_) => format!(
                        "<a href=\"{}\"><code>{}</code></a>",
                        escape(&page_file(base)),
                        escape(n)
                    ),
                    None => format!("<code>{}</code>", escape(n)),
                }
            })
            .collect();
        let _ = writeln!(s, "<p>include {}</p>", names.join(", "));
    }
    match (&page.doc, &loaded.readme) {
        (Some(d), _) => s.push_str(&markdown_html(loaded, api, Some(page.id), &d.text)),
        // A library's root module: its README.
        (None, Some(readme)) if page.span.start == 0 => {
            s.push_str(&markdown_html(loaded, api, Some(page.id), readme))
        }
        _ => {}
    }
    let at = loaded.location(page.span.start);
    if !at.is_empty() {
        let _ = writeln!(s, "<p class=\"loc\">{}</p>", escape(&at));
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
        Some(md) => s.push_str(&markdown_html(loaded, api, None, md)),
        None => {
            let _ = writeln!(s, "<h1>{}</h1>", escape(&loaded.title));
        }
    }
    s.push_str("<h2>Classes and modules</h2>\n");
    let all: Vec<&Page> = api.pages.iter().collect();
    s.push_str(&summary_list(api, &all));
    if !api.constants.is_empty() {
        s.push_str("<h2>Constants</h2>\n");
        for k in &api.constants {
            let _ = writeln!(s, "<section class=\"member\" id=\"{}\">", anchor(k));
            let _ = writeln!(s, "<h3><code>{}</code></h3>", escape(&k.signature));
            if let Some(d) = &k.doc {
                s.push_str(&markdown_html(loaded, api, None, &d.text));
            }
            let _ = writeln!(
                s,
                "<p class=\"loc\">{}</p>\n</section>",
                escape(&loaded.location(k.span.start))
            );
        }
    }
    s
}

fn search_index(api: &Api) -> String {
    let mut entries: Vec<String> = Vec::new();
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
