//! Links in a doc's text (docs/13 §3, #881): `[Name]`, `[Name][]` and
//! `[text][Name]` name a declaration, which Markdown alone would leave as
//! a reference to nothing. A code span is plain code.

use pulldown_cmark::{BrokenLink, CowStr, Event, LinkType, Options, Parser, Tag, TagEnd};

use super::{method_name, name_shaped};

/// Whether a bracket at byte `start` of `md` may open a link: not right
/// after a word character, where it is an index or a type argument
/// (`a[i]`, `Array[Int]`, `Hash[K][V]`). The one place this is decided.
pub(crate) fn link_at(md: &str, start: usize) -> bool {
    !md.get(..start)
        .and_then(|s| s.chars().next_back())
        .is_some_and(|c| c.is_alphanumeric() || matches!(c, '_' | '?' | '!' | ']' | ')'))
}

/// The name a link's label gives, if it has a name's grammar: a name's
/// shape (`Foo`, `Foo::Bar`, `Foo#bar`, `Foo.bar`, `#bar`, `.bar`) or a
/// bare method name (`pop`). A backslash escapes a bracket of an
/// operator's name (`Array#\[\]` is `Array#[]`).
pub(crate) fn link_name(label: &str) -> Option<String> {
    let mut name = String::with_capacity(label.len());
    let mut chars = label.chars();
    while let Some(c) = chars.next() {
        match (c, chars.clone().next()) {
            ('\\', Some(n)) if n.is_ascii_punctuation() => {
                name.push(n);
                chars.next();
            }
            _ => name.push(c),
        }
    }
    (name_shaped(&name) || method_name(&name)).then_some(name)
}

/// A name written as a link's label: its brackets escaped.
pub(crate) fn label_of(name: &str) -> String {
    let mut s = String::with_capacity(name.len() + 2);
    for c in name.chars() {
        if matches!(c, '[' | ']' | '\\') {
            s.push('\\');
        }
        s.push(c);
    }
    s
}

/// A doc's Markdown events, with each bracket that names something
/// `dest` gives a destination for made a link: `Tag::Link` with that
/// destination and, as its title, the name. Its type tells the form:
/// `ShortcutUnknown` or `CollapsedUnknown` (`[Name]`, `[Name][]`, shown
/// as the name in code style) or `ReferenceUnknown` (`[text][Name]`,
/// shown as its text). `dest` is called with the name and the bracket's
/// byte range in `md`.
pub(crate) fn events<'a>(
    md: &'a str,
    options: Options,
    mut dest: impl FnMut(&str, std::ops::Range<usize>) -> Option<String> + 'a,
) -> impl Iterator<Item = (Event<'a>, std::ops::Range<usize>)> + 'a {
    let callback = move |link: BrokenLink<'a>| {
        if !link_at(md, link.span.start) {
            return None;
        }
        let name = link_name(&link.reference)?;
        let to = dest(&name, link.span.clone())?;
        Some((CowStr::from(to), CowStr::from(name)))
    };
    Parser::new_with_broken_link_callback(md, options, Some(callback)).into_offset_iter()
}

/// Whether `link_type` is one of a bracket link's (see `events`), with
/// its name shown in place of its text.
pub(crate) fn shows_name(link_type: LinkType) -> Option<bool> {
    match link_type {
        LinkType::ShortcutUnknown | LinkType::CollapsedUnknown => Some(true),
        LinkType::ReferenceUnknown => Some(false),
        _ => None,
    }
}

/// `events` as the pages and the terminal show them: a `[Name]` or
/// `[Name][]` link has the name in code style as its text, and a
/// `[text][Name]` link keeps its text; both are plain `Reference` links
/// with no title.
pub(crate) fn rendered<'a>(
    md: &'a str,
    options: Options,
    dest: impl FnMut(&str, std::ops::Range<usize>) -> Option<String> + 'a,
) -> impl Iterator<Item = Event<'a>> + 'a {
    let mut shown: Option<CowStr<'a>> = None;
    events(md, options, dest).flat_map(move |(e, _)| -> Vec<Event<'a>> {
        match e {
            Event::Start(Tag::Link {
                link_type,
                dest_url,
                title,
                id,
            }) if shows_name(link_type).is_some() => {
                if shows_name(link_type) == Some(true) {
                    shown = Some(title);
                }
                vec![Event::Start(Tag::Link {
                    link_type: LinkType::Reference,
                    dest_url,
                    title: CowStr::from(""),
                    id,
                })]
            }
            Event::End(TagEnd::Link) if shown.is_some() => {
                let name = shown.take().unwrap_or(CowStr::Borrowed(""));
                vec![Event::Code(name), Event::End(TagEnd::Link)]
            }
            _ if shown.is_some() => Vec::new(),
            other => vec![other],
        }
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_bracket_glued_to_a_word_is_no_link() {
        assert!(link_at("[Int]", 0));
        assert!(link_at("see [Int]", 4));
        assert!(link_at("(see [Int])", 5));
        assert!(!link_at("Array[Int]", 5));
        assert!(!link_at("a[i]", 1));
        assert!(!link_at("Hash[K][V]", 7));
        assert!(!link_at("f(x)[0]", 4));
    }

    #[test]
    fn names_in_brackets() {
        assert_eq!(link_name("Array#push").as_deref(), Some("Array#push"));
        assert_eq!(link_name("#pop").as_deref(), Some("#pop"));
        assert_eq!(link_name("pop").as_deref(), Some("pop"));
        assert_eq!(link_name("empty?").as_deref(), Some("empty?"));
        assert_eq!(link_name("Array#\\[\\]").as_deref(), Some("Array#[]"));
        assert_eq!(link_name("1"), None);
        assert_eq!(link_name("the push method"), None);
        assert_eq!(link_name("Array[Int]"), None);
        assert_eq!(label_of("Array#[]="), "Array#\\[\\]=");
        assert_eq!(
            link_name(&label_of("Hash#[]=")).as_deref(),
            Some("Hash#[]=")
        );
    }

    fn html(md: &str) -> String {
        let mut s = String::new();
        let events = rendered(md, Options::empty(), |name, _| {
            (name != "Nothing").then(|| format!("{name}.html"))
        });
        pulldown_cmark::html::push_html(&mut s, events);
        s
    }

    #[test]
    fn the_forms_of_a_link() {
        assert_eq!(
            html("See [Foo]."),
            "<p>See <a href=\"Foo.html\"><code>Foo</code></a>.</p>\n"
        );
        assert_eq!(
            html("See [Foo][]."),
            "<p>See <a href=\"Foo.html\"><code>Foo</code></a>.</p>\n"
        );
        assert_eq!(
            html("See [the foo][Foo]."),
            "<p>See <a href=\"Foo.html\">the foo</a>.</p>\n"
        );
        assert_eq!(html("See [Nothing]."), "<p>See [Nothing].</p>\n");
        assert_eq!(
            html("An Array[Int], a[i]."),
            "<p>An Array[Int], a[i].</p>\n"
        );
        assert_eq!(
            // (A code span is code; `[1]` is no name; a bare word links
            // only when it names something, here every word does.)
            html("`[Foo]` [1] [sic]"),
            "<p><code>[Foo]</code> [1] <a href=\"sic.html\"><code>sic</code></a></p>\n"
        );
        assert_eq!(
            html("[x](https://e.org) [Foo]"),
            "<p><a href=\"https://e.org\">x</a> <a href=\"Foo.html\"><code>Foo</code></a></p>\n"
        );
        assert_eq!(
            html("[Array#\\[\\]]"),
            "<p><a href=\"Array#%5B%5D.html\"><code>Array#[]</code></a></p>\n"
        );
    }
}
