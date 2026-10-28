//! The TextMate grammar (`editors/textmate/quarz.tmLanguage.json`, used by
//! the website's highlighting) knows the lexer's keywords: adding one to
//! `Keyword` fails here until the grammar has it too.

use std::collections::BTreeSet;

use quarz_syntax::Keyword;
use serde_json::Value;

fn grammar() -> Value {
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../editors/textmate/quarz.tmLanguage.json"
    );
    let text = std::fs::read_to_string(path).expect("read the grammar");
    serde_json::from_str(&text).expect("the grammar is JSON")
}

#[test]
fn names_the_language() {
    let g = grammar();
    assert_eq!(g["name"], "quarz");
    assert_eq!(g["scopeName"], "source.quarz");
}

/// The words of the `keywords` rules, each written
/// `(?<!...)(?:word|word|...)(?!...)`.
fn grammar_keywords(g: &Value) -> BTreeSet<String> {
    let mut words = BTreeSet::new();
    let patterns = g["repository"]["keywords"]["patterns"]
        .as_array()
        .expect("a `keywords` rule with patterns");
    for p in patterns {
        let m = p["match"].as_str().expect("a match");
        let (_, rest) = m.split_once(")(?:").expect("`(?:` after the lookbehind");
        let (list, _) = rest.split_once(')').expect("the list's `)`");
        for w in list.split('|') {
            let w = w.replace('\\', "");
            assert!(words.insert(w.clone()), "{w} is in the grammar twice");
        }
    }
    words
}

#[test]
fn keywords_match_the_lexer() {
    let g = grammar();
    let top = g["patterns"].as_array().expect("top-level patterns");
    assert!(
        top.iter().any(|p| p["include"] == "#keywords"),
        "the grammar does not use its `keywords` rule"
    );
    let in_grammar = grammar_keywords(&g);
    let in_lexer: BTreeSet<String> = Keyword::ALL
        .iter()
        .map(|k| k.as_str().to_string())
        .collect();
    for k in Keyword::ALL {
        assert_eq!(Keyword::from_ident(k.as_str()), Some(*k));
    }
    let missing: Vec<_> = in_lexer.difference(&in_grammar).collect();
    let extra: Vec<_> = in_grammar.difference(&in_lexer).collect();
    assert!(
        missing.is_empty() && extra.is_empty(),
        "editors/textmate/quarz.tmLanguage.json's `keywords` differ from token.rs: \
         missing {missing:?}, not keywords {extra:?}"
    );
}
