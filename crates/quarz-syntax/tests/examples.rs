//! Every example program must lex without errors.

use quarz_syntax::{parse, tokenize, SourceFile, TokenKind};
use std::fs;
use std::path::Path;

#[test]
fn examples_lex_cleanly() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples");
    let mut count = 0;
    for entry in fs::read_dir(&dir).expect("examples directory") {
        let path = entry.unwrap().path();
        if path.extension().and_then(|e| e.to_str()) != Some("qz") {
            continue;
        }
        count += 1;
        let text = fs::read_to_string(&path).unwrap();
        let file = SourceFile::new(path.display().to_string(), text);
        let lexed = tokenize(&file.text);
        let errors: Vec<String> = lexed
            .diagnostics
            .iter()
            .filter(|d| d.is_error())
            .map(|d| d.render(&file))
            .collect();
        assert!(errors.is_empty(), "{}", errors.join("\n"));
        assert!(matches!(lexed.tokens.last().unwrap().kind, TokenKind::Eof));
        assert!(
            !lexed
                .tokens
                .iter()
                .any(|t| matches!(t.kind, TokenKind::Error)),
            "{}: error tokens",
            path.display()
        );
    }
    assert!(count >= 7, "expected the example programs to be present");
}

#[test]
fn examples_parse_cleanly() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples");
    for entry in fs::read_dir(&dir).expect("examples directory") {
        let path = entry.unwrap().path();
        if path.extension().and_then(|e| e.to_str()) != Some("qz") {
            continue;
        }
        let text = fs::read_to_string(&path).unwrap();
        let file = SourceFile::new(path.display().to_string(), text);
        let parsed = parse(&file.text);
        let messages: Vec<String> = parsed.diagnostics.iter().map(|d| d.render(&file)).collect();
        assert!(messages.is_empty(), "{}", messages.join("\n"));
        assert!(!parsed.program.body.is_empty());
    }
}
