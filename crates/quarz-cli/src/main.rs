//! The `quarz` command. Only `quarz tokens FILE` exists so far.

use std::process::ExitCode;

use quarz_syntax::{tokenize, SourceFile, TokenKind};

const USAGE: &str = "\
usage: quarz <command> [args]

commands:
  tokens FILE    print the tokens of FILE (for debugging the lexer)
";

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match args.first().map(String::as_str) {
        Some("tokens") => match args.get(1) {
            Some(path) => tokens(path),
            None => usage(),
        },
        Some("-h" | "--help" | "help") => {
            print!("{USAGE}");
            ExitCode::SUCCESS
        }
        _ => usage(),
    }
}

fn usage() -> ExitCode {
    eprint!("{USAGE}");
    ExitCode::from(2)
}

fn tokens(path: &str) -> ExitCode {
    let text = match std::fs::read_to_string(path) {
        Ok(text) => text,
        Err(err) => {
            eprintln!("quarz: {path}: {err}");
            return ExitCode::FAILURE;
        }
    };
    let file = SourceFile::new(path, text);
    let lexed = tokenize(&file.text);

    for tok in &lexed.tokens {
        let lc = file.line_col(tok.span.start);
        let space = if tok.space_before { " " } else { "" };
        println!("{:>4}:{:<3} {}{}", lc.line, lc.col, space, tok.kind);
        if matches!(tok.kind, TokenKind::Eof) {
            break;
        }
    }
    if let Some(offset) = lexed.data_offset {
        println!("__END__ data: {} bytes", file.text.len() - offset);
    }

    let mut failed = false;
    for diag in &lexed.diagnostics {
        eprint!("{}", diag.render(&file));
        failed |= diag.is_error();
    }
    if failed {
        ExitCode::FAILURE
    } else {
        ExitCode::SUCCESS
    }
}
