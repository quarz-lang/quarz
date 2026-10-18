//! The `quarz` command.

use std::process::ExitCode;

use quarz_syntax::{parse, tokenize, SourceFile, TokenKind};

const USAGE: &str = "\
usage: quarz <command> [args]

commands:
  tokens FILE    print the tokens of FILE (for debugging the lexer)
  parse FILE     print the syntax tree of FILE (for debugging the parser)
";

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match args.first().map(String::as_str) {
        Some("tokens") => match args.get(1) {
            Some(path) => tokens(path),
            None => usage(),
        },
        Some("parse") => match args.get(1) {
            Some(path) => parse_file(path),
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

fn read_source(path: &str) -> Result<SourceFile, ExitCode> {
    match std::fs::read_to_string(path) {
        Ok(text) => Ok(SourceFile::new(path, text)),
        Err(err) => {
            eprintln!("quarz: {path}: {err}");
            Err(ExitCode::FAILURE)
        }
    }
}

fn parse_file(path: &str) -> ExitCode {
    let file = match read_source(path) {
        Ok(file) => file,
        Err(code) => return code,
    };
    let parsed = parse(&file.text);
    print!("{}", quarz_syntax::sexp::program_to_sexp(&parsed.program));
    let mut failed = false;
    for diag in &parsed.diagnostics {
        eprint!("{}", diag.render(&file));
        failed |= diag.is_error();
    }
    if failed {
        ExitCode::FAILURE
    } else {
        ExitCode::SUCCESS
    }
}

fn tokens(path: &str) -> ExitCode {
    let file = match read_source(path) {
        Ok(file) => file,
        Err(code) => return code,
    };
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
