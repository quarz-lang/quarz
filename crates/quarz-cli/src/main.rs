//! The `quarz` command.

use std::process::ExitCode;

use quarz_syntax::{parse, tokenize, SourceFile, TokenKind};

const USAGE: &str = "\
usage: quarz <command> [args]

commands:
  tokens FILE    print the tokens of FILE (for debugging the lexer)
  parse FILE     print the syntax tree of FILE (for debugging the parser)
  check FILE     type-check FILE
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
        Some("check") => match args.get(1) {
            Some(path) => check_file(path),
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

/// Parse the prelude and the user file, then type-check. Returns the
/// checked program if there were no errors.
fn load_and_check(file: &SourceFile) -> Option<quarz_types::Checked> {
    let prelude_file = SourceFile::new("<prelude>", quarz_types::PRELUDE_SOURCE);
    let prelude = parse(&prelude_file.text);
    let parsed = parse(&file.text);
    let mut failed = false;
    for diag in &prelude.diagnostics {
        eprint!("{}", diag.render(&prelude_file));
        failed |= diag.is_error();
    }
    for diag in &parsed.diagnostics {
        eprint!("{}", diag.render(file));
        failed |= diag.is_error();
    }
    if failed {
        return None;
    }
    let (checked, diagnostics) = quarz_types::check(&prelude.program, &parsed.program);
    for (file_index, diag) in &diagnostics {
        let f = if *file_index == 0 {
            &prelude_file
        } else {
            file
        };
        eprint!("{}", diag.render(f));
    }
    checked
}

fn check_file(path: &str) -> ExitCode {
    let file = match read_source(path) {
        Ok(file) => file,
        Err(code) => return code,
    };
    match load_and_check(&file) {
        Some(_) => ExitCode::SUCCESS,
        None => ExitCode::FAILURE,
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
