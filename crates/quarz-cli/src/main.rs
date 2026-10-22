//! The `quarz` command.

use std::process::ExitCode;

mod repl;

use quarz_syntax::{parse, tokenize, SourceFile, TokenKind};

const USAGE: &str = "\
usage: quarz <command> [args]

commands:
  tokens FILE    print the tokens of FILE (for debugging the lexer)
  parse FILE     print the syntax tree of FILE (for debugging the parser)
  check FILE     type-check FILE
  ir FILE        print the QIR of FILE (for debugging the lowering)
  build FILE [-o OUT]
                 compile FILE to a native executable (default: FILE without .qz)
  run FILE [ARGS...]   type-check and run FILE
  repl           start an interactive session
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
        Some("ir") => match args.get(1) {
            Some(path) => ir_file(path),
            None => usage(),
        },
        Some("build") => match args.get(1) {
            Some(path) => {
                let out = match args.iter().position(|a| a == "-o") {
                    Some(i) => match args.get(i + 1) {
                        Some(o) => std::path::PathBuf::from(o),
                        None => return usage(),
                    },
                    None => {
                        let p = std::path::Path::new(path);
                        p.with_extension("")
                    }
                };
                build_file(path, &out)
            }
            None => usage(),
        },
        Some("repl") => repl::repl(),
        Some("run") => match args.get(1) {
            Some(path) => run_file(path, args[2..].to_vec()),
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

/// Load the file and everything it requires, then type-check. Returns the
/// checked program and the source files by index (0 = the prelude) if
/// there were no errors.
fn load_and_check(path: &str) -> Option<(quarz_types::Checked, Vec<SourceFile>)> {
    let prelude_file = SourceFile::new("<prelude>", quarz_types::PRELUDE_SOURCE);
    let prelude = parse(&prelude_file.text);
    let mut failed = false;
    for diag in &prelude.diagnostics {
        eprint!("{}", diag.render(&prelude_file));
        failed |= diag.is_error();
    }
    let (units, diagnostics) = quarz_types::load(std::path::Path::new(path));
    for (file, diag) in &diagnostics {
        eprint!("{}", diag.render(file));
        failed |= diag.is_error();
    }
    if failed {
        return None;
    }
    let sources: Vec<SourceFile> = units.iter().map(|u| u.source.clone()).collect();
    let to_check: Vec<quarz_types::Unit> = units
        .into_iter()
        .map(|u| quarz_types::Unit {
            name: u.name,
            program: u.program,
        })
        .collect();
    let (checked, diagnostics) = quarz_types::check_units(&prelude.program, &to_check);
    for (file_index, diag) in &diagnostics {
        let f = if *file_index == 0 {
            &prelude_file
        } else {
            &sources[*file_index as usize - 1]
        };
        eprint!("{}", diag.render(f));
    }
    let mut files = vec![prelude_file];
    files.extend(sources);
    checked.map(|c| (c, files))
}

fn run_file(path: &str, argv: Vec<String>) -> ExitCode {
    let Some((checked, files)) = load_and_check(path) else {
        return ExitCode::FAILURE;
    };
    let code = quarz_cli::run(checked, &files, argv);
    ExitCode::from(code.clamp(0, 255) as u8)
}

fn ir_file(path: &str) -> ExitCode {
    let Some((checked, files)) = load_and_check(path) else {
        return ExitCode::FAILURE;
    };
    let module = quarz_cli::lower(&checked, &files);
    print!("{}", quarz_ir::dump::dump_module(&module));
    ExitCode::SUCCESS
}

fn build_file(path: &str, out: &std::path::Path) -> ExitCode {
    let Some((checked, files)) = load_and_check(path) else {
        return ExitCode::FAILURE;
    };
    match quarz_cli::build(checked, &files, out) {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("quarz: {e}");
            ExitCode::FAILURE
        }
    }
}

fn check_file(path: &str) -> ExitCode {
    match load_and_check(path) {
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
