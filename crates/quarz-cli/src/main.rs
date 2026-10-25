//! The `quarz` command.

use std::process::ExitCode;

mod cog;
mod doc;
mod repl;
mod test;

use quarz_syntax::{parse, tokenize, SourceFile, TokenKind};

const USAGE: &str = "\
usage: quarz <command> [args]

commands:
  tokens FILE    print the tokens of FILE (for debugging the lexer)
  parse FILE     print the syntax tree of FILE (for debugging the parser)
  check [TARGET] type-check TARGET
  ir [TARGET]    print the QIR of TARGET (for debugging the lowering)
  build [TARGET] [-o OUT]
                 compile TARGET to a native executable (default: a script
                 without .qz, or the cog's name in its directory)
  run [TARGET] [ARGS...]   type-check and run TARGET (`--` before ARGS
                 when TARGET is left out)
  test [PATHS...] [OPTIONS]
                 run the tests of PATHS (`*_test.qz` files, or directories
                 of them; default: the cog's test/), `--release` compiled;
                 OPTIONS: -n NAME, -v, --list, --order=random, --seed=N,
                 --fail-fast, --parallel[=N], --timeout=D, --junit=PATH
  repl           start an interactive session
  cog COMMAND    manage the cogs (packages) of the application here:
    init                      write a Cog.toml (and src/main.qz)
    add URL [--tag vX.Y.Z | --rev COMMIT] [--as KEY] [--subdir DIR] [--dev]
                              add a dependency and resolve
    update                    resolve again and rewrite Cog.lock
    fetch                     fetch and verify what Cog.lock names
    vendor                    copy the locked cogs into vendor/
    tree                      print the dependency graph
    outdated                  show newer version tags of the locked cogs
    verify                    check the fetched cogs against Cog.lock

TARGET is a script (FILE.qz), or an application: a directory with a
Cog.toml, its src/main.qz, or (left out) the one around the current
directory. With an application, --locked fails rather than write
Cog.lock, and --offline fetches nothing.
";

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    // The prelude declared and checked when `quarz` was built (build.rs);
    // `QUARZ_NO_PRELUDE_CACHE=1` checks it from its source instead.
    if std::env::var_os("QUARZ_NO_PRELUDE_CACHE").is_none_or(|v| v == "0") {
        quarz_types::set_prelude_cache(include_bytes!(concat!(env!("OUT_DIR"), "/prelude.bin")));
    }
    match args.first().map(String::as_str) {
        Some("tokens") => match args.get(1) {
            Some(path) => tokens(path),
            None => usage(),
        },
        Some("parse") => match args.get(1) {
            Some(path) => parse_file(path),
            None => usage(),
        },
        Some("check") => match Target::parse(&args[1..]) {
            Ok((target, rest)) if rest.is_empty() => check_file(&target),
            Ok(_) => usage(),
            Err(code) => code,
        },
        Some("ir") => match Target::parse(&args[1..]) {
            Ok((target, rest)) if rest.is_empty() => ir_file(&target),
            Ok(_) => usage(),
            Err(code) => code,
        },
        Some("build") => {
            let mut rest: Vec<String> = args[1..].to_vec();
            let mut out = None;
            if let Some(i) = rest.iter().position(|a| a == "-o") {
                match rest.get(i + 1) {
                    Some(o) => out = Some(std::path::PathBuf::from(o)),
                    None => return usage(),
                }
                rest.drain(i..i + 2);
            }
            match Target::parse(&rest) {
                Ok((target, extra)) if extra.is_empty() => {
                    let out = out.unwrap_or_else(|| target.default_output());
                    build_file(&target, &out)
                }
                Ok(_) => usage(),
                Err(code) => code,
            }
        }
        Some("repl") => repl::repl(),
        Some("run") => match Target::parse(&args[1..]) {
            Ok((target, argv)) => run_file(&target, argv),
            Err(code) => code,
        },
        Some("cog") => cog::command(&args[1..]),
        Some("test") => test::command(&args[1..]),
        Some("doc") => doc::command(&args[1..]),
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

/// What `run`, `check`, `build` and `ir` work on: a script, or the
/// application of a movement.
enum Target {
    Script(String),
    App {
        root: std::path::PathBuf,
        opts: quarz_cog::Options,
    },
}

impl Target {
    /// The target and the arguments after it: `--locked` and `--offline`
    /// first, then a script, a directory with a Cog.toml or an
    /// application's src/main.qz, or nothing (or `--`) for the application
    /// around the current directory.
    fn parse(args: &[String]) -> Result<(Target, Vec<String>), ExitCode> {
        let mut opts = quarz_cog::Options {
            verbose: true,
            ..Default::default()
        };
        let mut i = 0;
        while let Some(a) = args.get(i) {
            match a.as_str() {
                "--locked" => opts.locked = true,
                "--offline" => opts.offline = true,
                _ => break,
            }
            i += 1;
        }
        let app = |root: std::path::PathBuf, opts| Target::App { root, opts };
        match args.get(i).map(String::as_str) {
            None | Some("--") => {
                let here = std::env::current_dir().unwrap_or_default();
                match quarz_cog::find_root(&here) {
                    Some(root) => Ok((
                        app(root, opts),
                        args.get(i + 1..).unwrap_or_default().to_vec(),
                    )),
                    None => {
                        eprintln!("quarz: no Cog.toml here or above; give a file to run");
                        Err(ExitCode::from(2))
                    }
                }
            }
            Some(path) => {
                let p = std::path::Path::new(path);
                let rest = args[i + 1..].to_vec();
                if p.is_dir() {
                    if p.join(quarz_cog::manifest::MANIFEST).is_file() {
                        let root = std::fs::canonicalize(p).unwrap_or_else(|_| p.to_path_buf());
                        return Ok((app(root, opts), rest));
                    }
                    eprintln!("quarz: {path} has no Cog.toml");
                    return Err(ExitCode::FAILURE);
                }
                // An application's main file.
                if let Some(root) = std::fs::canonicalize(p).ok().and_then(|f| {
                    Some(f.parent()?.parent()?.to_path_buf()).filter(|r| {
                        r.join(quarz_cog::manifest::MANIFEST).is_file()
                            && r.join("src").join("main.qz") == f
                    })
                }) {
                    return Ok((app(root, opts), rest));
                }
                Ok((Target::Script(path.to_string()), rest))
            }
        }
    }

    fn default_output(&self) -> std::path::PathBuf {
        match self {
            Target::Script(path) => std::path::Path::new(path).with_extension(""),
            Target::App { root, .. } => {
                let name = quarz_cog::manifest::Manifest::read(root)
                    .map(|m| m.cog.name)
                    .unwrap_or_else(|_| "app".to_string());
                root.join(name)
            }
        }
    }
}

/// Load the target and everything it requires, then type-check. Returns
/// the checked program and the source files by index (0 = the prelude) if
/// there were no errors.
fn load_and_check(target: &Target) -> Option<(quarz_types::Checked, Vec<SourceFile>)> {
    let prelude_file = SourceFile::new("<prelude>", quarz_types::PRELUDE_SOURCE);
    let prelude = quarz_types::parse_prelude();
    let mut failed = false;
    for diag in &prelude.diagnostics {
        eprint!("{}", diag.render(&prelude_file));
        failed |= diag.is_error();
    }
    let (units, cogs, diagnostics) = match target {
        Target::Script(path) => {
            let (units, diagnostics) = quarz_types::load(std::path::Path::new(path));
            (units, Vec::new(), diagnostics)
        }
        Target::App { root, opts } => {
            let movement = match quarz_cog::open(root, opts) {
                Ok(m) => m,
                Err(e) => {
                    eprintln!("quarz: {e}");
                    return None;
                }
            };
            // Not the cogs only dev-dependencies reach (`quarz test`'s).
            let specs: Vec<quarz_types::CogSpec> = movement.cogs[..movement.dev_from]
                .iter()
                .enumerate()
                .map(|(i, c)| quarz_types::CogSpec {
                    name: c.name.clone(),
                    version: c.version.clone(),
                    module: (i > 0).then(|| c.module.clone()),
                    src: c.dir.join("src"),
                    imports: c
                        .imports
                        .iter()
                        .map(|(k, j)| (k.clone(), *j as u32))
                        .collect(),
                })
                .collect();
            quarz_types::load_movement(&specs)
        }
    };
    for (file, diag) in &diagnostics {
        eprint!("{}", diag.render(file));
        failed |= diag.is_error();
    }
    if failed {
        return None;
    }
    let sources: Vec<SourceFile> = units.iter().map(|u| u.source.clone()).collect();
    let to_check: Vec<quarz_types::Unit> = units.into_iter().map(quarz_types::Unit::from).collect();
    let (checked, diagnostics) = quarz_types::check_movement(&prelude.program, &to_check, &cogs);
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

fn run_file(target: &Target, argv: Vec<String>) -> ExitCode {
    let Some((checked, files)) = load_and_check(target) else {
        return ExitCode::FAILURE;
    };
    let code = quarz_cli::run(checked, &files, argv);
    ExitCode::from(code.clamp(0, 255) as u8)
}

fn ir_file(target: &Target) -> ExitCode {
    let Some((checked, files)) = load_and_check(target) else {
        return ExitCode::FAILURE;
    };
    let module = quarz_cli::lower(&checked, &files);
    print!("{}", quarz_ir::dump::dump_module(&module));
    ExitCode::SUCCESS
}

fn build_file(target: &Target, out: &std::path::Path) -> ExitCode {
    let Some((checked, files)) = load_and_check(target) else {
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

fn check_file(target: &Target) -> ExitCode {
    match load_and_check(target) {
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
