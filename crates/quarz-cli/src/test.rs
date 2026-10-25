//! `quarz test`: load the test files, list the `Test::Case` classes and
//! their `test_*` methods once they are checked, and add a runner calling
//! `Test.run` as one more unit (docs/12-testing.md).

use std::path::{Path, PathBuf};
use std::process::ExitCode;

use quarz_syntax::ast::{ParamKind, Visibility};
use quarz_syntax::{parse, Diagnostic, SourceFile, Span};
use quarz_types::{ClassId, ClassKind, FileDiagnostic, Member, World};

/// The runner's file name, which `Test.location` leaves out of backtraces.
const RUNNER: &str = "<test-runner>";

pub fn command(args: &[String]) -> ExitCode {
    let mut paths: Vec<PathBuf> = Vec::new();
    let mut argv: Vec<String> = Vec::new();
    let mut release = false;
    let mut opts = quarz_cog::Options {
        verbose: true,
        ..Default::default()
    };
    let mut i = 0;
    while let Some(a) = args.get(i) {
        match a.as_str() {
            "--release" => release = true,
            "--locked" => opts.locked = true,
            "--offline" => opts.offline = true,
            "--" => {
                argv.extend(args[i + 1..].iter().cloned());
                break;
            }
            "-n" | "--name" => {
                argv.push(a.clone());
                if let Some(v) = args.get(i + 1) {
                    argv.push(v.clone());
                    i += 1;
                }
            }
            _ if a.starts_with('-') => argv.push(a.clone()),
            _ => paths.push(PathBuf::from(a)),
        }
        i += 1;
    }
    // The cog around the current directory, when the tests are its own
    // (none given, or all under its test/).
    let here = std::env::current_dir().unwrap_or_default();
    let cog = quarz_cog::find_root(&here).filter(|root| {
        let tests = root.join("test");
        paths
            .iter()
            .all(|p| std::fs::canonicalize(p).is_ok_and(|p| p.starts_with(&tests)))
    });
    if paths.is_empty() {
        match &cog {
            Some(root) => paths.push(root.join("test")),
            None => {
                eprintln!("quarz test: no Cog.toml here or above; give the test files");
                return ExitCode::from(2);
            }
        }
    }
    let files = match test_files(&paths) {
        Ok(f) => f,
        Err(code) => return code,
    };
    if files.is_empty() {
        eprintln!("quarz test: no test files (`*_test.qz`)");
        return ExitCode::FAILURE;
    }
    let Some((checked, sources)) = load_and_check(&files, cog.as_deref(), &opts) else {
        return ExitCode::FAILURE;
    };
    if release {
        let dir = std::env::temp_dir().join(format!("quarz-test-{}", std::process::id()));
        if let Err(e) = std::fs::create_dir_all(&dir) {
            eprintln!("quarz test: {}: {e}", dir.display());
            return ExitCode::FAILURE;
        }
        let exe = dir.join("test");
        let built = quarz_cli::build(checked, &sources, &exe);
        let code = match built {
            Ok(()) => match std::process::Command::new(&exe).args(&argv).status() {
                Ok(status) => ExitCode::from(status.code().unwrap_or(1).clamp(0, 255) as u8),
                Err(e) => {
                    eprintln!("quarz test: {}: {e}", exe.display());
                    ExitCode::FAILURE
                }
            },
            Err(e) => {
                eprintln!("quarz: {e}");
                ExitCode::FAILURE
            }
        };
        let _ = std::fs::remove_dir_all(&dir);
        return code;
    }
    let code = quarz_cli::run(checked, &sources, argv);
    ExitCode::from(code.clamp(0, 255) as u8)
}

/// The files to load: those given, a directory standing for its
/// `**/*_test.qz`, with a `test_helper.qz` in it first.
fn test_files(paths: &[PathBuf]) -> Result<Vec<PathBuf>, ExitCode> {
    let mut out: Vec<PathBuf> = Vec::new();
    for p in paths {
        if p.is_dir() {
            let helper = p.join("test_helper.qz");
            if helper.is_file() {
                out.push(helper);
            }
            let mut found = Vec::new();
            collect(p, &mut found);
            found.sort();
            out.extend(found);
        } else if p.is_file() {
            out.push(p.clone());
        } else {
            eprintln!("quarz test: {}: no such file or directory", p.display());
            return Err(ExitCode::FAILURE);
        }
    }
    Ok(out)
}

fn collect(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for e in entries.flatten() {
        let p = e.path();
        if p.is_dir() {
            collect(&p, out);
        } else if p
            .file_name()
            .and_then(|n| n.to_str())
            .is_some_and(|n| n.ends_with("_test.qz"))
        {
            out.push(p);
        }
    }
}

/// The cogs to load for testing the cog in `root`: an application with
/// its dependencies and dev-dependencies, the test files joining its
/// files; for a library, a root of the test files' own, importing the
/// library under its module, its dependencies and dev-dependencies.
fn test_specs(root: &Path, opts: &quarz_cog::Options) -> Result<Vec<quarz_types::CogSpec>, String> {
    let movement = quarz_cog::open(root, opts).map_err(|e| e.to_string())?;
    let spec = |c: &quarz_cog::CogEntry, module: Option<String>, shift: u32| quarz_types::CogSpec {
        name: c.name.clone(),
        version: c.version.clone(),
        module,
        src: c.dir.join("src"),
        imports: c
            .imports
            .iter()
            .map(|(k, j)| (k.clone(), *j as u32 + shift))
            .collect(),
    };
    let app = &movement.cogs[0];
    if app.dir.join("src").join("main.qz").is_file() {
        let mut specs: Vec<quarz_types::CogSpec> = movement
            .cogs
            .iter()
            .enumerate()
            .map(|(i, c)| spec(c, (i > 0).then(|| c.module.clone()), 0))
            .collect();
        for (k, j) in &app.dev_imports {
            if !specs[0].imports.iter().any(|(m, _)| m == k) {
                specs[0].imports.push((k.clone(), *j as u32));
            }
        }
        return Ok(specs);
    }
    let mut imports = vec![(app.module.clone(), 1)];
    for (k, j) in app.imports.iter().chain(&app.dev_imports) {
        if !imports.iter().any(|(m, _)| m == k) {
            imports.push((k.clone(), *j as u32 + 1));
        }
    }
    let mut specs = vec![quarz_types::CogSpec {
        name: format!("{}-test", app.name),
        version: app.version.clone(),
        module: None,
        // No src/: the root has only the test files.
        src: PathBuf::new(),
        imports,
    }];
    specs.extend(
        movement
            .cogs
            .iter()
            .map(|c| spec(c, Some(c.module.clone()), 1)),
    );
    Ok(specs)
}

fn load_and_check(
    files: &[PathBuf],
    cog: Option<&Path>,
    opts: &quarz_cog::Options,
) -> Option<(quarz_types::Checked, Vec<SourceFile>)> {
    let prelude_file = SourceFile::new("<prelude>", quarz_types::PRELUDE_SOURCE);
    let prelude = parse(&prelude_file.text);
    let (units, decls, diagnostics) = match cog {
        Some(root) => match test_specs(root, opts) {
            Ok(specs) => quarz_types::load_movement_tests(&specs, files),
            Err(e) => {
                eprintln!("quarz: {e}");
                return None;
            }
        },
        None => {
            let (units, diagnostics) = quarz_types::load::load_files(files, &["test"]);
            (units, Vec::new(), diagnostics)
        }
    };
    let mut failed = false;
    for (file, diag) in &diagnostics {
        eprint!("{}", diag.render(file));
        failed |= diag.is_error();
    }
    if failed {
        return None;
    }
    let mut sources: Vec<SourceFile> = units.iter().map(|u| u.source.clone()).collect();
    let to_check: Vec<quarz_types::Unit> = units.into_iter().map(quarz_types::Unit::from).collect();
    let base = quarz_types::load::unit_base(to_check.len() as u32);
    let mut runner: Option<SourceFile> = None;
    let mut extra = |world: &World| {
        let text = runner_source(world, &sources)?;
        let source = SourceFile::with_base(RUNNER, text, base);
        runner = Some(source.clone());
        Ok(source)
    };
    let (checked, diagnostics) =
        quarz_types::check_with_extra(&prelude.program, &to_check, &decls, Some(&mut extra));
    let runner_file = to_check.len() as u32 + 1;
    let runner = runner.unwrap_or_else(|| SourceFile::with_base(RUNNER, String::new(), base));
    for (file_index, diag) in &diagnostics {
        // The runner's warnings (unreachable code after a test that
        // always raises) are not the user's.
        if *file_index == runner_file && !diag.is_error() {
            continue;
        }
        let f = match *file_index {
            0 => &prelude_file,
            i if i == runner_file => &runner,
            i => &sources[i as usize - 1],
        };
        eprint!("{}", diag.render(f));
    }
    let mut files = vec![prelude_file];
    files.append(&mut sources);
    files.push(runner);
    checked.map(|c| (c, files))
}

/// A Quarz string literal for `s`.
fn literal(s: &str) -> String {
    let mut out = String::from("\"");
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '#' => out.push_str("\\#"),
            '\n' => out.push_str("\\n"),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

/// The runner: `Test.run` over the test classes of the loaded files, in
/// file order and then declaration order. Errors name a test method the
/// runner cannot call.
fn runner_source(world: &World, sources: &[SourceFile]) -> Result<String, Vec<FileDiagnostic>> {
    let case = world
        .top_class("Test")
        .and_then(|t| match world.member_in(Some(t), "Case") {
            Some(Member::Class(c)) => Some(c),
            _ => None,
        })
        .ok_or_else(|| {
            vec![(
                0,
                Diagnostic::error("`Test::Case` is not loaded", Span::empty(0)),
            )]
        })?;
    let mut classes: Vec<ClassId> = world
        .classes
        .iter()
        .filter(|c| {
            c.kind == ClassKind::Class
                && c.id != case
                && c.file != 0
                && !world.std_files.contains(&c.file)
                && !c.is_abstract
                && c.type_params.is_empty()
                && world.class_is_a(c.id, case)
        })
        .map(|c| c.id)
        .collect();
    classes.sort_by_key(|c| world.class(*c).span.start);
    let mut errors = Vec::new();
    let mut suites = Vec::new();
    for cid in classes {
        let class = world.class(cid);
        let name = &class.name;
        // The `test_*` methods of the class and of its ancestors below
        // `Test::Case`, the most derived definition of each name.
        let below_case: Vec<ClassId> = world
            .ancestor_ids(cid)
            .into_iter()
            .take_while(|a| *a != case)
            .collect();
        // The runner makes each instance with `new` and no arguments.
        let init = below_case
            .iter()
            .find_map(|a| world.class(*a).methods.get("initialize"))
            .filter(|ids| {
                !ids.iter()
                    .any(|i| world.method(*i).params.iter().all(|p| p.default.is_some()))
            });
        if let Some(ids) = init {
            let m = world.method(ids[0]);
            errors.push((
                world.class(m.owner).file,
                Diagnostic::error(
                    format!("{name}: a test class is made by `new` with no arguments, which this initialize does not take"),
                    m.span,
                ),
            ));
            continue;
        }
        let mut tests: Vec<(String, quarz_types::MethodId)> = Vec::new();
        for a in &below_case {
            let mut names: Vec<&String> = world
                .class(*a)
                .methods
                .keys()
                .filter(|n| n.starts_with("test_"))
                .collect();
            names.sort();
            for n in names {
                if tests.iter().any(|(t, _)| t == n) {
                    continue;
                }
                let ids = &world.class(*a).methods[n];
                if ids.len() > 1 {
                    let m = world.method(ids[1]);
                    let file = world.class(m.owner).file;
                    errors.push((
                        file,
                        Diagnostic::error(
                            format!("{name}#{n}: a test method cannot be overloaded"),
                            m.span,
                        ),
                    ));
                    continue;
                }
                tests.push((n.clone(), ids[0]));
            }
        }
        tests.sort_by_key(|(_, m)| world.method(*m).span.start);
        let file = sources
            .get(class.file as usize - 1)
            .map(|s| s.name.clone())
            .unwrap_or_default();
        let mut entries = Vec::new();
        for (test, mid) in &tests {
            let m = world.method(*mid);
            let at = world.class(m.owner).file;
            let mut error = |msg: String| errors.push((at, Diagnostic::error(msg, m.span)));
            let source = (at as usize).checked_sub(1).and_then(|i| sources.get(i));
            let line = source.map(|s| s.line_col(m.span.start).line).unwrap_or(0);
            let method_file = literal(&source.map(|s| s.name.clone()).unwrap_or_default());
            if m.visibility != Visibility::Public {
                error(format!("{name}#{test}: a test method must be public"));
                continue;
            }
            let required: Vec<_> = m
                .params
                .iter()
                .filter(|p| p.default.is_none() || !matches!(p.kind, ParamKind::Positional))
                .collect();
            match required.as_slice() {
                [] => entries.push(format!(
                    "    Test::Entry.plain({}, {method_file}, {line}, ->(c: Test::Case) {{ c.as({name}).{test}; nil }}),",
                    literal(test)
                )),
                [p] if matches!(p.kind, ParamKind::Positional) => {
                    let data = format!("data_{}", &test["test_".len()..]);
                    let has_data = below_case.iter().any(|a| {
                        world.class(*a).methods.get(&data).is_some_and(|ids| {
                            ids.iter().any(|d| world.method(*d).params.is_empty())
                        })
                    });
                    if !has_data {
                        error(format!("{name}#{test} takes a parameter but `{data}` is not defined"));
                        continue;
                    }
                    entries.push(format!(
                        "    Test::Entry.each({}, {method_file}, {line}, ->(c: Test::Case) {{ c.as({name}).{data}.keys }},\n      \
                         ->(c: Test::Case, row: String) {{ t = c.as({name}); t.{test}(t.{data}[row]); nil }}),",
                        literal(test)
                    ));
                }
                _ => error(format!(
                    "{name}#{test}: a test method takes no parameters, or one with a `data_` method"
                )),
            }
        }
        suites.push(format!(
            "  Test::Suite.new({}, {}, -> {{ {name}.new }}, [\n{}\n  ], -> {{ {name}.startup }}, -> {{ {name}.shutdown }}, {name}.timeout, {name}.serial?),",
            literal(name),
            literal(&file),
            entries.join("\n")
        ));
    }
    if !errors.is_empty() {
        return Err(errors);
    }
    Ok(format!(
        "suites: Array[Test::Suite] = [\n{}\n]\nexit Test.run(ARGV, suites)\n",
        suites.join("\n")
    ))
}
