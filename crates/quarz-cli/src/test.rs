//! `quarz test`: load the test files, list the `Test::Case` classes and
//! their `test_*` methods once they are checked, and add a runner calling
//! `Test.run` as one more unit (docs/12-testing.md).

use std::path::{Path, PathBuf};
use std::process::ExitCode;

use quarz_syntax::ast::{ParamKind, Visibility};
use quarz_syntax::{Diagnostic, SourceFile, Span};
use quarz_types::{ClassId, ClassKind, FileDiagnostic, Member, World};

/// The runner's file name, which `Test.location` leaves out of backtraces.
const RUNNER: &str = "<test-runner>";

/// Which tests run: the test files', the examples in documentation
/// comments (docs/13-doc-comments.md §4), or both.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Docs {
    Both,
    Only,
    None,
}

pub fn command(args: &[String]) -> ExitCode {
    let mut paths: Vec<PathBuf> = Vec::new();
    let mut argv: Vec<String> = Vec::new();
    let mut release = false;
    let mut docs = Docs::Both;
    let mut std_docs = false;
    let mut opts = quarz_cog::Options {
        verbose: true,
        ..Default::default()
    };
    let mut i = 0;
    while let Some(a) = args.get(i) {
        match a.as_str() {
            "--release" => release = true,
            "--doc" => docs = Docs::Only,
            "--no-doc" => docs = Docs::None,
            "--std" => {
                std_docs = true;
                docs = Docs::Only
            }
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
        !std_docs
            && paths
                .iter()
                .all(|p| std::fs::canonicalize(p).is_ok_and(|p| p.starts_with(&tests)))
    });
    if paths.is_empty() && !std_docs {
        match &cog {
            Some(root) if root.join("test").is_dir() || docs != Docs::Both => {
                if root.join("test").is_dir() {
                    paths.push(root.join("test"))
                }
            }
            Some(_) => {}
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
    if files.is_empty() && docs == Docs::None {
        eprintln!("quarz test: no test files (`*_test.qz`)");
        return ExitCode::FAILURE;
    }
    // `--doc`: a cog's or a script's examples, without its tests (the
    // given files still load, for their examples).
    let test_classes = docs != Docs::Only;
    if docs != Docs::None {
        quarz_types::want_docs();
    }
    let Some((checked, sources, lowerer)) =
        load_and_check(&files, cog.as_deref(), &opts, docs, std_docs, test_classes)
    else {
        return ExitCode::FAILURE;
    };
    if release {
        let dir = std::env::temp_dir().join(format!("quarz-test-{}", std::process::id()));
        if let Err(e) = std::fs::create_dir_all(&dir) {
            eprintln!("quarz test: {}: {e}", dir.display());
            return ExitCode::FAILURE;
        }
        let exe = dir.join("test");
        let built = quarz_cli::build_with(checked, &sources, lowerer, &exe);
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
    let code = quarz_cli::run_with(checked, &sources, lowerer, argv);
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
pub(crate) fn test_specs(
    root: &Path,
    opts: &quarz_cog::Options,
) -> Result<Vec<quarz_types::CogSpec>, String> {
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
    docs: Docs,
    std_docs: bool,
    test_classes: bool,
) -> Option<(quarz_types::Checked, Vec<SourceFile>, quarz_lower::Lowerer)> {
    let prelude_file = SourceFile::new("<prelude>", quarz_types::PRELUDE_SOURCE);
    let prelude = quarz_types::parse_prelude();
    let all_std: Vec<&str> = quarz_types::STD_MODULES.iter().map(|(n, _)| *n).collect();
    // The cog whose files' examples run: the application's (0) or the
    // library's (1, under the tests' own root).
    let own_cog = cog.map(|root| {
        if root.join("src").join("main.qz").is_file() {
            0
        } else {
            1
        }
    });
    let (units, decls, diagnostics) = match cog {
        Some(root) => match test_specs(root, opts) {
            Ok(specs) => quarz_types::load_movement_tests(&specs, files),
            Err(e) => {
                eprintln!("quarz: {e}");
                return None;
            }
        },
        None if std_docs => {
            let (units, diagnostics) = quarz_types::load::load_files(&[], &all_std);
            (units, Vec::new(), diagnostics)
        }
        None => {
            let (units, diagnostics) = quarz_types::load::load_files(files, &["test"]);
            (units, Vec::new(), diagnostics)
        }
    };
    // The files whose examples run.
    let mut own: Vec<u32> = Vec::new();
    if docs != Docs::None {
        for (i, u) in units.iter().enumerate() {
            let is_std = u.name.starts_with("<std:");
            let mine = match own_cog {
                Some(c) => u.cog == Some(c),
                None if std_docs => true,
                None => !is_std,
            };
            if mine {
                own.push(i as u32 + 1);
            }
        }
        if std_docs {
            own.push(0);
        }
    }
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
    let first_extra = to_check.len() as u32 + 1;
    // The extra units: the examples' (each with its line map), then the
    // runner.
    let mut extras: Vec<Extra> = Vec::new();
    // Checks in examples that apply to nothing.
    let mut example_errors: Vec<String> = Vec::new();
    let unit_cog = own_cog.map(|_| 0);
    // The class bodies' `static` statements run during the check (docs/14).
    let mut runner_files = vec![prelude_file.clone()];
    runner_files.extend(sources.iter().cloned());
    let mut runner = quarz_cli::static_run::Runner::new(runner_files.clone());
    let mut extra = |world: &World| {
        let mut all_files = vec![prelude_file.clone()];
        all_files.extend(sources.iter().cloned());
        let examples = crate::doc::examples::gather(world, &all_files, &own);
        let mut out = Vec::new();
        let mut suites = Vec::new();
        for (k, ex) in examples.iter().enumerate() {
            let unit = crate::doc::examples::unit(ex, k + 1);
            for (line, message) in &unit.errors {
                example_errors.push(format!(
                    "{}:{line}: error: {message} (in an example)",
                    ex.file
                ));
            }
            let base = quarz_types::load::unit_base(to_check.len() as u32 + k as u32);
            let name = format!("<doc:{}>", k + 1);
            let source = SourceFile::with_base(name, unit.text, base);
            extras.push(Extra {
                source: source.clone(),
                example: Some((unit.lines, ex.line)),
                file: ex.file.clone(),
            });
            out.push(quarz_types::ExtraSource {
                source,
                cog: unit_cog,
            });
            suites.push(ExampleSuite {
                class: unit.class,
                decl: ex.decl.clone(),
                index: ex.index,
                file: ex.file.clone(),
                line: ex.line,
            });
        }
        let base = quarz_types::load::unit_base(to_check.len() as u32 + examples.len() as u32);
        let text = runner_source(world, &sources, &suites, test_classes)?;
        let source = SourceFile::with_base(RUNNER, text, base);
        extras.push(Extra {
            source: source.clone(),
            example: None,
            file: String::new(),
        });
        out.push(quarz_types::ExtraSource { source, cog: None });
        Ok(out)
    };
    let (checked, mut diagnostics) = quarz_types::check_with_extra(
        &prelude.program,
        &to_check,
        &decls,
        Some(&mut extra),
        Some(&mut runner),
    );
    for e in &example_errors {
        eprintln!("{e}");
    }
    let checked = checked.filter(|_| example_errors.is_empty());
    let checked = checked.filter(|c| {
        let errors = quarz_cli::static_run::compile_time_only_calls(c, &runner_files, &mut runner);
        let ok = errors.is_empty();
        diagnostics.extend(errors);
        ok
    });
    for (file_index, diag) in &diagnostics {
        let extra = file_index
            .checked_sub(first_extra)
            .and_then(|k| extras.get(k as usize));
        match extra {
            // The runner's warnings (unreachable code after a test that
            // always raises) are not the user's, nor are its errors
            // anything but a test's shape.
            Some(Extra {
                source: src,
                example: None,
                ..
            }) => {
                if diag.is_error() {
                    eprint!("{}", diag.render(src));
                }
            }
            // An example's, at its line in the comment. A warning about
            // a line the unit adds (the `nil` after a statement that
            // always raises) is not the example's.
            Some(Extra {
                source: src,
                example: Some((lines, first)),
                file,
            }) => {
                let lc = src.line_col(diag.span.start);
                let line = lines.get(lc.line - 1).copied().unwrap_or(0);
                if line == 0 && !diag.is_error() {
                    continue;
                }
                let line = if line == 0 { *first } else { line };
                let kind = if diag.is_error() { "error" } else { "warning" };
                eprintln!("{file}:{line}: {kind}: {} (in an example)", diag.message);
            }
            None => {
                let f = if *file_index == 0 {
                    &prelude_file
                } else {
                    &sources[*file_index as usize - 1]
                };
                eprint!("{}", diag.render(f));
            }
        }
    }
    let mut files = vec![prelude_file];
    files.append(&mut sources);
    files.extend(extras.into_iter().map(|e| e.source));
    checked.map(|c| (c, files, runner.into_lowerer()))
}

/// A unit `quarz test` adds: an example's (with the comment's line of each
/// of its lines, and its first line) or the runner.
struct Extra {
    source: SourceFile,
    example: Option<(Vec<usize>, usize)>,
    /// The file the example's comment is in.
    file: String,
}

/// An example's test, for the runner.
struct ExampleSuite {
    class: String,
    decl: String,
    index: usize,
    file: String,
    line: usize,
}

/// A Quarz string literal for `s`.
pub(crate) fn literal(s: &str) -> String {
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
/// file order and then declaration order (none when `test_classes` is
/// false), then the examples' classes, which are in units declared with
/// the runner and so not in `world`. Errors name a test method the runner
/// cannot call.
fn runner_source(
    world: &World,
    sources: &[SourceFile],
    examples: &[ExampleSuite],
    test_classes: bool,
) -> Result<String, Vec<FileDiagnostic>> {
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
            test_classes
                && c.kind == ClassKind::Class
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
    for ex in examples {
        let class = &ex.class;
        suites.push(format!(
            "  Test::Suite.new({}, {}, -> {{ {class}.new }}, [\n    Test::Entry.plain({}, {}, {}, ->(c: Test::Case) {{ c.as({class}).test_example; nil }}),\n  ], -> {{ nil }}, -> {{ nil }}, nil, false),",
            literal(&ex.decl),
            literal(&ex.file),
            literal(&format!("example {}", ex.index)),
            literal(&ex.file),
            ex.line
        ));
    }
    Ok(format!(
        "suites: Array[Test::Suite] = [\n{}\n]\nexit Test.run(ARGV, suites)\n",
        suites.join("\n")
    ))
}
