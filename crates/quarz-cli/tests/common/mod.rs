//! Helpers shared by the interpreter tests.

use quarz_syntax::{parse, parse_with_bases, SourceFile};
use quarz_types::load::unit_base;
use quarz_types::PRELUDE_SOURCE;

/// Type-check and run a program, returning the exit code and its standard
/// output. Panics on compile errors.
pub fn run(src: &str, argv: &[&str]) -> (i32, String) {
    let (checked, files) = check(src);
    let argv = argv.iter().map(|s| s.to_string()).collect();
    quarz_cli::run_capturing(checked, &files, argv)
}

/// Type-check and lower a program. Panics on compile errors.
#[allow(dead_code)]
pub fn lower(src: &str) -> quarz_ir::Module {
    let (checked, files) = check(src);
    quarz_cli::lower(&checked, &files)
}

/// `lower`, then class `class`'s rows for module method `module#name`
/// pointed at that method itself, as though nothing implemented it: the
/// run time reaches the abstract method (#630's arm). No program the
/// checker accepts reaches it since the safety net's error stage and R0's
/// recorded witnesses (#632, #557), so its tests make the rows so.
#[allow(dead_code)]
pub fn lower_with_no_witness(src: &str, class: &str, module: &str, name: &str) -> quarz_ir::Module {
    let mut m = lower(src);
    let w = &mut m.world;
    let cid = w
        .classes
        .iter()
        .position(|c| c.name == class)
        .expect("the class") as quarz_ir::ClassId;
    let mid = w
        .methods
        .iter()
        .position(|x| x.name == name && w.classes[x.owner as usize].name == module)
        .expect("the method") as quarz_ir::MethodId;
    for row in w.override_rows.iter_mut() {
        if row.0 == cid && row.1 == mid {
            row.2 = mid;
        }
    }
    for row in w.witness_rows.iter_mut() {
        if row.0 == cid && row.1 == mid {
            row.2 = None;
        }
    }
    w.ext_impls.retain(|e| !(e.0 == cid && e.1 == mid));
    // (The rows read the witness record, and shake makes them again from
    // it, #536 step 3's S2: the record's entry goes too.)
    for row in w.witness_record.iter_mut() {
        if row.0 == cid && row.1 == mid {
            row.2 = None;
        }
    }
    m
}

/// Type-check a program, with the sources to lower it from. Panics on
/// compile errors.
fn check(src: &str) -> (quarz_types::Checked, Vec<SourceFile>) {
    let prelude = parse(PRELUDE_SOURCE);
    // The program's spans and node ids must not collide with the prelude's.
    let base = unit_base(0);
    let parsed = parse_with_bases(src, base, base);
    let file = SourceFile::with_base("test", src, base);
    let errors: Vec<String> = parsed
        .diagnostics
        .iter()
        .filter(|d| d.is_error())
        .map(|d| d.render(&file))
        .collect();
    assert!(errors.is_empty(), "parse errors:\n{}", errors.join("\n"));
    let (checked, diags) = quarz_types::check(&prelude.program, &parsed.program);
    let errors: Vec<String> = diags
        .iter()
        .filter(|(_, d)| d.is_error())
        .map(|(_, d)| d.render(&file))
        .collect();
    assert!(errors.is_empty(), "check errors:\n{}", errors.join("\n"));
    let prelude_file = SourceFile::new("<prelude>", PRELUDE_SOURCE);
    (checked.unwrap(), vec![prelude_file, file])
}

/// Load a file (and what it requires), check and run it.
#[allow(dead_code)]
pub fn run_path(path: &std::path::Path, argv: &[&str]) -> (i32, String) {
    let prelude = parse(PRELUDE_SOURCE);
    let (units, diags) = quarz_types::load(path);
    let errors: Vec<String> = diags
        .iter()
        .filter(|(_, d)| d.is_error())
        .map(|(f, d)| d.render(f))
        .collect();
    assert!(errors.is_empty(), "load errors:\n{}", errors.join("\n"));
    let sources: Vec<SourceFile> = units.iter().map(|u| u.source.clone()).collect();
    let to_check: Vec<quarz_types::Unit> = units.into_iter().map(quarz_types::Unit::from).collect();
    let (checked, diags) = quarz_types::check_units(&prelude.program, &to_check);
    let errors: Vec<String> = diags
        .iter()
        .filter(|(_, d)| d.is_error())
        .map(|(f, d)| d.render(&sources[(*f as usize).saturating_sub(1)]))
        .collect();
    assert!(errors.is_empty(), "check errors:\n{}", errors.join("\n"));
    let argv = argv.iter().map(|s| s.to_string()).collect();
    let mut files = vec![SourceFile::new("<prelude>", PRELUDE_SOURCE)];
    files.extend(sources);
    quarz_cli::run_capturing(checked.unwrap(), &files, argv)
}

/// Run and assert the output.
#[allow(dead_code)]
pub fn expect(src: &str, expected: &str) {
    let (code, out) = run(src, &[]);
    assert_eq!(code, 0, "exit code for {src:?}, output: {out:?}");
    assert_eq!(out, expected, "output for {src:?}");
}

/// Type-check a program and return its diagnostics (errors and
/// warnings), rendered.
#[allow(dead_code)]
pub fn diagnostics(src: &str) -> Vec<String> {
    let prelude = parse(PRELUDE_SOURCE);
    let base = unit_base(0);
    let parsed = parse_with_bases(src, base, base);
    let file = SourceFile::with_base("test", src, base);
    let mut out: Vec<String> = parsed.diagnostics.iter().map(|d| d.render(&file)).collect();
    let (_, diags) = quarz_types::check(&prelude.program, &parsed.program);
    out.extend(diags.iter().map(|(_, d)| d.render(&file)));
    out
}
