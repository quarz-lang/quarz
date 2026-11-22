//! `quarz build`: every example compiles to a native executable whose
//! output and exit code match the VM's.

mod common;

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Mutex;

use quarz_syntax::{parse, SourceFile};
use quarz_types::PRELUDE_SOURCE;

/// Type-check a file (and what it requires) and compile it to `output`.
fn build(path: &Path, output: &Path) {
    let prelude = parse(PRELUDE_SOURCE);
    let (units, diags) = quarz_types::load(path);
    assert!(
        diags.iter().all(|(_, d)| !d.is_error()),
        "load errors in {}",
        path.display()
    );
    let sources: Vec<SourceFile> = units.iter().map(|u| u.source.clone()).collect();
    let to_check: Vec<quarz_types::Unit> = units.into_iter().map(quarz_types::Unit::from).collect();
    let (checked, diags) = quarz_types::check_units(&prelude.program, &to_check);
    let errors: Vec<String> = diags
        .iter()
        .filter(|(_, d)| d.is_error())
        .map(|(f, d)| d.render(&sources[(*f as usize).saturating_sub(1)]))
        .collect();
    assert!(errors.is_empty(), "check errors:\n{}", errors.join("\n"));
    let mut files = vec![SourceFile::new("<prelude>", PRELUDE_SOURCE)];
    files.extend(sources);
    quarz_cli::build(checked.unwrap(), &files, output).expect("build");
}

/// Compile and run `path` natively, returning the exit code and output.
fn run_native(path: &Path, argv: &[&str]) -> (i32, String) {
    // A directory per build: builds run at once, and each leaves its
    // intermediate files next to its executable.
    static N: AtomicUsize = AtomicUsize::new(0);
    let dir = std::env::temp_dir().join(format!(
        "quarz-build-test-{}-{}",
        std::process::id(),
        N.fetch_add(1, Ordering::SeqCst)
    ));
    fs::create_dir_all(&dir).unwrap();
    let name = path.file_stem().unwrap().to_string_lossy().into_owned();
    let exe: PathBuf = dir.join(name);
    build(path, &exe);
    let output = Command::new(&exe)
        .args(argv)
        .output()
        .expect("run the executable");
    let _ = fs::remove_dir_all(&dir);
    (
        output.status.code().unwrap_or(-1),
        String::from_utf8_lossy(&output.stdout).into_owned(),
    )
}

fn same_as_vm(path: &Path, argv: &[&str]) {
    let (vm_code, vm_out) = common::run_path(path, argv);
    let (native_code, native_out) = run_native(path, argv);
    assert_eq!(native_out, vm_out, "output of {}", path.display());
    assert_eq!(native_code, vm_code, "exit code of {}", path.display());
}

/// The shard `k` of `n` (1-based) of the fixture lists this run takes,
/// from `QUARZ_TEST_SHARD=k/n`: CI splits `tests/build.rs` over two jobs
/// (#1048), each compiling the cases whose index in each sorted list is
/// `k - 1` modulo `n`, so every case is compiled by exactly one of them.
/// Unset, every case.
fn shard() -> Option<(usize, usize)> {
    let v = std::env::var("QUARZ_TEST_SHARD").ok()?;
    let (k, n) = v.split_once('/')?;
    let (k, n): (usize, usize) = (k.parse().ok()?, n.parse().ok()?);
    assert!(n >= 1 && (1..=n).contains(&k), "QUARZ_TEST_SHARD={v}");
    Some((k, n))
}

/// `same_as_vm` for each of `cases`, several at once: compiling with
/// clang is most of the time, and the programs are independent. The
/// failures are reported together. A worker stops at its first failure:
/// a panic in the VM may leave its thread's scheduler state behind, which
/// would fail the next programs there too; the others go on, and the
/// cases no worker got to are listed.
fn all_same_as_vm(cases: &[(PathBuf, Vec<String>)]) {
    let cases: Vec<(PathBuf, Vec<String>)> = match shard() {
        Some((k, n)) => {
            let mine: Vec<_> = cases
                .iter()
                .enumerate()
                .filter(|(i, _)| i % n == k - 1)
                .map(|(_, c)| c.clone())
                .collect();
            // (The list, for counting that the shards cover each case
            // once: shown with `--nocapture`.)
            for (path, _) in &mine {
                eprintln!("shard {k}/{n} case {}", path.display());
            }
            mine
        }
        None => cases.to_vec(),
    };
    let cases = &cases[..];
    let workers = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(1)
        .clamp(1, 4);
    let next = AtomicUsize::new(0);
    let failures = Mutex::new(Vec::new());
    std::thread::scope(|s| {
        for _ in 0..workers {
            s.spawn(|| loop {
                let i = next.fetch_add(1, Ordering::SeqCst);
                let Some((path, argv)) = cases.get(i) else {
                    break;
                };
                let argv: Vec<&str> = argv.iter().map(String::as_str).collect();
                let result = std::panic::catch_unwind(|| same_as_vm(path, &argv));
                if let Err(e) = result {
                    let message = e
                        .downcast_ref::<String>()
                        .cloned()
                        .or_else(|| e.downcast_ref::<&str>().map(|s| s.to_string()))
                        .unwrap_or_default();
                    failures
                        .lock()
                        .unwrap()
                        .push(format!("{}: {message}", path.display()));
                    break;
                }
            });
        }
    });
    let mut failures = failures.into_inner().unwrap();
    let started = next.into_inner().min(cases.len());
    for (path, _) in &cases[started..] {
        failures.push(format!(
            "{}: not run (every worker stopped)",
            path.display()
        ));
    }
    assert!(failures.is_empty(), "{}", failures.join("\n\n"));
}

fn example(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join(format!("../../examples/{name}.qz"))
}

fn fixture(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join(format!("tests/fixtures/{name}"))
}

#[test]
fn examples_compile_and_match_the_vm() {
    let mut cases = Vec::new();
    for name in [
        "shapes",
        "pipeline",
        "bank_actor",
        "extension",
        "builder",
        "geometry",
        "multi_file",
        "json_report",
        "markdown",
        "sales_report",
        "workers",
    ] {
        cases.push((example(name), Vec::new()));
    }
    cases.push((example("hello"), vec!["Quarz".to_string()]));
    let files = [fixture("a.txt"), fixture("b.txt")];
    cases.push((
        example("wordcount"),
        files.iter().map(|f| f.display().to_string()).collect(),
    ));
    all_same_as_vm(&cases);
}

#[test]
fn builtins_match_the_vm() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/builtins");
    let mut paths: Vec<PathBuf> = fs::read_dir(&dir)
        .expect("fixtures directory")
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().is_some_and(|e| e == "qz"))
        .collect();
    paths.sort();
    let cases: Vec<(PathBuf, Vec<String>)> = paths.into_iter().map(|p| (p, Vec::new())).collect();
    all_same_as_vm(&cases);
}

/// Every `.qz` directly under `tests/fixtures`: its output and exit code
/// (control_flow.qz exits with 3).
#[test]
fn top_level_fixtures_match_the_vm() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures");
    let mut paths: Vec<PathBuf> = fs::read_dir(&dir)
        .expect("fixtures directory")
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().is_some_and(|e| e == "qz"))
        .collect();
    paths.sort();
    assert!(paths.contains(&fixture("control_flow.qz")), "{paths:?}");
    let cases: Vec<(PathBuf, Vec<String>)> = paths.into_iter().map(|p| (p, Vec::new())).collect();
    all_same_as_vm(&cases);
}

/// A compiled function that reads its activation's frame word (the
/// fourth of the 32-byte `[args, self, nargs, frame]` slot) stores it
/// first: a block whose only use of its activation is an in-place update
/// of a captured variable read it uninitialized (#474).
#[test]
fn frame_word_is_set_before_it_is_read() {
    let path = fixture("owned_call_frame.qz");
    let dir = std::env::temp_dir().join(format!("quarz-frame-word-test-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let exe = dir.join("owned_call_frame");
    let built = Command::new(env!("CARGO_BIN_EXE_quarz"))
        .arg("build")
        .arg(&path)
        .arg("-o")
        .arg(&exe)
        .env("QUARZ_KEEP_IR", "1")
        .output()
        .expect("run quarz build");
    assert!(
        built.status.success(),
        "{}",
        String::from_utf8_lossy(&built.stderr)
    );
    // (The kept IR: each partition's, in `<exe>.quarz-build/`.)
    let mut build_dir = exe.as_os_str().to_owned();
    build_dir.push(".quarz-build");
    let mut lls: Vec<_> = fs::read_dir(&build_dir)
        .unwrap()
        .flatten()
        .map(|e| e.path())
        .filter(|p| p.extension().is_some_and(|e| e == "ll"))
        .collect();
    lls.sort();
    let ir: String = lls.iter().map(|p| fs::read_to_string(p).unwrap()).collect();
    let _ = fs::remove_dir_all(&dir);
    // `ptrs` is a compiled function's sixth stack slot (after the
    // registers, the scratch list, the activation buffer, the result
    // slot and the body pointer: gen.rs); its frame word is at 24.
    if ir.contains("i8*") {
        eprintln!("skipped: clang 14's typed-pointer IR");
        return;
    }
    let mut reads = 0;
    let mut unset = Vec::new();
    for func in ir.split("\ndefine ").skip(1) {
        let body = func.split("\n}").next().unwrap();
        if !body.contains("%slot5 = alloca [32 x i8], align 8") {
            continue;
        }
        let words: Vec<&str> = body
            .lines()
            .filter_map(|l| {
                l.trim()
                    .strip_suffix("= getelementptr i8, ptr %slot5, i64 24")
            })
            .map(str::trim)
            .collect();
        let read = words
            .iter()
            .any(|w| body.contains(&format!("load ptr, ptr {w},")));
        let written = words.iter().any(|w| {
            body.lines()
                .any(|l| l.trim().starts_with("store ptr ") && l.contains(&format!(", ptr {w},")))
        });
        if read {
            reads += 1;
            if !written {
                unset.push(func.split('(').next().unwrap().to_string());
            }
        }
    }
    assert!(reads > 0, "no function of the fixture reads its frame word");
    assert!(unset.is_empty(), "frame word read unset in {unset:?}");
}

/// #786: `quarz build` of `path` to `exe` with `envs`, its output.
fn quarz_build(
    path: &Path,
    exe: &Path,
    args: &[&str],
    envs: &[(&str, &str)],
) -> std::process::Output {
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_quarz"));
    cmd.arg("build").arg(path).arg("-o").arg(exe).args(args);
    // (Split only where a test asks, whatever the run's environment.)
    cmd.env_remove("QUARZ_BUILD_PARTITION_BYTES");
    for (k, v) in envs {
        cmd.env(k, v);
    }
    cmd.output().expect("run quarz build")
}

/// #786: programs split into partitions (`QUARZ_BUILD_PARTITION_BYTES=1`
/// cuts at every method, so direct calls, typed and early entries, blocks
/// and the tables cross partitions) run as on the VM, leave no build
/// directory, and build the same executable for every number of jobs. The
/// fixtures: blocks (`block_destructure_padding`, `keyword_procs`), typed
/// entries and backtraces (`builtins/typed_backtrace`), generics and
/// witnesses (`extension_generic_module_witness`), exceptions and
/// deinitializers (`rescue_flows`, `deinitialize_once`), tasks
/// (`blocking_captures`, `task_block_self_release`), and all of these
/// (`deep_values`).
#[test]
fn partitioned_builds_run_as_on_the_vm() {
    let dir = std::env::temp_dir().join(format!("quarz-partitions-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let split = [
        ("QUARZ_BUILD_PARTITION_BYTES", "1"),
        ("QUARZ_BUILD_TIMINGS", "1"),
    ];
    for name in [
        "block_destructure_padding.qz",
        "keyword_procs.qz",
        "builtins/typed_backtrace.qz",
        "extension_generic_module_witness.qz",
        "rescue_flows.qz",
        "deinitialize_once.qz",
        "blocking_captures.qz",
        "task_block_self_release.qz",
        "deep_values.qz",
    ] {
        let path = fixture(name);
        let (vm_code, vm_out) = common::run_path(&path, &[]);
        let mut exes = Vec::new();
        for jobs in ["1", "4"] {
            let exe = dir.join(format!("split_{jobs}"));
            let built = quarz_build(&path, &exe, &["-j", jobs], &split);
            let err = String::from_utf8_lossy(&built.stderr);
            assert!(built.status.success(), "{name} -j {jobs}: {err}");
            let clang = err
                .lines()
                .find(|l| l.contains("stage=clang "))
                .unwrap_or("");
            assert!(
                !clang.contains(" partitions=1 "),
                "{name}: not split: {clang}"
            );
            if jobs == "1" {
                assert!(clang.contains(" jobs=1 "), "{clang}");
            }
            let mut build_dir = exe.as_os_str().to_owned();
            build_dir.push(".quarz-build");
            assert!(
                !Path::new(&build_dir).exists(),
                "{name}: the build directory is left"
            );
            let out = Command::new(&exe).output().expect("run the executable");
            assert_eq!(
                String::from_utf8_lossy(&out.stdout),
                vm_out,
                "output of {name} -j {jobs}"
            );
            assert_eq!(
                out.status.code().unwrap_or(-1),
                vm_code,
                "exit code of {name} -j {jobs}"
            );
            exes.push(fs::read(&exe).unwrap());
        }
        assert!(
            exes[0] == exes[1],
            "{name}: -j 1 and -j 4 built different executables"
        );
    }
    // Unsplit, a small program is one partition, the tables with it.
    let whole = quarz_build(
        &fixture("control_flow.qz"),
        &dir.join("whole"),
        &[],
        &[("QUARZ_BUILD_TIMINGS", "1")],
    );
    let _ = fs::remove_dir_all(&dir);
    let err = String::from_utf8_lossy(&whole.stderr);
    assert!(
        err.lines()
            .any(|l| l.contains("stage=clang ") && l.contains(" partitions=1 ")),
        "{err}"
    );
}

/// #786: `-j 0` and a `-j` that is not a number are errors, as is such a
/// `QUARZ_BUILD_JOBS`.
#[test]
fn build_jobs_must_be_a_positive_number() {
    let path = fixture("control_flow.qz");
    let dir = std::env::temp_dir().join(format!("quarz-jobs-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    for (args, envs, what) in [
        (
            &["-j", "0"][..],
            &[][..],
            "-j must be a number of jobs, 1 or more, not \"0\"",
        ),
        (
            &["-jx"][..],
            &[][..],
            "-j must be a number of jobs, 1 or more, not \"x\"",
        ),
        (
            &[][..],
            &[("QUARZ_BUILD_JOBS", "many")][..],
            "QUARZ_BUILD_JOBS must be a number of jobs, 1 or more, not \"many\"",
        ),
    ] {
        let built = quarz_build(&path, &dir.join("out"), args, envs);
        let err = String::from_utf8_lossy(&built.stderr);
        assert!(!built.status.success(), "{args:?} {envs:?} built");
        assert!(err.contains(what), "{args:?} {envs:?}: {err}");
    }
    let _ = fs::remove_dir_all(&dir);
}

/// #786: a clang that fails, or is killed, on one partition fails the
/// build with that partition named and leaves no build directory or
/// executable; `QUARZ_KEEP_IR` keeps the directory with each partition's
/// IR, and says where.
#[test]
fn a_failing_partition_fails_the_build_and_leaves_nothing() {
    let path = fixture("control_flow.qz");
    let dir = std::env::temp_dir().join(format!("quarz-partition-fail-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let clang = Command::new("sh")
        .args([
            "-c",
            "if [ -n \"$QUARZ_CLANG\" ]; then command -v \"$QUARZ_CLANG\"; else command -v clang; fi",
        ])
        .output()
        .unwrap();
    let real = String::from_utf8_lossy(&clang.stdout).trim().to_string();
    if real.is_empty() {
        eprintln!("skipped: no clang on PATH to wrap");
        let _ = fs::remove_dir_all(&dir);
        return;
    }
    for (name, act) in [
        ("fails", "echo broken partition >&2; exit 1"),
        ("killed", "kill -9 $$"),
    ] {
        // A clang that does `act` on the second partition and compiles the others.
        let fake = dir.join(format!("clang-{name}"));
        fs::write(
            &fake,
            format!("#!/bin/sh\ncase \"$*\" in *p001.ll*) {act};; esac\nexec {real} \"$@\"\n"),
        )
        .unwrap();
        Command::new("chmod").arg("+x").arg(&fake).status().unwrap();
        let exe = dir.join(format!("out-{name}"));
        let built = quarz_build(
            &path,
            &exe,
            &["-j", "2"],
            &[
                ("QUARZ_BUILD_PARTITION_BYTES", "1"),
                ("QUARZ_CLANG", fake.to_str().unwrap()),
            ],
        );
        let err = String::from_utf8_lossy(&built.stderr);
        assert!(!built.status.success(), "{name}: built");
        assert!(err.contains("failed on partition 1"), "{name}: {err}");
        let mut build_dir = exe.as_os_str().to_owned();
        build_dir.push(".quarz-build");
        assert!(
            !Path::new(&build_dir).exists(),
            "{name}: the build directory is left"
        );
        assert!(!exe.exists(), "{name}: an executable is left");
    }
    let exe = dir.join("kept");
    let built = quarz_build(
        &path,
        &exe,
        &[],
        &[("QUARZ_BUILD_PARTITION_BYTES", "1"), ("QUARZ_KEEP_IR", "1")],
    );
    let err = String::from_utf8_lossy(&built.stderr);
    let mut build_dir = exe.as_os_str().to_owned();
    build_dir.push(".quarz-build");
    let kept: Vec<String> = fs::read_dir(&build_dir)
        .map(|d| {
            d.flatten()
                .map(|e| e.file_name().to_string_lossy().into_owned())
                .collect()
        })
        .unwrap_or_default();
    let _ = fs::remove_dir_all(&dir);
    assert!(built.status.success(), "{err}");
    assert!(
        err.contains("the IR is kept in") && err.contains(".quarz-build"),
        "{err}"
    );
    assert!(
        kept.iter().any(|f| f == "p000.ll") && kept.iter().any(|f| f == "p001.ll"),
        "{kept:?}"
    );
    assert!(!kept.iter().any(|f| f.ends_with(".o")), "{kept:?}");
}

/// `QUARZ_AOT_OPT` picks clang's level (0 and 2 both build a program
/// that runs as the VM does); anything but 0 to 3 is an error naming it.
#[test]
fn aot_opt_levels() {
    let path = fixture("control_flow.qz");
    let want = fs::read_to_string(path.with_extension("out")).unwrap();
    let dir = std::env::temp_dir().join(format!("quarz-aot-opt-test-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let build = |level: &str, exe: &Path| {
        Command::new(env!("CARGO_BIN_EXE_quarz"))
            .arg("build")
            .arg(&path)
            .arg("-o")
            .arg(exe)
            .env("QUARZ_AOT_OPT", level)
            .output()
            .expect("run quarz build")
    };
    for level in ["0", "2"] {
        let exe = dir.join(format!("control_flow_{level}"));
        let built = build(level, &exe);
        assert!(
            built.status.success(),
            "QUARZ_AOT_OPT={level}: {}",
            String::from_utf8_lossy(&built.stderr)
        );
        let out = Command::new(&exe).output().expect("run the executable");
        assert_eq!(
            String::from_utf8_lossy(&out.stdout),
            want,
            "QUARZ_AOT_OPT={level}"
        );
    }
    let built = build("x", &dir.join("control_flow_x"));
    let _ = fs::remove_dir_all(&dir);
    let err = String::from_utf8_lossy(&built.stderr);
    assert!(!built.status.success(), "QUARZ_AOT_OPT=x built");
    assert!(
        err.contains("QUARZ_AOT_OPT") && err.contains("\"x\""),
        "{err}"
    );
}

/// #785: `QUARZ_BUILD_TIMINGS=1` makes `quarz build` print one line per
/// stage on standard error, `total` last (no values asserted: they are
/// times), and changes nothing it builds; without it, nothing is printed.
#[test]
fn build_timings_print_every_stage_and_change_nothing() {
    let path = fixture("control_flow.qz");
    let dir = std::env::temp_dir().join(format!("quarz-build-timings-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let build = |exe: &Path, timed: bool| {
        let mut cmd = Command::new(env!("CARGO_BIN_EXE_quarz"));
        // (Every stage runs: `strip` is skipped under `QUARZ_NO_STRIP`.)
        cmd.arg("build")
            .arg(&path)
            .arg("-o")
            .arg(exe)
            .env_remove("QUARZ_NO_STRIP");
        if timed {
            cmd.env("QUARZ_BUILD_TIMINGS", "1");
        } else {
            cmd.env_remove("QUARZ_BUILD_TIMINGS");
        }
        cmd.output().expect("run quarz build")
    };
    let (plain_exe, timed_exe) = (dir.join("plain"), dir.join("timed"));
    let plain = build(&plain_exe, false);
    let timed = build(&timed_exe, true);
    let same = fs::read(&plain_exe).ok() == fs::read(&timed_exe).ok();
    let _ = fs::remove_dir_all(&dir);
    assert!(plain.status.success() && timed.status.success());
    assert!(
        plain.stderr.is_empty(),
        "{}",
        String::from_utf8_lossy(&plain.stderr)
    );
    assert!(same, "the executables differ");
    let err = String::from_utf8_lossy(&timed.stderr);
    let lines: Vec<&str> = err.lines().collect();
    let stages = [
        "parse",
        "check",
        "declare",
        "lower",
        "shake",
        "clang_version",
        "emit",
        "clang",
        "link",
        "strip",
        "total",
    ];
    for (line, stage) in lines.iter().zip(stages) {
        assert!(
            line.starts_with(&format!("quarz-build-timing stage={stage} ms=")),
            "{err}"
        );
    }
    assert_eq!(lines.len(), stages.len(), "{err}");
    assert!(
        lines[1].contains(" cache_hits=") && lines[1].contains(" cache_misses="),
        "{err}"
    );
    assert!(
        lines[6].contains(" bytes=") && lines[6].contains(" functions="),
        "{err}"
    );
    assert!(lines[7].contains(" level="), "{err}");
}

/// #972: `b[i]` with an Int on a `Bytes` is `BytesIndex` (the byte read
/// in place), and `each_byte` with a literal block a loop of them, with
/// no block function and no call per byte; a block value stays a call.
#[test]
fn a_bytes_index_and_each_byte_read_in_place() {
    let module = common::lower(
        "def at(b: Bytes, i: Int) -> Int = b[i]\n\
         def sum(b: Bytes) -> Int\n  s = 0\n  b.each_byte { |c| s += c }\n  s\nend\n\
         def each_of(b: Bytes, &blk: (Int) -> Void) -> Void = b.each_byte(&blk)\n\
         p at(b\"ab\", 1), sum(b\"ab\")\n\
         each_of(b\"a\") { |c| p c }\n",
    );
    let insts = |name: &str| -> Vec<quarz_ir::Inst> {
        let f = module
            .functions
            .iter()
            .find(|f| f.name == format!("main#{name}"))
            .unwrap_or_else(|| panic!("no function {name}"));
        f.blocks
            .iter()
            .flat_map(|b| b.insts.iter().cloned())
            .collect()
    };
    let index_reads = |name: &str| {
        insts(name)
            .iter()
            .filter(|i| matches!(i, quarz_ir::Inst::BytesIndex { .. }))
            .count()
    };
    let calls = |name: &str| {
        insts(name)
            .iter()
            .filter(|i| {
                matches!(
                    i,
                    quarz_ir::Inst::Call { .. } | quarz_ir::Inst::MakeBlock { .. }
                )
            })
            .count()
    };
    assert_eq!((index_reads("at"), calls("at")), (1, 0));
    // (The loop's one call: `Bytes#size`, before it.)
    assert_eq!((index_reads("sum"), calls("sum")), (1, 1));
    assert_eq!(index_reads("each_of"), 0);
}

/// #921: a `data` construction leaving fields to literal defaults is
/// lowered with every field, as one written in full (so the AOT's
/// `alloc_data` and `sroa` make it inline), by keywords too, in the
/// constructor's order (#971); a non-literal default left out or a
/// type's own `initialize` leave the call as it was.
#[test]
fn a_data_construction_with_literal_defaults_has_every_field() {
    let module = common::lower(
        "LIMIT = 7\n\
         data Kind = (cls: Type[Object]?, item: Type[Object]? = nil, nils: Bool = false)\n\
         data Mixed = (a: Int, k: Int = LIMIT)\n\
         data Pt(x: Int, y: Int = 0)\n  def initialize(s: String)\n    @x = s.size\n    @y = 1\n  end\nend\n\
         enum Shape\n  variant Circle(r: Float = 1.0, filled: Bool = false)\nend\n\
         def literal -> Kind = Kind.new(Int)\n\
         def keyword -> Kind = Kind.new(Int, nils: true)\n\
         def reordered -> Kind = Kind.new(nils: true, cls: Int)\n\
         data Inner2 = (x: Int, y: Int = 1)\n\
         data Outer2 = (i: Inner2, n: Int = 2)\n\
         def nested -> Outer2 = Outer2.new(n: 3, i: Inner2.new(4))\n\
         def nested_pos -> Outer2 = Outer2.new(Inner2.new(4), 3)\n\
         def keyword_constant -> Mixed = Mixed.new(a: 1)\n\
         def constant -> Mixed = Mixed.new(1)\n\
         def own -> Pt = Pt.new(\"s\")\n\
         def variant -> Shape = Shape::Circle.new\n\
         data Source = (table: String, keep: Array[Symbol] = [], tags: Hash[Symbol, Int] = {}, s: String = \"x\")\n\
         data Big = (a: Int, xs: Array[Int] = [1, 2, 3, 4, 5, 6, 7, 8, 9])\n\
         data Interp = (a: Int, s: String = \"n=#{1 + 1}\")\n\
         def collections -> Source = Source.new(\"t\")\n\
         def big -> Big = Big.new(1)\n\
         def interp -> Interp = Interp.new(1)\n\
         p nested, nested_pos\n\
         p literal, keyword, reordered, keyword_constant, constant, own, variant, collections, big, interp\n",
    );
    let construct_args = |name: &str| -> (usize, usize) {
        let f = module
            .functions
            .iter()
            .find(|f| f.name == format!("main#{name}"))
            .unwrap_or_else(|| panic!("no function {name}"));
        f.blocks
            .iter()
            .flat_map(|b| b.insts.iter())
            .find_map(|i| match i {
                quarz_ir::Inst::Call {
                    kind: quarz_ir::CallKind::Construct { .. },
                    args,
                    kw,
                    ..
                } => Some((args.len(), kw.len())),
                _ => None,
            })
            .unwrap_or_else(|| panic!("no construction in {name}"))
    };
    assert_eq!(construct_args("literal"), (3, 0));
    assert_eq!(construct_args("variant"), (2, 0));
    assert_eq!(construct_args("keyword"), (3, 0));
    assert_eq!(construct_args("reordered"), (3, 0));
    assert_eq!(construct_args("keyword_constant"), (0, 1));
    // A `data` value held in place, given by keyword: flattened after the
    // keywords are put in order, as the positional form is (the outer
    // construction is the function's last).
    let last_construct = |name: &str| -> (usize, usize) {
        let f = module
            .functions
            .iter()
            .find(|f| f.name == format!("main#{name}"))
            .unwrap_or_else(|| panic!("no function {name}"));
        f.blocks
            .iter()
            .flat_map(|b| b.insts.iter())
            .filter_map(|i| match i {
                quarz_ir::Inst::Call {
                    kind: quarz_ir::CallKind::Construct { .. },
                    args,
                    kw,
                    ..
                } => Some((args.len(), kw.len())),
                _ => None,
            })
            .next_back()
            .unwrap_or_else(|| panic!("no construction in {name}"))
    };
    assert_eq!(last_construct("nested"), last_construct("nested_pos"));
    assert_eq!(last_construct("nested").1, 0);
    assert_eq!(construct_args("constant"), (1, 0));
    assert_eq!(construct_args("own"), (1, 0));
    // #940: strings without interpolation and small array and hash
    // literals too; not nine elements, nor an interpolation.
    assert_eq!(construct_args("collections"), (4, 0));
    assert_eq!(construct_args("big"), (1, 0));
    assert_eq!(construct_args("interp"), (1, 0));
}

/// #921 across files: the default's node is the declaring file's, lowered
/// in the constructing file's function with the checker's tables for it.
/// Filled, and the same output, interpreted and compiled, with both files
/// checked afresh, both read back, and each read back while the other is
/// checked.
#[test]
fn a_data_construction_fills_defaults_declared_in_another_file() {
    let dir = std::env::temp_dir().join(format!("quarz-litdefaults-{}", std::process::id()));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    let cache = dir.join("cache");
    fs::write(
        dir.join("lib.qz"),
        "data D = (a: Int, b: Int = -3, c: Float = 1, e: Symbol = :s, k: Array[Symbol] = [], h: Hash[Symbol, Int] = {})\ndef note -> String = \"v1\"\n",
    )
    .unwrap();
    let app_src = "require_relative \"lib\"\nd = D.new(1)\np d, d.c + 0.5, d == D.new(1, -3, 1.0, :s, [], {})\nk = d.k.push(:x)\np k, d.h.put(:y, 2)\n";
    fs::write(dir.join("app.qz"), app_src).unwrap();
    let want = "D(a: 1, b: -3, c: 1.0, e: :s, k: [], h: {})\n1.5\ntrue\n[:x]\n{y: 2}\n";
    let quarz = |args: &[&str]| {
        let out = Command::new(env!("CARGO_BIN_EXE_quarz"))
            .args(args)
            .current_dir(&dir)
            .env("QUARZ_CACHE_DIR", &cache)
            .env("QUARZ_THREADS", "1")
            .output()
            .unwrap();
        assert!(
            out.status.success(),
            "quarz {args:?}: {}",
            String::from_utf8_lossy(&out.stderr)
        );
        String::from_utf8_lossy(&out.stdout).into_owned()
    };
    let check = |state: &str| {
        assert_eq!(quarz(&["run", "app.qz"]), want, "{state}: run");
        // `D.new(1)` has its six fields.
        let ir = quarz(&["ir", "app.qz"]);
        let filled = ir
            .lines()
            .filter(|l| l.contains("Construct { class") && l.contains("args: ["))
            .filter(|l| {
                let args = l
                    .split("args: [")
                    .nth(1)
                    .unwrap()
                    .split(']')
                    .next()
                    .unwrap();
                args.split(',').count() == 6
            })
            .count();
        assert_eq!(filled, 2, "{state}: {ir}");
        let exe = dir.join("app.bin");
        let _ = fs::remove_file(&exe);
        quarz(&["build", "app.qz", "-o", exe.to_str().unwrap()]);
        let out = Command::new(&exe).output().unwrap();
        assert_eq!(
            String::from_utf8_lossy(&out.stdout),
            want,
            "{state}: compiled"
        );
    };
    check("cold");
    check("warm");
    fs::write(dir.join("app.qz"), format!("{app_src}x = 1\n")).unwrap();
    check("lib read back, app checked");
    fs::write(
        dir.join("lib.qz"),
        "data D = (a: Int, b: Int = -3, c: Float = 1, e: Symbol = :s, k: Array[Symbol] = [], h: Hash[Symbol, Int] = {})\ndef note -> String = \"v2\"\n",
    )
    .unwrap();
    check("app read back, lib checked");
    let _ = fs::remove_dir_all(&dir);
}

/// #536 step 10b: a compiled `FieldGet`'s fast path reads a field where
/// its class lays it out, trusting the object to be of that class. A
/// program compiled with the checks (by a `quarz` that checks the facts
/// itself, as this debug test binary does: `quarz_vm::verify::enabled`)
/// checks it when it runs with them, as the interpreter does
/// (tests/verify.rs): reads of `A`'s field claiming it is `B`'s stop the
/// program; with `QUARZ_VERIFY=0` they are not checked.
#[test]
fn a_field_read_on_another_class_compiled() {
    if !quarz_vm::verify::enabled() {
        // (A release test binary with `QUARZ_VERIFY` unset compiles
        // without the checks: nothing to see.)
        return;
    }
    let dir = std::env::temp_dir().join(format!("quarz-fieldclass-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let mut module = common::lower(
        "class A\n  var @x: Int\n  def initialize(@x: Int) end\n  def x -> Int = @x\nend\n\
         class B\n  var @y: Int\n  def initialize(@y: Int) end\nend\n\
         p A.new(1).x\np B.new(2)\n",
    );
    let class = |name: &str| {
        module
            .world
            .classes
            .iter()
            .position(|c| c.name == name)
            .unwrap() as u32
    };
    let (a, b) = (class("A"), class("B"));
    let mut changed = false;
    for inst in module
        .functions
        .iter_mut()
        .flat_map(|f| f.blocks.iter_mut())
        .flat_map(|b| b.insts.iter_mut())
    {
        if let quarz_ir::Inst::FieldGet { class, .. } = inst {
            if *class == a {
                *class = b;
                changed = true;
            }
        }
    }
    assert!(changed, "no FieldGet of A");
    let exe = dir.join("main");
    quarz_aot::build(&module, &exe).expect("build");
    for (verify, code, want) in [
        (
            "moves",
            Some(101),
            "QIR fact violated: FieldGet of B on a A",
        ),
        ("0", Some(0), ""),
    ] {
        let out = Command::new(&exe)
            .env("QUARZ_VERIFY", verify)
            .output()
            .expect("run the executable");
        let err = String::from_utf8_lossy(&out.stderr);
        assert_eq!(out.status.code(), code, "{verify}: {err}");
        assert!(err.contains(want), "{verify}: {err}");
    }
    fs::remove_dir_all(&dir).ok();
}

/// #842: the same for a `FieldSet` fast path, whose `A` the rewrite makes
/// claim `B` (the field's word lands where `B`'s first `Int` field is, so
/// the program runs on without the check).
#[test]
fn a_field_write_on_another_class_compiled() {
    if !quarz_vm::verify::enabled() {
        return;
    }
    let dir = std::env::temp_dir().join(format!("quarz-fieldset-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let mut module = common::lower(
        "class A\n  var @x: Int\n  def initialize(@x: Int) end\n  def set(v: Int) -> Void\n    @x = v\n  end\n  def x -> Int = @x\nend\n\
         class B\n  var @y: Int\n  def initialize(@y: Int) end\nend\n\
         a = A.new(1)\na.set(5)\np a.x\np B.new(2)\n",
    );
    let class = |name: &str| {
        module
            .world
            .classes
            .iter()
            .position(|c| c.name == name)
            .unwrap() as u32
    };
    let (a, b) = (class("A"), class("B"));
    let mut changed = false;
    for inst in module
        .functions
        .iter_mut()
        .flat_map(|f| f.blocks.iter_mut())
        .flat_map(|b| b.insts.iter_mut())
    {
        if let quarz_ir::Inst::FieldSet { class, .. } = inst {
            if *class == a {
                *class = b;
                changed = true;
            }
        }
    }
    assert!(changed, "no FieldSet of A");
    let exe = dir.join("main");
    quarz_aot::build(&module, &exe).expect("build");
    for (verify, code, want) in [
        (
            "moves",
            Some(101),
            "QIR fact violated: FieldSet of B on a A",
        ),
        ("0", Some(0), ""),
    ] {
        let out = Command::new(&exe)
            .env("QUARZ_VERIFY", verify)
            .output()
            .expect("run the executable");
        let err = String::from_utf8_lossy(&out.stderr);
        assert_eq!(out.status.code(), code, "{verify}: {err}");
        assert!(err.contains(want), "{verify}: {err}");
    }
    fs::remove_dir_all(&dir).ok();
}

/// #630, compiled: an abstract method reached at run time is a violation
/// under `QUARZ_VERIFY` and a `TypeError` without it, as on the VM
/// (tests/verify.rs). No program the `quarz` command accepts reaches one,
/// so #557's program, now accepted, is lowered through the library API with
/// its row for `K` pointed at the requirement itself
/// (`common::lower_with_no_witness`) and compiled.
#[test]
fn an_abstract_method_reached_compiled() {
    let dir = std::env::temp_dir().join(format!("quarz-abstract-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let src = "module Named\n  abstract def label -> String\nend\nmodule Gives\n  def label -> String = \"Gives\"\nend\nclass K\n  def initialize; end\nend\nmodule S2\n  extension K\n    include Gives\n    include Named\n  end\n  def self.n(k: K) -> Named = k\nend\ndef via(n: Named) -> String = n.label\nputs via(S2.n(K.new))\n";
    let exe = dir.join("main");
    quarz_aot::build(
        &common::lower_with_no_witness(src, "K", "Named", "label"),
        &exe,
    )
    .expect("build");
    for (verify, code, want) in [
        ("moves", 101, "QIR fact violated: abstract method `label` called on K, which no check saw implemented"),
        ("0", 1, "TypeError: abstract method `label` called on K, which no check saw implemented"),
    ] {
        let out = Command::new(&exe)
            .env("QUARZ_VERIFY", verify)
            .output()
            .expect("run the executable");
        let err = String::from_utf8_lossy(&out.stderr);
        assert_eq!(out.status.code(), Some(code), "{verify}: {err}");
        assert!(err.contains(want), "{verify}: {err}");
    }
    fs::remove_dir_all(&dir).ok();
}
// CI probe for #1048: a mixed change. Not to be merged.
