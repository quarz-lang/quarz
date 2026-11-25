//! The tests of the language and its standard library written in Quarz
//! (`std/test/*_test.qz`, run by `quarz test`): interpreted, compiled,
//! and interpreted with the tests in parallel tasks on four workers; and
//! the examples in the standard library's documentation comments.
//!
//! The interpreted and compiled runs and the examples run one `quarz`
//! process per test file or module, on a pool of threads, as
//! tests/build.rs does (#455): one process over them all took most of the
//! suite's time.
//!
//! The interpreted `in_parallel` run still loads every test file together,
//! so clashes between files are caught at check time; a clash visible only
//! when everything is compiled as one program is not covered (decided on
//! #461).

use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Mutex;

fn root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

/// Run `job` on each of `items` on a pool of threads, and give what each
/// returned, in order; every failure is reported, together.
fn pool<T: Sync>(items: &[T], job: impl Fn(&T) -> Result<usize, String> + Sync) -> Vec<usize> {
    let workers = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(1)
        .clamp(1, 4);
    let next = AtomicUsize::new(0);
    let results = Mutex::new(vec![0; items.len()]);
    let failures = Mutex::new(Vec::new());
    std::thread::scope(|s| {
        for _ in 0..workers {
            s.spawn(|| loop {
                let i = next.fetch_add(1, Ordering::SeqCst);
                let Some(item) = items.get(i) else {
                    break;
                };
                match job(item) {
                    Ok(n) => results.lock().unwrap()[i] = n,
                    Err(e) => failures.lock().unwrap().push(e),
                }
            });
        }
    });
    let failures = failures.into_inner().unwrap();
    assert!(failures.is_empty(), "{}", failures.join("\n\n"));
    results.into_inner().unwrap()
}

/// Run `quarz test ARGS` in the repository's root and give the number of
/// tests its summary reports, when every one passed (none failed,
/// pending or omitted).
fn quarz_test(args: &[&str], threads: &str) -> Result<usize, String> {
    let out = Command::new(env!("CARGO_BIN_EXE_quarz"))
        .arg("test")
        .args(args)
        .current_dir(root())
        .env("QUARZ_THREADS", threads)
        .output()
        .expect("run quarz test");
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    let summary = stdout
        .lines()
        .find(|l| l.contains(" tests, "))
        .unwrap_or_default();
    let tests: usize = summary
        .split(' ')
        .next()
        .and_then(|n| n.parse().ok())
        .unwrap_or(0);
    if out.status.success() && summary.contains(" 0 failures, 0 errors, 0 pendings, 0 omissions") {
        Ok(tests)
    } else {
        Err(format!("quarz test {args:?}:\n{stdout}{stderr}"))
    }
}

/// `std/test/*_test.qz`, relative to the root.
fn test_files() -> Vec<String> {
    let mut files: Vec<String> = std::fs::read_dir(root().join("std/test"))
        .unwrap()
        .filter_map(|e| e.ok()?.file_name().into_string().ok())
        .filter(|n| n.ends_with("_test.qz"))
        .map(|n| format!("std/test/{n}"))
        .collect();
    files.sort();
    files
}

/// At least as many tests as std/test held when this was written: a file
/// whose tests are no longer found fails.
const STD_TESTS: usize = 461;

/// Each test file in a process of its own; every test found and passed,
/// each file running some.
fn each_test_file(release: bool) {
    let files = test_files();
    let tests: usize = pool(&files, |f| {
        let mut args = Vec::new();
        if release {
            args.push("--release");
        }
        args.push(f.as_str());
        match quarz_test(&args, "1")? {
            0 => Err(format!("quarz test {args:?}: no tests found")),
            n => Ok(n),
        }
    })
    .iter()
    .sum();
    assert!(tests >= STD_TESTS, "{tests} tests in std/test");
}

#[test]
fn on_the_vm() {
    each_test_file(false);
}

#[test]
fn compiled() {
    each_test_file(true);
}

/// One process, as it tests the parallel runner itself.
#[test]
fn in_parallel() {
    let tests = quarz_test(&["--parallel=8", "std/test"], "4").unwrap_or_else(|e| panic!("{e}"));
    assert!(tests >= STD_TESTS, "{tests} tests in std/test");
}

/// The examples in the standard library's documentation comments
/// (docs/13-doc-comments.md §4), interpreted and compiled, one module at
/// a time (`--std=NAME`); and its docs' links.
#[test]
fn the_standard_librarys_examples_and_links() {
    let mut runs: Vec<(String, bool)> = Vec::new();
    for e in std::fs::read_dir(root().join("std")).unwrap() {
        let name = e.unwrap().file_name().into_string().unwrap();
        if let Some(module) = name.strip_suffix(".qz") {
            for release in [false, true] {
                runs.push((module.to_string(), release));
            }
        }
    }
    // One pool for both kinds, the longest first: the prelude's,
    // compiled.
    runs.sort_by_key(|(m, r)| (m != "prelude", !*r, m.clone()));
    let counts = pool(&runs, |(module, release)| {
        let flag = format!("--std={module}");
        let mut args = vec![flag.as_str()];
        if *release {
            args.push("--release");
        }
        quarz_test(&args, "1")
    });
    for release in [false, true] {
        let examples: usize = runs
            .iter()
            .zip(&counts)
            .filter(|((_, r), _)| *r == release)
            .map(|(_, n)| n)
            .sum();
        assert!(examples > 0, "no examples (release: {release})");
    }
    let out = Command::new(env!("CARGO_BIN_EXE_quarz"))
        .args(["doc", "--std", "--check"])
        .current_dir(root())
        .output()
        .unwrap();
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
}

// ----- standard-library sets made at first use (#1097) ----------------------

/// A program requiring the set `test` (with `command_line`), made at first
/// use: its own test class, and one that uses `CommandLine` itself.
const SET_PROGRAM: &str = "require \"test\"\n\
class Opts < CommandLine\n  flag :verbose\n  option :name, String, default: \"x\"\nend\n\
class MinTest < Test::Case\n  def test_one\n    assert_equal(2, 1 + 1)\n  end\n\
  def test_options\n    o = Opts.parse([\"--verbose\", \"--name\", \"y\"], exit: false)\n    assert_true(o.verbose)\n    assert_equal(\"y\", o.name)\n  end\nend\n";

/// A directory of its own for `name`, empty.
fn set_dir(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("quarz-std-set-{name}-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

/// `quarz ARGS` on `prog` in `dir` with `env`: its standard output and
/// error, with the run times taken out.
fn quarz_in(dir: &Path, args: &[&str], env: &[(&str, &str)]) -> String {
    let out = Command::new(env!("CARGO_BIN_EXE_quarz"))
        .args(args)
        .current_dir(dir)
        .env("QUARZ_THREADS", "1")
        .env_remove("QUARZ_NO_STD_CACHE")
        .env_remove("QUARZ_NO_CACHE")
        .envs(env.iter().copied())
        .output()
        .expect("run quarz");
    let text = format!(
        "status {:?}\n{}{}",
        out.status.code(),
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    text.lines()
        .filter(|l| !l.starts_with("Finished in "))
        .map(|l| format!("{l}\n"))
        .collect()
}

/// Replace each number after one of `marks` in `line` by `name(number)`.
fn map_numbers(line: &str, marks: &[&str], name: &dyn Fn(u32) -> String) -> String {
    let mut out = String::new();
    let mut rest = line;
    loop {
        let next = marks
            .iter()
            .filter_map(|m| rest.find(m).map(|i| (i, m.len())))
            .min();
        let Some((i, len)) = next else { break };
        out.push_str(&rest[..i + len]);
        rest = &rest[i + len..];
        let n = rest
            .find(|c: char| !c.is_ascii_digit())
            .unwrap_or(rest.len());
        match rest[..n].parse::<u32>() {
            Ok(id) => out.push_str(&name(id)),
            Err(_) => out.push_str(&rest[..n]),
        }
        rest = &rest[n..];
    }
    out.push_str(rest);
    out
}

/// `quarz ir`'s dump of the shaken module with its ids replaced by names
/// that do not depend on the order things were declared or lowered in:
/// a method by its line in the method table (with its place among equal
/// ones), a method's function by its method, a block by its maker and its
/// place there, the other functions (top levels, initializers) by their
/// names. The members a set's statements generate are declared before the
/// program's own when the set is made, after them when its modules are
/// checked in the program: the same methods under other ids. Functions
/// the program cannot reach (shaken out, or the empty bodies a set's seed
/// keeps ids with) are left out: what remains is every function the
/// program reaches, the standard library's included.
fn mapped_ir(dump: &str) -> String {
    let mut funcs: Vec<(u32, String, Vec<String>)> = Vec::new();
    let mut methods: Vec<(u32, String, Option<u32>)> = Vec::new();
    for line in dump.lines() {
        if let Some(rest) = line.strip_prefix("fn ") {
            let id: u32 = rest.split(' ').next().unwrap().parse().unwrap();
            funcs.push((id, line.to_string(), Vec::new()));
        } else if let Some(rest) = line.strip_prefix("method ") {
            let (id, text) = rest.split_once(' ').unwrap_or((rest, ""));
            let (text, func) = match text.split_once(" fn=") {
                Some((t, f)) => {
                    let f = f.split(' ').next().unwrap().parse().ok();
                    (t.to_string(), f)
                }
                None => (text.to_string(), None),
            };
            methods.push((id.parse().unwrap(), text, func));
        } else if let Some(f) = funcs.last_mut() {
            f.2.push(line.to_string());
        }
    }
    // Methods: by their line, and their place among equal lines.
    let mut method_names: std::collections::HashMap<u32, String> = Default::default();
    let mut seen: std::collections::HashMap<String, usize> = Default::default();
    for (id, text, _) in &methods {
        let k = seen.entry(text.clone()).or_default();
        method_names.insert(*id, format!("[{text} #{k}]"));
        *k += 1;
    }
    let method = |id: u32| {
        method_names
            .get(&id)
            .cloned()
            .unwrap_or(format!("[method {id}?]"))
    };
    let empty = |f: &(u32, String, Vec<String>)| {
        f.1.contains(" \"\" ") && f.2.iter().filter(|l| !l.trim().is_empty()).count() <= 2
    };
    let mut names: std::collections::HashMap<u32, String> = Default::default();
    for (mid, _, func) in &methods {
        if let Some(f) = func {
            names.insert(*f, format!("<fn of {}>", method(*mid)));
        }
    }
    for f in &funcs {
        if !names.contains_key(&f.0) && !empty(f) {
            let name = f.1.split('"').nth(1).unwrap_or_default();
            names.insert(f.0, format!("<fn {name}>"));
        }
    }
    // Blocks by their maker, in the order its body makes them.
    let mut changed = true;
    while changed {
        changed = false;
        for f in &funcs {
            let Some(parent) = names.get(&f.0).cloned() else {
                continue;
            };
            let mut k = 0;
            for l in &f.2 {
                for t in l.split("func: ").skip(1) {
                    let n = t.find(|c: char| !c.is_ascii_digit()).unwrap_or(t.len());
                    let child: u32 = t[..n].parse().unwrap();
                    let name = format!("{parent}/block {k}");
                    k += 1;
                    if names.get(&child) != Some(&name) {
                        names.insert(child, name);
                        changed = true;
                    }
                }
            }
        }
    }
    let func = |id: u32| names.get(&id).cloned().unwrap_or(format!("<fn {id}?>"));
    let method_marks = [
        "Method(",
        "Super(",
        "Function(",
        "method: Some(",
        "method: ",
        "init: Some(",
    ];
    let rename = |line: &str| -> String {
        let line = map_numbers(line, &["func: "], &func);
        let line = map_numbers(&line, &method_marks, &method);
        // `among`'s pairs: (type, method).
        match line.split_once("among: [") {
            Some((head, tail)) => {
                let (list, rest) = tail.split_once(']').unwrap_or((tail, ""));
                let list = map_numbers(list, &[", "], &method);
                format!("{head}among: [{list}]{rest}")
            }
            None => line,
        }
    };
    let mut blocks: Vec<String> = funcs
        .iter()
        .filter(|f| !empty(f))
        .map(|f| {
            let header = f.1.split_once(' ').unwrap().1.split_once(' ').unwrap().1;
            let mut text = format!("{} {}\n", names[&f.0], rename(header));
            for l in &f.2 {
                text.push_str(&rename(l));
                text.push('\n');
            }
            text
        })
        .collect();
    blocks.sort();
    let mut lines: Vec<String> = methods
        .iter()
        .map(|(id, _, f)| {
            let f = f.map(|f| format!(" {}", func(f))).unwrap_or_default();
            format!("{}{f}\n", method(*id))
        })
        .collect();
    lines.sort();
    lines.extend(blocks);
    lines.concat()
}

/// What the three ways of loading the set give for `SET_PROGRAM`, which
/// must be the same: from source (`QUARZ_NO_STD_CACHE=1`, its modules
/// checked in the program's world, statements run), with the set made
/// (an empty cache directory) and read back (the same directory again,
/// under `QUARZ_VERIFY=std`: the set made again must encode to the same
/// bytes). Compared: the check's diagnostics and generated members
/// (`--expand`), the program's lowered functions (`quarz ir`, shaken,
/// ids mapped), and the tests' runs interpreted and compiled.
#[test]
fn a_set_made_at_first_use_checks_and_runs_as_from_source() {
    let commands: [(&str, &[&str]); 4] = [
        ("expand", &["check", "--expand", "prog_test.qz"]),
        ("ir", &["ir", "prog_test.qz"]),
        ("vm", &["test", "prog_test.qz"]),
        ("compiled", &["test", "--release", "prog_test.qz"]),
    ];
    for (what, args) in commands {
        let source = set_dir(&format!("source-{what}"));
        std::fs::write(source.join("prog_test.qz"), SET_PROGRAM).unwrap();
        let cache = source.join("cache");
        let cache = cache.to_str().unwrap();
        let ir = [("QUARZ_IR_SHAKE", "1")];
        let mut env: Vec<(&str, &str)> = vec![("QUARZ_CACHE_DIR", cache)];
        if what == "ir" {
            env.extend(ir);
        }
        let from_source = {
            let mut e = env.clone();
            e.push(("QUARZ_NO_STD_CACHE", "1"));
            quarz_in(&source, args, &e)
        };
        let _ = std::fs::remove_dir_all(source.join("cache"));
        let made = quarz_in(&source, args, &env);
        let entries = std::fs::read_dir(source.join("cache/sets"))
            .map(|d| d.count())
            .unwrap_or(0);
        assert!(entries >= 1, "{what}: no entry kept under sets/");
        let read_back = {
            let mut e = env.clone();
            e.push(("QUARZ_VERIFY", "std"));
            quarz_in(&source, args, &e)
        };
        assert!(
            from_source.starts_with("status Some(0)"),
            "{what}:\n{from_source}"
        );
        let (from_source, made, read_back) = if what == "ir" {
            (
                mapped_ir(&from_source),
                mapped_ir(&made),
                mapped_ir(&read_back),
            )
        } else {
            (from_source, made, read_back)
        };
        // (Kept for reading when they differ: the texts are long.)
        for (name, a, b) in [
            ("made", &made, &from_source),
            ("read-back", &read_back, &made),
        ] {
            if a != b {
                let keep = std::env::temp_dir().join(format!("quarz-std-set-{what}-{name}"));
                std::fs::write(keep.with_extension("left"), a).unwrap();
                std::fs::write(keep.with_extension("right"), b).unwrap();
                panic!(
                    "{what}: the set {name} differs from {}: {}.left against .right",
                    if name == "made" {
                        "from source"
                    } else {
                        "made"
                    },
                    keep.display()
                );
            }
        }
        let _ = std::fs::remove_dir_all(&source);
    }
}

/// The set's entry in `cache`, its only one.
fn set_entry(cache: &Path) -> PathBuf {
    let entries: Vec<PathBuf> = std::fs::read_dir(cache.join("sets"))
        .unwrap()
        .filter_map(|e| Some(e.ok()?.path()))
        .filter(|p| p.extension().is_some_and(|x| x == "bin"))
        .collect();
    assert_eq!(entries.len(), 1, "{entries:?}");
    entries.into_iter().next().unwrap()
}

/// An entry cut short, one with a byte changed, and one of another build
/// (its header's build id changed) are each a miss: the set is made
/// again, with the same result, and the entry replaced by the one made.
#[test]
fn a_damaged_or_foreign_set_entry_is_made_again() {
    let dir = set_dir("damaged");
    std::fs::write(dir.join("prog_test.qz"), SET_PROGRAM).unwrap();
    let cache = dir.join("cache");
    let env = [("QUARZ_CACHE_DIR", cache.to_str().unwrap())];
    let first = quarz_in(&dir, &["test", "prog_test.qz"], &env);
    assert!(first.starts_with("status Some(0)"), "{first}");
    let entry = set_entry(&cache);
    let good = std::fs::read(&entry).unwrap();
    // The build id: the first run of 12 or more hex digits in the header.
    let build_at = good
        .windows(12)
        .position(|w| w.iter().all(|b| b.is_ascii_hexdigit()))
        .expect("the build id in the header");
    let mut foreign = good.clone();
    foreign[build_at] = if foreign[build_at] == b'0' {
        b'1'
    } else {
        b'0'
    };
    let mut flipped = good.clone();
    let last = flipped.len() - 1;
    flipped[last] ^= 0x01;
    let damages: [(&str, Vec<u8>); 3] = [
        ("cut short", good[..good.len() / 2].to_vec()),
        ("a byte changed", flipped),
        ("another build's", foreign),
    ];
    for (how, bytes) in damages {
        std::fs::write(&entry, &bytes).unwrap();
        let again = quarz_in(&dir, &["test", "prog_test.qz"], &env);
        assert_eq!(again, first, "an entry {how}");
        assert_eq!(
            std::fs::read(&entry).unwrap(),
            good,
            "an entry {how}: made again and kept"
        );
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// A cache directory that cannot be written: the set is made in every
/// process and kept in none, with the same result.
#[cfg(unix)]
#[test]
fn a_set_made_where_the_cache_cannot_be_written_is_used_and_not_kept() {
    use std::os::unix::fs::PermissionsExt;
    let dir = set_dir("read-only");
    std::fs::write(dir.join("prog_test.qz"), SET_PROGRAM).unwrap();
    let cache = dir.join("cache");
    std::fs::create_dir_all(&cache).unwrap();
    std::fs::set_permissions(&cache, std::fs::Permissions::from_mode(0o555)).unwrap();
    // (Not as root, whom the mode does not stop.)
    if std::fs::create_dir(cache.join("probe")).is_ok() {
        let _ = std::fs::set_permissions(&cache, std::fs::Permissions::from_mode(0o755));
        let _ = std::fs::remove_dir_all(&dir);
        return;
    }
    let env = [("QUARZ_CACHE_DIR", cache.to_str().unwrap())];
    let first = quarz_in(&dir, &["test", "prog_test.qz"], &env);
    let second = quarz_in(&dir, &["test", "prog_test.qz"], &env);
    assert!(first.starts_with("status Some(0)"), "{first}");
    assert_eq!(second, first);
    assert!(
        !cache.join("sets").exists(),
        "an entry kept under a read-only directory"
    );
    let _ = std::fs::set_permissions(&cache, std::fs::Permissions::from_mode(0o755));
    let _ = std::fs::remove_dir_all(&dir);
}
