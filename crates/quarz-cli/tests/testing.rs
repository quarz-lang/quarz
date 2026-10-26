//! `quarz test` (docs/12-testing.md): the runner over `test_cmd/`, on the
//! VM and compiled (`--release`), its options, the errors in test
//! signatures, and the tests of a cog with its dev-dependencies.

use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU32, Ordering};

fn tests_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests")
}

fn quarz_in(dir: &Path, args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_quarz"))
        .arg("test")
        .args(args)
        .current_dir(dir)
        .output()
        .expect("run quarz test")
}

fn quarz(args: &[&str]) -> Output {
    quarz_in(&tests_dir(), args)
}

fn stdout(out: &Output) -> String {
    String::from_utf8_lossy(&out.stdout).into_owned()
}

fn stderr(out: &Output) -> String {
    String::from_utf8_lossy(&out.stderr).into_owned()
}

/// The report with its times taken out.
fn normalized(text: &str) -> String {
    text.lines()
        .map(|l| {
            if l.starts_with("Finished in ") {
                "Finished in T seconds.".to_string()
            } else {
                l.to_string()
            }
        })
        .collect::<Vec<_>>()
        .join("\n")
        + "\n"
}

fn expected(name: &str) -> String {
    std::fs::read_to_string(tests_dir().join(format!("test_cmd/{name}.out"))).unwrap()
}

#[test]
fn the_report_on_the_vm() {
    let out = quarz(&["test_cmd/all_test.qz", "--timeout=200ms"]);
    assert_eq!(out.status.code(), Some(1), "{}", stderr(&out));
    assert_eq!(normalized(&stdout(&out)), expected("all_test"));
}

#[test]
fn the_report_compiled() {
    let out = quarz(&["--release", "test_cmd/all_test.qz", "--timeout=200ms"]);
    assert_eq!(out.status.code(), Some(1), "{}", stderr(&out));
    assert_eq!(normalized(&stdout(&out)), expected("all_test"));
}

#[test]
fn what_fails_around_the_tests_is_reported() {
    for release in [false, true] {
        let mut args = vec!["test_cmd/errors_test.qz", "--timeout=500ms"];
        if release {
            args.insert(0, "--release");
        }
        let out = quarz(&args);
        assert_eq!(out.status.code(), Some(1), "{}", stderr(&out));
        assert_eq!(
            normalized(&stdout(&out)),
            expected("errors_test"),
            "release: {release}"
        );
    }
}

#[test]
fn fail_fast_cancels_parallel_tests() {
    let started = std::time::Instant::now();
    let out = Command::new(env!("CARGO_BIN_EXE_quarz"))
        .args([
            "test",
            "test_cmd/fail_fast_test.qz",
            "--parallel",
            "--fail-fast",
        ])
        .current_dir(tests_dir())
        .env("QUARZ_THREADS", "4")
        .output()
        .unwrap();
    assert_eq!(out.status.code(), Some(1));
    assert!(stdout(&out).contains("\nF\n"), "{}", stdout(&out));
    assert!(
        stdout(&out).contains("1 tests, 1 assertions, 1 failures"),
        "{}",
        stdout(&out)
    );
    assert!(started.elapsed() < std::time::Duration::from_millis(1500));
}

/// An `exit` in a test is raised in that test, also run in parallel
/// (each test a scope child of the runner) with several workers.
#[test]
fn an_exit_in_a_test_is_caught_in_it() {
    for args in [
        vec!["test_cmd/exit_test.qz"],
        vec!["test_cmd/exit_test.qz", "--parallel=4"],
    ] {
        let out = Command::new(env!("CARGO_BIN_EXE_quarz"))
            .arg("test")
            .args(&args)
            .current_dir(tests_dir())
            .env("QUARZ_THREADS", "4")
            .output()
            .unwrap();
        assert_eq!(
            out.status.code(),
            Some(0),
            "{args:?}: {}{}",
            stdout(&out),
            stderr(&out)
        );
        assert!(
            stdout(&out).contains("3 tests, 3 assertions, 0 failures, 0 errors"),
            "{args:?}: {}",
            stdout(&out)
        );
    }
}

#[test]
fn list_and_names() {
    let out = quarz(&[
        "test_cmd/all_test.qz",
        "--list",
        "-n",
        "/double|sleep/",
        "-n",
        "test_flunk",
    ]);
    assert_eq!(
        stdout(&out),
        "StackTest#test_flunk\nStackTest#test_double[one]\nStackTest#test_double[bad]\nSerialTest#test_sleep\n"
    );
    let out = quarz(&["test_cmd/all_test.qz", "-n", "test_push_pop"]);
    assert_eq!(out.status.code(), Some(0), "{}", stdout(&out));
    assert!(
        stdout(&out).contains("1 tests, 2 assertions, 0 failures"),
        "{}",
        stdout(&out)
    );
}

#[test]
fn random_order_is_set_by_the_seed() {
    let run = || {
        let out = quarz(&[
            "test_cmd/all_test.qz",
            "--seed=42",
            "-v",
            "-n",
            "Stack",
            "--timeout=200ms",
        ]);
        stdout(&out)
            .lines()
            .filter(|l| l.starts_with("StackTest#"))
            .map(|l| l.split(':').next().unwrap().to_string())
            .collect::<Vec<_>>()
    };
    let first = run();
    assert_eq!(first.len(), 15, "{first:?}");
    assert_eq!(first, run());
    let mut defined = first.clone();
    defined.sort();
    assert_ne!(first, defined);
}

#[test]
fn fail_fast_and_junit() {
    static N: AtomicU32 = AtomicU32::new(0);
    let xml = std::env::temp_dir().join(format!(
        "quarz-junit-{}-{}.xml",
        std::process::id(),
        N.fetch_add(1, Ordering::SeqCst)
    ));
    let junit = format!("--junit={}", xml.display());
    let out = quarz(&["test_cmd/all_test.qz", "--fail-fast", &junit]);
    assert_eq!(out.status.code(), Some(1));
    assert!(
        stdout(&out).contains("5 tests, 10 assertions, 1 failures, 0 errors"),
        "{}",
        stdout(&out)
    );
    let report = std::fs::read_to_string(&xml).unwrap();
    let _ = std::fs::remove_file(&xml);
    assert!(
        report.contains("<testsuites tests=\"5\" failures=\"1\" errors=\"0\" skipped=\"0\""),
        "{report}"
    );
    assert!(
        report.contains(
            "<failure message=\"&lt;IndexError&gt; exception was expected but none was thrown.\">"
        ),
        "{report}"
    );
}

#[test]
fn parallel_tests_wait_together() {
    let started = std::time::Instant::now();
    let out = Command::new(env!("CARGO_BIN_EXE_quarz"))
        .args(["test", "test_cmd/parallel_test.qz", "--parallel=8"])
        .current_dir(tests_dir())
        .env("QUARZ_THREADS", "4")
        .output()
        .unwrap();
    assert_eq!(out.status.code(), Some(0), "{}", stdout(&out));
    assert!(stdout(&out).contains("\n........\n"), "{}", stdout(&out));
    assert!(stdout(&out).contains("8 tests, 0 assertions, 0 failures, 0 errors"));
    // Eight sleeps of 500 ms one after another would take 4 s.
    assert!(started.elapsed() < std::time::Duration::from_secs(3));
}

#[test]
fn test_signatures_are_checked() {
    let out = quarz(&["test_cmd/bad/signatures.qz"]);
    assert_eq!(out.status.code(), Some(1));
    let err = stderr(&out);
    for want in [
        "signatures.qz:2:3: error: BadTest#test_private_one: a test method must be public",
        "signatures.qz:7:3: error: BadTest#test_needs takes a parameter but `data_needs` is not defined",
        "signatures.qz:11:3: error: BadTest#test_two: a test method takes no parameters, or one with a `data_` method",
        "signatures.qz:19:3: error: ArgTest: a test class is made by `new` with no arguments",
    ] {
        assert!(err.contains(want), "{want}\n{err}");
    }
    assert_eq!(stdout(&out), "");
}

/// A temporary directory of repositories and cogs.
struct Dir(PathBuf);

impl Drop for Dir {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

impl Dir {
    fn new() -> Dir {
        static N: AtomicU32 = AtomicU32::new(0);
        let dir = std::env::temp_dir().join(format!(
            "quarz-testing-{}-{}",
            std::process::id(),
            N.fetch_add(1, Ordering::SeqCst)
        ));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        Dir(dir)
    }

    fn write(&self, rel: &str, text: &str) {
        let path = self.0.join(rel);
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(path, text).unwrap();
    }

    fn git(&self, repo: &str, args: &[&str]) {
        let out = Command::new("git")
            .args(args)
            .current_dir(self.0.join(repo))
            .env("GIT_AUTHOR_NAME", "t")
            .env("GIT_AUTHOR_EMAIL", "t@example.com")
            .env("GIT_COMMITTER_NAME", "t")
            .env("GIT_COMMITTER_EMAIL", "t@example.com")
            .output()
            .expect("git");
        assert!(
            out.status.success(),
            "git {args:?}: {}",
            String::from_utf8_lossy(&out.stderr)
        );
    }

    /// A cog `fixtures` 1.0.0 in a repository of its own.
    fn fixtures(&self) -> String {
        self.write(
            "fixtures/Cog.toml",
            "[cog]\nname = \"fixtures\"\nversion = \"1.0.0\"\n",
        );
        self.write(
            "fixtures/src/f.qz",
            "def self.numbers -> Array[Int] = [1, 2, 3]\n",
        );
        self.git("fixtures", &["init", "-q", "-b", "main"]);
        self.git("fixtures", &["add", "-A"]);
        self.git("fixtures", &["commit", "-q", "-m", "commit"]);
        self.git("fixtures", &["tag", "v1.0.0"]);
        format!(
            "[dev-dependencies]\nFixtures = {{ git = \"file://{}\", tag = \"v1.0.0\" }}\n",
            self.0.join("fixtures").display()
        )
    }

    fn quarz(&self, cwd: &str, args: &[&str]) -> Output {
        Command::new(env!("CARGO_BIN_EXE_quarz"))
            .args(args)
            .current_dir(self.0.join(cwd))
            .env("QUARZ_CACHE", self.0.join("cache"))
            .output()
            .expect("quarz")
    }
}

#[test]
fn an_application_is_tested_with_its_dev_dependencies() {
    let d = Dir::new();
    let dev = d.fixtures();
    d.write(
        "app/Cog.toml",
        &format!("[cog]\nname = \"app\"\nversion = \"0.1.0\"\n\n{dev}"),
    );
    d.write("app/src/main.qz", "puts \"main runs\"\np Calc.add(1, 2)\n");
    d.write(
        "app/src/calc.qz",
        "module Calc\n  def self.add(a: Int, b: Int) -> Int = a + b\nend\n",
    );
    d.write(
        "app/test/test_helper.qz",
        "module Helper\n  def self.three -> Int = 3\nend\n",
    );
    d.write(
        "app/test/calc/calc_test.qz",
        "require_relative \"../test_helper\"\n\nclass CalcTest < Test::Case\n  def test_add\n    assert_equal(Helper.three, Calc.add(1, 2))\n    assert_equal(6, Fixtures.numbers.sum)\n  end\nend\n",
    );
    let out = d.quarz("app", &["test"]);
    assert_eq!(
        out.status.code(),
        Some(0),
        "{}{}",
        stdout(&out),
        stderr(&out)
    );
    // The main file's statements do not run.
    assert!(!stdout(&out).contains("main runs"), "{}", stdout(&out));
    assert!(
        stdout(&out).contains("1 tests, 2 assertions, 0 failures"),
        "{}",
        stdout(&out)
    );
    let lock = std::fs::read_to_string(d.0.join("app/Cog.lock")).unwrap();
    assert!(lock.contains("name = \"fixtures\""), "{lock}");
    // A file given under test/ is tested in the cog too.
    let out = d.quarz("app", &["test", "test/calc/calc_test.qz"]);
    assert_eq!(
        out.status.code(),
        Some(0),
        "{}{}",
        stdout(&out),
        stderr(&out)
    );
    // The program does not see the dev-dependencies.
    let out = d.quarz("app", &["run", "--locked"]);
    assert_eq!(stdout(&out), "main runs\n3\n");
    d.write("app/src/main.qz", "p Fixtures.numbers\n");
    let out = d.quarz("app", &["run", "--locked"]);
    assert!(
        stderr(&out).contains("unknown constant `Fixtures`"),
        "{}",
        stderr(&out)
    );
}

#[test]
fn a_library_is_tested_under_its_module() {
    let d = Dir::new();
    let dev = d.fixtures();
    d.write(
        "mathx/Cog.toml",
        &format!("[cog]\nname = \"mathx\"\nversion = \"0.1.0\"\n\n{dev}"),
    );
    d.write(
        "mathx/src/mathx.qz",
        "def self.square(x: Int) -> Int = x * x\ndata Vec = (x: Int)\n",
    );
    d.write(
        "mathx/test/mathx_test.qz",
        "class MathxTest < Test::Case\n  def test_square\n    assert_equal(9, Mathx.square(3))\n    assert_equal(2, Mathx::Vec.new(2).x)\n    assert_equal(3, Fixtures.numbers.size)\n  end\n\n  def test_fails\n    assert_equal(1, Mathx.square(2))\n  end\nend\n",
    );
    let out = d.quarz("mathx", &["test"]);
    assert_eq!(
        out.status.code(),
        Some(1),
        "{}{}",
        stdout(&out),
        stderr(&out)
    );
    let report = stdout(&out);
    assert!(
        report.contains("2 tests, 4 assertions, 1 failures, 0 errors"),
        "{report}"
    );
    assert!(
        report.contains("1) Failure: test_fails(MathxTest) ["),
        "{report}"
    );
    assert!(
        report.contains("mathx_test.qz:9]:\n<1> expected but was\n<4>"),
        "{report}"
    );
}
