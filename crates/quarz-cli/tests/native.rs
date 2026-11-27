//! A cog's native code (#677, docs/15): the fixture cog `tests/native/demo`
//! (an application whose `Cog.toml` declares `[native] crate = "native"`),
//! its native package built once per run by the workspace's cargo into a
//! target directory under `target/` (`CARGO_TARGET_TMPDIR`), from a copy
//! of the fixture in a temporary directory: a run leaves nothing in the
//! source tree. The package's only dependency is `quarz-ext`, by path, so
//! the build needs no network (`--offline`).

use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::OnceLock;

/// The fixture's files, in the source tree.
fn fixture_src() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/native/demo")
}

/// The target directory the fixture's package is built into (and that
/// `quarz` finds its library in: cargo's `CARGO_TARGET_DIR`).
fn target_dir() -> PathBuf {
    Path::new(env!("CARGO_TARGET_TMPDIR")).join("native-demo-target")
}

/// `from` copied to `to`, but `target/`.
fn copy_dir(from: &Path, to: &Path) {
    std::fs::create_dir_all(to).unwrap();
    for e in std::fs::read_dir(from).unwrap().flatten() {
        let p = e.path();
        if e.file_name() == "target" {
            continue;
        }
        if p.is_dir() {
            copy_dir(&p, &to.join(e.file_name()));
        } else {
            std::fs::copy(&p, to.join(e.file_name())).unwrap();
        }
    }
}

/// A fresh copy of the fixture, with `src` overriding files of `src/`
/// (name, text), its native package's `Cargo.toml` written with
/// `quarz-ext`'s absolute path.
fn fixture(name: &str, src: &[(&str, &str)]) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("quarz-native-{name}-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    copy_dir(&fixture_src(), &dir);
    let ext = Path::new(env!("CARGO_MANIFEST_DIR")).join("../quarz-ext");
    std::fs::write(
        dir.join("native/Cargo.toml"),
        format!(
            "[package]\nname = \"demo-native\"\nversion = \"0.1.0\"\nedition = \"2021\"\n\n[lib]\ncrate-type = [\"cdylib\"]\n\n[dependencies]\nquarz-ext = {{ path = {:?} }}\n\n[workspace]\n",
            std::fs::canonicalize(ext).unwrap()
        ),
    )
    .unwrap();
    for (file, text) in src {
        std::fs::write(dir.join("src").join(file), text).unwrap();
    }
    dir
}

/// Build the fixture's native package, once per run.
fn built() -> &'static Result<(), String> {
    static BUILT: OnceLock<Result<(), String>> = OnceLock::new();
    BUILT.get_or_init(|| {
        let dir = fixture("build", &[]);
        let cargo = std::env::var("CARGO").unwrap_or_else(|_| "cargo".to_string());
        let out = Command::new(cargo)
            .args(["build", "--release", "--offline", "--quiet"])
            .current_dir(dir.join("native"))
            .env("CARGO_TARGET_DIR", target_dir())
            .output()
            .map_err(|e| e.to_string())?;
        let _ = std::fs::remove_dir_all(&dir);
        if out.status.success() {
            Ok(())
        } else {
            Err(String::from_utf8_lossy(&out.stderr).into_owned())
        }
    })
}

/// `quarz args` in `dir`, finding the native library in `target_dir()`:
/// (status, stdout, stderr).
fn quarz(dir: &Path, args: &[&str], envs: &[(&str, &str)]) -> (bool, String, String) {
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_quarz"));
    cmd.args(args)
        .current_dir(dir)
        .env("CARGO_TARGET_DIR", target_dir())
        .env("QUARZ_THREADS", "1");
    for (k, v) in envs {
        cmd.env(k, v);
    }
    let out = cmd.output().unwrap();
    (
        out.status.success(),
        String::from_utf8_lossy(&out.stdout).into_owned(),
        String::from_utf8_lossy(&out.stderr).into_owned(),
    )
}

/// The fixture's program runs its natives: each of the ABI's functions,
/// keyword-only defaults filled in, an exception raised by class, a panic
/// as `NativePanic`, a lent array not changed, a class that needs its
/// `initialize` refused, another call's handle refused.
#[test]
fn a_cogs_native_methods_run() {
    built().as_ref().unwrap();
    let dir = fixture("run", &[]);
    let (ok, out, err) = quarz(&dir, &["run"], &[]);
    let _ = std::fs::remove_dir_all(&dir);
    assert!(ok, "{err}");
    let want = "\
42
\"nil\"
\"int\"
\"float\"
\"string\"
\"symbol\"
\"array\"
\"hash\"
\"other\"
\"olléh\"
294
b\"\\x00\\x00\\x00\\x07\"
[0, 1, 4, 9, 16]
10
{1 => \"a\", 2 => \"b\"}
:abc
3.0
4.5
nil
ArgumentError
\"bad input\"
DemoError
\"from native code\"
\"a native method cannot raise `FancyError`: not an exception class made from a message alone (it is abstract or generic, or one of its classes up to the built-in ones declares an `initialize` or a field, docs/15)\"
\"a native method cannot raise `AbstractError`: not an exception class made from a message alone (it is abstract or generic, or one of its classes up to the built-in ones declares an `initialize` or a field, docs/15)\"
\"a native method cannot raise `GenericError`: not an exception class made from a message alone (it is abstract or generic, or one of its classes up to the built-in ones declares an `initialize` or a field, docs/15)\"
NativePanic
\"the demo panics\"
\"a native method pushed to an array it did not make: values are immutable (docs/15)\"
\"QUIET\"
5
\"a native method used a handle that is not one of its call's (docs/15)\"
\"hi|a long string, longer than any kept inline in its value\"
5320
\"40 ok\"
{0 => 0, 1 => 10, 2 => 20}
10
true
{0 => 0, 1 => 10, 2 => 20, 5 => 50}
33
[0.0, 0.5, 1.0]
1.0
true
[0.0, 1.0, 2.0]
2
true
[2, 2]
:done
";
    assert_eq!(out, want);
}

/// A native cog whose library is not built: an error naming the cog and
/// the path looked at, before anything runs.
#[test]
fn a_missing_native_library_is_an_error() {
    let dir = fixture("missing", &[]);
    let empty = dir.join("no-target");
    let (ok, out, err) = quarz(
        &dir,
        &["run"],
        &[("CARGO_TARGET_DIR", empty.to_str().unwrap())],
    );
    let _ = std::fs::remove_dir_all(&dir);
    assert!(!ok);
    assert_eq!(out, "");
    assert!(
        err.contains("quarz: cog `demo` brings native code, but its library is not built: no ")
            && err.contains("libdemo_native.so")
            && err.contains("cargo build --release"),
        "{err}"
    );
}

/// `quarz build` of a program with a native cog: refused, until #677
/// links one.
#[test]
fn quarz_build_refuses_a_native_cog_for_now() {
    let dir = fixture("build-refused", &[]);
    let exe = dir.join("demo-bin");
    let (ok, _, err) = quarz(&dir, &["build", "-o", exe.to_str().unwrap()], &[]);
    let exists = exe.exists();
    let _ = std::fs::remove_dir_all(&dir);
    assert!(!ok);
    assert!(!exists, "an executable was left");
    assert!(
        err.contains("cog `demo` brings native code, which `quarz build` cannot build into an executable yet (#677)"),
        "{err}"
    );
}

/// What a cog's native returns is tested against its declared result's
/// class on every call, `QUARZ_VERIFY` or not (decided on #677), by the
/// test `QUARZ_VERIFY` runs for the standard natives: a mismatch is a
/// `TypeError` the program can rescue. A singleton method's declared
/// `Self` is tested as its class.
#[test]
fn a_cogs_native_result_is_checked() {
    built().as_ref().unwrap();
    let main = "begin\n  Demo.wrong\nrescue TypeError => e\n  p e.message\nend\nbegin\n  Crate.make\nrescue TypeError => e\n  p e.message\nend\n";
    let dir = fixture("verify", &[("main.qz", main)]);
    let (ok, out, err) = quarz(&dir, &["run"], &[("QUARZ_VERIFY", "0")]);
    let _ = std::fs::remove_dir_all(&dir);
    assert!(ok, "{err}");
    assert_eq!(
        out,
        "\"native `Demo.wrong` returned a value of class String, but its declared result is Int\"\n\
         \"native `Crate.make` returned a value of class String, but its declared result is Crate\"\n"
    );
}

/// A library cog with native code (`[native]`; no library is needed to
/// check), a git repository tagged `v0.1.0` in `dir/natlib`, and an
/// application depending on it in `dir/app` whose main file is `main`.
fn library_and_app(dir: &Path, lib: &str, main: &str) {
    let _ = std::fs::remove_dir_all(dir);
    let natlib = dir.join("natlib");
    std::fs::create_dir_all(natlib.join("src")).unwrap();
    std::fs::write(
        natlib.join("Cog.toml"),
        "[cog]\nname = \"natlib\"\nversion = \"0.1.0\"\n\n[native]\ncrate = \"native\"\n",
    )
    .unwrap();
    std::fs::write(natlib.join("src/natlib.qz"), lib).unwrap();
    for args in [
        &["init", "-q", "-b", "main"][..],
        &["add", "-A"],
        &["commit", "-q", "-m", "natlib"],
        &["tag", "v0.1.0"],
    ] {
        let ok = Command::new("git")
            .args(args)
            .current_dir(&natlib)
            .env("GIT_AUTHOR_NAME", "t")
            .env("GIT_AUTHOR_EMAIL", "t@example.com")
            .env("GIT_COMMITTER_NAME", "t")
            .env("GIT_COMMITTER_EMAIL", "t@example.com")
            .status()
            .unwrap()
            .success();
        assert!(ok, "git {args:?}");
    }
    let app = dir.join("app");
    std::fs::create_dir_all(app.join("src")).unwrap();
    std::fs::write(
        app.join("Cog.toml"),
        format!(
            "[cog]\nname = \"app\"\nversion = \"0.1.0\"\n\n[dependencies]\nNatlib = {{ git = \"file://{}\", tag = \"v0.1.0\" }}\n",
            natlib.display()
        ),
    )
    .unwrap();
    std::fs::write(app.join("src/main.qz"), main).unwrap();
}

/// A cog's native never runs at compile time, refused by its kind: also
/// one on `String`, whose natives the compile-time runs take as pure by
/// its class's name, reached through a method of the cog's in Quarz.
#[test]
fn a_cogs_native_is_refused_at_compile_time() {
    let lib = "class Calc\n  native def self.add(a: Int, b: Int) -> Int\n  def self.loud(s: String) -> String = s.shout\nend\n\nextension String\n  native def shout -> String\nend\n";
    for (main, want) in [
        (
            "X = static(Natlib::Calc.add(1, 2))\np X\n",
            "`add` reaches `Natlib::Calc.add`, which cannot run at compile time",
        ),
        (
            "Y = static(Natlib::Calc.loud(\"a\"))\np Y\n",
            "`loud` reaches `String#shout`, which cannot run at compile time",
        ),
    ] {
        let dir = std::env::temp_dir().join(format!("quarz-native-static-{}", std::process::id()));
        library_and_app(&dir, lib, main);
        let cache = dir.join("cache");
        let (ok, _, err) = quarz(
            &dir.join("app"),
            &["check"],
            &[("QUARZ_CACHE", cache.to_str().unwrap())],
        );
        let _ = std::fs::remove_dir_all(&dir);
        assert!(!ok, "{main}");
        assert!(err.contains(want), "{main}: {err}");
    }
}

/// A method of another cog (here the application, native itself: a
/// native and one with a body) named as a cog's natives on the same class
/// is no overload of them: each is
/// bound on its own (`RtMethod::ext`, the cog's index, and its key in
/// that cog's module; a method with a body runs its body), so the two
/// share no entry.
#[test]
fn another_cogs_method_of_a_natives_name_is_its_own() {
    let lib = "class Calc\n  native def self.add(a: Int, b: Int) -> Int\nend\n\nextension String\n  native def shout -> String\n  native def whisper -> String\nend\n";
    let main = "extension String\n  native def shout(times: Int) -> String\n  def whisper(times: Int) -> String = self\nend\n\np \"a\".whisper(2)\n";
    let dir = std::env::temp_dir().join(format!("quarz-native-other-{}", std::process::id()));
    library_and_app(&dir, lib, main);
    let manifest = dir.join("app/Cog.toml");
    let text = std::fs::read_to_string(&manifest).unwrap();
    std::fs::write(&manifest, text + "\n[native]\ncrate = \"native\"\n").unwrap();
    let cache = dir.join("cache");
    let (ok, _, err) = quarz(
        &dir.join("app"),
        &["check"],
        &[("QUARZ_CACHE", cache.to_str().unwrap())],
    );
    let _ = std::fs::remove_dir_all(&dir);
    assert!(ok, "{err}");
}

/// What a cog's `native def` may not declare in ABI 1.0, refused by
/// `quarz check` (which needs no library): a `*rest`, a `**rest`, a
/// default that is not a literal, an overload; and `native def` in a cog
/// whose manifest declares no native code.
#[test]
fn a_cogs_native_def_is_checked() {
    for (decl, want) in [
        (
            "module Bad\n  native def self.f(*xs: Int) -> Int\nend\n",
            "a cog's native method takes no `*rest` or `**rest` (docs/15)",
        ),
        (
            "module Bad\n  native def self.f(**kw: Int) -> Int\nend\n",
            "a cog's native method takes no `*rest` or `**rest` (docs/15)",
        ),
        (
            "module Bad\n  native def self.f(x: Int = 1 + 1) -> Int\nend\n",
            "a cog's native method's default is a literal (nil, true, false, an Int, a Float or a Symbol): `x`'s is not (docs/15)",
        ),
        (
            "module Bad\n  native def self.f(x: Int) -> Int\n  native def self.f(x: String) -> Int\nend\n",
            "a cog's native method has no overloads: `Bad.f` is declared twice",
        ),
    ] {
        let dir = fixture("decl", &[("bad.qz", decl)]);
        let (ok, _, err) = quarz(&dir, &["check"], &[]);
        let _ = std::fs::remove_dir_all(&dir);
        assert!(!ok, "{decl}");
        assert!(err.contains(want), "{decl}: {err}");
    }
    // Overloads through extensions (#677): one entry per key, whatever
    // the blocks or files of the cog's extensions declare it in; a
    // standard method of the class counts too.
    let twice = "a cog's native method has no overloads: `String#twice` is declared twice";
    for (files, want) in [
        (
            &[("bad.qz", "extension String\n  native def twice(x: Int) -> String\n  native def twice(x: String) -> String\nend\n")][..],
            twice,
        ),
        (
            &[("bad.qz", "extension String\n  native def twice(x: Int) -> String\nend\nextension String\n  native def twice(x: String) -> String\nend\n")],
            twice,
        ),
        (
            &[
                ("bad.qz", "extension String\n  native def twice(x: Int) -> String\nend\n"),
                ("bad2.qz", "extension String\n  native def twice(x: String) -> String\nend\n"),
            ],
            twice,
        ),
        (
            &[("bad.qz", "extension String\n  def twice(x: Int) -> String = self\nend\nextension String\n  native def twice(x: String) -> String\nend\n")],
            twice,
        ),
        (
            &[("bad.qz", "extension String\n  native def upcase(x: Int) -> Int\nend\n")],
            "a cog's native method has no overloads: `String#upcase` is declared twice",
        ),
    ] {
        let dir = fixture("ext", files);
        let (ok, _, err) = quarz(&dir, &["check"], &[]);
        let _ = std::fs::remove_dir_all(&dir);
        assert!(!ok, "{files:?}");
        assert!(err.contains(want), "{files:?}: {err}");
    }
    let dir = fixture("not-native", &[]);
    std::fs::write(
        dir.join("Cog.toml"),
        "[cog]\nname = \"demo\"\nversion = \"0.1.0\"\n",
    )
    .unwrap();
    let (ok, _, err) = quarz(&dir, &["check"], &[]);
    let _ = std::fs::remove_dir_all(&dir);
    assert!(!ok);
    assert!(
        err.contains("`native def` is for the standard library: a method of a program or a cog is written in Quarz, with a body"),
        "{err}"
    );
}
