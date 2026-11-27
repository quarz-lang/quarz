//! A cog's native code (#677, docs/10, docs/15). Fixtures:
//! - `tests/native/demo`, an application whose `Cog.toml` declares
//!   `[native] crate = "native"`: a local cog, built by `quarz` itself
//!   with cargo in the cache directory (`QUARZ_CACHE_DIR`, under
//!   `target/` for `cargo test`), from a copy of the fixture in a
//!   temporary directory: a run leaves nothing in the source tree. Its
//!   package's only dependency is `quarz-ext`, by path: no network.
//! - `tests/native/zlib`, the proof cog on `miniz_oxide` and `crc32fast`
//!   (crates.io: downloaded once, then from cargo's cache), fetched from a
//!   git repository the test makes.
//! - a cog written here whose package has no dependency at all, which
//!   implements the ABI by hand: a fetched cog the lock pins, kept by its
//!   key.

use std::path::{Path, PathBuf};
use std::process::Command;

/// The fixture `name`'s files, in the source tree.
fn fixture_src(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/native")
        .join(name)
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

/// `quarz-ext`'s directory, absolute.
fn quarz_ext() -> PathBuf {
    std::fs::canonicalize(Path::new(env!("CARGO_MANIFEST_DIR")).join("../quarz-ext")).unwrap()
}

/// A native package's `Cargo.toml` depending on `quarz-ext` by its
/// absolute path, with `deps` besides.
fn package_manifest(name: &str, deps: &str) -> String {
    format!(
        "[package]\nname = \"{name}\"\nversion = \"0.1.0\"\nedition = \"2021\"\n\n[lib]\ncrate-type = [\"cdylib\", \"staticlib\"]\n\n[dependencies]\nquarz-ext = {{ path = {:?} }}\n{deps}\n[workspace]\n",
        quarz_ext()
    )
}

/// A fresh copy of the demo fixture, with `src` overriding files of
/// `src/` (name, text), its native package's `Cargo.toml` written.
fn fixture(name: &str, src: &[(&str, &str)]) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("quarz-native-{name}-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    copy_dir(&fixture_src("demo"), &dir);
    std::fs::write(
        dir.join("native/Cargo.toml"),
        package_manifest("demo-native", ""),
    )
    .unwrap();
    for (file, text) in src {
        std::fs::write(dir.join("src").join(file), text).unwrap();
    }
    dir
}

/// `quarz args` in `dir` with `envs`: (status, stdout, stderr).
fn quarz(dir: &Path, args: &[&str], envs: &[(&str, &str)]) -> (bool, String, String) {
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_quarz"));
    cmd.args(args).current_dir(dir).env("QUARZ_THREADS", "1");
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

/// `git args` in `dir`, with an author.
fn git(dir: &Path, args: &[&str]) {
    let ok = Command::new("git")
        .args(args)
        .current_dir(dir)
        .env("GIT_AUTHOR_NAME", "t")
        .env("GIT_AUTHOR_EMAIL", "t@example.com")
        .env("GIT_COMMITTER_NAME", "t")
        .env("GIT_COMMITTER_EMAIL", "t@example.com")
        .status()
        .unwrap()
        .success();
    assert!(ok, "git {args:?} in {}", dir.display());
}

/// `dir` made a git repository, its files committed and tagged `v0.1.0`.
fn commit_tagged(dir: &Path) {
    git(dir, &["init", "-q", "-b", "main"]);
    git(dir, &["add", "-A"]);
    git(dir, &["commit", "-q", "-m", "cog"]);
    git(dir, &["tag", "v0.1.0"]);
}

/// An application `app` in `dir/app` depending on the cog repository
/// `repo` as `Dep` (tag `v0.1.0`), its main file `main`.
fn app_on(dir: &Path, key: &str, repo: &Path, main: &str) -> PathBuf {
    let app = dir.join("app");
    std::fs::create_dir_all(app.join("src")).unwrap();
    std::fs::write(
        app.join("Cog.toml"),
        format!(
            "[cog]\nname = \"app\"\nversion = \"0.1.0\"\n\n[dependencies]\n{key} = {{ git = \"file://{}\", tag = \"v0.1.0\" }}\n",
            repo.display()
        ),
    )
    .unwrap();
    std::fs::write(app.join("src/main.qz"), main).unwrap();
    app
}

/// The environment of a run on its own caches: cogs fetched into
/// `dir/cogs`, builds kept in `dir/cache`.
fn own_caches(dir: &Path) -> Vec<(&'static str, String)> {
    vec![
        ("QUARZ_CACHE", dir.join("cogs").display().to_string()),
        ("QUARZ_CACHE_DIR", dir.join("cache").display().to_string()),
    ]
}

fn as_refs<'a>(envs: &'a [(&'static str, String)]) -> Vec<(&'static str, &'a str)> {
    envs.iter().map(|(k, v)| (*k, v.as_str())).collect()
}

/// A cog `raw` whose native package has no dependency but `deps` (none:
/// no `quarz-ext` either) and implements the ABI by hand: `Raw::Calc.answer`
/// returns `value` (a Rust expression). Its `Cargo.lock` is made here
/// (offline: a path dependency at most), and the repository tagged.
fn raw_cog(repo: &Path, value: &str, deps: &str) {
    let _ = std::fs::remove_dir_all(repo);
    std::fs::create_dir_all(repo.join("src")).unwrap();
    std::fs::create_dir_all(repo.join("native/src")).unwrap();
    std::fs::write(
        repo.join("Cog.toml"),
        "[cog]\nname = \"raw\"\nversion = \"0.1.0\"\n\n[native]\ncrate = \"native\"\n",
    )
    .unwrap();
    std::fs::write(
        repo.join("src/raw.qz"),
        "class Calc\n  native def self.answer -> Int\nend\n",
    )
    .unwrap();
    std::fs::write(
        repo.join("native/Cargo.toml"),
        format!("[package]\nname = \"raw-native\"\nversion = \"0.1.0\"\nedition = \"2021\"\n\n[lib]\ncrate-type = [\"cdylib\", \"staticlib\"]\n\n[dependencies]\n{deps}\n[workspace]\n"),
    )
    .unwrap();
    std::fs::write(
        repo.join("native/src/lib.rs"),
        format!(
            r#"//! The ABI 1.0 by hand (docs/15): the prefix of `QzApi` up to
//! `int_new`, one method.
use std::sync::atomic::{{AtomicPtr, Ordering}};

type Entry = unsafe extern "C" fn(*mut u8, u64, *const u64, usize, u64, *mut u64) -> i32;

#[repr(C)]
pub struct Api {{
    abi_major: u32,
    abi_minor: u32,
    size: usize,
    kind: usize,
    nil: usize,
    bool_new: usize,
    bool_get: usize,
    int_new: unsafe extern "C" fn(*mut u8, i64) -> u64,
}}

#[repr(C)]
pub struct Method {{
    key: *const u8,
    key_len: usize,
    entry: Entry,
}}

#[repr(C)]
pub struct Module {{
    abi_major: u32,
    abi_minor: u32,
    methods: *const Method,
    n_methods: usize,
    method_size: usize,
}}

struct Shared<T>(T);
unsafe impl<T> Sync for Shared<T> {{}}

static API: AtomicPtr<Api> = AtomicPtr::new(std::ptr::null_mut());

unsafe extern "C" fn answer(cx: *mut u8, _: u64, _: *const u64, _: usize, _: u64, out: *mut u64) -> i32 {{
    let api = &*API.load(Ordering::Acquire);
    *out = (api.int_new)(cx, {value});
    0
}}

static KEY: &[u8] = b"Raw::Calc.answer";
static METHODS: Shared<[Method; 1]> = Shared([Method {{ key: b"Raw::Calc.answer".as_ptr(), key_len: 16, entry: answer }}]);
static MODULE: Shared<Module> = Shared(Module {{
    abi_major: 1,
    abi_minor: 0,
    methods: &METHODS.0 as *const [Method; 1] as *const Method,
    n_methods: 1,
    method_size: std::mem::size_of::<Method>(),
}});

/// # Safety
/// Called by quarz with its API.
#[no_mangle]
pub unsafe extern "C" fn qz_cog_init_raw(api: *const Api) -> *const Module {{
    let _ = KEY;
    API.store(api as *mut Api, Ordering::Release);
    &MODULE.0
}}
"#
        ),
    )
    .unwrap();
    let cargo = std::env::var("CARGO").unwrap_or_else(|_| "cargo".to_string());
    let ok = Command::new(cargo)
        .args(["generate-lockfile", "--offline", "--quiet"])
        .current_dir(repo.join("native"))
        .status()
        .unwrap()
        .success();
    assert!(ok, "cargo generate-lockfile");
    commit_tagged(repo);
}

/// The fixture's program runs its natives: each of the ABI's functions,
/// keyword-only defaults filled in, an exception raised by class, a panic
/// as `NativePanic`, a lent array not changed, a class that needs its
/// `initialize` refused, another call's handle refused.
#[test]
fn a_cogs_native_methods_run() {
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
\"80 texts, the last v79\"
3.0
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

/// A wrong native package, checked before cargo runs: each error names
/// the cog and the fix.
#[test]
fn a_wrong_native_package_is_refused() {
    // (name, what spoils the package, the error wanted)
    type Case<'a> = (&'a str, &'a dyn Fn(&Path), &'a str);
    let cases: [Case; 5] = [
        (
            "no-dir",
            &|d| {
                let m = std::fs::read_to_string(d.join("Cog.toml")).unwrap();
                std::fs::write(d.join("Cog.toml"), m.replace("crate = \"native\"", "crate = \"nope\"")).unwrap();
            },
            "cog `demo` declares `[native] crate = \"nope\"`, but there is no directory ",
        ),
        (
            "no-manifest",
            &|d| std::fs::remove_file(d.join("native/Cargo.toml")).unwrap(),
            "has no Cargo.toml",
        ),
        (
            "crate-type",
            &|d| {
                let m = std::fs::read_to_string(d.join("native/Cargo.toml")).unwrap();
                std::fs::write(d.join("native/Cargo.toml"), m.replace("[\"cdylib\", \"staticlib\"]", "[\"cdylib\"]")).unwrap();
            },
            "cog `demo`: its native package's `[lib] crate-type` must include \"cdylib\" and \"staticlib\" (it is [\"cdylib\"])",
        ),
        (
            "workspace",
            &|d| {
                let m = std::fs::read_to_string(d.join("native/Cargo.toml")).unwrap();
                std::fs::write(d.join("native/Cargo.toml"), m.replace("[workspace]\n", "")).unwrap();
            },
            "cog `demo`: its native package must be a workspace of its own: add an empty `[workspace]` table to native/Cargo.toml",
        ),
        (
            "no-lock",
            &|d| std::fs::remove_file(d.join("native/Cargo.lock")).unwrap(),
            "has no Cargo.lock, which must be committed (built with `--locked`)",
        ),
    ];
    for (name, spoil, want) in cases {
        let dir = fixture(name, &[]);
        spoil(&dir);
        let (ok, out, err) = quarz(&dir, &["run"], &[]);
        let _ = std::fs::remove_dir_all(&dir);
        assert!(!ok, "{name}");
        assert_eq!(out, "", "{name}");
        assert!(err.contains(want), "{name}: {err}");
    }
}

/// The toolchain: the rustc that built `quarz`, else an error saying what
/// to install. Stubs stand for the programs: no cargo at all; another
/// rustc without rustup; rustup without that toolchain.
#[test]
fn a_native_build_needs_quarzs_rustc() {
    let dir = fixture("toolchain", &[]);
    let bin = dir.join("stub-bin");
    std::fs::create_dir_all(&bin).unwrap();
    let empty = dir.join("empty-bin");
    std::fs::create_dir_all(&empty).unwrap();
    let script = |name: &str, body: &str| {
        let p = bin.join(name);
        std::fs::write(&p, format!("#!/bin/sh\n{body}\n")).unwrap();
        use std::os::unix::fs::PermissionsExt;
        std::fs::set_permissions(&p, std::fs::Permissions::from_mode(0o755)).unwrap();
        p
    };
    let rustc = script(
        "rustc",
        "printf 'rustc 1.0.0 (deadbeef0 2015-05-15)\\nbinary: rustc\\ncommit-hash: deadbeef00\\nrelease: 1.0.0\\n'",
    );
    let empty_path = empty.display().to_string();
    let bin_path = bin.display().to_string();
    let missing = dir.join("no-such-program").display().to_string();
    // No cargo, no rustc, no rustup.
    let (ok, _, err) = quarz(
        &dir,
        &["run"],
        &[
            ("PATH", &empty_path),
            ("CARGO", &missing),
            ("RUSTC", &missing),
        ],
    );
    assert!(!ok);
    assert!(
        err.contains("quarz: cog `demo` brings native code, built with cargo, but no `cargo` was found: install Rust "),
        "{err}"
    );
    // Another rustc, no rustup.
    let (ok, _, err) = quarz(
        &dir,
        &["run"],
        &[
            ("PATH", &bin_path),
            ("CARGO", &missing),
            ("RUSTC", rustc.to_str().unwrap()),
        ],
    );
    assert!(!ok);
    assert!(
        err.contains("brings native code, which must be built by rustc ")
            && err.contains(", the version this quarz was built with, but `")
            && err.contains("` is rustc 1.0.0 (deadbeef0 2015-05-15): put rustc ")
            && err.contains(" and its cargo first on PATH, or install rustup"),
        "{err}"
    );
    // rustup, without that toolchain.
    script(
        "rustup",
        "if [ \"$1\" = --version ]; then echo 'rustup 1.0.0'; exit 0; fi\nexit 1",
    );
    let (ok, _, err) = quarz(
        &dir,
        &["run"],
        &[
            ("PATH", &bin_path),
            ("CARGO", &missing),
            ("RUSTC", rustc.to_str().unwrap()),
        ],
    );
    let _ = std::fs::remove_dir_all(&dir);
    assert!(!ok);
    assert!(
        err.contains(", the version this quarz was built with, but that toolchain is not installed: run `rustup toolchain install "),
        "{err}"
    );
}

/// A fetched cog's native code: its package installed with its tree
/// (and hashed), the lock recording `native = true`, its build kept by its
/// key: a second run builds nothing (no cargo needed), a profile of the
/// user's is a miss; a lock disagreeing with the cog's manifest refused.
#[test]
fn a_fetched_cogs_native_build_is_kept_by_its_key() {
    let dir = std::env::temp_dir().join(format!("quarz-native-fetched-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    raw_cog(&dir.join("raw"), "42", "");
    let app = app_on(&dir, "Raw", &dir.join("raw"), "p Raw::Calc.answer\n");
    let envs = own_caches(&dir);
    let building = "quarz: building the native code of cog raw (app → raw) with cargo";
    let (ok, out, err) = quarz(&app, &["run"], &as_refs(&envs));
    assert!(ok, "{err}");
    assert_eq!(out, "42\n");
    assert!(err.contains(building), "{err}");
    let lock = std::fs::read_to_string(app.join("Cog.lock")).unwrap();
    assert!(lock.contains("native = true"), "{lock}");
    // Kept: no cargo runs (none could).
    let missing = dir.join("no-such-program").display().to_string();
    let mut no_cargo = envs.clone();
    no_cargo.push(("CARGO", missing.clone()));
    no_cargo.push(("RUSTC", missing));
    let (ok, out, err) = quarz(&app, &["run"], &as_refs(&no_cargo));
    assert!(ok, "{err}");
    assert_eq!(out, "42\n");
    assert!(!err.contains("building"), "{err}");
    // A profile of the user's: another key.
    let mut profiled = envs.clone();
    profiled.push(("CARGO_PROFILE_RELEASE_OPT_LEVEL", "1".to_string()));
    let (ok, out, err) = quarz(&app, &["run"], &as_refs(&profiled));
    assert!(ok, "{err}");
    assert_eq!(out, "42\n");
    assert!(err.contains(building), "{err}");
    // A lock that says otherwise.
    std::fs::write(app.join("Cog.lock"), lock.replace("native = true\n", "")).unwrap();
    let (ok, _, err) = quarz(&app, &["run"], &as_refs(&envs));
    let _ = std::fs::remove_dir_all(&dir);
    assert!(!ok);
    assert!(
        err.contains("Cog.lock says `raw` 0.1.0 brings no native code, but its Cog.toml declares `[native]`: run `quarz cog update`"),
        "{err}"
    );
}

/// A fetched cog whose package depends on a path outside its tree: built
/// by cargo on every run, never kept by the cog's key, so that an edit of
/// that dependency is seen.
#[test]
fn a_path_dependency_makes_a_fetched_cog_local() {
    let dir = std::env::temp_dir().join(format!("quarz-native-pathdep-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    let helper = dir.join("helper");
    std::fs::create_dir_all(helper.join("src")).unwrap();
    std::fs::write(
        helper.join("Cargo.toml"),
        "[package]\nname = \"helper\"\nversion = \"0.1.0\"\nedition = \"2021\"\n",
    )
    .unwrap();
    std::fs::write(helper.join("src/lib.rs"), "pub fn value() -> i64 { 7 }\n").unwrap();
    raw_cog(
        &dir.join("raw"),
        "helper::value()",
        &format!("helper = {{ path = {:?} }}\n", helper),
    );
    let app = app_on(&dir, "Raw", &dir.join("raw"), "p Raw::Calc.answer\n");
    let envs = own_caches(&dir);
    let (ok, out, err) = quarz(&app, &["run"], &as_refs(&envs));
    assert!(ok, "{err}");
    assert_eq!(out, "7\n");
    std::fs::write(helper.join("src/lib.rs"), "pub fn value() -> i64 { 8 }\n").unwrap();
    let (ok, out, err) = quarz(&app, &["run"], &as_refs(&envs));
    let _ = std::fs::remove_dir_all(&dir);
    assert!(ok, "{err}");
    assert_eq!(out, "8\n");
    assert!(
        err.contains("quarz: building the native code of cog raw (app → raw) with cargo"),
        "{err}"
    );
}

/// A cog's repository without the native package its manifest declares,
/// at the version locked: refused when it is fetched.
#[test]
fn a_fetched_cog_without_its_native_package_is_refused() {
    let dir = std::env::temp_dir().join(format!("quarz-native-nopkg-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    let repo = dir.join("raw");
    std::fs::create_dir_all(repo.join("src")).unwrap();
    std::fs::write(
        repo.join("Cog.toml"),
        "[cog]\nname = \"raw\"\nversion = \"0.1.0\"\n\n[native]\ncrate = \"native\"\n",
    )
    .unwrap();
    std::fs::write(repo.join("src/raw.qz"), "class Calc\nend\n").unwrap();
    commit_tagged(&repo);
    let app = app_on(&dir, "Raw", &repo, "p 1\n");
    let envs = own_caches(&dir);
    let (ok, _, err) = quarz(&app, &["run"], &as_refs(&envs));
    let _ = std::fs::remove_dir_all(&dir);
    assert!(!ok);
    assert!(
        err.contains(
            "declares `[native] crate = \"native\"`, but its repository has no `native/` at "
        ),
        "{err}"
    );
}

/// The proof cog: compression on pure-Rust crates, fetched from a git
/// repository, its package installed with its tree; a round trip and a
/// cog's own exception.
#[test]
fn the_zlib_cog_round_trips() {
    let dir = std::env::temp_dir().join(format!("quarz-native-zlib-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    let repo = dir.join("zlib");
    copy_dir(&fixture_src("zlib"), &repo);
    std::fs::write(
        repo.join("native/Cargo.toml"),
        package_manifest(
            "zlib-native",
            "miniz_oxide = \"=0.8.9\"\ncrc32fast = \"=1.5.0\"\n",
        ),
    )
    .unwrap();
    commit_tagged(&repo);
    let main = "data = \"hello hello hello hello hello hello\".to_bytes\nz = Zlib::Codec.deflate(data)\np z.size < data.size\np Zlib::Codec.inflate(z) == data\np Zlib::Codec.inflate(Zlib::Codec.deflate(data, level: 0)) == data\np Zlib::Codec.crc32(\"hello\".to_bytes)\nbegin\n  Zlib::Codec.inflate(\"not zlib\".to_bytes)\nrescue Zlib::DataError => e\n  p e.message\nend\n";
    let app = app_on(&dir, "Zlib", &repo, main);
    let envs = own_caches(&dir);
    let (ok, out, err) = quarz(&app, &["run"], &as_refs(&envs));
    let _ = std::fs::remove_dir_all(&dir);
    assert!(ok, "{err}");
    assert_eq!(
        out,
        "true\ntrue\ntrue\n907060870\n\"not in the zlib format\"\n"
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

/// A library cog with native code (`[native]`; `check` builds nothing,
/// so its package is a placeholder), a git repository tagged `v0.1.0` in `dir/natlib`, and an
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
    // (A package `check` never builds, installed with the tree.)
    std::fs::create_dir_all(natlib.join("native")).unwrap();
    std::fs::write(
        natlib.join("native/Cargo.toml"),
        "[package]\nname = \"natlib-native\"\nversion = \"0.1.0\"\n",
    )
    .unwrap();
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
