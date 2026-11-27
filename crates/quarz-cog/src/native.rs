//! A cog's native package (`[native] crate`, #677, docs/10): its checks,
//! the toolchain that builds it (the rustc that built `quarz`), the
//! environment cargo runs in, and the build. Where the built library is
//! kept is the caller's (`quarz_cli::native`).

use std::ffi::OsString;
use std::io::{BufRead, Read};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use crate::Error;

/// The rustc that built `quarz` (`build.rs`): its release (`1.100.0`),
/// commit hash and version line (`rustc 1.100.0 (0ef1bc386 2026-11-05)`).
/// Empty when it could not be asked.
pub struct Rustc {
    pub release: &'static str,
    pub commit: &'static str,
    pub line: &'static str,
}

const fn or_empty(s: Option<&'static str>) -> &'static str {
    match s {
        Some(s) => s,
        None => "",
    }
}

pub const QUARZ_RUSTC: Rustc = Rustc {
    release: or_empty(option_env!("QUARZ_RUSTC_RELEASE")),
    commit: or_empty(option_env!("QUARZ_RUSTC_COMMIT")),
    line: or_empty(option_env!("QUARZ_RUSTC_LINE")),
};

/// A native package that passed `check_package`.
pub struct Package {
    /// Its directory (with its `Cargo.toml` and `Cargo.lock`).
    pub dir: PathBuf,
    /// The file cargo makes of its dynamic library (`libzlib_native.so`).
    pub library: String,
    /// The file cargo makes of its static library (`libzlib_native.a`),
    /// beside the dynamic one.
    pub archive: String,
    /// Whether its `Cargo.lock` holds a path package besides itself: one
    /// whose files no hash of the cog's covers, so that a build of it is
    /// never kept by the cog's key (`quarz_cli::native`). (A path package
    /// inside the cog's tree counts too: the rule errs towards building.)
    pub path_dependencies: bool,
}

fn read_toml(path: &Path) -> Result<toml::Table, Error> {
    let text = std::fs::read_to_string(path)
        .map_err(|e| Error::new(format!("{}: {e}", path.display())))?;
    toml::from_str(&text).map_err(|e| Error::new(format!("{}: {}", path.display(), e.message())))
}

/// Check the native package `declared` (as the manifest writes it) at
/// `dir` before cargo runs, each failure naming `who` (``cog `zlib` (app
/// → zlib)``) and the fix: a directory with a `Cargo.toml` that is a
/// workspace of its own (cargo would otherwise look for one above it, in
/// the cog's root or the cache's directories), a library whose crate
/// types include `cdylib` and `staticlib`, and a committed `Cargo.lock`.
pub fn check_package(who: &str, declared: &str, dir: &Path) -> Result<Package, Error> {
    if !dir.is_dir() {
        return Err(Error::new(format!(
            "{who} declares `[native] crate = \"{declared}\"`, but there is no directory {}",
            dir.display()
        )));
    }
    let manifest = dir.join("Cargo.toml");
    if !manifest.is_file() {
        return Err(Error::new(format!(
            "{who}: its native package {} has no Cargo.toml",
            dir.display()
        )));
    }
    // The toolchain is quarz's (#677): rustup's proxies obey such a file
    // in the directory they run in, and would install what it names
    // before the comparison refuses it.
    for file in ["rust-toolchain", "rust-toolchain.toml"] {
        if dir.join(file).exists() {
            return Err(Error::new(format!(
                "{who}: its native package holds {declared}/{file}: it is built by the rustc that built quarz, so it names no toolchain (remove the file)"
            )));
        }
    }
    let doc = read_toml(&manifest)?;
    if !doc.contains_key("workspace") {
        return Err(Error::new(format!(
            "{who}: its native package must be a workspace of its own: add an empty `[workspace]` table to {declared}/Cargo.toml (a workspace or a Cargo.lock in a parent directory is not used)"
        )));
    }
    let lib = doc.get("lib").and_then(|l| l.as_table());
    let types: Vec<String> = lib
        .and_then(|l| l.get("crate-type"))
        .and_then(|t| t.as_array())
        .map(|a| {
            a.iter()
                .filter_map(|v| v.as_str().map(str::to_string))
                .collect()
        })
        .unwrap_or_default();
    if !types.iter().any(|t| t == "cdylib") || !types.iter().any(|t| t == "staticlib") {
        let shown: Vec<String> = types.iter().map(|t| format!("\"{t}\"")).collect();
        return Err(Error::new(format!(
            "{who}: its native package's `[lib] crate-type` must include \"cdylib\" and \"staticlib\" (it is [{}])",
            shown.join(", ")
        )));
    }
    let package = doc
        .get("package")
        .and_then(|p| p.get("name"))
        .and_then(|n| n.as_str())
        .ok_or_else(|| Error::new(format!("{}: no `[package] name`", manifest.display())))?
        .to_string();
    let name = lib
        .and_then(|l| l.get("name"))
        .and_then(|n| n.as_str())
        .map(str::to_string)
        .unwrap_or_else(|| package.replace('-', "_"));
    let lock = dir.join("Cargo.lock");
    if !lock.is_file() {
        return Err(Error::new(format!(
            "{who}: its native package in {} has no Cargo.lock, which must be committed (built with `--locked`)",
            dir.display()
        )));
    }
    let path_dependencies = read_toml(&lock)?
        .get("package")
        .and_then(|p| p.as_array())
        .is_some_and(|ps| {
            ps.iter().any(|p| {
                // (A path package has no `source`: a registry's carries
                // its checksum, a git one its commit.)
                p.get("source").is_none()
                    && p.get("name").and_then(|n| n.as_str()) != Some(package.as_str())
            })
        });
    let library = if cfg!(target_os = "macos") {
        format!("lib{name}.dylib")
    } else {
        format!("lib{name}.so")
    };
    Ok(Package {
        dir: dir.to_path_buf(),
        library,
        archive: format!("lib{name}.a"),
        path_dependencies,
    })
}

/// How cargo is run: as found (`$CARGO`, else `cargo` on `PATH`), given
/// the rustc compared as its `RUSTC`, so that it builds with that one by
/// construction; or through rustup with the toolchain of `QUARZ_RUSTC`'s
/// release.
pub enum Cargo {
    Found(OsString),
    Rustup(String),
}

/// The `rustc -vV` of `cmd` run in `dir` (a `rust-toolchain` file there
/// counts, as it does for cargo): its version line and commit hash, or
/// `None` when it does not run.
fn version_of(mut cmd: Command, dir: &Path) -> Option<(String, String)> {
    let out = cmd.current_dir(dir).output().ok()?;
    if !out.status.success() {
        return None;
    }
    let text = String::from_utf8_lossy(&out.stdout).into_owned();
    let line = text.lines().next()?.trim().to_string();
    let commit = text
        .lines()
        .find_map(|l| l.strip_prefix("commit-hash:"))?
        .trim()
        .to_string();
    Some((line, commit))
}

fn runs(program: &OsString) -> bool {
    Command::new(program)
        .arg("--version")
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status()
        .is_ok()
}

fn cargo_program() -> OsString {
    std::env::var_os("CARGO").unwrap_or_else(|| OsString::from("cargo"))
}

/// The cargo that builds `who`'s package in `dir` with the rustc that
/// built `quarz` (decided on #677, for every command): the `cargo` found
/// when its rustc (`$RUSTC`, else `rustc`) has that commit, else rustup's
/// toolchain of that release; else an error saying what to install.
pub fn toolchain(who: &str, dir: &Path) -> Result<Cargo, Error> {
    let want = &QUARZ_RUSTC;
    let release = want.release;
    let rustc = std::env::var_os("RUSTC").unwrap_or_else(|| OsString::from("rustc"));
    let mut cmd = Command::new(&rustc);
    cmd.arg("-vV");
    let here = version_of(cmd, dir);
    if let Some((_, commit)) = &here {
        if !want.commit.is_empty() && *commit == want.commit {
            return Ok(Cargo::Found(rustc));
        }
    }
    let rustup = runs(&OsString::from("rustup"));
    if rustup && !release.is_empty() && !release.contains('-') {
        let mut cmd = Command::new("rustup");
        cmd.args(["run", release, "rustc", "-vV"]);
        match version_of(cmd, dir) {
            Some((_, commit)) if commit == want.commit => {
                return Ok(Cargo::Rustup(release.to_string()))
            }
            Some(_) => {}
            None => {
                return Err(Error::new(format!(
                    "{who} brings native code, which must be built by {}, the version this quarz was built with, but that toolchain is not installed: run `rustup toolchain install {release}`",
                    want.line
                )))
            }
        }
    }
    match here {
        None if !rustup && !runs(&cargo_program()) => Err(Error::new(format!(
            "{who} brings native code, built with cargo, but no `cargo` was found: install Rust {release}, the version this quarz was built with (https://rustup.rs)"
        ))),
        None => Err(Error::new(format!(
            "{who} brings native code, which must be built by {}, the version this quarz was built with, but `{}` does not run",
            want.line,
            rustc.to_string_lossy()
        ))),
        Some((line, _)) => {
            let fix = if release.contains('-') {
                "put that rustc and its cargo first on PATH".to_string()
            } else {
                format!("put rustc {release} and its cargo first on PATH, or install rustup")
            };
            Err(Error::new(format!(
                "{who} brings native code, which must be built by {}, the version this quarz was built with, but `{}` is {line}: {fix}",
                want.line,
                rustc.to_string_lossy()
            )))
        }
    }
}

/// The variables cleared for cargo: the flags that would reach rustc
/// (`CARGO_ENCODED_RUSTFLAGS` is then set empty, which also overrides
/// every configuration file's `rustflags`), wrappers, a target or a
/// target directory of the user's, and what cargo sets for a package it
/// builds or tests (a `quarz` run from a build script or a test).
const CLEARED: &[&str] = &[
    "RUSTFLAGS",
    "RUSTDOCFLAGS",
    "CARGO_ENCODED_RUSTDOCFLAGS",
    "CARGO_BUILD_RUSTFLAGS",
    "CARGO_BUILD_RUSTDOCFLAGS",
    "RUSTC_WRAPPER",
    "RUSTC_WORKSPACE_WRAPPER",
    "CARGO_BUILD_RUSTC_WRAPPER",
    "CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER",
    "CARGO_INCREMENTAL",
    "CARGO_BUILD_INCREMENTAL",
    "CARGO_BUILD_TARGET",
    "CARGO_BUILD_TARGET_DIR",
    "CARGO_BUILD_BUILD_DIR",
    "CARGO_CRATE_NAME",
    "CARGO_PRIMARY_PACKAGE",
    "CARGO_TARGET_TMPDIR",
    "OUT_DIR",
];
const CLEARED_PREFIXES: &[&str] = &["CARGO_PKG_", "CARGO_MANIFEST_", "CARGO_BIN_"];

fn cleared(name: &str) -> bool {
    CLEARED.contains(&name) || CLEARED_PREFIXES.iter().any(|p| name.starts_with(p))
}

/// What of the environment changes a native build besides the package's
/// files, its toolchain and what `build` sets: every variable named
/// `CARGO_PROFILE_*`, `CARGO_BUILD_*` or `CARGO_TARGET_*` that `build`
/// neither clears nor sets (name and value), and the bytes of every
/// configuration file cargo reads for `dir` (`.cargo/config.toml` and
/// `.cargo/config` in `dir` and each directory above it, and
/// `config.toml` and `config` in `$CARGO_HOME`). Part of a kept build's
/// key, so that a profile or a linker of the user's never serves a build
/// made without it.
///
/// Approximations, each erring towards a stale build (`QUARZ_NO_CACHE=1`
/// rebuilds):
/// - a configuration file's (unstable) `include` is not followed, so a
///   change in an included file keeps the key (#1204);
/// - what a build script reads is not in the key: the variables it
///   likes (`CC`, `CFLAGS`, `PKG_CONFIG_PATH`, any other), files outside
///   the package, the system's libraries. A kept library can be stale
///   against those; making the key cover them would mean knowing what
///   each build script reads, which nothing declares.
pub fn environment(dir: &Path) -> String {
    let mut vars: Vec<(String, String)> = std::env::vars_os()
        .filter_map(|(k, v)| Some((k.into_string().ok()?, v.to_string_lossy().into_owned())))
        .filter(|(k, _)| {
            (k.starts_with("CARGO_PROFILE_")
                || k.starts_with("CARGO_BUILD_")
                || k.starts_with("CARGO_TARGET_"))
                && !cleared(k)
                && k != "CARGO_TARGET_DIR"
                && k != "CARGO_PROFILE_RELEASE_PANIC"
        })
        .collect();
    vars.sort();
    let mut out = String::new();
    for (k, v) in vars {
        out.push_str(&format!("{}:{k}={}:{v}\n", k.len(), v.len()));
    }
    let mut files: Vec<PathBuf> = Vec::new();
    for d in dir.ancestors() {
        files.push(d.join(".cargo").join("config.toml"));
        files.push(d.join(".cargo").join("config"));
    }
    let home = std::env::var_os("CARGO_HOME")
        .filter(|h| !h.is_empty())
        .map(PathBuf::from)
        .or_else(|| std::env::var_os("HOME").map(|h| PathBuf::from(h).join(".cargo")));
    if let Some(h) = home {
        files.push(h.join("config.toml"));
        files.push(h.join("config"));
    }
    for p in files {
        if let Ok(bytes) = std::fs::read(&p) {
            let name = p.display().to_string();
            out.push_str(&format!("{}:{name}\n{}:", name.len(), bytes.len()));
            out.push_str(&String::from_utf8_lossy(&bytes));
            out.push('\n');
        }
    }
    out
}

/// Build `who`'s `package` with `cargo` into `target` (`cargo build
/// --release --locked --lib`, `--offline` when `offline`) in the
/// environment `environment` describes, the flags cleared and the panic
/// strategy unwinding. cargo's output is kept, and shown only when it
/// fails; `rebuilding` runs once, when cargo reports the first unit it
/// compiles (not one it finds fresh). The library built, in `target`.
pub fn build(
    who: &str,
    package: &Package,
    cargo: &Cargo,
    target: &Path,
    offline: bool,
    rebuilding: &mut dyn FnMut(),
) -> Result<PathBuf, Error> {
    let mut cmd = match cargo {
        Cargo::Found(rustc) => {
            let mut c = Command::new(cargo_program());
            c.env("RUSTC", rustc);
            c
        }
        Cargo::Rustup(toolchain) => {
            let mut c = Command::new("rustup");
            c.args(["run", toolchain, "cargo"]);
            c
        }
    };
    cmd.args([
        "build",
        "--release",
        "--locked",
        "--lib",
        "--message-format=json-render-diagnostics",
    ]);
    if offline {
        cmd.arg("--offline");
    }
    for (k, _) in std::env::vars_os() {
        if let Some(k) = k.to_str() {
            if cleared(k) {
                cmd.env_remove(k);
            }
        }
    }
    cmd.env("CARGO_ENCODED_RUSTFLAGS", "")
        .env("CARGO_PROFILE_RELEASE_PANIC", "unwind")
        .env("CARGO_TARGET_DIR", target)
        .current_dir(&package.dir)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    let mut child = match cmd.spawn() {
        Ok(c) => c,
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
            return Err(Error::new(format!(
                "{who} brings native code, built with cargo, but no `cargo` was found: install Rust {}, the version this quarz was built with (https://rustup.rs)",
                QUARZ_RUSTC.release
            )))
        }
        Err(e) => return Err(Error::new(format!("{who}: cannot run cargo: {e}"))),
    };
    // (stderr is read aside, so that neither pipe fills while the other
    // is read.)
    let mut stderr = child.stderr.take().expect("piped");
    let errors = std::thread::spawn(move || {
        let mut text = Vec::new();
        let _ = stderr.read_to_end(&mut text);
        text
    });
    let mut told = false;
    if let Some(out) = child.stdout.take() {
        for line in std::io::BufReader::new(out).lines().map_while(Result::ok) {
            if !told
                && line.contains("\"reason\":\"compiler-artifact\"")
                && line.contains("\"fresh\":false")
            {
                told = true;
                rebuilding();
            }
        }
    }
    let status = child
        .wait()
        .map_err(|e| Error::new(format!("{who}: cargo: {e}")))?;
    let errors = errors.join().unwrap_or_default();
    if !status.success() {
        eprint!("{}", String::from_utf8_lossy(&errors));
        return Err(Error::new(format!(
            "{who}: `cargo build --release --locked` failed in {}{}",
            package.dir.display(),
            if offline {
                " (offline: its crates must be in cargo's cache already)"
            } else {
                ""
            }
        )));
    }
    let library = target.join("release").join(&package.library);
    if !library.is_file() {
        return Err(Error::new(format!(
            "{who}: cargo built no {} in {}",
            package.library,
            target.join("release").display()
        )));
    }
    Ok(library)
}
