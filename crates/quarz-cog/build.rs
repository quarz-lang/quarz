//! Record the commit `quarz` is built from (`QUARZ_GIT_SHA`, read by
//! `quarz_cog::GIT_SHA`): `quarz --version` shows it, and `quarz doc` links
//! the standard library's declarations to their source at it. Built from a
//! tree with no `.git` (a tarball), nothing is recorded. (Here, not in
//! quarz-cli's build script, whose rerun would change the checker's build
//! id, and so empty the checker's cache, at every commit.)

use std::path::PathBuf;
use std::process::Command;

fn git(args: &[&str]) -> Option<String> {
    let dir = std::env::var("CARGO_MANIFEST_DIR").ok()?;
    let out = Command::new("git")
        .args(args)
        .current_dir(dir)
        .output()
        .ok()?;
    if !out.status.success() {
        return None;
    }
    let s = String::from_utf8(out.stdout).ok()?.trim().to_string();
    (!s.is_empty()).then_some(s)
}

fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    // Only in quarz's own repository (not a copy unpacked inside another).
    let dir = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap_or_default());
    let workspace = std::fs::canonicalize(dir.join("../..")).ok();
    let top = git(&["rev-parse", "--show-toplevel"]).and_then(|t| std::fs::canonicalize(t).ok());
    if workspace.is_none() || top != workspace {
        return;
    }
    // Again when HEAD moves: HEAD itself (another branch), its reflog (a
    // commit), the ref it names, the packed refs and a reftable's list;
    // only those that exist (Cargo takes a missing one as always changed).
    let mut watched = vec![
        "HEAD".to_string(),
        "logs/HEAD".to_string(),
        "packed-refs".to_string(),
        // (A reftable repository keeps its refs in `reftable/`.)
        "reftable/tables.list".to_string(),
    ];
    if let Some(r) = git(&["symbolic-ref", "-q", "HEAD"]) {
        watched.push(r);
    }
    for path in watched {
        if let Some(p) = git(&["rev-parse", "--git-path", &path]) {
            let p = absolute(&p);
            if p.exists() {
                println!("cargo:rerun-if-changed={}", p.display());
            }
        }
    }
    if let Some(sha) = git(&["rev-parse", "HEAD"]) {
        if sha.len() == 40 && sha.chars().all(|c| c.is_ascii_hexdigit()) {
            println!("cargo:rustc-env=QUARZ_GIT_SHA={sha}");
        }
    }
}

/// A path git gave, relative to the crate's directory.
fn absolute(p: &str) -> PathBuf {
    let p = PathBuf::from(p);
    if p.is_absolute() {
        p
    } else {
        PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap_or_default()).join(p)
    }
}
