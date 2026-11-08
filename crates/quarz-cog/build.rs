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
    // Again when HEAD moves: HEAD itself (another branch), the ref it
    // names (a commit) and the packed refs.
    for path in ["HEAD", "packed-refs"] {
        if let Some(p) = git(&["rev-parse", "--git-path", path]) {
            println!("cargo:rerun-if-changed={}", absolute(&p).display());
        }
    }
    if let Some(r) = git(&["symbolic-ref", "-q", "HEAD"]) {
        if let Some(p) = git(&["rev-parse", "--git-path", &r]) {
            println!("cargo:rerun-if-changed={}", absolute(&p).display());
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
