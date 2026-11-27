//! A cog's native package (`[native] crate`, #677): where the library
//! built from it is.

use std::path::{Path, PathBuf};

use crate::Error;

/// The dynamic library cargo builds from the native package in `dir`
/// (`cargo build --release`): `<target>/release/lib<name>.so`, where the
/// target directory is cargo's (`CARGO_TARGET_DIR`, else `dir/target`)
/// and `name` the package's library's (`[lib] name`, else the package's
/// name with `-` as `_`).
pub fn library(dir: &Path) -> Result<PathBuf, Error> {
    let manifest = dir.join("Cargo.toml");
    let text = std::fs::read_to_string(&manifest)
        .map_err(|e| Error::new(format!("{}: {e}", manifest.display())))?;
    let doc: toml::Table =
        toml::from_str(&text).map_err(|e| Error::new(format!("{}: {e}", manifest.display())))?;
    let name = doc
        .get("lib")
        .and_then(|l| l.get("name"))
        .and_then(|n| n.as_str())
        .map(str::to_string)
        .or_else(|| {
            doc.get("package")
                .and_then(|p| p.get("name"))
                .and_then(|n| n.as_str())
                .map(|n| n.replace('-', "_"))
        })
        .ok_or_else(|| Error::new(format!("{}: no package name", manifest.display())))?;
    let target = match std::env::var_os("CARGO_TARGET_DIR") {
        Some(t) if !t.is_empty() => PathBuf::from(t),
        _ => dir.join("target"),
    };
    let file = if cfg!(target_os = "macos") {
        format!("lib{name}.dylib")
    } else {
        format!("lib{name}.so")
    };
    Ok(target.join("release").join(file))
}
