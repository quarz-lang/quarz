//! The content hash of a cog: what the lock file verifies a fetched tree
//! against.

use std::path::{Path, PathBuf};

use sha2::{Digest, Sha256};

use crate::manifest::MANIFEST;

/// `h1:` and the base64 of a SHA-256 over one line per file of the cog
/// (`Cog.toml` and everything under `src/`), in path order: the file's
/// SHA-256 in hex, two spaces and its path (as Go's module hashes). The
/// tree must pass `check_tree`, so that no two trees share their lines.
pub fn tree_hash(dir: &Path) -> std::io::Result<String> {
    let mut files = Vec::new();
    let manifest = dir.join(MANIFEST);
    match std::fs::symlink_metadata(&manifest) {
        Ok(m) if m.file_type().is_file() => files.push(PathBuf::from(MANIFEST)),
        Ok(_) => return Err(bad(format!("{} is not a regular file", manifest.display()))),
        Err(_) => {}
    }
    let src = dir.join("src");
    match std::fs::symlink_metadata(&src) {
        Ok(m) if m.file_type().is_dir() => collect(dir, &src, &mut files)?,
        Ok(_) => return Err(bad(format!("{} is not a directory", src.display()))),
        Err(_) => {}
    }
    files.sort();
    let mut summary = String::new();
    for rel in &files {
        let bytes = std::fs::read(dir.join(rel))?;
        let digest = Sha256::digest(&bytes);
        summary.push_str(&hex(&digest));
        summary.push_str("  ");
        summary.push_str(&checked_name(rel)?);
        summary.push('\n');
    }
    Ok(digest(summary.as_bytes()))
}

/// Refuse what a cog's tree may not hold: a symbolic link (its target is
/// outside what the lock verifies, and may be anywhere on the machine),
/// anything that is neither a file nor a directory, and a name that is
/// not UTF-8 or holds a control character (a newline in a name would let
/// two different trees hash alike).
pub fn check_tree(dir: &Path) -> std::io::Result<()> {
    fn walk(base: &Path, dir: &Path) -> std::io::Result<()> {
        for entry in std::fs::read_dir(dir)? {
            let entry = entry?;
            let path = entry.path();
            let rel = path.strip_prefix(base).unwrap();
            checked_name(rel)?;
            let ft = entry.file_type()?;
            if ft.is_symlink() {
                return Err(bad(format!("`{}` is a symbolic link", rel.display())));
            } else if ft.is_dir() {
                walk(base, &path)?;
            } else if !ft.is_file() {
                return Err(bad(format!("`{}` is not a regular file", rel.display())));
            }
        }
        Ok(())
    }
    walk(dir, dir)
}

/// A relative path as the hash writes it, `/`-separated; an error for a
/// name that is not UTF-8 or holds a control character.
fn checked_name(rel: &Path) -> std::io::Result<String> {
    let mut parts = Vec::new();
    for c in rel.components() {
        let name = c.as_os_str().to_str().ok_or_else(|| {
            bad(format!(
                "`{}`: a file name that is not UTF-8",
                rel.display()
            ))
        })?;
        if name.chars().any(char::is_control) {
            return Err(bad(format!(
                "{name:?}: a file name with a control character"
            )));
        }
        parts.push(name);
    }
    Ok(parts.join("/"))
}

fn bad(message: String) -> std::io::Error {
    std::io::Error::new(std::io::ErrorKind::InvalidData, message)
}

/// `h1:` and the base64 of the SHA-256 of `bytes`.
pub fn digest(bytes: &[u8]) -> String {
    format!("h1:{}", base64(&Sha256::digest(bytes)))
}

/// The files under `dir`, never following a symbolic link.
fn collect(base: &Path, dir: &Path, out: &mut Vec<PathBuf>) -> std::io::Result<()> {
    for entry in std::fs::read_dir(dir)? {
        let entry = entry?;
        let path = entry.path();
        let rel = path.strip_prefix(base).unwrap().to_path_buf();
        let ft = entry.file_type()?;
        if ft.is_symlink() {
            return Err(bad(format!("`{}` is a symbolic link", rel.display())));
        } else if ft.is_dir() {
            collect(base, &path, out)?;
        } else if ft.is_file() {
            out.push(rel);
        } else {
            return Err(bad(format!("`{}` is not a regular file", rel.display())));
        }
    }
    Ok(())
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn base64(bytes: &[u8]) -> String {
    const TABLE: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
    let mut out = String::new();
    for chunk in bytes.chunks(3) {
        let b = [
            chunk[0],
            *chunk.get(1).unwrap_or(&0),
            *chunk.get(2).unwrap_or(&0),
        ];
        let n = (u32::from(b[0]) << 16) | (u32::from(b[1]) << 8) | u32::from(b[2]);
        for i in 0..4 {
            if i <= chunk.len() {
                out.push(TABLE[(n >> (18 - 6 * i) & 63) as usize] as char);
            } else {
                out.push('=');
            }
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn scratch(name: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!("quarz-hash-{}-{name}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(dir.join("src")).unwrap();
        std::fs::write(dir.join(MANIFEST), "[cog]\nname = \"x\"\n").unwrap();
        dir
    }

    #[test]
    fn names_that_could_collide_are_refused() {
        // Two files a.qz and b.qz against one file whose name spells out
        // b.qz's line: the summaries would be the same text.
        let dir = scratch("newline");
        std::fs::write(dir.join("src").join("a.qz\n0000  b.qz"), "X").unwrap();
        assert!(tree_hash(&dir)
            .unwrap_err()
            .to_string()
            .contains("control character"));
        assert!(check_tree(&dir).is_err());
        std::fs::remove_dir_all(&dir).unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn symbolic_links_are_refused_not_followed() {
        let dir = scratch("link");
        std::os::unix::fs::symlink("/etc/hostname", dir.join("src/leak.txt")).unwrap();
        assert!(tree_hash(&dir)
            .unwrap_err()
            .to_string()
            .contains("symbolic link"));
        assert!(check_tree(&dir).is_err());
        std::fs::remove_file(dir.join("src/leak.txt")).unwrap();
        // A loop is not walked either.
        std::os::unix::fs::symlink("..", dir.join("src/up")).unwrap();
        assert!(tree_hash(&dir).is_err());
        std::fs::remove_dir_all(&dir).unwrap();
    }

    #[test]
    fn base64_encodes() {
        assert_eq!(base64(b""), "");
        assert_eq!(base64(b"f"), "Zg==");
        assert_eq!(base64(b"fo"), "Zm8=");
        assert_eq!(base64(b"foo"), "Zm9v");
        assert_eq!(base64(b"foobar"), "Zm9vYmFy");
    }
}
