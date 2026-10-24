//! The content hash of a cog: what the lock file verifies a fetched tree
//! against.

use std::path::{Path, PathBuf};

use sha2::{Digest, Sha256};

use crate::manifest::MANIFEST;

/// `h1:` and the base64 of a SHA-256 over one line per file of the cog
/// (`Cog.toml` and everything under `src/`), in path order: the file's
/// SHA-256 in hex, two spaces and its path (as Go's module hashes).
pub fn tree_hash(dir: &Path) -> std::io::Result<String> {
    let mut files = Vec::new();
    if dir.join(MANIFEST).is_file() {
        files.push(PathBuf::from(MANIFEST));
    }
    let src = dir.join("src");
    if src.is_dir() {
        collect(dir, &src, &mut files)?;
    }
    files.sort();
    let mut summary = String::new();
    for rel in &files {
        let bytes = std::fs::read(dir.join(rel))?;
        let digest = Sha256::digest(&bytes);
        let path: Vec<String> = rel
            .components()
            .map(|c| c.as_os_str().to_string_lossy().into_owned())
            .collect();
        summary.push_str(&hex(&digest));
        summary.push_str("  ");
        summary.push_str(&path.join("/"));
        summary.push('\n');
    }
    Ok(format!(
        "h1:{}",
        base64(&Sha256::digest(summary.as_bytes()))
    ))
}

/// `h1:` and the base64 of the SHA-256 of `bytes`.
pub fn digest(bytes: &[u8]) -> String {
    format!("h1:{}", base64(&Sha256::digest(bytes)))
}

fn collect(base: &Path, dir: &Path, out: &mut Vec<PathBuf>) -> std::io::Result<()> {
    for entry in std::fs::read_dir(dir)? {
        let path = entry?.path();
        if path.is_dir() {
            collect(base, &path, out)?;
        } else {
            out.push(path.strip_prefix(base).unwrap().to_path_buf());
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

    #[test]
    fn base64_encodes() {
        assert_eq!(base64(b""), "");
        assert_eq!(base64(b"f"), "Zg==");
        assert_eq!(base64(b"fo"), "Zm8=");
        assert_eq!(base64(b"foo"), "Zm9v");
        assert_eq!(base64(b"foobar"), "Zm9vYmFy");
    }
}
