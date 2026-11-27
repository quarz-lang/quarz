//! The cache of the objects clang makes from a build's partitions
//! (#1182): an object is a function of the partition's text, the clang
//! that compiles it and its flags, so a partition whose text a build
//! made before is not compiled again.
//!
//! Entries are `<dir>/<2 hex>/<key>.o`, with `<key>.sum` holding the
//! object's SHA-256: the key is the SHA-256 of `KEY_VERSION`, clang's
//! identity (`clang_identity`), the flags and the partition's text, all
//! made by the build; no part of a key or a file name comes from outside
//! it. `dir` is `objects/` in the cache directory the checker uses
//! (`quarz_types::cache::dir`: `QUARZ_CACHE_DIR`, else `quarz` in
//! `$XDG_CACHE_HOME` or `~/.cache`; `QUARZ_NO_CACHE=1` turns both off).
//!
//! What protects it: the directory is the user's, as the checker's
//! cache is. The checksum guards against damage (a truncated or altered
//! file is a miss, compiled again and replaced), not against someone who
//! can write there: such a writer could replace an object and its sum
//! together, and that object would be linked into the programs built.
//!
//! Entries are written aside and renamed, so a reader never sees half of
//! one; two builds compiling one partition write the same bytes, and the
//! last rename wins. A hit touches the object (its time is its last use);
//! once a day a store sweeps: entries unused for `UNUSED` are removed,
//! then the least recently used until the objects take at most `BOUND`.

use std::path::{Path, PathBuf};
use std::time::{Duration, SystemTime};

use sha2::{Digest, Sha256};

/// Changed when what an object depends on beyond its key's inputs
/// changes: a new value makes every older entry a miss.
const KEY_VERSION: &str = "quarz-obj-1";

/// Entries unused for this long are removed.
const UNUSED: Duration = Duration::from_secs(30 * 24 * 60 * 60);

/// The objects' bound, in bytes: past it, the least recently used go.
const BOUND: u64 = 2 * 1024 * 1024 * 1024;

/// How often a store sweeps, at most.
const SWEEP_EVERY: Duration = Duration::from_secs(24 * 60 * 60);

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// The key of a partition's object: the SHA-256 of `KEY_VERSION`,
/// clang's identity, the flags and the text, each after its length (so
/// that no two lists of parts hash the same text), in hexadecimal (64
/// digits).
pub fn key(identity: &str, flags: &str, text: &str) -> String {
    let mut h = Sha256::new();
    for part in [KEY_VERSION, identity, flags, text] {
        h.update((part.len() as u64).to_le_bytes());
        h.update(part.as_bytes());
    }
    hex(&h.finalize())
}

/// What tells one clang from another: the file it runs from (its
/// resolved path, size and modification time, which a new install
/// changes) and what it says of itself (`clang --version`: the version,
/// the distribution's build, the target and where it is installed).
pub fn clang_identity(clang: &str, version: &str) -> String {
    let file = if clang.contains('/') {
        Some(PathBuf::from(clang))
    } else {
        std::env::var_os("PATH").and_then(|p| {
            std::env::split_paths(&p)
                .map(|d| d.join(clang))
                .find(|f| f.is_file())
        })
    };
    let file = file.and_then(|f| std::fs::canonicalize(f).ok());
    let stamp = file
        .as_ref()
        .and_then(|f| std::fs::metadata(f).ok())
        .map(|m| {
            let t = m
                .modified()
                .ok()
                .and_then(|t| t.duration_since(SystemTime::UNIX_EPOCH).ok())
                .map_or(0, |d| d.as_nanos());
            format!("{} {t}", m.len())
        })
        .unwrap_or_default();
    format!(
        "{}\n{stamp}\n{version}",
        file.map(|f| f.display().to_string()).unwrap_or_default()
    )
}

/// The objects' cache in `dir`.
pub struct Cache {
    dir: PathBuf,
}

impl Cache {
    pub fn new(dir: &Path) -> Cache {
        Cache {
            dir: dir.to_path_buf(),
        }
    }

    fn entry(&self, key: &str) -> PathBuf {
        self.dir.join(&key[..2]).join(format!("{key}.o"))
    }

    /// The object of `key`, when the cache holds it whole (its sum is
    /// the SHA-256 of its bytes); its time is set to now.
    pub fn fetch(&self, key: &str) -> Option<Vec<u8>> {
        let path = self.entry(key);
        let bytes = std::fs::read(&path).ok()?;
        let sum = std::fs::read_to_string(path.with_extension("sum")).ok()?;
        if sum.trim() != hex(&Sha256::digest(&bytes)) {
            return None;
        }
        if let Ok(f) = std::fs::File::options().append(true).open(&path) {
            let _ = f.set_modified(SystemTime::now());
        }
        Some(bytes)
    }

    /// Keep `bytes` as the object of `key` (written aside and renamed,
    /// the object first: an object without its sum is a miss).
    pub fn store(&self, key: &str, bytes: &[u8]) {
        let path = self.entry(key);
        let Some(shard) = path.parent() else { return };
        if std::fs::create_dir_all(shard).is_err() {
            return;
        }
        let aside = |p: &Path| p.with_extension(format!("tmp{}", std::process::id()));
        let put = |p: &Path, data: &[u8]| {
            let tmp = aside(p);
            if std::fs::write(&tmp, data).is_err() || std::fs::rename(&tmp, p).is_err() {
                let _ = std::fs::remove_file(&tmp);
                return false;
            }
            true
        };
        if put(&path, bytes) {
            put(
                &path.with_extension("sum"),
                hex(&Sha256::digest(bytes)).as_bytes(),
            );
        }
    }

    /// At most once a day (the time of `swept` says when it last ran):
    /// the entries unused for `UNUSED` and files left half written are
    /// removed, then the least recently used entries until the objects
    /// take at most `bound` bytes.
    pub fn sweep(&self, bound: u64) {
        let now = SystemTime::now();
        let age = |m: &std::fs::Metadata| {
            m.modified()
                .ok()
                .and_then(|t| now.duration_since(t).ok())
                .unwrap_or_default()
        };
        let mark = self.dir.join("swept");
        match std::fs::metadata(&mark) {
            Ok(m) if age(&m) < SWEEP_EVERY => return,
            Ok(_) => {}
            Err(_) => {
                // (A new cache: nothing to remove yet.)
                let _ = std::fs::create_dir_all(&self.dir);
                let _ = std::fs::write(&mark, "");
                return;
            }
        }
        let _ = std::fs::write(&mark, "");
        self.sweep_now(bound);
    }

    /// `sweep`'s removals, whenever it last ran.
    pub fn sweep_now(&self, bound: u64) {
        let now = SystemTime::now();
        let age = |m: &std::fs::Metadata| {
            m.modified()
                .ok()
                .and_then(|t| now.duration_since(t).ok())
                .unwrap_or_default()
        };
        // The objects, with their time and size (and their sum's).
        let mut kept: Vec<(SystemTime, u64, PathBuf)> = Vec::new();
        let Ok(shards) = std::fs::read_dir(&self.dir) else {
            return;
        };
        for shard in shards.flatten() {
            let Ok(files) = std::fs::read_dir(shard.path()) else {
                continue;
            };
            for f in files.flatten() {
                let p = f.path();
                let Ok(m) = f.metadata() else { continue };
                let ext = p.extension().and_then(|e| e.to_str()).unwrap_or("");
                if ext.starts_with("tmp") {
                    if age(&m) > SWEEP_EVERY {
                        let _ = std::fs::remove_file(&p);
                    }
                    continue;
                }
                if ext != "o" {
                    continue;
                }
                if age(&m) > UNUSED {
                    let _ = std::fs::remove_file(&p);
                    let _ = std::fs::remove_file(p.with_extension("sum"));
                    continue;
                }
                let sum = std::fs::metadata(p.with_extension("sum")).map_or(0, |s| s.len());
                kept.push((m.modified().unwrap_or(now), m.len() + sum, p));
            }
        }
        let mut total: u64 = kept.iter().map(|(_, n, _)| n).sum();
        kept.sort();
        for (_, n, p) in kept {
            if total <= bound {
                break;
            }
            let _ = std::fs::remove_file(&p);
            let _ = std::fs::remove_file(p.with_extension("sum"));
            total -= n;
        }
    }
}

/// The objects' bound: `BOUND`, or `QUARZ_OBJECT_CACHE_BOUND` bytes (for
/// tests).
pub fn bound() -> u64 {
    std::env::var("QUARZ_OBJECT_CACHE_BOUND")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(BOUND)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn dir(name: &str) -> PathBuf {
        let d = std::env::temp_dir().join(format!("quarz-objcache-{name}-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&d);
        std::fs::create_dir_all(&d).unwrap();
        d
    }

    fn key_of(n: u8) -> String {
        key("clang", "-O0", &format!("text {n}"))
    }

    /// Set `key`'s object's time `ago` in the past.
    fn age(c: &Cache, key: &str, ago: Duration) {
        let f = std::fs::File::options()
            .append(true)
            .open(c.entry(key))
            .unwrap();
        f.set_modified(SystemTime::now() - ago).unwrap();
    }

    #[test]
    fn a_stored_object_is_fetched_and_a_damaged_one_is_not() {
        let d = dir("fetch");
        let c = Cache::new(&d);
        let k = key_of(1);
        assert_eq!(c.fetch(&k), None);
        c.store(&k, b"object");
        assert_eq!(c.fetch(&k).as_deref(), Some(&b"object"[..]));
        std::fs::write(c.entry(&k), b"objecT").unwrap();
        assert_eq!(c.fetch(&k), None);
        // (An object without its sum.)
        c.store(&k, b"object");
        std::fs::remove_file(c.entry(&k).with_extension("sum")).unwrap();
        assert_eq!(c.fetch(&k), None);
        let _ = std::fs::remove_dir_all(&d);
    }

    #[test]
    fn a_key_takes_every_input() {
        let k = key("a", "b", "c");
        assert_eq!(k.len(), 64);
        assert_ne!(k, key("a2", "b", "c"));
        assert_ne!(k, key("a", "b2", "c"));
        assert_ne!(k, key("a", "b", "c2"));
        // (The parts do not run into each other.)
        assert_ne!(key("a\nb", "c", "d"), key("a", "b\nc", "d"));
    }

    #[test]
    fn the_sweep_removes_the_unused_and_the_least_recently_used_past_the_bound() {
        let d = dir("sweep");
        let c = Cache::new(&d);
        for n in 0..4 {
            c.store(&key_of(n), &[n; 1000]);
        }
        // Unused for longer than `UNUSED`: removed whatever the bound.
        age(&c, &key_of(0), UNUSED + Duration::from_secs(60));
        // The least recently used of the others: 1, then 2.
        age(&c, &key_of(1), Duration::from_secs(300));
        age(&c, &key_of(2), Duration::from_secs(200));
        // A file left half written a day ago.
        let tmp = c.entry(&key_of(3)).with_extension("tmp1");
        std::fs::write(&tmp, b"half").unwrap();
        std::fs::File::options()
            .append(true)
            .open(&tmp)
            .unwrap()
            .set_modified(SystemTime::now() - SWEEP_EVERY - Duration::from_secs(60))
            .unwrap();
        // Room for two entries (an object and its 64-byte sum each).
        c.sweep_now(2 * 1064);
        let held: Vec<bool> = (0..4).map(|n| c.fetch(&key_of(n)).is_some()).collect();
        assert_eq!(held, [false, false, true, true]);
        assert!(!tmp.exists());
        assert!(!c.entry(&key_of(0)).with_extension("sum").exists());
        let _ = std::fs::remove_dir_all(&d);
    }

    #[test]
    fn the_sweep_runs_at_most_once_a_day() {
        let d = dir("daily");
        let c = Cache::new(&d);
        c.store(&key_of(0), b"x");
        age(&c, &key_of(0), UNUSED + Duration::from_secs(60));
        // The first sweep of a cache only marks it; the next, within a day,
        // does nothing.
        c.sweep(0);
        c.sweep(0);
        assert!(c.entry(&key_of(0)).exists());
        // A day later it runs.
        std::fs::File::options()
            .append(true)
            .open(d.join("swept"))
            .unwrap()
            .set_modified(SystemTime::now() - SWEEP_EVERY - Duration::from_secs(60))
            .unwrap();
        c.sweep(u64::MAX);
        assert!(!c.entry(&key_of(0)).exists());
        let _ = std::fs::remove_dir_all(&d);
    }
}
