//! The native code of a movement's cogs (#677, docs/10): built with
//! cargo by the rustc that built `quarz` (`quarz_cog::native`), kept,
//! and loaded into the interpreter (`quarz_vm::native_ext`).
//!
//! Where builds are kept, under the cache directory the checker uses
//! (`quarz_types::cache::dir`), in `native/`:
//! - `lib/` and `archive/`: the dynamic libraries and the archives, by
//!   key, with the object cache's rules
//!   (`quarz_aot::objcache`: written aside and renamed, checked by their
//!   sum, touched on use, swept by age and size). A library is only ever
//!   loaded from there, never from a target directory, which a concurrent
//!   cargo may rewrite under a loaded library.
//! - A cog the lock pins (fetched, or in `vendor/`), whose package has no
//!   path dependency, is keyed by the lock's hash of its tree, the rustc,
//!   the ABI's major version and the environment
//!   (`quarz_cog::native::environment`): a hit runs no cargo. A miss
//!   builds in a temporary target directory, removed once the library is
//!   kept.
//! - Any other cog (the application's own package, a `[patch]`, a package
//!   with a path dependency) is built by cargo on every run, which judges
//!   what changed, in `target/<cog>` (its use stamp `target/<cog>.used`;
//!   unused for the object cache's `UNUSED`, it is removed), and its
//!   library is kept by the SHA-256 of its bytes.
//!
//! With the cache off (`QUARZ_NO_CACHE=1`), each build is made in a
//! temporary directory, and its library is loaded from a copy removed
//! once loaded.

use std::path::{Path, PathBuf};
use std::time::SystemTime;

use quarz_aot::objcache::{self, Cache};
use quarz_cog::native::{self as cog_native, QUARZ_RUSTC};
use sha2::{Digest, Sha256};

/// A cog of the movement that brings native code.
#[derive(Clone, Debug)]
pub struct NativeCog {
    pub name: String,
    /// The dependency path that brought it, from the application
    /// (`app → web → zlib`); empty for the application itself.
    pub path: String,
    /// `[native] crate` as its manifest writes it (relative to the cog).
    pub declared: String,
    /// The package's directory.
    pub dir: PathBuf,
    /// The lock's hash of its tree, for a cog the lock pins.
    pub hash: Option<String>,
}

impl NativeCog {
    /// How errors name it: ``cog `zlib` (app → web → zlib)``.
    fn who(&self) -> String {
        if self.path.is_empty() {
            format!("cog `{}`", self.name)
        } else {
            format!("cog `{}` ({})", self.name, self.path)
        }
    }

    /// The line said before a build: `cog zlib (app → web → zlib)`.
    fn plain(&self) -> String {
        if self.path.is_empty() {
            format!("cog {}", self.name)
        } else {
            format!("cog {} ({})", self.name, self.path)
        }
    }
}

/// The cogs of `cogs` (a movement's, the application first) that bring
/// native code, each with the dependency path that brought it (the
/// shortest, by the imports).
pub fn of(cogs: &[quarz_cog::CogEntry]) -> Vec<NativeCog> {
    let mut parent: Vec<Option<usize>> = vec![None; cogs.len()];
    let mut seen = vec![false; cogs.len()];
    let mut queue = std::collections::VecDeque::new();
    if !cogs.is_empty() {
        seen[0] = true;
        queue.push_back(0);
    }
    while let Some(i) = queue.pop_front() {
        for (_, j) in cogs[i].imports.iter().chain(&cogs[i].dev_imports) {
            if *j < cogs.len() && !seen[*j] {
                seen[*j] = true;
                parent[*j] = Some(i);
                queue.push_back(*j);
            }
        }
    }
    cogs.iter()
        .enumerate()
        .filter_map(|(i, c)| {
            let dir = c.native.clone()?;
            let mut chain = vec![c.name.clone()];
            let mut k = i;
            while let Some(p) = parent[k] {
                chain.push(cogs[p].name.clone());
                k = p;
            }
            chain.reverse();
            let declared = dir
                .strip_prefix(&c.dir)
                .map(|d| d.to_string_lossy().into_owned())
                .unwrap_or_else(|_| dir.display().to_string());
            Some(NativeCog {
                name: c.name.clone(),
                path: if i == 0 {
                    String::new()
                } else {
                    chain.join(" → ")
                },
                declared,
                dir,
                hash: c.hash.clone(),
            })
        })
        .collect()
}

/// A key's parts, each after its length, hashed (SHA-256, hex).
fn key(parts: &[&[u8]]) -> String {
    let mut h = Sha256::new();
    for p in parts {
        h.update((p.len() as u64).to_le_bytes());
        h.update(p);
    }
    h.finalize().iter().map(|b| format!("{b:02x}")).collect()
}

/// Changed when what a kept build depends on beyond its key's inputs
/// changes: a new value makes every older one a miss. (2: a key holds
/// the archive beside the dynamic library, #677's fourth step.)
const KEY_VERSION: &str = "quarz-native-2";

/// What a command does with a cog's build: load its dynamic library
/// (`quarz run`, `quarz test`), or link its archive (`quarz build`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Use {
    Load,
    Link,
}

/// The file a command uses: where, and whether it is a copy to remove
/// once used (the cache off).
pub struct Built {
    pub file: PathBuf,
    pub remove_after: bool,
}

/// Build (or find kept) the file `used` needs of each of `cogs`, `offline`
/// passed to cargo: in the order given, the first failure an error naming
/// the cog.
pub fn build_all(
    cogs: &[NativeCog],
    offline: bool,
    used: Use,
) -> Result<Vec<(String, Built)>, String> {
    let root = quarz_types::cache::dir().map(|d| d.join("native"));
    cogs.iter()
        .map(|c| {
            Ok((
                c.name.clone(),
                build_one(c, root.as_deref(), offline, used)?,
            ))
        })
        .collect()
}

/// A new directory under `parent` that only this process made: its name
/// unpredictable (`what-` and 16 hex digits from a randomly keyed hash),
/// created exclusively (an existing one is never used: another name is
/// tried) and, on Unix, with mode 0700. A library is copied into it and
/// loaded from it: in a directory others can write (the system's
/// temporary directory, with the cache off), one made by someone else
/// first could have its file swapped between the copy and the load, and
/// their code would run as the user of `quarz`.
pub fn private_dir(parent: &Path, what: &str) -> std::io::Result<PathBuf> {
    use std::hash::{BuildHasher, Hasher};
    std::fs::create_dir_all(parent)?;
    let mut last = None;
    for attempt in 0..16u32 {
        let mut h = std::collections::hash_map::RandomState::new().build_hasher();
        h.write_u32(std::process::id());
        h.write_u32(attempt);
        if let Ok(t) = SystemTime::now().duration_since(SystemTime::UNIX_EPOCH) {
            h.write_u128(t.as_nanos());
        }
        let dir = parent.join(format!("{what}-{:016x}", h.finish()));
        match new_private(&dir) {
            Ok(()) => return Ok(dir),
            Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => last = Some(e),
            Err(e) => return Err(e),
        }
    }
    Err(last.unwrap_or_else(|| std::io::Error::other("no directory")))
}

/// Create `dir` itself (not its parents), failing if it exists; mode 0700
/// on Unix.
fn new_private(dir: &Path) -> std::io::Result<()> {
    let mut b = std::fs::DirBuilder::new();
    #[cfg(unix)]
    {
        use std::os::unix::fs::DirBuilderExt;
        b.mode(0o700);
    }
    b.create(dir)
}

/// Remove what builds killed before their end left in `builds`
/// (`native/build`): directories older than a day.
fn sweep_builds(builds: &Path) {
    let now = SystemTime::now();
    let Ok(entries) = std::fs::read_dir(builds) else {
        return;
    };
    for e in entries.flatten() {
        let old = e
            .metadata()
            .and_then(|m| m.modified())
            .ok()
            .and_then(|t| now.duration_since(t).ok())
            .is_some_and(|age| age > std::time::Duration::from_secs(24 * 60 * 60));
        if old {
            let _ = std::fs::remove_dir_all(e.path());
        }
    }
}

fn build_one(
    cog: &NativeCog,
    root: Option<&Path>,
    offline: bool,
    used: Use,
) -> Result<Built, String> {
    let who = cog.who();
    let package =
        cog_native::check_package(&who, &cog.declared, &cog.dir).map_err(|e| e.to_string())?;
    let say = || {
        eprintln!(
            "quarz: building the native code of {} with cargo",
            cog.plain()
        )
    };
    // The file of a build `used` needs, in cargo's target directory.
    let wanted = |library: &Path| match used {
        Use::Load => library.to_path_buf(),
        Use::Link => library.with_file_name(&package.archive),
    };
    let Some(root) = root else {
        // The cache off: a temporary build, used from a copy, in a
        // directory of this process's own (`private_dir`).
        let tmp = private_dir(&std::env::temp_dir(), "quarz-native")
            .map_err(|e| format!("{who}: a directory to build in: {e}"))?;
        let cargo = cog_native::toolchain(&who, &package.dir).map_err(|e| e.to_string())?;
        let mut told = false;
        let built = cog_native::build(
            &who,
            &package,
            &cargo,
            &tmp.join("target"),
            offline,
            &mut || {
                if !told {
                    told = true;
                    say();
                }
            },
        );
        let result = built.map_err(|e| e.to_string()).and_then(|lib| {
            let from = wanted(&lib);
            let copy = tmp.join(from.file_name().unwrap_or_default());
            std::fs::copy(&from, &copy).map_err(|e| format!("{who}: {e}"))?;
            Ok(copy)
        });
        let _ = std::fs::remove_dir_all(tmp.join("target"));
        return Ok(Built {
            file: result?,
            remove_after: true,
        });
    };
    // The kept builds: libraries and archives, by key, the same rules,
    // each in a directory of its own (an entry's sum is `<key>.sum`).
    let stores = [
        Cache::with_extension(&root.join("lib"), "so"),
        Cache::with_extension(&root.join("archive"), "a"),
    ];
    let store_of = |u: Use| &stores[usize::from(u == Use::Link)];
    // Keep both files of a build under `k`, the archive first, and give
    // the one `used` needs.
    let keep = |library: &[u8], archive: &[u8], k: &str| -> Result<Built, String> {
        stores[1].store(k, archive);
        stores[0].store(k, library);
        for s in &stores {
            s.sweep(objcache::bound());
        }
        let file = store_of(used)
            .fetch_path(k)
            .ok_or_else(|| format!("{who}: its build could not be kept in {}", root.display()))?;
        Ok(Built {
            file,
            remove_after: false,
        })
    };
    let read_both = |lib: &Path| -> Result<(Vec<u8>, Vec<u8>), String> {
        let library = std::fs::read(lib).map_err(|e| format!("{who}: {e}"))?;
        let archive_path = lib.with_file_name(&package.archive);
        let archive = std::fs::read(&archive_path)
            .map_err(|e| format!("{who}: {}: {e}", archive_path.display()))?;
        Ok((library, archive))
    };
    if let (Some(hash), false) = (&cog.hash, package.path_dependencies) {
        // A tree the lock pins: kept by its key. A hit (the file the
        // command uses kept whole) runs no cargo; a miss builds both.
        let abi = quarz_ext::sys::QZ_ABI_MAJOR.to_string();
        let env = cog_native::environment(&package.dir);
        let k = key(&[
            KEY_VERSION.as_bytes(),
            hash.as_bytes(),
            QUARZ_RUSTC.commit.as_bytes(),
            abi.as_bytes(),
            package.library.as_bytes(),
            env.as_bytes(),
        ]);
        if let Some(file) = store_of(used).fetch_path(&k) {
            return Ok(Built {
                file,
                remove_after: false,
            });
        }
        let cargo = cog_native::toolchain(&who, &package.dir).map_err(|e| e.to_string())?;
        say();
        let builds = root.join("build");
        sweep_builds(&builds);
        let target = private_dir(&builds, &cog.name)
            .map_err(|e| format!("{who}: a directory to build in: {e}"))?;
        let built = cog_native::build(&who, &package, &cargo, &target, offline, &mut || {});
        let files = built
            .map_err(|e| e.to_string())
            .and_then(|lib| read_both(&lib));
        let _ = std::fs::remove_dir_all(&target);
        let (library, archive) = files?;
        return keep(&library, &archive, &k);
    }
    // Any other: cargo on every run, in the cog's own target directory;
    // the file the command uses kept by the SHA-256 of its bytes.
    let cargo = cog_native::toolchain(&who, &package.dir).map_err(|e| e.to_string())?;
    let targets = root.join("target");
    let _ = std::fs::create_dir_all(&targets);
    sweep_targets(&targets);
    let stamp = targets.join(format!("{}.used", cog.name));
    let _ = std::fs::write(&stamp, "");
    let mut told = false;
    let lib = cog_native::build(
        &who,
        &package,
        &cargo,
        &targets.join(&cog.name),
        offline,
        &mut || {
            if !told {
                told = true;
                say();
            }
        },
    )
    .map_err(|e| e.to_string())?;
    let from = wanted(&lib);
    let bytes = std::fs::read(&from).map_err(|e| format!("{who}: {}: {e}", from.display()))?;
    let k = key(&[b"quarz-native-local-2", &bytes]);
    let store = store_of(used);
    store.store(&k, &bytes);
    store.sweep(objcache::bound());
    let file = store
        .fetch_path(&k)
        .ok_or_else(|| format!("{who}: its build could not be kept in {}", root.display()))?;
    Ok(Built {
        file,
        remove_after: false,
    })
}

/// Remove the target directories of local cogs not built for the object
/// cache's `UNUSED` (their stamp `<cog>.used` says when they last were).
fn sweep_targets(targets: &Path) {
    let now = SystemTime::now();
    let Ok(entries) = std::fs::read_dir(targets) else {
        return;
    };
    for e in entries.flatten() {
        let p = e.path();
        if p.extension().and_then(|x| x.to_str()) != Some("used") {
            continue;
        }
        let old = e
            .metadata()
            .and_then(|m| m.modified())
            .ok()
            .and_then(|t| now.duration_since(t).ok())
            .is_some_and(|age| age > objcache::UNUSED);
        if old {
            let _ = std::fs::remove_dir_all(p.with_extension(""));
            let _ = std::fs::remove_file(&p);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A directory that exists is never taken: `new_private` refuses it,
    /// and `private_dir` makes another, its own, with mode 0700.
    #[test]
    fn a_private_dir_is_never_one_that_exists() {
        let parent =
            std::env::temp_dir().join(format!("quarz-private-test-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&parent);
        std::fs::create_dir_all(&parent).unwrap();
        let taken = parent.join("taken");
        std::fs::create_dir(&taken).unwrap();
        assert_eq!(
            new_private(&taken).unwrap_err().kind(),
            std::io::ErrorKind::AlreadyExists
        );
        let a = private_dir(&parent, "x").unwrap();
        let b = private_dir(&parent, "x").unwrap();
        assert_ne!(a, b);
        assert!(a.is_dir() && a.file_name().unwrap().to_str().unwrap().len() == 18);
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            let mode = std::fs::metadata(&a).unwrap().permissions().mode() & 0o777;
            assert_eq!(mode, 0o700);
        }
        let _ = std::fs::remove_dir_all(&parent);
    }
}
