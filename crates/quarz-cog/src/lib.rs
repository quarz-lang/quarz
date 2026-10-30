//! Cogs, the packages of Quarz (docs/10-cogs.md): a cog is a git
//! repository with a `Cog.toml`, fetched as source and pinned to a commit
//! by `Cog.lock`. This crate reads manifests and lock files, resolves a
//! movement's versions by minimal version selection, fetches and verifies
//! the cogs' trees, and says where each one's files are; checking and
//! compiling them is the rest of the compiler's business.

pub mod git;
pub mod hash;
pub mod lock;
pub mod manifest;
pub mod version;

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::path::{Path, PathBuf};

use git::Mirror;
use lock::{Lock, LockedCog, LOCK};
use manifest::{Dependency, Manifest, Ref, Source, MANIFEST};
use version::Version;

/// The language version manifests' `quarz` is compared with.
pub const LANGUAGE_VERSION: &str = env!("CARGO_PKG_VERSION");

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Error(pub String);

impl Error {
    pub fn new(message: impl Into<String>) -> Error {
        Error(message.into())
    }
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

impl std::error::Error for Error {}

/// How `open` may get to the cogs.
#[derive(Clone, Debug, Default)]
pub struct Options {
    /// Fetch nothing: use the cache and `vendor/` only.
    pub offline: bool,
    /// Fail instead of writing `Cog.lock`.
    pub locked: bool,
    /// Resolve again whatever the lock says (`quarz cog update`).
    pub refresh: bool,
    /// Report fetches on standard error.
    pub verbose: bool,
    /// Read the cogs from the cache even when `vendor/` exists (to fill
    /// it again).
    pub ignore_vendor: bool,
}

/// A movement: the application (`cogs[0]`) and every cog it brings in.
#[derive(Clone, Debug)]
pub struct Movement {
    /// The directory of the application's `Cog.toml`.
    pub root: PathBuf,
    pub cogs: Vec<CogEntry>,
    /// `cogs[dev_from..]` are reached only through the application's
    /// `[dev-dependencies]` (`quarz test` loads them; `run` and `build`
    /// leave them out).
    pub dev_from: usize,
    pub lock: Option<Lock>,
}

#[derive(Clone, Debug)]
pub struct CogEntry {
    pub name: String,
    pub version: String,
    /// The module its declarations live in.
    pub module: String,
    /// The directory of its `Cog.toml` (its files are under `src/`).
    pub dir: PathBuf,
    /// Its dependencies: the key of its manifest and the index of the cog.
    pub imports: Vec<(String, usize)>,
    /// The application's `[dev-dependencies]`, as `imports` (empty for
    /// every other cog: theirs are not resolved).
    pub dev_imports: Vec<(String, usize)>,
    /// Where it comes from; `None` for the application and a `[patch]`.
    pub source: Option<Source>,
    pub rev: Option<String>,
}

/// The cache: `$QUARZ_CACHE`, else `$XDG_CACHE_HOME/quarz`, else
/// `~/.cache/quarz`.
pub fn cache_dir() -> PathBuf {
    if let Some(d) = std::env::var_os("QUARZ_CACHE").filter(|d| !d.is_empty()) {
        return PathBuf::from(d);
    }
    if let Some(d) = std::env::var_os("XDG_CACHE_HOME").filter(|d| !d.is_empty()) {
        return PathBuf::from(d).join("quarz");
    }
    let home = std::env::var_os("HOME")
        .map(PathBuf::from)
        .unwrap_or_default();
    home.join(".cache").join("quarz")
}

/// The nearest directory from `start` upward that holds a `Cog.toml`.
pub fn find_root(start: &Path) -> Option<PathBuf> {
    let start = std::fs::canonicalize(start).ok()?;
    let mut dir = Some(start.as_path());
    while let Some(d) = dir {
        if d.join(MANIFEST).is_file() {
            return Some(d.to_path_buf());
        }
        dir = d.parent();
    }
    None
}

/// What `from_lock` found wrong with a lock: it no longer matches the
/// manifests (resolve again), or something cannot be done at all.
enum LockProblem {
    Stale(String),
    Fatal(Error),
}

impl From<Error> for LockProblem {
    fn from(e: Error) -> LockProblem {
        LockProblem::Fatal(e)
    }
}

struct Ctx<'a> {
    root: &'a Path,
    cache: PathBuf,
    opts: &'a Options,
    /// `[patch]`: sources replaced by local directories.
    patches: HashMap<Source, PathBuf>,
    /// `vendor/`, when it exists: the cogs are read from there.
    vendor: Option<PathBuf>,
    /// `git ls-remote` results by URL.
    remotes: HashMap<String, Vec<(String, String)>>,
}

/// Open the movement whose application is in `root`: use `Cog.lock` when
/// it matches the manifests, resolve and write it otherwise, and fetch and
/// verify every cog.
pub fn open(root: &Path, opts: &Options) -> Result<Movement, Error> {
    let manifest = Manifest::read(root)?;
    manifest.check_language(LANGUAGE_VERSION)?;
    let mut ctx = Ctx::new(root, &manifest, opts)?;
    let existing = Lock::read(root)?;
    if manifest.dependencies.is_empty()
        && manifest.dev_dependencies.is_empty()
        && existing.is_none()
    {
        return ctx
            .movement_from_lock(&manifest, &empty_lock())
            .map_err(|p| match p {
                LockProblem::Stale(s) | LockProblem::Fatal(Error(s)) => Error(s),
            });
    }
    let inputs = ctx.inputs(&manifest)?;
    let current = existing
        .as_ref()
        .filter(|l| l.inputs.as_deref() == Some(inputs.as_str()));
    if !opts.refresh {
        if existing.is_some() && current.is_none() {
            if opts.locked {
                return Err(Error::new(
                    "Cog.lock is out of date (the dependencies in the manifests changed); run `quarz cog update` (--locked)",
                ));
            }
            if opts.verbose {
                eprintln!("quarz: resolving again: the dependencies in the manifests changed");
            }
        } else if let Some(lock) = current {
            match ctx.movement_from_lock(&manifest, lock) {
                Ok(mut movement) => {
                    // A lock that names cogs nothing needs any more is
                    // pruned (no fetching involved).
                    let reached = movement.lock.clone().unwrap();
                    if reached != *lock {
                        if opts.locked {
                            return Err(Error::new(
                                "Cog.lock names cogs the manifests no longer need (--locked)",
                            ));
                        }
                        reached.write(root)?;
                    }
                    movement.lock = Some(reached);
                    return Ok(movement);
                }
                Err(LockProblem::Fatal(e)) => return Err(e),
                Err(LockProblem::Stale(reason)) => {
                    if opts.locked {
                        return Err(Error::new(format!(
                            "Cog.lock is out of date ({reason}); run `quarz cog update` (--locked)"
                        )));
                    }
                    if opts.verbose {
                        eprintln!("quarz: resolving again: {reason}");
                    }
                }
            }
        } else if opts.locked {
            return Err(Error::new("there is no Cog.lock (--locked)"));
        }
    }
    if opts.offline {
        return Err(Error::new(
            "resolving the dependencies needs git (Cog.lock is missing or out of date): drop --offline",
        ));
    }
    let mut lock = ctx.resolve(&manifest)?;
    lock.inputs = Some(inputs);
    if existing.as_ref() != Some(&lock) {
        if opts.locked {
            return Err(Error::new("Cog.lock would change (--locked)"));
        }
        lock.write(root)?;
    }
    ctx.movement_from_lock(&manifest, &lock)
        .map_err(|p| match p {
            LockProblem::Stale(s) => Error::new(format!("the resolved lock does not hold: {s}")),
            LockProblem::Fatal(e) => e,
        })
}

fn empty_lock() -> Lock {
    Lock {
        version: 1,
        inputs: None,
        cogs: Vec::new(),
    }
}

/// A requirement met during resolution: who asks for which version.
struct Requirement {
    from: String,
    source: Source,
    version: Version,
    /// From the application's manifest with a `rev`: the version is also
    /// the ceiling.
    pin: bool,
}

/// A version of a cog that resolution visited.
struct Node {
    version: Version,
    rev: String,
    manifest: Manifest,
}

impl<'a> Ctx<'a> {
    fn new(root: &'a Path, manifest: &Manifest, opts: &'a Options) -> Result<Ctx<'a>, Error> {
        let mut patches = HashMap::new();
        for (key, patch) in &manifest.patch {
            let dep = manifest
                .dependencies
                .get(key)
                .or_else(|| manifest.dev_dependencies.get(key))
                .unwrap();
            let dir = root.join(&patch.path);
            if !dir.join(MANIFEST).is_file() {
                return Err(Error::new(format!(
                    "[patch] `{key}`: {} has no Cog.toml",
                    dir.display()
                )));
            }
            patches.insert(dep.source(), dir);
        }
        let vendor = Some(root.join("vendor")).filter(|v| v.is_dir() && !opts.ignore_vendor);
        Ok(Ctx {
            root,
            cache: cache_dir(),
            opts,
            patches,
            vendor,
            remotes: HashMap::new(),
        })
    }

    /// Build the movement from `lock`, which `open` has found to be the
    /// resolution of the current manifests: every cog they reach must be in
    /// it (or patched). The lock returned in the movement is `lock`
    /// restricted to what was reached.
    /// No cog is a copy of the application (docs/10 §4): one with its
    /// `[cog] name` that comes from its own repository (its `origin`, at
    /// its directory), or that declares its module too. `cogs`: (name,
    /// module, version, source: `None` for a `[patch]`).
    fn check_app_copy(
        &self,
        app: &Manifest,
        cogs: &[(String, String, String, Option<Source>)],
    ) -> Result<(), Error> {
        let module = app.module();
        let mut origin: Option<Option<Source>> = None;
        for (name, m, version, source) in cogs {
            if *name != app.cog.name {
                continue;
            }
            let at = match source {
                Some(s) => format!("{s} at {version}"),
                None => format!("the [patch] of {name} {version}"),
            };
            let own = origin.get_or_insert_with(|| {
                git::origin(self.root).map(|(url, subdir)| Source { url, subdir })
            });
            if source.is_some() && own.as_ref() == source.as_ref() {
                return Err(Error::new(format!(
                    "{at} comes from the application's own repository (its origin): a copy of the application cannot be a dependency"
                )));
            }
            if *m == module {
                return Err(Error::new(format!(
                    "{at} declares the application's name `{name}` and module `{module}`: a copy of the application cannot be a dependency (rename one of them)"
                )));
            }
        }
        Ok(())
    }

    fn movement_from_lock(
        &mut self,
        manifest: &Manifest,
        lock: &Lock,
    ) -> Result<Movement, LockProblem> {
        let mut by_source: HashMap<Source, &LockedCog> = HashMap::new();
        for c in &lock.cogs {
            let source = Source::parse_lock_string(&c.source).ok_or_else(|| {
                LockProblem::Fatal(Error::new(format!("Cog.lock: bad source `{}`", c.source)))
            })?;
            by_source.insert(source, c);
        }
        let mut cogs = vec![CogEntry {
            name: manifest.cog.name.clone(),
            version: manifest.cog.version.clone(),
            module: manifest.module(),
            dir: self.root.to_path_buf(),
            imports: Vec::new(),
            dev_imports: Vec::new(),
            source: None,
            rev: None,
        }];
        let mut manifests = vec![manifest.clone()];
        let mut index: HashMap<Source, usize> = HashMap::new();
        let mut reached: BTreeSet<Source> = BTreeSet::new();
        let mut next = 0;
        let mut dev_from = None;
        loop {
            // The cogs the dependencies reach, then (`next` at the end
            // again) those only the application's dev-dependencies reach.
            let (i, deps, dev) = if next < cogs.len() {
                let deps: Vec<(String, Dependency)> = manifests[next]
                    .dependencies
                    .iter()
                    .map(|(k, d)| (k.clone(), d.clone()))
                    .collect();
                next += 1;
                (next - 1, deps, false)
            } else if dev_from.is_none() {
                dev_from = Some(cogs.len());
                let deps: Vec<(String, Dependency)> = manifest
                    .dev_dependencies
                    .iter()
                    .map(|(k, d)| (k.clone(), d.clone()))
                    .collect();
                (0, deps, true)
            } else {
                break;
            };
            for (key, dep) in deps {
                let source = dep.source();
                let j = match index.get(&source) {
                    Some(&j) => j,
                    None => {
                        let entry = if let Some(dir) = self.patches.get(&source).cloned() {
                            let m = Manifest::read(&dir)?;
                            m.check_language(LANGUAGE_VERSION)?;
                            let entry = CogEntry {
                                name: m.cog.name.clone(),
                                version: m.cog.version.clone(),
                                module: m.module(),
                                dir,
                                imports: Vec::new(),
                                dev_imports: Vec::new(),
                                source: None,
                                rev: None,
                            };
                            manifests.push(m);
                            entry
                        } else {
                            let Some(locked) = by_source.get(&source) else {
                                return Err(LockProblem::Stale(format!("{source} is not in it")));
                            };
                            let dir = self.locked_tree(&source, locked)?;
                            let m = Manifest::read(&dir)?;
                            m.check_language(LANGUAGE_VERSION)?;
                            if m.cog.name != locked.name || m.module() != locked.module {
                                return Err(LockProblem::Fatal(Error::new(format!(
                                    "Cog.lock says {source} is `{}` (module {}), its Cog.toml says `{}` (module {})",
                                    locked.name,
                                    locked.module,
                                    m.cog.name,
                                    m.module()
                                ))));
                            }
                            check_local_deps(&source, &m)?;
                            reached.insert(source.clone());
                            let entry = CogEntry {
                                name: m.cog.name.clone(),
                                version: locked.version.clone(),
                                module: m.module(),
                                dir,
                                imports: Vec::new(),
                                dev_imports: Vec::new(),
                                source: Some(source.clone()),
                                rev: Some(locked.rev.clone()),
                            };
                            manifests.push(m);
                            entry
                        };
                        cogs.push(entry);
                        index.insert(source.clone(), cogs.len() - 1);
                        cogs.len() - 1
                    }
                };
                if dev {
                    cogs[i].dev_imports.push((key, j));
                } else {
                    cogs[i].imports.push((key, j));
                }
            }
        }
        let dev_from = dev_from.unwrap_or(cogs.len());
        let pruned = Lock {
            version: 1,
            inputs: lock.inputs.clone(),
            cogs: lock
                .cogs
                .iter()
                .filter(|c| {
                    Source::parse_lock_string(&c.source).is_some_and(|s| reached.contains(&s))
                })
                .cloned()
                .collect(),
        };
        let seen: Vec<(String, String, String, Option<Source>)> = cogs[1..]
            .iter()
            .map(|c| {
                (
                    c.name.clone(),
                    c.module.clone(),
                    c.version.clone(),
                    c.source.clone(),
                )
            })
            .collect();
        self.check_app_copy(manifest, &seen)
            .map_err(LockProblem::Fatal)?;
        let names: Vec<String> = cogs.iter().map(|c| c.name.clone()).collect();
        let edges: Vec<Vec<usize>> = cogs
            .iter()
            .map(|c| c.imports.iter().map(|(_, j)| *j).collect())
            .collect();
        check_cycle(&names, &edges).map_err(LockProblem::Fatal)?;
        Ok(Movement {
            root: self.root.to_path_buf(),
            cogs,
            dev_from,
            lock: Some(pruned),
        })
    }

    /// The directory of a locked cog's tree: in `vendor/`, or in the
    /// cache (fetched when missing), verified against the lock's hash.
    fn locked_tree(&mut self, source: &Source, locked: &LockedCog) -> Result<PathBuf, Error> {
        let dir = match &self.vendor {
            Some(vendor) => {
                let dir = vendor.join(&locked.name);
                if !dir.join(MANIFEST).is_file() {
                    return Err(Error::new(format!(
                        "vendor/ has no `{}`: run `quarz cog vendor` again, or remove vendor/",
                        locked.name
                    )));
                }
                dir
            }
            None => {
                let dir = self.src_dir(&locked.name, &locked.rev, source.subdir.as_deref());
                if !dir.join(MANIFEST).is_file() {
                    if self.opts.offline {
                        return Err(Error::new(format!(
                            "`{}` {} is not in the cache (--offline)",
                            locked.name, locked.version
                        )));
                    }
                    let mirror = Mirror::open(&self.cache, &source.url)?;
                    self.log(&format!("fetching {} {}", locked.name, locked.version));
                    mirror.fetch_commit(&locked.rev)?;
                    self.install(&mirror, &locked.rev, source.subdir.as_deref(), &dir)?;
                }
                dir
            }
        };
        let hash =
            hash::tree_hash(&dir).map_err(|e| Error::new(format!("{}: {e}", dir.display())))?;
        if hash != locked.hash {
            return Err(Error::new(format!(
                "the files of `{}` {} ({}) do not match Cog.lock: expected {}, found {hash}; the repository's history may have been rewritten",
                locked.name,
                locked.version,
                dir.display(),
                locked.hash
            )));
        }
        Ok(dir)
    }

    /// A digest of what resolution reads that can change: the
    /// dependencies of the application's manifest and of the patched cogs'
    /// (every other manifest is pinned by its commit). A lock resolved from
    /// the same inputs is the resolution itself: only `quarz cog update`
    /// moves a branch.
    fn inputs(&self, manifest: &Manifest) -> Result<String, Error> {
        fn table(out: &mut String, owner: &str, m: &Manifest) {
            for (key, dep) in &m.dependencies {
                out.push_str(&format!(
                    "{owner}\t{key}\t{}\t{}\n",
                    dep.source().to_lock_string(),
                    describe_ref(&dep.reference()),
                ));
            }
        }
        let mut text = String::new();
        table(&mut text, "", manifest);
        // The application's dev-dependencies, which only it has resolved.
        for (key, dep) in &manifest.dev_dependencies {
            text.push_str(&format!(
                "dev\t{key}\t{}\t{}\n",
                dep.source().to_lock_string(),
                describe_ref(&dep.reference()),
            ));
        }
        let mut patched: Vec<(&Source, &PathBuf)> = self.patches.iter().collect();
        patched.sort();
        for (source, dir) in patched {
            let m = Manifest::read(dir)?;
            table(&mut text, &source.to_lock_string(), &m);
        }
        Ok(hash::digest(text.as_bytes()))
    }

    /// Where a cog's tree is kept in the cache: by name, commit and, for a
    /// cog in a subdirectory, a digest of the subdirectory (two cogs of one
    /// commit may share a name).
    fn src_dir(&self, name: &str, rev: &str, subdir: Option<&str>) -> PathBuf {
        let short: String = rev.chars().take(12).collect();
        let leaf = match subdir {
            Some(d) => {
                let tag: String = hash::digest(d.as_bytes())
                    .chars()
                    .skip(3)
                    .filter(char::is_ascii_alphanumeric)
                    .take(8)
                    .collect();
                format!("{name}-{short}-{tag}")
            }
            None => format!("{name}-{short}"),
        };
        self.cache.join("src").join(leaf)
    }

    fn log(&self, message: &str) {
        if self.opts.verbose {
            eprintln!("quarz: {message}");
        }
    }

    /// Write a commit's tree into `dest`, through a temporary directory of
    /// its own (several `quarz` processes may fetch the same cog at once,
    /// and none may see a tree half written), its files read-only, and
    /// return the tree's hash. A `dest` that another process installed
    /// first is kept if it holds the same tree.
    fn install(
        &self,
        mirror: &Mirror,
        rev: &str,
        subdir: Option<&str>,
        dest: &Path,
    ) -> Result<String, Error> {
        static N: std::sync::atomic::AtomicU32 = std::sync::atomic::AtomicU32::new(0);
        let n = N.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
        let parent = dest.parent().unwrap_or(Path::new("."));
        std::fs::create_dir_all(parent)
            .map_err(|e| Error::new(format!("{}: {e}", parent.display())))?;
        let tmp = parent.join(format!(
            ".{}.tmp{}-{n}",
            dest.file_name().unwrap_or_default().to_string_lossy(),
            std::process::id()
        ));
        let _ = std::fs::remove_dir_all(&tmp);
        let prepared = (|| {
            mirror.export(rev, subdir, &tmp)?;
            if !tmp.join(MANIFEST).is_file() {
                return Err(Error::new(format!(
                    "{} has no Cog.toml at {rev}{}",
                    mirror.url,
                    subdir.map(|d| format!(" in {d}")).unwrap_or_default()
                )));
            }
            hash::check_tree(&tmp)
                .map_err(|e| Error::new(format!("{} at {rev}: {e}", mirror.url)))?;
            let hash = hash::tree_hash(&tmp)
                .map_err(|e| Error::new(format!("{} at {rev}: {e}", mirror.url)))?;
            set_read_only(&tmp);
            Ok(hash)
        })();
        let hash = match prepared {
            Ok(h) => h,
            Err(e) => {
                let _ = std::fs::remove_dir_all(&tmp);
                return Err(e);
            }
        };
        if std::fs::rename(&tmp, dest).is_ok() {
            return Ok(hash);
        }
        let _ = std::fs::remove_dir_all(&tmp);
        // Another process was first (or the tree was there already).
        let existing =
            hash::tree_hash(dest).map_err(|e| Error::new(format!("{}: {e}", dest.display())))?;
        if existing != hash {
            return Err(Error::new(format!(
                "{} does not hold the tree git gives for {rev} (expected {hash}, found {existing}); remove it to fetch it again",
                dest.display()
            )));
        }
        Ok(hash)
    }

    fn remote_refs(&mut self, url: &str) -> Result<&Vec<(String, String)>, Error> {
        if !self.remotes.contains_key(url) {
            let refs = git::ls_remote(url)?;
            self.remotes.insert(url.to_string(), refs);
        }
        Ok(&self.remotes[url])
    }

    /// The commit a reference denotes and its version.
    fn locate(&mut self, source: &Source, reference: &Ref) -> Result<(String, Version), Error> {
        let mirror = Mirror::open(&self.cache, &source.url)?;
        let find = |refs: &[(String, String)], name: &str| {
            refs.iter().find(|(n, _)| n == name).map(|(_, c)| c.clone())
        };
        match reference {
            Ref::Tag(tag) => {
                let refs = self.remote_refs(&source.url)?;
                let commit = find(refs, &format!("refs/tags/{tag}"))
                    .ok_or_else(|| Error::new(format!("{} has no tag `{tag}`", source.url)))?;
                mirror.fetch_commit(&commit)?;
                Ok((commit, Version::parse_tag(tag).unwrap()))
            }
            Ref::Branch(branch) => {
                let refs = self.remote_refs(&source.url)?.clone();
                let commit = find(&refs, &format!("refs/heads/{branch}")).ok_or_else(|| {
                    Error::new(format!("{} has no branch `{branch}`", source.url))
                })?;
                let v = version_of(&mirror, &commit, &refs)?;
                Ok((commit, v))
            }
            Ref::Head => {
                let refs = self.remote_refs(&source.url)?.clone();
                let commit = find(&refs, "HEAD")
                    .ok_or_else(|| Error::new(format!("{} has no default branch", source.url)))?;
                let v = version_of(&mirror, &commit, &refs)?;
                Ok((commit, v))
            }
            Ref::Rev(rev) => {
                let refs = self.remote_refs(&source.url)?.clone();
                let v = version_of(&mirror, rev, &refs)?;
                Ok((rev.clone(), v))
            }
        }
    }

    fn manifest_at(&self, source: &Source, rev: &str) -> Result<Manifest, Error> {
        let mirror = Mirror::open(&self.cache, &source.url)?;
        mirror.fetch_commit(rev)?;
        let path = match &source.subdir {
            Some(d) => format!("{d}/{MANIFEST}"),
            None => MANIFEST.to_string(),
        };
        let text = mirror
            .show(rev, &path)?
            .ok_or_else(|| Error::new(format!("{source} has no Cog.toml at {rev}")))?;
        let m = Manifest::parse(&text)
            .map_err(|e| Error::new(format!("{source} at {rev}: Cog.toml: {e}")))?;
        m.check_language(LANGUAGE_VERSION)?;
        Ok(m)
    }

    /// Minimal version selection: visit every version the manifests ask
    /// for, take for each cog the highest, and keep what the application
    /// reaches through the chosen versions.
    fn resolve(&mut self, manifest: &Manifest) -> Result<Lock, Error> {
        let mut nodes: HashMap<(Source, String), Node> = HashMap::new();
        let mut versions: BTreeMap<Source, Vec<(Version, String)>> = BTreeMap::new();
        // (who asks, whether it may name repositories on this machine,
        // dependency)
        let mut queue: Vec<(String, bool, Dependency)> = manifest
            .dependencies
            .values()
            .chain(manifest.dev_dependencies.values())
            .map(|d| ("the application".to_string(), true, d.clone()))
            .collect();
        let mut patched_seen: BTreeSet<Source> = BTreeSet::new();
        // Located references, so that a branch is read once.
        let mut located: HashMap<(Source, Ref), (String, Version)> = HashMap::new();
        while let Some((from, local_ok, dep)) = queue.pop() {
            let source = dep.source();
            if !local_ok && git::is_local_url(&source.url) {
                return Err(local_dep_error(&from, &source));
            }
            if let Some(dir) = self.patches.get(&source).cloned() {
                if patched_seen.insert(source.clone()) {
                    let m = Manifest::read(&dir)?;
                    for d in m.dependencies.values() {
                        queue.push((m.cog.name.clone(), true, d.clone()));
                    }
                }
                continue;
            }
            let reference = dep.reference();
            let key = (source.clone(), reference.clone());
            let (rev, version) = match located.get(&key) {
                Some(found) => found.clone(),
                None => {
                    self.log(&format!(
                        "looking up {source} ({})",
                        describe_ref(&reference)
                    ));
                    let found = self
                        .locate(&source, &reference)
                        .map_err(|e| Error::new(format!("{e} (required by {from})")))?;
                    located.insert(key, found.clone());
                    found
                }
            };
            let node_key = (source.clone(), rev.clone());
            if nodes.contains_key(&node_key) {
                continue;
            }
            let m = self.manifest_at(&source, &rev)?;
            let local = git::is_local_url(&source.url);
            for d in m.dependencies.values() {
                queue.push((format!("{} {version}", m.cog.name), local, d.clone()));
            }
            versions
                .entry(source.clone())
                .or_default()
                .push((version.clone(), rev.clone()));
            nodes.insert(
                node_key,
                Node {
                    version,
                    rev,
                    manifest: m,
                },
            );
        }
        let chosen: HashMap<Source, (Version, String)> = versions
            .into_iter()
            .map(|(s, mut vs)| {
                vs.sort();
                (s, vs.pop().unwrap())
            })
            .collect();
        // What the application reaches through the chosen versions, and
        // the requirements on the way.
        let mut reqs: Vec<Requirement> = Vec::new();
        let mut reached: BTreeSet<Source> = BTreeSet::new();
        let mut stack: Vec<(String, bool, Manifest)> =
            vec![("the application".to_string(), true, manifest.clone())];
        let mut patched_done: BTreeSet<Source> = BTreeSet::new();
        while let Some((from, is_app, m)) = stack.pop() {
            let dev = if is_app {
                Some(&m.dev_dependencies)
            } else {
                None
            };
            for dep in m
                .dependencies
                .values()
                .chain(dev.into_iter().flat_map(|d| d.values()))
            {
                let source = dep.source();
                if let Some(dir) = self.patches.get(&source) {
                    if patched_done.insert(source.clone()) {
                        let pm = Manifest::read(dir)?;
                        stack.push((pm.cog.name.clone(), false, pm));
                    }
                    continue;
                }
                let (rev, version) = located[&(source.clone(), dep.reference())].clone();
                let _ = rev;
                reqs.push(Requirement {
                    from: from.clone(),
                    source: source.clone(),
                    version,
                    pin: is_app && matches!(dep.reference(), Ref::Rev(_)),
                });
                if reached.insert(source.clone()) {
                    let (v, rev) = &chosen[&source];
                    let node = &nodes[&(source.clone(), rev.clone())];
                    stack.push((
                        format!("{} {v}", node.manifest.cog.name),
                        false,
                        node.manifest.clone(),
                    ));
                }
            }
        }
        for r in &reqs {
            let (v, _) = &chosen[&r.source];
            if !v.compatible(&r.version) {
                let other = reqs
                    .iter()
                    .find(|o| o.source == r.source && o.version == *v)
                    .map(|o| o.from.clone())
                    .unwrap_or_else(|| "another cog".to_string());
                return Err(Error::new(format!(
                    "{} needs {} {}, but {other} needs {v}, which is not compatible; pin one of them with `rev`, or replace it with [patch]",
                    r.from, r.source, r.version
                )));
            }
            if r.pin && *v != r.version {
                let other = reqs
                    .iter()
                    .find(|o| o.source == r.source && o.version == *v)
                    .map(|o| o.from.clone())
                    .unwrap_or_else(|| "another cog".to_string());
                return Err(Error::new(format!(
                    "the application pins {} to {} with `rev`, but {other} needs {v}",
                    r.source, r.version
                )));
            }
        }
        // A chosen cog's `[patch]` with a path, a copy of the application,
        // and a cycle among the cogs (patched ones included), before
        // anything is fetched or written.
        for source in &reached {
            let rev = &chosen[source].1;
            check_local_patches(source, &nodes[&(source.clone(), rev.clone())].manifest)?;
        }
        let mut seen: Vec<(String, String, String, Option<Source>)> = reached
            .iter()
            .map(|source| {
                let (version, rev) = &chosen[source];
                let m = &nodes[&(source.clone(), rev.clone())].manifest;
                (
                    m.cog.name.clone(),
                    m.module(),
                    version.to_string(),
                    Some(source.clone()),
                )
            })
            .collect();
        for source in &patched_seen {
            if let Some(dir) = self.patches.get(source) {
                let m = Manifest::read(dir)?;
                seen.push((m.cog.name.clone(), m.module(), m.cog.version.clone(), None));
            }
        }
        self.check_app_copy(manifest, &seen)?;
        let mut graph: Vec<(Source, Manifest)> = Vec::new();
        for source in &reached {
            let rev = &chosen[source].1;
            graph.push((
                source.clone(),
                nodes[&(source.clone(), rev.clone())].manifest.clone(),
            ));
        }
        for source in &patched_seen {
            if let Some(dir) = self.patches.get(source) {
                graph.push((source.clone(), Manifest::read(dir)?));
            }
        }
        let names: Vec<String> = graph.iter().map(|(_, m)| m.cog.name.clone()).collect();
        let edges: Vec<Vec<usize>> = graph
            .iter()
            .map(|(_, m)| {
                m.dependencies
                    .values()
                    .filter_map(|d| {
                        let to = d.source();
                        graph.iter().position(|(s, _)| *s == to)
                    })
                    .collect()
            })
            .collect();
        check_cycle(&names, &edges)?;
        let mut cogs = Vec::new();
        for source in &reached {
            let (version, rev) = &chosen[source];
            let node = &nodes[&(source.clone(), rev.clone())];
            let dir = self.src_dir(&node.manifest.cog.name, rev, source.subdir.as_deref());
            let mirror = Mirror::open(&self.cache, &source.url)?;
            self.log(&format!("fetching {} {version}", node.manifest.cog.name));
            mirror.fetch_commit(rev)?;
            // The lock's hash is the hash of what git gives, never of what
            // the cache happens to hold.
            let hash = self.install(&mirror, rev, source.subdir.as_deref(), &dir)?;
            let mut dependencies: Vec<String> = node
                .manifest
                .dependencies
                .values()
                .map(|d| d.source().to_lock_string())
                .collect();
            dependencies.sort();
            dependencies.dedup();
            cogs.push(LockedCog {
                name: node.manifest.cog.name.clone(),
                module: node.manifest.module(),
                source: source.to_lock_string(),
                version: node.version.to_string(),
                rev: node.rev.clone(),
                hash,
                dependencies,
            });
        }
        Ok(Lock {
            version: 1,
            inputs: None,
            cogs,
        })
    }
}

/// Cogs depend on each other in no cycle (docs/10 §4): a `static def`
/// runs only from a cog that depends on its own, which would be both.
/// `edges[i]`: the cogs cog `i` depends on.
fn check_cycle(names: &[String], edges: &[Vec<usize>]) -> Result<(), Error> {
    // 0: not visited, 1: on the path, 2: done.
    fn visit(
        i: usize,
        edges: &[Vec<usize>],
        state: &mut [u8],
        path: &mut Vec<usize>,
    ) -> Option<usize> {
        state[i] = 1;
        path.push(i);
        for &j in &edges[i] {
            if state[j] == 1 {
                return Some(j);
            }
            if state[j] == 0 {
                if let Some(c) = visit(j, edges, state, path) {
                    return Some(c);
                }
            }
        }
        path.pop();
        state[i] = 2;
        None
    }
    let mut state = vec![0u8; names.len()];
    for i in 0..names.len() {
        let mut path = Vec::new();
        if state[i] == 0 {
            if let Some(j) = visit(i, edges, &mut state, &mut path) {
                let from = path.iter().position(|k| *k == j).unwrap_or(0);
                let cycle: Vec<&str> = path[from..]
                    .iter()
                    .chain([&j])
                    .map(|k| names[*k].as_str())
                    .collect();
                return Err(Error::new(format!(
                    "the cogs depend on each other in a cycle: {}; a cog's dependencies cannot lead back to it",
                    cycle.join(" -> ")
                )));
            }
        }
    }
    Ok(())
}

fn describe_ref(r: &Ref) -> String {
    match r {
        Ref::Tag(t) => format!("tag {t}"),
        Ref::Rev(r) => format!("rev {r}"),
        Ref::Branch(b) => format!("branch {b}"),
        Ref::Head => "the default branch".to_string(),
    }
}

/// A cog fetched from elsewhere may not name a repository on this machine
/// (`file://` or a path): only the application, a patched cog and a cog
/// that is itself local may.
fn check_local_deps(source: &Source, m: &Manifest) -> Result<(), Error> {
    if git::is_local_url(&source.url) {
        return Ok(());
    }
    for d in m.dependencies.values() {
        if git::is_local_url(&d.git) {
            return Err(local_dep_error(&m.cog.name, &d.source()));
        }
    }
    check_local_patches(source, m)
}

/// A `[patch]` names a directory on this machine, which a cog fetched from
/// elsewhere may not; only the application's patches apply in any case.
fn check_local_patches(source: &Source, m: &Manifest) -> Result<(), Error> {
    if git::is_local_url(&source.url) {
        return Ok(());
    }
    match m.patch.iter().next() {
        Some((key, p)) => Err(Error::new(format!(
            "{} {} has a [patch] `{key}` naming {}, a directory on this machine, which a cog fetched from elsewhere may not name (and only the application's [patch] applies)",
            m.cog.name,
            m.cog.version,
            p.path.display()
        ))),
        None => Ok(()),
    }
}

fn local_dep_error(from: &str, dep: &Source) -> Error {
    Error::new(format!(
        "{from} names {dep}, a repository on this machine: only the application, a patched cog or a local cog may"
    ))
}

/// The version of a commit: the highest version tag naming it, or a
/// pseudo-version from the nearest tag among its ancestors.
fn version_of(mirror: &Mirror, rev: &str, remote: &[(String, String)]) -> Result<Version, Error> {
    mirror.fetch_history(rev)?;
    // Only tags the repository itself shows, naming the same commit.
    let genuine = |name: &str, commit: &str| {
        remote
            .iter()
            .any(|(n, c)| n.strip_prefix("refs/tags/") == Some(name) && c == commit)
    };
    let tags: Vec<(Version, bool)> = mirror
        .tags_merged(rev)?
        .iter()
        .filter(|(name, commit)| genuine(name, commit))
        .filter_map(|(name, commit)| Some((Version::parse_tag(name)?, commit == rev)))
        .collect();
    // The highest version tag naming the commit, else a pseudo-version
    // after the highest one among its ancestors.
    if let Some(v) = tags.iter().filter(|(_, at)| *at).map(|(v, _)| v).max() {
        return Ok(v.clone());
    }
    let base = tags.iter().map(|(v, _)| v).max();
    let time = mirror.commit_time(rev)?;
    Ok(Version::pseudo(base, time, rev))
}

/// Visit the regular files under `dir`, never following a symbolic link.
fn each_file(dir: &Path, f: &mut dyn FnMut(&Path)) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let Ok(ft) = entry.file_type() else {
            continue;
        };
        if ft.is_dir() {
            each_file(&entry.path(), f);
        } else if ft.is_file() {
            f(&entry.path());
        }
    }
}

/// A cached file is read-only for everyone; a vendored one is the
/// owner's to change (`0o644`), as a checked-out file is.
fn set_mode(path: &Path, writable: bool) {
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        let mode = if writable { 0o644 } else { 0o444 };
        let _ = std::fs::set_permissions(path, std::fs::Permissions::from_mode(mode));
    }
    #[cfg(not(unix))]
    if let Ok(meta) = std::fs::metadata(path) {
        let mut perms = meta.permissions();
        #[allow(clippy::permissions_set_readonly_false)]
        perms.set_readonly(!writable);
        let _ = std::fs::set_permissions(path, perms);
    }
}

fn set_read_only(dir: &Path) {
    each_file(dir, &mut |p| set_mode(p, false));
}

// ----- commands --------------------------------------------------------

/// `quarz cog init`: a `Cog.toml` for `dir` (named after it) and a
/// `src/main.qz` when there is none.
pub fn init(dir: &Path) -> Result<String, Error> {
    let manifest = dir.join(MANIFEST);
    if manifest.exists() {
        return Err(Error::new(format!("{} already exists", manifest.display())));
    }
    let base = std::fs::canonicalize(dir)
        .ok()
        .and_then(|d| d.file_name().map(|n| n.to_string_lossy().into_owned()))
        .unwrap_or_else(|| "app".to_string());
    let mut name: String = base
        .to_ascii_lowercase()
        .chars()
        .map(|c| {
            if c.is_ascii_alphanumeric() || c == '-' || c == '_' {
                c
            } else {
                '-'
            }
        })
        .collect();
    if !name.starts_with(|c: char| c.is_ascii_lowercase()) {
        name = format!("app-{name}");
    }
    let language: Vec<&str> = LANGUAGE_VERSION.split('.').take(2).collect();
    let text = format!(
        "[cog]\nname = \"{name}\"\nversion = \"0.1.0\"\nquarz = \"{}\"\n\n[dependencies]\n",
        language.join(".")
    );
    std::fs::write(&manifest, text)
        .map_err(|e| Error::new(format!("{}: {e}", manifest.display())))?;
    let main = dir.join("src").join("main.qz");
    if !main.exists() {
        std::fs::create_dir_all(dir.join("src"))
            .map_err(|e| Error::new(format!("{}: {e}", dir.display())))?;
        std::fs::write(&main, "puts \"Hello from #{cog.name}!\"\n")
            .map_err(|e| Error::new(format!("{}: {e}", main.display())))?;
    }
    Ok(name)
}

/// What `quarz cog add` is given.
#[derive(Clone, Debug, Default)]
pub struct AddRequest {
    pub url: String,
    pub tag: Option<String>,
    pub rev: Option<String>,
    pub key: Option<String>,
    pub subdir: Option<String>,
    pub dev: bool,
}

/// `quarz cog add`: write the dependency into `Cog.toml` (a `tag`, or the
/// default branch's head as a `tag` when a version tag names it, else as a
/// `rev`) under the key `key`, or the module the cog declares. Returns the
/// key and what was written.
pub fn add(root: &Path, req: &AddRequest, opts: &Options) -> Result<(String, String), Error> {
    let manifest = Manifest::read(root)?;
    let mut ctx = Ctx::new(root, &manifest, opts)?;
    let source = Source {
        url: req.url.clone(),
        subdir: req.subdir.clone(),
    };
    let (reference, rev) = if let Some(tag) = &req.tag {
        if Version::parse_tag(tag).is_none() {
            return Err(Error::new(format!(
                "`{tag}` is not a version tag (vMAJOR.MINOR.PATCH)"
            )));
        }
        let (rev, _) = ctx.locate(&source, &Ref::Tag(tag.clone()))?;
        (("tag", tag.clone()), rev)
    } else if let Some(rev) = &req.rev {
        if rev.len() != 40 || !rev.chars().all(|c| c.is_ascii_hexdigit()) {
            return Err(Error::new(
                "--rev takes a full commit id (40 hexadecimal digits)",
            ));
        }
        ctx.locate(&source, &Ref::Rev(rev.clone()))?;
        (("rev", rev.clone()), rev.clone())
    } else {
        let (rev, version) = ctx.locate(&source, &Ref::Head)?;
        let tag_ref = format!("refs/tags/{}", version.tag());
        let tagged = version.pre.is_empty()
            && ctx
                .remote_refs(&source.url)?
                .iter()
                .any(|(n, c)| *n == tag_ref && *c == rev);
        if tagged {
            (("tag", version.tag()), rev)
        } else {
            (("rev", rev.clone()), rev)
        }
    };
    let theirs = ctx.manifest_at(&source, &rev)?;
    let key = req.key.clone().unwrap_or_else(|| theirs.module());
    if !manifest::is_const_name(&key) {
        return Err(Error::new(format!(
            "the key `{key}` is not a constant name"
        )));
    }
    let table_name = if req.dev {
        "dev-dependencies"
    } else {
        "dependencies"
    };
    let path = root.join(MANIFEST);
    let text = std::fs::read_to_string(&path)
        .map_err(|e| Error::new(format!("{}: {e}", path.display())))?;
    let mut doc: toml_edit::DocumentMut = text
        .parse()
        .map_err(|e: toml_edit::TomlError| Error::new(format!("{}: {e}", path.display())))?;
    if doc.get(table_name).is_none() {
        doc[table_name] = toml_edit::table();
    }
    let table = doc[table_name]
        .as_table_mut()
        .ok_or_else(|| Error::new(format!("[{table_name}] is not a table")))?;
    if table.contains_key(&key) {
        return Err(Error::new(format!(
            "[{table_name}] already has `{key}`; give another key with --as"
        )));
    }
    let mut inline = toml_edit::InlineTable::new();
    inline.insert("git", req.url.clone().into());
    inline.insert(reference.0, reference.1.clone().into());
    if let Some(d) = &req.subdir {
        inline.insert("subdir", d.clone().into());
    }
    table.insert(&key, toml_edit::value(inline));
    let new_text = doc.to_string();
    // The edited manifest must still be valid before it is written.
    Manifest::parse(&new_text).map_err(|e| Error::new(format!("{}: {e}", path.display())))?;
    std::fs::write(&path, &new_text).map_err(|e| Error::new(format!("{}: {e}", path.display())))?;
    if !req.dev {
        let refresh = Options {
            refresh: true,
            ..opts.clone()
        };
        if let Err(e) = open(root, &refresh) {
            std::fs::write(&path, &text)
                .map_err(|e| Error::new(format!("{}: {e}", path.display())))?;
            return Err(e);
        }
    }
    Ok((key, format!("{} = \"{}\"", reference.0, reference.1)))
}

/// `quarz cog tree`: the dependency graph, one line per cog and indented
/// by depth (a cog already shown is marked `(*)`).
pub fn tree(movement: &Movement) -> String {
    fn walk(
        m: &Movement,
        i: usize,
        key: Option<&str>,
        depth: usize,
        seen: &mut BTreeSet<usize>,
        out: &mut String,
    ) {
        let c = &m.cogs[i];
        let label = match key {
            Some(k) if k != c.module => format!("{k} = {} {}", c.name, c.version),
            _ => format!("{} {}", c.name, c.version),
        };
        let place = match (&c.source, i) {
            (_, 0) => String::new(),
            (Some(s), _) => format!(" ({s})"),
            (None, _) => format!(" (patched: {})", c.dir.display()),
        };
        let again = !seen.insert(i);
        out.push_str(&format!(
            "{}{label}{place}{}\n",
            "  ".repeat(depth),
            if again { " (*)" } else { "" }
        ));
        if again {
            return;
        }
        for (k, j) in &c.imports {
            walk(m, *j, Some(k), depth + 1, seen, out);
        }
    }
    let mut out = String::new();
    walk(movement, 0, None, 0, &mut BTreeSet::new(), &mut out);
    out
}

/// `quarz cog outdated`: for each locked cog, the newest version tag of
/// its repository when it is newer than the locked version.
pub fn outdated(movement: &Movement) -> Result<Vec<(String, String, String)>, Error> {
    let mut out = Vec::new();
    let Some(lock) = &movement.lock else {
        return Ok(out);
    };
    for c in &lock.cogs {
        let Some(source) = Source::parse_lock_string(&c.source) else {
            continue;
        };
        let refs = git::ls_remote(&source.url)?;
        let newest = refs
            .iter()
            .filter_map(|(n, _)| n.strip_prefix("refs/tags/"))
            .filter_map(Version::parse_tag)
            .filter(|v| v.pre.is_empty())
            .max();
        let locked = Version::parse(&c.version);
        if let (Some(newest), Some(locked)) = (newest, locked) {
            if newest > locked {
                out.push((c.name.clone(), locked.to_string(), newest.to_string()));
            }
        }
    }
    Ok(out)
}

/// `quarz cog verify`: check every locked cog's files in the cache (or
/// `vendor/`) against the lock's hashes; returns the problems found.
pub fn verify(root: &Path) -> Result<Vec<String>, Error> {
    let Some(lock) = Lock::read(root)? else {
        return Err(Error::new("there is no Cog.lock"));
    };
    let manifest = Manifest::read(root)?;
    let opts = Options {
        offline: true,
        ..Options::default()
    };
    let ctx = Ctx::new(root, &manifest, &opts)?;
    let mut problems = Vec::new();
    for c in &lock.cogs {
        let dir = match &ctx.vendor {
            Some(v) => v.join(&c.name),
            None => {
                let subdir = Source::parse_lock_string(&c.source).and_then(|s| s.subdir);
                ctx.src_dir(&c.name, &c.rev, subdir.as_deref())
            }
        };
        match hash::tree_hash(&dir) {
            _ if !dir.join(MANIFEST).is_file() => problems.push(format!(
                "{} {}: not fetched ({})",
                c.name,
                c.version,
                dir.display()
            )),
            Ok(h) if h == c.hash => {}
            Ok(h) => problems.push(format!(
                "{} {}: {} has {h}, Cog.lock says {}",
                c.name,
                c.version,
                dir.display(),
                c.hash
            )),
            Err(e) => problems.push(format!("{} {}: {e}", c.name, c.version)),
        }
    }
    Ok(problems)
}

/// `quarz cog vendor`: copy every locked cog into `vendor/<name>/`. The
/// cogs are resolved and fetched (from the cache, not from the current
/// `vendor/`) and copied into a new directory first; only then does it
/// replace `vendor/`, so a failure leaves the old one as it was.
pub fn vendor(root: &Path, opts: &Options) -> Result<usize, Error> {
    let opts = Options {
        ignore_vendor: true,
        ..opts.clone()
    };
    let movement = open(root, &opts)?;
    let vendor = root.join("vendor");
    let tmp = root.join(format!(".vendor.tmp{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&tmp);
    let filled = (|| {
        std::fs::create_dir_all(&tmp).map_err(|e| Error::new(format!("{}: {e}", tmp.display())))?;
        let mut names = BTreeSet::new();
        for c in movement.cogs.iter().skip(1).filter(|c| c.source.is_some()) {
            if !names.insert(c.name.clone()) {
                return Err(Error::new(format!(
                    "two cogs are named `{}`: vendor/ cannot hold both",
                    c.name
                )));
            }
            copy_tree(&c.dir, &tmp.join(&c.name))?;
        }
        Ok(names.len())
    })();
    let count = match filled {
        Ok(n) => n,
        Err(e) => {
            let _ = std::fs::remove_dir_all(&tmp);
            return Err(e);
        }
    };
    let old = root.join(format!(".vendor.old{}", std::process::id()));
    if vendor.exists() {
        std::fs::rename(&vendor, &old)
            .map_err(|e| Error::new(format!("{}: {e}", vendor.display())))?;
    }
    if let Err(e) = std::fs::rename(&tmp, &vendor) {
        let _ = std::fs::rename(&old, &vendor);
        let _ = std::fs::remove_dir_all(&tmp);
        return Err(Error::new(format!("{}: {e}", vendor.display())));
    }
    // On Unix a read-only file can be removed; elsewhere it must be made
    // writable first (a vendor/ that an older quarz wrote may hold some).
    #[cfg(not(unix))]
    each_file(&old, &mut |p| set_mode(p, true));
    let _ = std::fs::remove_dir_all(&old);
    Ok(count)
}

/// Copy a cog's tree (no symbolic links: `install` refused them).
fn copy_tree(from: &Path, to: &Path) -> Result<(), Error> {
    std::fs::create_dir_all(to).map_err(|e| Error::new(format!("{}: {e}", to.display())))?;
    for entry in
        std::fs::read_dir(from).map_err(|e| Error::new(format!("{}: {e}", from.display())))?
    {
        let entry = entry.map_err(|e| Error::new(e.to_string()))?;
        let path = entry.path();
        let dest = to.join(entry.file_name());
        let ft = entry.file_type().map_err(|e| Error::new(e.to_string()))?;
        if ft.is_dir() {
            copy_tree(&path, &dest)?;
        } else if ft.is_file() {
            std::fs::copy(&path, &dest)
                .map_err(|e| Error::new(format!("{}: {e}", dest.display())))?;
            set_mode(&dest, true);
        } else {
            return Err(Error::new(format!(
                "{}: not a regular file",
                path.display()
            )));
        }
    }
    Ok(())
}

/// The path of the lock file of the application in `root`.
pub fn lock_path(root: &Path) -> PathBuf {
    root.join(LOCK)
}
