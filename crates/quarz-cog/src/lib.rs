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
}

/// A movement: the application (`cogs[0]`) and every cog it brings in.
#[derive(Clone, Debug)]
pub struct Movement {
    /// The directory of the application's `Cog.toml`.
    pub root: PathBuf,
    pub cogs: Vec<CogEntry>,
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
    if manifest.dependencies.is_empty() && existing.is_none() {
        return ctx
            .movement_from_lock(&manifest, &empty_lock())
            .map_err(|p| match p {
                LockProblem::Stale(s) | LockProblem::Fatal(Error(s)) => Error(s),
            });
    }
    if !opts.refresh {
        if let Some(lock) = &existing {
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
    let lock = ctx.resolve(&manifest)?;
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
        let vendor = Some(root.join("vendor")).filter(|v| v.is_dir());
        Ok(Ctx {
            root,
            cache: cache_dir(),
            opts,
            patches,
            vendor,
            remotes: HashMap::new(),
        })
    }

    /// Build the movement from `lock`: every cog the manifests reach must
    /// be in it (or patched) and satisfy what the application and the
    /// patched cogs ask for (the locked cogs' own requirements held when
    /// the lock was resolved, and their manifests are pinned). The lock
    /// returned in the movement is `lock` restricted to what was reached.
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
            source: None,
            rev: None,
        }];
        let mut manifests = vec![manifest.clone()];
        let mut index: HashMap<Source, usize> = HashMap::new();
        let mut reached: BTreeSet<Source> = BTreeSet::new();
        // Every requirement on a locked cog, from every manifest reached.
        let mut wanted: HashMap<Source, Vec<Ref>> = HashMap::new();
        let mut next = 0;
        while next < cogs.len() {
            let i = next;
            next += 1;
            // The application and patched cogs: their requirements are
            // checked against the lock.
            let checked = i == 0 || cogs[i].source.is_none();
            let deps: Vec<(String, Dependency)> = manifests[i]
                .dependencies
                .iter()
                .map(|(k, d)| (k.clone(), d.clone()))
                .collect();
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
                            reached.insert(source.clone());
                            let entry = CogEntry {
                                name: m.cog.name.clone(),
                                version: locked.version.clone(),
                                module: m.module(),
                                dir,
                                imports: Vec::new(),
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
                wanted
                    .entry(source.clone())
                    .or_default()
                    .push(dep.reference());
                if checked {
                    if let Some(locked) = by_source.get(&source) {
                        if !self.patches.contains_key(&source) {
                            satisfies(&dep, locked).map_err(LockProblem::Stale)?;
                        }
                    }
                }
                cogs[i].imports.push((key, j));
            }
        }
        // Minimal version selection picks the highest version asked for: a
        // lock holding a higher one than every requirement names (one that
        // was dropped) is stale. A requirement by a branch, or by another
        // commit, has a version only git can tell; it is taken as met.
        for (source, refs) in &wanted {
            let Some(locked) = by_source.get(source) else {
                continue;
            };
            if self.patches.contains_key(source) {
                continue;
            }
            let Some(have) = Version::parse(&locked.version) else {
                continue;
            };
            let mut highest: Option<Version> = None;
            let mut all_known = true;
            for r in refs {
                let v = match r {
                    Ref::Tag(t) => Version::parse_tag(t),
                    Ref::Rev(rev) if *rev == locked.rev => Some(have.clone()),
                    _ => None,
                };
                match v {
                    Some(v) => highest = highest.max(Some(v)),
                    None => all_known = false,
                }
            }
            if let Some(h) = highest {
                if all_known && h != have {
                    return Err(LockProblem::Stale(format!(
                        "{source} is locked at {have}, but the highest version asked for is {h}"
                    )));
                }
            }
        }
        let pruned = Lock {
            version: 1,
            cogs: lock
                .cogs
                .iter()
                .filter(|c| {
                    Source::parse_lock_string(&c.source).is_some_and(|s| reached.contains(&s))
                })
                .cloned()
                .collect(),
        };
        Ok(Movement {
            root: self.root.to_path_buf(),
            cogs,
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
                let dir = self.src_dir(&locked.name, &locked.rev);
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
                    self.export(&mirror, &locked.rev, source.subdir.as_deref(), &dir)?;
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

    fn src_dir(&self, name: &str, rev: &str) -> PathBuf {
        let short: String = rev.chars().take(12).collect();
        self.cache.join("src").join(format!("{name}-{short}"))
    }

    fn log(&self, message: &str) {
        if self.opts.verbose {
            eprintln!("quarz: {message}");
        }
    }

    /// Write a commit's tree into `dest` (through a temporary directory, so
    /// that a tree is never seen half written), its files read-only.
    fn export(
        &self,
        mirror: &Mirror,
        rev: &str,
        subdir: Option<&str>,
        dest: &Path,
    ) -> Result<(), Error> {
        let tmp = dest.with_extension(format!("tmp{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&tmp);
        mirror.export(rev, subdir, &tmp)?;
        if !tmp.join(MANIFEST).is_file() {
            let _ = std::fs::remove_dir_all(&tmp);
            return Err(Error::new(format!(
                "{} has no Cog.toml at {rev}{}",
                mirror.url,
                subdir.map(|d| format!(" in {d}")).unwrap_or_default()
            )));
        }
        set_read_only(&tmp);
        if dest.exists() {
            let _ = std::fs::remove_dir_all(&tmp);
            return Ok(());
        }
        std::fs::rename(&tmp, dest).map_err(|e| Error::new(format!("{}: {e}", dest.display())))
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
                let refs = self.remote_refs(&source.url)?;
                let commit = find(refs, &format!("refs/heads/{branch}")).ok_or_else(|| {
                    Error::new(format!("{} has no branch `{branch}`", source.url))
                })?;
                let v = version_of(&mirror, &commit)?;
                Ok((commit, v))
            }
            Ref::Head => {
                let refs = self.remote_refs(&source.url)?;
                let commit = find(refs, "HEAD")
                    .ok_or_else(|| Error::new(format!("{} has no default branch", source.url)))?;
                let v = version_of(&mirror, &commit)?;
                Ok((commit, v))
            }
            Ref::Rev(rev) => {
                let v = version_of(&mirror, rev)?;
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
        // (who asks, the manifest is the application's or a patched cog's, dependency)
        let mut queue: Vec<(String, bool, Dependency)> = manifest
            .dependencies
            .values()
            .map(|d| ("the application".to_string(), true, d.clone()))
            .collect();
        let mut patched_seen: BTreeSet<Source> = BTreeSet::new();
        // Located references, so that a branch is read once.
        let mut located: HashMap<(Source, Ref), (String, Version)> = HashMap::new();
        while let Some((from, _, dep)) = queue.pop() {
            let source = dep.source();
            if let Some(dir) = self.patches.get(&source).cloned() {
                if patched_seen.insert(source.clone()) {
                    let m = Manifest::read(&dir)?;
                    for d in m.dependencies.values() {
                        queue.push((m.cog.name.clone(), false, d.clone()));
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
            for d in m.dependencies.values() {
                queue.push((format!("{} {version}", m.cog.name), false, d.clone()));
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
            for dep in m.dependencies.values() {
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
        let mut cogs = Vec::new();
        for source in &reached {
            let (version, rev) = &chosen[source];
            let node = &nodes[&(source.clone(), rev.clone())];
            let dir = self.src_dir(&node.manifest.cog.name, rev);
            if !dir.join(MANIFEST).is_file() {
                let mirror = Mirror::open(&self.cache, &source.url)?;
                self.log(&format!("fetching {} {version}", node.manifest.cog.name));
                mirror.fetch_commit(rev)?;
                self.export(&mirror, rev, source.subdir.as_deref(), &dir)?;
            }
            let hash =
                hash::tree_hash(&dir).map_err(|e| Error::new(format!("{}: {e}", dir.display())))?;
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
        Ok(Lock { version: 1, cogs })
    }
}

/// Whether a locked cog meets a dependency of the application (or of a
/// patched cog).
fn satisfies(dep: &Dependency, locked: &LockedCog) -> Result<(), String> {
    let source = dep.source();
    let have = Version::parse(&locked.version)
        .ok_or_else(|| format!("bad version `{}` for {source}", locked.version))?;
    match dep.reference() {
        Ref::Tag(tag) => {
            let want = Version::parse_tag(&tag).unwrap();
            if have < want || !have.compatible(&want) {
                return Err(format!(
                    "{source} is locked at {have}, the manifest asks for {tag}"
                ));
            }
        }
        Ref::Rev(rev) => {
            if locked.rev != rev {
                return Err(format!(
                    "{source} is locked at {}, the manifest asks for {rev}",
                    locked.rev
                ));
            }
        }
        Ref::Branch(_) | Ref::Head => {}
    }
    Ok(())
}

fn describe_ref(r: &Ref) -> String {
    match r {
        Ref::Tag(t) => format!("tag {t}"),
        Ref::Rev(r) => format!("rev {}", &r[..r.len().min(12)]),
        Ref::Branch(b) => format!("branch {b}"),
        Ref::Head => "the default branch".to_string(),
    }
}

/// The version of a commit: the highest version tag naming it, or a
/// pseudo-version from the nearest tag among its ancestors.
fn version_of(mirror: &Mirror, rev: &str) -> Result<Version, Error> {
    mirror.fetch_history(rev)?;
    let mut tagged: Vec<Version> = mirror
        .tags_at(rev)?
        .iter()
        .filter_map(|t| Version::parse_tag(t))
        .collect();
    tagged.sort();
    if let Some(v) = tagged.pop() {
        return Ok(v);
    }
    let base = mirror.nearest_tag(rev).and_then(|t| Version::parse_tag(&t));
    let time = mirror.commit_time(rev)?;
    Ok(Version::pseudo(base.as_ref(), time, rev))
}

fn set_read_only(dir: &Path) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            set_read_only(&path);
        } else if let Ok(meta) = std::fs::metadata(&path) {
            let mut perms = meta.permissions();
            perms.set_readonly(true);
            let _ = std::fs::set_permissions(&path, perms);
        }
    }
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
        let tagged = version.pre.is_empty()
            && Mirror::open(&ctx.cache, &source.url)?
                .tags_at(&rev)?
                .contains(&version.tag());
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
            None => ctx.src_dir(&c.name, &c.rev),
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

/// `quarz cog vendor`: copy every locked cog into `vendor/<name>/`.
pub fn vendor(root: &Path, opts: &Options) -> Result<usize, Error> {
    // Read the cogs from the cache, not from a previous vendor/.
    let vendor = root.join("vendor");
    if vendor.exists() {
        make_writable(&vendor);
        std::fs::remove_dir_all(&vendor)
            .map_err(|e| Error::new(format!("{}: {e}", vendor.display())))?;
    }
    let movement = open(root, opts)?;
    let mut names = BTreeSet::new();
    let mut count = 0;
    for c in movement.cogs.iter().skip(1).filter(|c| c.source.is_some()) {
        if !names.insert(c.name.clone()) {
            return Err(Error::new(format!(
                "two cogs are named `{}`: vendor/ cannot hold both",
                c.name
            )));
        }
        copy_tree(&c.dir, &vendor.join(&c.name))?;
        count += 1;
    }
    Ok(count)
}

fn copy_tree(from: &Path, to: &Path) -> Result<(), Error> {
    std::fs::create_dir_all(to).map_err(|e| Error::new(format!("{}: {e}", to.display())))?;
    for entry in
        std::fs::read_dir(from).map_err(|e| Error::new(format!("{}: {e}", from.display())))?
    {
        let entry = entry.map_err(|e| Error::new(e.to_string()))?;
        let path = entry.path();
        let dest = to.join(entry.file_name());
        if path.is_dir() {
            copy_tree(&path, &dest)?;
        } else {
            std::fs::copy(&path, &dest)
                .map_err(|e| Error::new(format!("{}: {e}", dest.display())))?;
            if let Ok(meta) = std::fs::metadata(&dest) {
                let mut perms = meta.permissions();
                #[allow(clippy::permissions_set_readonly_false)]
                perms.set_readonly(false);
                let _ = std::fs::set_permissions(&dest, perms);
            }
        }
    }
    Ok(())
}

fn make_writable(dir: &Path) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            make_writable(&path);
        } else if let Ok(meta) = std::fs::metadata(&path) {
            let mut perms = meta.permissions();
            #[allow(clippy::permissions_set_readonly_false)]
            perms.set_readonly(false);
            let _ = std::fs::set_permissions(&path, perms);
        }
    }
}

/// The path of the lock file of the application in `root`.
pub fn lock_path(root: &Path) -> PathBuf {
    root.join(LOCK)
}
