//! The check results of each file, kept between runs (docs/05 §2): a
//! file whose source is unchanged, in a program whose files' interfaces
//! are unchanged, is declared again (cheap) but its bodies are not
//! checked again: what checking them recorded is read back, renumbered
//! (`reloc`) for this program.

use std::hash::{Hash, Hasher};
use std::path::PathBuf;

use quarz_syntax::Diagnostic;
use rustc_hash::FxHashMap as HashMap;

use crate::check::{Output, SelfNew};
use crate::reloc::{IdMap, Remap, Table};
use crate::types::*;
use crate::unit::{owned, unit_output, Owner, Owners};
use crate::world::*;

/// What checking a file's bodies recorded.
#[derive(serde::Serialize, serde::Deserialize)]
pub struct Checks {
    pub file: u32,
    /// The keys of the files its numbers refer to, its own first, and
    /// their file numbers where it was checked.
    pub keys: Vec<String>,
    pub key_files: Vec<u32>,
    pub owners: Owners,
    pub output: Output,
    /// Of its own methods and constants, in order: frame sizes and types.
    pub frames: Vec<u32>,
    pub const_types: Vec<Option<Type>>,
    pub narrowed: Vec<(TypeParamId, TypeParamId, Type)>,
    pub self_news: Vec<SelfNew>,
    pub frame_size: u32,
    pub warnings: Vec<Diagnostic>,
    /// The constants' types of the whole program when it was checked
    /// (`const_types`): they are inferred, so not in the interfaces the
    /// key holds, and a file that uses another's constant is checked
    /// again when that changed.
    pub consts_seen: u64,
}

/// The constants' types of every file, inferred from their initializers.
pub fn const_types(world: &World, key: &dyn Fn(u32) -> String) -> u64 {
    let mut all: Vec<(String, String, Option<String>)> = world
        .consts
        .iter()
        .filter(|c| c.file != 0)
        .map(|c| {
            (
                key(c.file),
                c.name.clone(),
                c.ty.as_ref().map(|t| world.type_name(t)),
            )
        })
        .collect();
    // (Type numbers differ between programs: compared by name.)
    all.sort();
    hash(&all)
}

/// `t` without positions, for comparing declarations.
fn unplaced(t: &mut quarz_syntax::ast::TypeExpr) {
    use quarz_syntax::ast::TypeExprKind as K;
    t.span = Default::default();
    match &mut t.kind {
        K::Named { args, .. } | K::Union(args) | K::Tuple(args) => {
            args.iter_mut().for_each(unplaced)
        }
        K::Nilable(x) => unplaced(x),
        K::Proc {
            recv, params, ret, ..
        } => {
            if let Some(r) = recv {
                unplaced(r);
            }
            params.iter_mut().for_each(unplaced);
            unplaced(ret);
        }
        K::SelfType | K::Nothing | K::Void => {}
    }
}

/// The directory of the cache: `$QUARZ_CACHE_DIR`, or `quarz` in
/// `$XDG_CACHE_HOME` or `~/.cache`; none when `QUARZ_NO_CACHE` is set.
pub fn dir() -> Option<PathBuf> {
    if std::env::var_os("QUARZ_NO_CACHE").is_some_and(|v| v != "0") {
        return None;
    }
    if let Some(d) = std::env::var_os("QUARZ_CACHE_DIR") {
        return (!d.is_empty()).then(|| PathBuf::from(d));
    }
    let base = std::env::var_os("XDG_CACHE_HOME")
        .map(PathBuf::from)
        .or_else(|| std::env::var_os("HOME").map(|h| PathBuf::from(h).join(".cache")))?;
    Some(base.join("quarz"))
}

static BUILD: std::sync::OnceLock<String> = std::sync::OnceLock::new();

/// The compiler's build, part of every key (what an older build wrote is
/// not read). Without it, nothing is cached.
pub fn set_build(id: &str) {
    let _ = BUILD.set(id.to_string());
}

pub fn build() -> Option<&'static str> {
    BUILD.get().map(String::as_str)
}

pub fn hash<T: serde::Serialize>(x: &T) -> u64 {
    let bytes = bincode::serde::encode_to_vec(x, bincode::config::standard()).unwrap_or_default();
    let mut h = rustc_hash::FxHasher::default();
    bytes.hash(&mut h);
    h.finish()
}

/// The interface of file `file`: its entities' declarations, without
/// bodies, defaults' and constants' values, or positions. What another
/// file's check may depend on.
pub fn interface(world: &World, file: u32) -> u64 {
    let dummy = || {
        std::rc::Rc::new(quarz_syntax::ast::Expr {
            id: 0,
            span: Default::default(),
            kind: quarz_syntax::ast::ExprKind::Nil,
        })
    };
    let own = owned(world);
    let mut h = rustc_hash::FxHasher::default();
    let get = |m: &HashMap<u32, Vec<u32>>| m.get(&file).cloned().unwrap_or_default();
    for c in get(&own.classes) {
        let mut c = world.class(c).clone();
        c.span = Default::default();
        c.shareable = None;
        c.observable = None;
        // (A `using`'s position matters to its own file only, whose key
        // has its source: `Checker::usings_at`.)
        for u in &mut c.usings {
            u.0 = 0;
        }
        for f in &mut c.fields {
            f.span = Default::default();
            f.default = f.default.as_ref().map(|_| dummy());
        }
        hash(&c).hash(&mut h);
    }
    for m in get(&own.methods) {
        let mut m = world.method(m).clone();
        m.span = Default::default();
        m.body = None;
        m.checked = false;
        m.frame_size = 0;
        // A generated method's function number depends on what was
        // lowered before it, not on the interface; positions are not
        // part of it either.
        if let Some(g) = &mut m.generated {
            g.func = 0;
            g.by.1 = Default::default();
            g.block = Default::default();
        }
        for p in &mut m.params {
            p.span = Default::default();
            p.default = p.default.as_ref().map(|_| dummy());
        }
        hash(&m).hash(&mut h);
    }
    for c in get(&own.consts) {
        let mut c = world.consts[c as usize].clone();
        c.span = Default::default();
        c.value = None;
        c.checking = false;
        hash(&c).hash(&mut h);
    }
    for a in get(&own.aliases) {
        let mut a = world.aliases[a as usize].clone();
        unplaced(&mut a.expr);
        let params: Vec<String> = a.type_params.iter().map(|p| p.name.clone()).collect();
        hash(&(a.name, a.owner, params, a.expr)).hash(&mut h);
    }
    for e in get(&own.extensions) {
        let mut e = world.extensions[e as usize].clone();
        e.span = Default::default();
        hash(&e).hash(&mut h);
    }
    h.finish()
}

/// The movement's cogs as declared: names, root modules and the
/// dependencies in their scopes (the application's are top-level names).
pub fn cogs(world: &World) -> u64 {
    let all: Vec<_> = world
        .cogs
        .iter()
        .map(|c| {
            let mut imports: Vec<_> = c.imports.iter().collect();
            imports.sort();
            let root = c.root.map(|r| (r, world.class(r).name.as_str()));
            (c.name.as_str(), root, imports)
        })
        .collect();
    let roots: Vec<ClassId> = world.cogs.iter().filter_map(|c| c.root).collect();
    let mut app: Vec<(&String, ClassId)> = world
        .top
        .iter()
        .filter_map(|(k, m)| match m {
            Member::Class(c) if roots.contains(c) => Some((k, *c)),
            _ => None,
        })
        .collect();
    app.sort();
    hash(&(all, app))
}

/// Take out what checking file `file`'s bodies recorded.
#[allow(clippy::too_many_arguments)]
pub fn extract(
    world: &World,
    out: &Output,
    self_news: &[SelfNew],
    file: u32,
    base: u32,
    warnings: Vec<Diagnostic>,
    consts_seen: u64,
    key: &dyn Fn(u32) -> String,
) -> Checks {
    let (keys, key_files, owners) = crate::unit::owners(world, file, key);
    let own = owned(world);
    let get = |m: &HashMap<u32, Vec<u32>>| m.get(&file).cloned().unwrap_or_default();
    let output = unit_output(world, out, base, file);
    let mut narrowed = Vec::new();
    crate::unit::collect_narrowed(world, &output, &mut narrowed);
    Checks {
        file,
        keys,
        key_files,
        owners,
        frames: get(&own.methods)
            .iter()
            .map(|m| world.method(*m).frame_size)
            .collect(),
        const_types: get(&own.consts)
            .iter()
            .map(|c| world.consts[*c as usize].ty.clone())
            .collect(),
        narrowed,
        self_news: self_news
            .iter()
            .filter(|s| world.method(s.2).file == file)
            .cloned()
            .collect(),
        frame_size: out
            .unit_frame_sizes
            .get(file as usize)
            .copied()
            .unwrap_or(0),
        output,
        warnings,
        consts_seen,
    }
}

/// Read `checks` back for file `file` of this program (declared again
/// from its unchanged source), whose files' numbers by key `files` says.
/// `None` when something it refers to is not there.
pub fn apply(
    world: &mut World,
    out: &mut Output,
    self_news: &mut Vec<SelfNew>,
    mut checks: Checks,
    file: u32,
    files: &dyn Fn(&str) -> Option<u32>,
) -> Option<Vec<Diagnostic>> {
    let own = owned(world);
    let fs: Vec<u32> = checks
        .keys
        .iter()
        .map(|k| files(k))
        .collect::<Option<_>>()?;
    if fs.first() != Some(&file) || checks.key_files.len() != fs.len() {
        return None;
    }
    let table = |owners: &[Owner], list: &HashMap<u32, Vec<u32>>| -> Option<Table> {
        let mut map = Vec::with_capacity(owners.len());
        for (n, o) in owners.iter().enumerate() {
            map.push(match o {
                Owner::Prelude => n as u32,
                Owner::Unit(k, i) => *list.get(fs.get(*k as usize)?)?.get(*i as usize)?,
            });
        }
        Some(Table { base: 0, map })
    };
    let mut params: HashMap<u32, u32> = HashMap::default();
    for (p, o) in &checks.owners.type_params {
        let new = match o {
            Owner::Prelude => *p,
            Owner::Unit(k, i) => *own
                .type_params
                .get(fs.get(*k as usize)?)?
                .get(*i as usize)?,
        };
        params.insert(*p, new);
    }
    let mut file_map: Vec<u32> =
        (0..=checks.key_files.iter().copied().max().unwrap_or(0)).collect();
    for (k, f) in checks.key_files.iter().enumerate() {
        file_map[*f as usize] = fs[k];
    }
    let mut map = IdMap {
        classes: table(&checks.owners.classes, &own.classes)?,
        methods: table(&checks.owners.methods, &own.methods)?,
        consts: table(&checks.owners.consts, &own.consts)?,
        type_params: crate::unit::param_table(&params),
        files: Table {
            base: 0,
            map: file_map,
        },
    };
    for (p, base, mut bound) in std::mem::take(&mut checks.narrowed) {
        let base = params.get(&base).copied().unwrap_or(base);
        map.type_params = crate::unit::param_table(&params);
        bound.remap(&map);
        if let Type::Param(id) = world.narrowed_param(base, &bound) {
            params.insert(p, id);
        }
    }
    map.type_params = crate::unit::param_table(&params);
    let methods = own.methods.get(&file).cloned().unwrap_or_default();
    if methods.len() != checks.frames.len() {
        return None;
    }
    for (m, f) in methods.iter().zip(&checks.frames) {
        let info = world.method_mut(*m);
        info.frame_size = *f;
        info.checked = true;
    }
    let consts = own.consts.get(&file).cloned().unwrap_or_default();
    if consts.len() != checks.const_types.len() {
        return None;
    }
    for (c, t) in consts.iter().zip(std::mem::take(&mut checks.const_types)) {
        let mut t = t;
        t.remap(&map);
        world.consts[*c as usize].ty = t;
    }
    let mut o = std::mem::take(&mut checks.output);
    o.remap(&map);
    crate::unit::merge_output(out, o);
    if out.unit_frame_sizes.len() <= file as usize {
        out.unit_frame_sizes.resize(file as usize + 1, 0);
    }
    out.unit_frame_sizes[file as usize] = checks.frame_size;
    for (c, i, x, s, f) in std::mem::take(&mut checks.self_news) {
        self_news.push((
            map.classes.get(c),
            i.map(|i| map.methods.get(i)),
            map.methods.get(x),
            s,
            map.files.get(f),
        ));
    }
    Some(checks.warnings)
}

fn checksum(bytes: &[u8]) -> u64 {
    let mut h = rustc_hash::FxHasher::default();
    bytes.hash(&mut h);
    h.finish()
}

/// Where the checks with this key are kept.
fn path(key: u64) -> Option<PathBuf> {
    Some(dir()?.join("checks").join(format!("{key:016x}.bin")))
}

/// The key of a file's checks: the build, the file's syntax, and every
/// file's interface in this program.
pub fn key(program: &quarz_syntax::ast::Program, interfaces: u64) -> Option<u64> {
    let build = build()?;
    Some(hash(&(build, program, interfaces)))
}

/// Read the checks kept under `key`. (Its syntax, in the key, holds the
/// file's node ids and spans: checks read back are for the same range.)
pub fn load(key: u64) -> Option<Checks> {
    let p = path(key)?;
    let bytes = std::fs::read(&p).ok()?;
    let (sum, body): (u64, Vec<u8>) =
        bincode::serde::decode_from_slice(&bytes, bincode::config::standard())
            .ok()?
            .0;
    // (A damaged file is a miss.)
    if checksum(&body) != sum {
        return None;
    }
    let checks = bincode::serde::decode_from_slice(&body, bincode::config::standard())
        .ok()
        .map(|(c, _)| c)?;
    // (Its time says when it was last used: `sweep`.)
    if let Ok(f) = std::fs::File::options().append(true).open(&p) {
        let _ = f.set_modified(std::time::SystemTime::now());
    }
    Some(checks)
}

/// Entries unused for this long are removed.
const UNUSED: std::time::Duration = std::time::Duration::from_secs(30 * 24 * 60 * 60);

/// Remove the entries unused for `UNUSED` (and files left half written),
/// at most once a day: the time of the file `swept` says when it last ran.
fn sweep(dir: &std::path::Path) {
    let now = std::time::SystemTime::now();
    let age = |m: &std::fs::Metadata| {
        m.modified()
            .ok()
            .and_then(|t| now.duration_since(t).ok())
            .unwrap_or_default()
    };
    let mark = dir.join("swept");
    match std::fs::metadata(&mark) {
        Ok(m) if age(&m) < std::time::Duration::from_secs(24 * 60 * 60) => return,
        Ok(_) => {}
        // (A new directory: nothing to remove yet.)
        Err(_) => {
            let _ = std::fs::write(&mark, "");
            return;
        }
    }
    let _ = std::fs::write(&mark, "");
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for e in entries.flatten() {
        let p = e.path();
        let ours = p
            .extension()
            .is_some_and(|x| x == "bin" || x.to_str().is_some_and(|x| x.starts_with("tmp")));
        if ours && e.metadata().is_ok_and(|m| age(&m) > UNUSED) {
            let _ = std::fs::remove_file(p);
        }
    }
}

/// Keep `checks` under `key`.
pub fn store(key: u64, checks: &Checks) {
    let Some(p) = path(key) else { return };
    let Ok(body) = bincode::serde::encode_to_vec(checks, bincode::config::standard()) else {
        return;
    };
    let Ok(bytes) =
        bincode::serde::encode_to_vec((checksum(&body), body), bincode::config::standard())
    else {
        return;
    };
    if let Some(d) = p.parent() {
        let _ = std::fs::create_dir_all(d);
        sweep(d);
    }
    // Written aside and renamed, so that a reader never sees half of it.
    let tmp = p.with_extension(format!("tmp{}", std::process::id()));
    if std::fs::write(&tmp, bytes).is_ok() {
        let _ = std::fs::rename(&tmp, &p);
    }
}
