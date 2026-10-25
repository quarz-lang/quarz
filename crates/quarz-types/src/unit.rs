//! A unit's interface file (`.qzi`, docs/05 §2): what checking one file
//! added to the world, taken out of the program it was checked in
//! (`extract`) and read back into another (`apply`), renumbered
//! (`reloc`).

use rustc_hash::{FxHashMap as HashMap, FxHashSet as HashSet};

use crate::check::{Output, SelfNew};
use crate::reloc::{IdMap, Remap, Table};
use crate::types::*;
use crate::world::*;
use crate::CheckedUnit;

/// Whose an entity is: the prelude's (numbered the same in every
/// program) or a unit's, by its key and its position among that unit's
/// own of its kind.
#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum Owner {
    Prelude,
    Unit(u32, u32),
}

/// The owners of every number of one kind in the program a unit was
/// checked in (prelude numbers included, as `Owner::Prelude`).
#[derive(Clone, Debug, Default, serde::Serialize, serde::Deserialize)]
pub struct Owners {
    pub classes: Vec<Owner>,
    pub methods: Vec<Owner>,
    pub consts: Vec<Owner>,
    pub aliases: Vec<Owner>,
    pub extensions: Vec<Owner>,
    /// Type parameters of declared entities (narrowed ones are made
    /// again: `UnitDelta::narrowed`).
    pub type_params: HashMap<TypeParamId, Owner>,
}

/// What checking a unit added.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct UnitDelta {
    /// The unit's file number and syntax range where it was checked.
    pub file: u32,
    pub base: u32,
    /// The keys of the units its numbers refer to (`Owner::Unit`), its
    /// own first.
    pub keys: Vec<String>,
    /// Their file numbers where it was checked.
    pub key_files: Vec<u32>,
    pub owners: Owners,
    pub classes: Vec<ClassInfo>,
    pub methods: Vec<MethodInfo>,
    pub consts: Vec<ConstInfo>,
    pub aliases: Vec<TypeAliasInfo>,
    pub extensions: Vec<ExtensionInfo>,
    /// Its own type parameters, in order: number, name, lower bound.
    pub type_params: Vec<(TypeParamId, String, Option<Type>)>,
    /// Narrowed type parameters (`T & C`) its results mention: number,
    /// the parameter and the bound.
    pub narrowed: Vec<(TypeParamId, TypeParamId, Type)>,
    pub top: Vec<(String, Member)>,
    /// Names it adds to namespaces it does not own (`class Geo::Line`),
    /// and extensions it declares in them.
    pub members: Vec<(ClassId, String, Member)>,
    pub ns_extensions: Vec<(ClassId, ExtensionId)>,
    pub group: Option<UnitGroup>,
    pub std: bool,
    pub app_names: Vec<String>,
    pub ext_impls: Vec<(ClassId, MethodId, MethodId)>,
    pub docs: Vec<quarz_syntax::doc::Doc>,
    pub output: Output,
    pub frame_size: u32,
    pub self_news: Vec<SelfNew>,
    pub unit: CheckedUnit,
}

/// The entities of each kind each file owns, in order.
#[derive(Default)]
pub(crate) struct Owned {
    pub(crate) classes: HashMap<u32, Vec<ClassId>>,
    pub(crate) methods: HashMap<u32, Vec<MethodId>>,
    pub(crate) consts: HashMap<u32, Vec<ConstId>>,
    pub(crate) aliases: HashMap<u32, Vec<u32>>,
    pub(crate) extensions: HashMap<u32, Vec<ExtensionId>>,
    pub(crate) type_params: HashMap<u32, Vec<TypeParamId>>,
}

pub(crate) fn owned(world: &World) -> Owned {
    let mut o = Owned::default();
    for c in &world.classes {
        o.classes.entry(c.file).or_default().push(c.id);
    }
    for m in &world.methods {
        o.methods.entry(m.file).or_default().push(m.id);
    }
    for c in &world.consts {
        o.consts.entry(c.file).or_default().push(c.id);
    }
    for (i, a) in world.aliases.iter().enumerate() {
        o.aliases.entry(a.file).or_default().push(i as u32);
    }
    for e in &world.extensions {
        o.extensions.entry(e.file).or_default().push(e.id);
    }
    // Type parameters, by the entity that declares them.
    let mut params: Vec<(TypeParamId, u32)> = Vec::new();
    for c in &world.classes {
        params.extend(c.type_params.iter().map(|p| (p.id, c.file)));
    }
    for m in &world.methods {
        params.extend(m.type_params.iter().map(|p| (p.id, m.file)));
    }
    for e in &world.extensions {
        params.extend(e.type_params.iter().map(|p| (p.id, e.file)));
    }
    for a in &world.aliases {
        params.extend(a.type_params.iter().map(|p| (p.id, a.file)));
    }
    params.sort_unstable();
    params.dedup();
    for (p, f) in params {
        o.type_params.entry(f).or_default().push(p);
    }
    o
}

fn owners_of(list: &HashMap<u32, Vec<u32>>, count: usize, keys: &mut Keys) -> Vec<Owner> {
    let mut out = vec![Owner::Prelude; count];
    for (file, ids) in list {
        if *file == 0 {
            continue;
        }
        let k = keys.index(*file);
        for (i, id) in ids.iter().enumerate() {
            if let Some(slot) = out.get_mut(*id as usize) {
                *slot = Owner::Unit(k, i as u32);
            }
        }
    }
    out
}

/// The unit keys a delta names, by file.
struct Keys<'a> {
    names: &'a dyn Fn(u32) -> String,
    files: Vec<u32>,
}

impl Keys<'_> {
    fn index(&mut self, file: u32) -> u32 {
        match self.files.iter().position(|f| *f == file) {
            Some(i) => i as u32,
            None => {
                self.files.push(file);
                (self.files.len() - 1) as u32
            }
        }
    }
}

fn in_range(n: u32, base: u32) -> bool {
    n >= base && n - base < 1 << crate::load::UNIT_BITS
}

/// Take out what checking file `file` (of syntax range `base`) added.
/// `key` names each file's unit (its path, or `<std:name>`).
pub fn extract(
    world: &World,
    out: &Output,
    self_news: &[SelfNew],
    unit: &CheckedUnit,
    base: u32,
    key: &dyn Fn(u32) -> String,
) -> UnitDelta {
    let file = unit.file;
    let own = owned(world);
    let (keys, key_files, owners) = owners(world, file, key);
    let pick = |list: &HashMap<u32, Vec<u32>>| list.get(&file).cloned().unwrap_or_default();
    let classes: Vec<ClassInfo> = pick(&own.classes)
        .iter()
        .map(|c| world.class(*c).clone())
        .collect();
    let methods: Vec<MethodInfo> = pick(&own.methods)
        .iter()
        .map(|m| world.method(*m).clone())
        .collect();
    let consts: Vec<ConstInfo> = pick(&own.consts)
        .iter()
        .map(|c| world.consts[*c as usize].clone())
        .collect();
    let aliases: Vec<TypeAliasInfo> = pick(&own.aliases)
        .iter()
        .map(|a| world.aliases[*a as usize].clone())
        .collect();
    let extensions: Vec<ExtensionInfo> = pick(&own.extensions)
        .iter()
        .map(|e| world.extensions[*e as usize].clone())
        .collect();
    let type_params = pick(&own.type_params)
        .iter()
        .map(|p| {
            (
                *p,
                world.type_param_names.get(p).cloned().unwrap_or_default(),
                world.lower_bounds.get(p).cloned(),
            )
        })
        .collect();
    let owns = |m: &Member| match m {
        Member::Class(c) => world.class(*c).file == file,
        Member::Const(c) => world.consts[*c as usize].file == file,
        Member::Alias(a) => world.aliases[*a as usize].file == file,
    };
    let top: Vec<(String, Member)> = world
        .top
        .iter()
        .filter(|(_, m)| owns(m))
        .map(|(n, m)| (n.clone(), *m))
        .collect();
    let mut members = Vec::new();
    let mut ns_extensions = Vec::new();
    for c in &world.classes {
        if c.file == file {
            continue;
        }
        for (n, m) in &c.members {
            if owns(m) {
                members.push((c.id, n.clone(), *m));
            }
        }
        for e in &c.extensions {
            if world.extensions[*e as usize].file == file {
                ns_extensions.push((c.id, *e));
            }
        }
    }
    let owned_class = |c: ClassId| world.class(c).file == file;
    let owned_method = |m: MethodId| world.method(m).file == file;
    let ext_impls = world
        .ext_impls
        .iter()
        .filter(|(c, _, i)| owned_class(*c) || owned_method(*i))
        .copied()
        .collect();
    let app_names = top_names(&top);
    let docs = world
        .docs
        .iter()
        .filter(|d| in_range(d.span.start, base))
        .cloned()
        .collect();
    let output = unit_output(world, out, base, file);
    let mut narrowed = Vec::new();
    collect_narrowed(world, &output, &mut narrowed);
    let frame_size = out
        .unit_frame_sizes
        .get(file as usize)
        .copied()
        .unwrap_or(0);
    let self_news = self_news
        .iter()
        .filter(|(_, _, m, _, _)| owned_method(*m))
        .cloned()
        .collect();
    UnitDelta {
        file,
        base,
        keys,
        key_files,
        owners,
        classes,
        methods,
        consts,
        aliases,
        extensions,
        type_params,
        narrowed,
        top,
        members,
        ns_extensions,
        group: world.file_groups.get(&file).copied(),
        std: world.std_files.contains(&file),
        app_names,
        ext_impls,
        docs,
        output,
        frame_size,
        self_news,
        unit: unit.clone(),
    }
}

/// Whose each number of `world` is, for the units file `file`'s checks
/// refer to: their keys (its own first), their files, and the owners.
pub(crate) fn owners(
    world: &World,
    file: u32,
    key: &dyn Fn(u32) -> String,
) -> (Vec<String>, Vec<u32>, Owners) {
    let own = owned(world);
    let mut keys = Keys {
        names: key,
        files: vec![file],
    };
    let owners = Owners {
        classes: owners_of(&own.classes, world.classes.len(), &mut keys),
        methods: owners_of(&own.methods, world.methods.len(), &mut keys),
        consts: owners_of(&own.consts, world.consts.len(), &mut keys),
        aliases: owners_of(&own.aliases, world.aliases.len(), &mut keys),
        extensions: owners_of(&own.extensions, world.extensions.len(), &mut keys),
        type_params: {
            let mut t = HashMap::default();
            for (f, ids) in &own.type_params {
                if *f == 0 {
                    continue;
                }
                let k = keys.index(*f);
                for (i, p) in ids.iter().enumerate() {
                    t.insert(*p, Owner::Unit(k, i as u32));
                }
            }
            t
        },
    };
    let names = keys.files.iter().map(|f| (keys.names)(*f)).collect();
    (names, keys.files, owners)
}

fn top_names(top: &[(String, Member)]) -> Vec<String> {
    top.iter().map(|(n, _)| n.clone()).collect()
}

/// The entries of `out` for the syntax of the unit at `base`.
pub(crate) fn unit_output(world: &World, out: &Output, base: u32, file: u32) -> Output {
    use crate::check::SelfOwner;
    let mine = |n: &u32| in_range(*n, base);
    let span_mine = |s: &quarz_syntax::Span| in_range(s.start, base);
    let owner_mine = |o: &SelfOwner| match o {
        SelfOwner::Block(n) => mine(n),
        SelfOwner::Unit(f) => *f == file,
        SelfOwner::Method(m) => world.method(*m).file == file,
        SelfOwner::Init => false,
    };
    macro_rules! map {
        ($f:ident) => {
            out.$f
                .iter()
                .filter(|(k, _)| mine(k))
                .map(|(k, v)| (*k, v.clone()))
                .collect()
        };
    }
    macro_rules! set {
        ($f:ident) => {
            out.$f.iter().filter(|k| mine(k)).copied().collect()
        };
    }
    macro_rules! spans {
        ($f:ident) => {
            out.$f
                .iter()
                .filter(|(k, _)| span_mine(k))
                .map(|(k, v)| (*k, v.clone()))
                .collect()
        };
    }
    Output {
        node_types: map!(node_types),
        calls: map!(calls),
        const_targets: map!(const_targets),
        var_refs: spans!(var_refs),
        outer_self_calls: set!(outer_self_calls),
        dynamic_calls: set!(dynamic_calls),
        union_calls: map!(union_calls),
        union_conflicts: set!(union_conflicts),
        varied_types: set!(varied_types),
        varied_symbols: set!(varied_symbols),
        interp_conflicts: set!(interp_conflicts),
        interp_to_s: map!(interp_to_s),
        op_getters: map!(op_getters),
        op_operators: map!(op_operators),
        element_tests: set!(element_tests),
        bang_assign: set!(bang_assign),
        self_slots: out
            .self_slots
            .iter()
            .filter(|(k, _)| owner_mine(k))
            .map(|(k, v)| (*k, *v))
            .collect(),
        frame_sizes: map!(frame_sizes),
        unit_frame_sizes: Vec::new(),
        ivar_fields: map!(ivar_fields),
        pattern_classes: spans!(pattern_classes),
        block_pass: map!(block_pass),
        block_destructure: map!(block_destructure),
        rescue_classes: spans!(rescue_classes),
        float_literals: set!(float_literals),
        integer_literals: set!(integer_literals),
        discarded: set!(discarded),
        for_loops: set!(for_loops),
        logical_calls: map!(logical_calls),
        shareable_procs: set!(shareable_procs),
        self_new: set!(self_new),
        not_dispatch: map!(not_dispatch),
        lexical_slots: out
            .lexical_slots
            .iter()
            .filter(|(k, _)| owner_mine(k))
            .copied()
            .collect(),
        released_stmts: set!(released_stmts),
    }
}

/// The narrowed type parameters `out` mentions, each after those its
/// own definition does.
pub(crate) fn collect_narrowed(
    world: &World,
    out: &Output,
    list: &mut Vec<(TypeParamId, TypeParamId, Type)>,
) {
    let mut seen: HashSet<TypeParamId> = HashSet::default();
    let mut visit = |t: &Type, list: &mut Vec<(TypeParamId, TypeParamId, Type)>| {
        let mut stack = vec![t.clone()];
        while let Some(t) = stack.pop() {
            match &t {
                Type::Param(p) => {
                    if let Some(bounds) = world.narrowed_params.get(p) {
                        if seen.insert(*p) {
                            if let [Type::Param(base), bound] = &bounds[..] {
                                stack.push(Type::Param(*base));
                                stack.push(bound.clone());
                                list.push((*p, *base, bound.clone()));
                            }
                        }
                    }
                }
                Type::Class(_, a) | Type::ClassObject(_, a) | Type::Union(a) | Type::Tuple(a) => {
                    stack.extend(a.iter().cloned())
                }
                Type::Proc(r, ps, ret, _) => {
                    stack.extend(r.iter().map(|t| (**t).clone()));
                    stack.extend(ps.iter().cloned());
                    stack.push((**ret).clone());
                }
                _ => {}
            }
        }
    };
    for t in out.node_types.values() {
        visit(t, list);
    }
    // Defined before used, as `apply` makes them again in order.
    list.reverse();
}

/// What `apply` needs of the program it reads a unit into: the file
/// number each unit key has there.
pub struct Target<'a> {
    pub files: &'a dyn Fn(&str) -> Option<u32>,
    /// The syntax range of the unit read back.
    pub base: u32,
}

/// Why a unit could not be read back: something it refers to is not
/// there (its interface file is out of date).
#[derive(Debug)]
pub struct Stale;

/// Read `delta` back into `world` and `out`, renumbered.
pub fn apply(
    world: &mut World,
    out: &mut Output,
    self_news: &mut Vec<SelfNew>,
    mut delta: UnitDelta,
    target: &Target,
) -> Result<CheckedUnit, Stale> {
    let own = owned(world);
    let files: Vec<u32> = delta
        .keys
        .iter()
        .map(|k| (target.files)(k).ok_or(Stale))
        .collect::<Result<_, _>>()?;
    let file = files[0];
    // Where each kind's numbers go: the unit's own after what the world
    // has, another unit's by its position there.
    let lookup =
        |owners: &[Owner], list: &HashMap<u32, Vec<u32>>, next: u32| -> Result<Table, Stale> {
            let mut map = Vec::with_capacity(owners.len());
            for (n, o) in owners.iter().enumerate() {
                map.push(match o {
                    Owner::Prelude => n as u32,
                    Owner::Unit(0, i) => next + *i,
                    Owner::Unit(k, i) => *list
                        .get(&files[*k as usize])
                        .and_then(|ids| ids.get(*i as usize))
                        .ok_or(Stale)?,
                });
            }
            Ok(Table { base: 0, map })
        };
    let classes = lookup(
        &delta.owners.classes,
        &own.classes,
        world.classes.len() as u32,
    )?;
    let methods = lookup(
        &delta.owners.methods,
        &own.methods,
        world.methods.len() as u32,
    )?;
    let consts = lookup(&delta.owners.consts, &own.consts, world.consts.len() as u32)?;
    let aliases = lookup(
        &delta.owners.aliases,
        &own.aliases,
        world.aliases.len() as u32,
    )?;
    let extensions = lookup(
        &delta.owners.extensions,
        &own.extensions,
        world.extensions.len() as u32,
    )?;
    // Type parameters: the unit's own made anew, another unit's by its
    // position, the prelude's kept; narrowed ones made again below.
    let mut params: HashMap<u32, u32> = HashMap::default();
    for (p, o) in &delta.owners.type_params {
        let new = match o {
            Owner::Prelude => *p,
            Owner::Unit(0, _) => continue,
            Owner::Unit(k, i) => *own
                .type_params
                .get(&files[*k as usize])
                .and_then(|ids| ids.get(*i as usize))
                .ok_or(Stale)?,
        };
        params.insert(*p, new);
    }
    for (p, name, _) in &delta.type_params {
        let info = world.new_type_param(name, quarz_syntax::ast::Variance::Invariant);
        params.insert(*p, info.id);
    }
    let mut file_map: Vec<u32> = (0..=delta.key_files.iter().copied().max().unwrap_or(0)).collect();
    for (k, f) in delta.key_files.iter().enumerate() {
        file_map[*f as usize] = files[k];
    }
    let mut map = IdMap {
        classes,
        methods,
        consts,
        aliases,
        extensions,
        type_params: Table::identity(),
        files: Table {
            base: 0,
            map: file_map,
        },
        cogs: Table::identity(),
        nodes: (delta.base, target.base, 1 << crate::load::UNIT_BITS),
    };
    // Narrowed parameters, made again from their definitions in order.
    for (p, base, bound) in std::mem::take(&mut delta.narrowed) {
        let base = params.get(&base).copied().unwrap_or(base);
        let mut bound = bound;
        map.type_params = param_table(&params);
        bound.remap(&map);
        if let Type::Param(id) = world.narrowed_param(base, &bound) {
            params.insert(p, id);
        }
    }
    map.type_params = param_table(&params);
    let m = &map;
    for (p, _, lower) in &delta.type_params {
        if let Some(mut l) = lower.clone() {
            l.remap(m);
            world.lower_bounds.insert(params[p], l);
        }
    }
    for mut c in std::mem::take(&mut delta.classes) {
        c.remap(m);
        world.classes.push(c);
    }
    for mut x in std::mem::take(&mut delta.methods) {
        x.remap(m);
        world.methods.push(x);
    }
    for mut x in std::mem::take(&mut delta.consts) {
        x.remap(m);
        world.consts.push(x);
    }
    for mut x in std::mem::take(&mut delta.aliases) {
        x.remap(m);
        world.aliases.push(x);
    }
    for mut x in std::mem::take(&mut delta.extensions) {
        x.remap(m);
        world.extensions.push(x);
    }
    for (n, mut x) in std::mem::take(&mut delta.top) {
        x.remap(m);
        world.top.insert(n, x);
    }
    for (ns, n, mut x) in std::mem::take(&mut delta.members) {
        x.remap(m);
        let ns = m.classes.get(ns);
        world.class_mut(ns).members.insert(n, x);
    }
    for (ns, e) in std::mem::take(&mut delta.ns_extensions) {
        let (ns, e) = (m.classes.get(ns), m.extensions.get(e));
        world.class_mut(ns).extensions.push(e);
    }
    if let Some(mut g) = delta.group {
        g.remap(m);
        world.file_groups.insert(file, g);
    }
    if delta.std {
        world.std_files.insert(file);
    }
    if !delta.std && delta.group == Some(UnitGroup::App) {
        world.app_names.extend(delta.app_names.iter().cloned());
    }
    for (c, a, i) in std::mem::take(&mut delta.ext_impls) {
        world
            .ext_impls
            .push((m.classes.get(c), m.methods.get(a), m.methods.get(i)));
    }
    world.add_docs(&delta.docs);
    let mut o = std::mem::take(&mut delta.output);
    o.remap(m);
    merge_output(out, o);
    if out.unit_frame_sizes.len() <= file as usize {
        out.unit_frame_sizes.resize(file as usize + 1, 0);
    }
    out.unit_frame_sizes[file as usize] = delta.frame_size;
    for (c, i, x, s, f) in std::mem::take(&mut delta.self_news) {
        self_news.push((
            m.classes.get(c),
            i.map(|i| m.methods.get(i)),
            m.methods.get(x),
            s,
            m.files.get(f),
        ));
    }
    let mut unit = delta.unit;
    unit.file = file;
    unit.main_class = m.classes.get(unit.main_class);
    Ok(unit)
}

pub(crate) fn param_table(params: &HashMap<u32, u32>) -> Table {
    let max = params.keys().copied().max().map_or(0, |m| m + 1);
    let mut map: Vec<u32> = (0..max).collect();
    for (k, v) in params {
        map[*k as usize] = *v;
    }
    Table { base: 0, map }
}

pub(crate) fn merge_output(out: &mut Output, o: Output) {
    out.node_types.extend(o.node_types);
    out.calls.extend(o.calls);
    out.const_targets.extend(o.const_targets);
    out.var_refs.extend(o.var_refs);
    out.outer_self_calls.extend(o.outer_self_calls);
    out.dynamic_calls.extend(o.dynamic_calls);
    out.union_calls.extend(o.union_calls);
    out.union_conflicts.extend(o.union_conflicts);
    out.varied_types.extend(o.varied_types);
    out.varied_symbols.extend(o.varied_symbols);
    out.interp_conflicts.extend(o.interp_conflicts);
    out.interp_to_s.extend(o.interp_to_s);
    out.op_getters.extend(o.op_getters);
    out.op_operators.extend(o.op_operators);
    out.element_tests.extend(o.element_tests);
    out.bang_assign.extend(o.bang_assign);
    out.self_slots.extend(o.self_slots);
    out.frame_sizes.extend(o.frame_sizes);
    out.ivar_fields.extend(o.ivar_fields);
    out.pattern_classes.extend(o.pattern_classes);
    out.block_pass.extend(o.block_pass);
    out.block_destructure.extend(o.block_destructure);
    out.rescue_classes.extend(o.rescue_classes);
    out.float_literals.extend(o.float_literals);
    out.integer_literals.extend(o.integer_literals);
    out.discarded.extend(o.discarded);
    out.for_loops.extend(o.for_loops);
    out.logical_calls.extend(o.logical_calls);
    out.shareable_procs.extend(o.shareable_procs);
    out.self_new.extend(o.self_new);
    out.not_dispatch.extend(o.not_dispatch);
    out.lexical_slots.extend(o.lexical_slots);
    out.released_stmts.extend(o.released_stmts);
}

impl UnitDelta {
    pub fn encode(&self) -> Vec<u8> {
        bincode::serde::encode_to_vec(self, bincode::config::standard()).expect("encode a unit")
    }

    /// Decode, with the unit's syntax moved from `from` to `to`.
    pub fn decode(bytes: &[u8], from: u32, to: u32) -> Option<UnitDelta> {
        quarz_syntax::rebased(from, to, 1 << crate::load::UNIT_BITS, || {
            bincode::serde::decode_from_slice(bytes, bincode::config::standard())
                .ok()
                .map(|(d, _)| d)
        })
    }
}
