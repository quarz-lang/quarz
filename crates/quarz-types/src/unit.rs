//! What a file's check owns in the world and in the checker's results,
//! for keeping it between runs (`cache`, docs/05 §2): whose each number
//! is, the results for the file's own syntax, and how they merge back.

use rustc_hash::{FxHashMap as HashMap, FxHashSet as HashSet};

use crate::check::Output;
use crate::reloc::Table;
use crate::types::*;
use crate::world::*;

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
    /// Type parameters of declared entities (narrowed ones are made
    /// again: `cache::Checks::narrowed`).
    pub type_params: HashMap<TypeParamId, Owner>,
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

/// The files a check refers to, by key (its own first).
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
        usable_after: set!(usable_after),
        usable_on_entry: out
            .usable_on_entry
            .iter()
            .filter(|k| owner_mine(k))
            .copied()
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
                Type::TypeOf(t) => stack.push((**t).clone()),
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
    // Defined before used, as `cache::apply` makes them again in order.
    list.reverse();
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
    out.usable_after.extend(o.usable_after);
    out.usable_on_entry.extend(o.usable_on_entry);
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
