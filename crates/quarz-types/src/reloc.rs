//! Renumbering what a unit's check added to the world, for reading it
//! back into another program (docs/05 §2): the entities it refers to get
//! the numbers they have there, and its syntax nodes and spans move to
//! the unit's range. `IdMap` says how each kind of number changes;
//! `Remap` applies it to the structures that hold such numbers.

use rustc_hash::FxHashMap as HashMap;

use crate::check::{BlockPass, CallTarget, ConstTarget, Output, SelfOwner};
use crate::types::*;
use crate::world::*;

/// One kind of number: those below `base` stay, those from `base` on are
/// looked up in `map` (by `n - base`).
#[derive(Clone, Debug, Default)]
pub struct Table {
    pub base: u32,
    pub map: Vec<u32>,
}

impl Table {
    pub fn identity() -> Table {
        Table {
            base: u32::MAX,
            map: Vec::new(),
        }
    }

    pub fn get(&self, n: u32) -> u32 {
        if n < self.base {
            n
        } else {
            self.map.get((n - self.base) as usize).copied().unwrap_or(n)
        }
    }
}

/// How the numbers of a unit's check change between the program it was
/// checked in and the one it is read into.
#[derive(Clone, Debug)]
pub struct IdMap {
    pub classes: Table,
    pub methods: Table,
    pub consts: Table,
    pub aliases: Table,
    pub extensions: Table,
    pub type_params: Table,
    pub files: Table,
    pub cogs: Table,
    /// Node ids and spans in `[from, from + len)` move to `[to, to + len)`.
    pub nodes: (u32, u32, u32),
}

impl IdMap {
    pub fn identity() -> IdMap {
        IdMap {
            classes: Table::identity(),
            methods: Table::identity(),
            consts: Table::identity(),
            aliases: Table::identity(),
            extensions: Table::identity(),
            type_params: Table::identity(),
            files: Table::identity(),
            cogs: Table::identity(),
            nodes: (0, 0, 0),
        }
    }

    pub fn node(&self, n: u32) -> u32 {
        let (from, to, len) = self.nodes;
        if n >= from && n - from <= len {
            n - from + to
        } else {
            n
        }
    }
}

pub trait Remap {
    fn remap(&mut self, m: &IdMap);
}

impl<T: Remap> Remap for Vec<T> {
    fn remap(&mut self, m: &IdMap) {
        for x in self {
            x.remap(m);
        }
    }
}

impl<T: Remap> Remap for Option<T> {
    fn remap(&mut self, m: &IdMap) {
        if let Some(x) = self {
            x.remap(m);
        }
    }
}

impl<T: Remap> Remap for Box<T> {
    fn remap(&mut self, m: &IdMap) {
        (**self).remap(m);
    }
}

fn class(m: &IdMap, c: &mut ClassId) {
    *c = m.classes.get(*c);
}

fn method(m: &IdMap, x: &mut MethodId) {
    *x = m.methods.get(*x);
}

fn ext(m: &IdMap, x: &mut ExtensionId) {
    *x = m.extensions.get(*x);
}

fn method_table(m: &IdMap, t: &mut HashMap<String, Vec<MethodId>>) {
    for ids in t.values_mut() {
        for id in ids {
            method(m, id);
        }
    }
}

impl Remap for Type {
    fn remap(&mut self, m: &IdMap) {
        match self {
            Type::Class(c, args) | Type::ClassObject(c, args) => {
                class(m, c);
                args.remap(m);
            }
            Type::Union(ts) | Type::Tuple(ts) => ts.remap(m),
            Type::Proc(recv, ps, r, _) => {
                recv.remap(m);
                ps.remap(m);
                r.remap(m);
            }
            Type::Param(p) => {
                // The `Self` marker and the like stay.
                *p = m.type_params.get(*p);
            }
            Type::Nothing | Type::Var(_) => {}
        }
    }
}

impl Remap for TypeParamInfo {
    fn remap(&mut self, m: &IdMap) {
        self.id = m.type_params.get(self.id);
        self.bounds.remap(m);
        self.lower.remap(m);
    }
}

impl Remap for FieldInfo {
    fn remap(&mut self, m: &IdMap) {
        self.ty.remap(m);
    }
}

impl Remap for ParamInfo {
    fn remap(&mut self, m: &IdMap) {
        self.ty.remap(m);
    }
}

impl Remap for RetType {
    fn remap(&mut self, m: &IdMap) {
        if let RetType::Known(t) = self {
            t.remap(m);
        }
    }
}

impl Remap for MethodInfo {
    fn remap(&mut self, m: &IdMap) {
        method(m, &mut self.id);
        class(m, &mut self.owner);
        self.type_params.remap(m);
        self.params.remap(m);
        if let Some((_, t)) = &mut self.block {
            t.remap(m);
        }
        for e in &mut self.block_usings {
            ext(m, e);
        }
        self.ret.remap(m);
        if let Some(e) = &mut self.extension {
            ext(m, e);
        }
        if let Some(a) = &mut self.alias_of {
            method(m, a);
        }
        self.file = m.files.get(self.file);
    }
}

impl Remap for ConstInfo {
    fn remap(&mut self, m: &IdMap) {
        self.id = m.consts.get(self.id);
        if let Some(o) = &mut self.owner {
            class(m, o);
        }
        self.ty.remap(m);
        self.file = m.files.get(self.file);
    }
}

impl Remap for TypeAliasInfo {
    fn remap(&mut self, m: &IdMap) {
        if let Some(o) = &mut self.owner {
            class(m, o);
        }
        self.type_params.remap(m);
        self.resolved.remap(m);
        self.file = m.files.get(self.file);
    }
}

impl Remap for UnitGroup {
    fn remap(&mut self, m: &IdMap) {
        match self {
            UnitGroup::App => {}
            UnitGroup::Cog(c) => *c = m.cogs.get(*c),
            UnitGroup::Std(f) => *f = m.files.get(*f),
        }
    }
}

impl Remap for ExtensionInfo {
    fn remap(&mut self, m: &IdMap) {
        ext(m, &mut self.id);
        if let Some(o) = &mut self.module {
            class(m, o);
        }
        class(m, &mut self.target);
        self.type_params.remap(m);
        self.target_args.remap(m);
        self.includes.remap(m);
        method_table(m, &mut self.methods);
        self.group.remap(m);
        self.file = m.files.get(self.file);
    }
}

impl Remap for Member {
    fn remap(&mut self, m: &IdMap) {
        match self {
            Member::Class(c) => class(m, c),
            Member::Const(c) => *c = m.consts.get(*c),
            Member::Alias(a) => *a = m.aliases.get(*a),
        }
    }
}

impl Remap for ClassInfo {
    fn remap(&mut self, m: &IdMap) {
        class(m, &mut self.id);
        self.type_params.remap(m);
        self.superclass.remap(m);
        self.includes.remap(m);
        self.extends.remap(m);
        self.fields.remap(m);
        method_table(m, &mut self.methods);
        method_table(m, &mut self.singleton_methods);
        for v in self.members.values_mut() {
            v.remap(m);
        }
        if let Some(p) = &mut self.parent {
            class(m, p);
        }
        for v in &mut self.variants {
            class(m, v);
        }
        if let Some(v) = &mut self.variant_of {
            class(m, v);
        }
        for e in &mut self.extensions {
            ext(m, e);
        }
        for e in &mut self.usings {
            ext(m, e);
        }
        self.file = m.files.get(self.file);
        if let Some(c) = &mut self.cog {
            *c = m.cogs.get(*c);
        }
    }
}

impl Remap for CallTarget {
    fn remap(&mut self, m: &IdMap) {
        match self {
            CallTarget::Method { method: x } | CallTarget::Super { method: x } => method(m, x),
            CallTarget::Constructor { class: c, init } => {
                class(m, c);
                if let Some(i) = init {
                    method(m, i);
                }
            }
            CallTarget::IsA(t) | CallTarget::As { ty: t, .. } => t.remap(m),
            CallTarget::ProcCall | CallTarget::Constant(_) | CallTarget::Raise => {}
        }
    }
}

impl Remap for ConstTarget {
    fn remap(&mut self, m: &IdMap) {
        match self {
            ConstTarget::Class(c) | ConstTarget::VariantSingleton(c) => class(m, c),
            ConstTarget::Const(c) => *c = m.consts.get(*c),
        }
    }
}

impl Remap for BlockPass {
    fn remap(&mut self, m: &IdMap) {
        if let BlockPass::Symbol(_, x) = self {
            method(m, x);
        }
    }
}

impl Remap for SelfOwner {
    fn remap(&mut self, m: &IdMap) {
        match self {
            SelfOwner::Method(x) => method(m, x),
            SelfOwner::Block(n) => *n = m.node(*n),
            SelfOwner::Unit(f) => *f = m.files.get(*f),
            SelfOwner::Init => {}
        }
    }
}

/// Renumber the keys of a node-keyed table and what it holds.
fn nodes<V>(m: &IdMap, t: &mut HashMap<u32, V>, mut f: impl FnMut(&mut V)) {
    let old = std::mem::take(t);
    for (k, mut v) in old {
        f(&mut v);
        t.insert(m.node(k), v);
    }
}

fn node_set(m: &IdMap, s: &mut rustc_hash::FxHashSet<u32>) {
    let old = std::mem::take(s);
    s.extend(old.into_iter().map(|n| m.node(n)));
}

/// A span-keyed table: its keys are moved when it is read back
/// (`quarz_syntax::source::rebased`), like every `Span`.
fn spans<V>(_m: &IdMap, t: &mut HashMap<quarz_syntax::Span, V>, f: impl FnMut(&mut V)) {
    t.values_mut().for_each(f);
}

impl Remap for Output {
    fn remap(&mut self, m: &IdMap) {
        nodes(m, &mut self.node_types, |t| t.remap(m));
        nodes(m, &mut self.calls, |t| t.remap(m));
        nodes(m, &mut self.const_targets, |t| t.remap(m));
        spans(m, &mut self.var_refs, |_| {});
        node_set(m, &mut self.outer_self_calls);
        node_set(m, &mut self.dynamic_calls);
        nodes(m, &mut self.union_calls, |t| {
            for (ty, x) in t {
                ty.remap(m);
                method(m, x);
            }
        });
        node_set(m, &mut self.union_conflicts);
        node_set(m, &mut self.varied_types);
        node_set(m, &mut self.varied_symbols);
        node_set(m, &mut self.interp_conflicts);
        nodes(m, &mut self.interp_to_s, |t| {
            for (c, x) in t {
                class(m, c);
                if let Some(x) = x {
                    method(m, x);
                }
            }
        });
        nodes(m, &mut self.op_getters, |x| method(m, x));
        nodes(m, &mut self.op_operators, |x| method(m, x));
        node_set(m, &mut self.element_tests);
        node_set(m, &mut self.bang_assign);
        let old = std::mem::take(&mut self.self_slots);
        for (mut k, v) in old {
            k.remap(m);
            self.self_slots.insert(k, v);
        }
        nodes(m, &mut self.frame_sizes, |_| {});
        nodes(m, &mut self.ivar_fields, |_| {});
        spans(m, &mut self.pattern_classes, |c| class(m, c));
        nodes(m, &mut self.block_pass, |b| b.remap(m));
        nodes(m, &mut self.block_destructure, |_| {});
        spans(m, &mut self.rescue_classes, |cs| {
            for c in cs {
                class(m, c);
            }
        });
        node_set(m, &mut self.float_literals);
        node_set(m, &mut self.integer_literals);
        node_set(m, &mut self.discarded);
        node_set(m, &mut self.for_loops);
        // (The calls `a && b` stands for are read back with the unit's
        // nodes moved: `logical_calls`' values hold syntax only.)
        nodes(m, &mut self.logical_calls, |_| {});
        node_set(m, &mut self.shareable_procs);
        node_set(m, &mut self.self_new);
        nodes(m, &mut self.not_dispatch, |t| {
            for (ty, x) in t {
                ty.remap(m);
                method(m, x);
            }
        });
        let old = std::mem::take(&mut self.lexical_slots);
        for (mut k, v) in old {
            k.remap(m);
            self.lexical_slots.insert((k, v));
        }
        node_set(m, &mut self.released_stmts);
    }
}
