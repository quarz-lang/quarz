//! Renumbering a file's check results for reading them back into
//! another program (`cache`, docs/05 §2): the entities they refer to get
//! the numbers they have there. `IdMap` says how each kind of number
//! changes; `Remap` applies it to the structures that hold such numbers.
//! (Syntax nodes and spans stay: a file's checks are read back only for
//! the same syntax, so the same range, `cache::key`.)

use rustc_hash::FxHashMap as HashMap;

use crate::check::{BlockPass, CallTarget, ConstTarget, Output, SelfOwner};
use crate::types::*;

/// One kind of number: those below `base` stay, those from `base` on are
/// looked up in `map` (by `n - base`).
#[derive(Clone, Debug, Default)]
pub struct Table {
    pub base: u32,
    pub map: Vec<u32>,
}

impl Table {
    pub fn get(&self, n: u32) -> u32 {
        if n < self.base {
            n
        } else {
            self.map.get((n - self.base) as usize).copied().unwrap_or(n)
        }
    }
}

/// How the numbers of a file's check change between the program it was
/// checked in and the one it is read into.
#[derive(Clone, Debug)]
pub struct IdMap {
    pub classes: Table,
    pub methods: Table,
    pub consts: Table,
    pub type_params: Table,
    pub files: Table,
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
            SelfOwner::Unit(f) => *f = m.files.get(*f),
            SelfOwner::Block(_) | SelfOwner::Init => {}
        }
    }
}

/// What a table keyed by node or span holds.
fn values<K, V>(t: &mut HashMap<K, V>, f: impl FnMut(&mut V)) {
    t.values_mut().for_each(f);
}

impl Remap for Output {
    fn remap(&mut self, m: &IdMap) {
        values(&mut self.node_types, |t| t.remap(m));
        values(&mut self.calls, |t| t.remap(m));
        values(&mut self.const_targets, |t| t.remap(m));
        values(&mut self.union_calls, |t| {
            for (ty, x) in t {
                ty.remap(m);
                method(m, x);
            }
        });
        values(&mut self.interp_to_s, |t| {
            for (c, x) in t {
                class(m, c);
                if let Some(x) = x {
                    method(m, x);
                }
            }
        });
        values(&mut self.op_getters, |x| method(m, x));
        values(&mut self.op_operators, |x| method(m, x));
        let old = std::mem::take(&mut self.self_slots);
        for (mut k, v) in old {
            k.remap(m);
            self.self_slots.insert(k, v);
        }
        values(&mut self.pattern_classes, |c| class(m, c));
        values(&mut self.block_pass, |b| b.remap(m));
        values(&mut self.rescue_classes, |cs| {
            for c in cs {
                class(m, c);
            }
        });
        values(&mut self.not_dispatch, |t| {
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
    }
}
