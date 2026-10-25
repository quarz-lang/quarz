//! Iteration calls whose block is lowered in place as a loop instead of
//! a block function: `n.times { }`, `array.each { }`, `(lo..hi).map { }`
//! and the like. The block body then runs in the enclosing function (no
//! closure, no call per element), with `break`/`next` as jumps.

use quarz_syntax::ast::{self, Arg, Expr, ExprKind, ParamKind};
use quarz_types::{CallTarget, Output, Type, World};

use crate::capture::{captured_slots, has_real_closure};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kind {
    /// `Int#times`: the elements are `0...n`.
    Times,
    /// `Int#upto(limit)`: `n..limit`.
    Upto,
    Each,
    EachWithIndex,
    Map,
    Select,
    Reject,
    /// `reduce(initial)`: the block gets the accumulator and the element.
    Reduce,
    /// `count { }`: how many elements the block accepts.
    Count,
    /// `any? { }` / `all? { }`: stop at the first accepted / rejected element.
    Any,
    All,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Source {
    /// The receiver is an `Array`, iterated by index.
    Array,
    /// The receiver is a literal `lo..hi`/`lo...hi` over `Int`.
    Range,
}

#[derive(Clone, Copy, Debug)]
pub struct Shape {
    pub kind: Kind,
    /// For the collection kinds; `None` for `times`/`upto`.
    pub source: Option<Source>,
    /// `xs.map(&:name)`: no block, the method called on each element
    /// (as the checker resolved it for the element type).
    pub symbol: Option<quarz_types::types::MethodId>,
    /// An `Array[Int]` (`Some(false)`) or `Array[Float]` (`Some(true)`)
    /// receiver: its elements are read as machine words (`ArrayWords`).
    pub words: Option<bool>,
}

/// Whether `call` (expression `e`) is lowered in place, and how.
pub fn shape(e: &Expr, call: &ast::Call, out: &Output, world: &World) -> Option<Shape> {
    if call.safe_nav {
        return None;
    }
    // `&:name` as the only argument stands for a one-parameter block
    // calling `name` on it.
    let symbol = match (&call.block, call.args.as_slice()) {
        (None, [Arg::BlockPass(x)]) => match out.block_pass.get(&x.id) {
            Some(quarz_types::BlockPass::Symbol(_, m))
                if matches!(x.kind, ExprKind::Symbol(_)) && !out.varied_symbols.contains(&x.id) =>
            {
                Some(*m)
            }
            _ => return None,
        },
        _ => None,
    };
    if symbol.is_none() {
        let block = call.block.as_ref()?;
        let simple_params = block
            .params
            .list
            .iter()
            .all(|p| p.kind == ParamKind::Positional && p.default.is_none());
        if !simple_params || out.block_destructure.contains_key(&e.id) {
            return None;
        }
        if !call.args.iter().all(|a| matches!(a, Arg::Positional(_))) {
            return None;
        }
    }
    let Some(CallTarget::Method { method }) = out.calls.get(&e.id) else {
        return None;
    };
    let m = world.method(*method);
    // (Checks that found the method or typed the receiver differently, a
    // block's once per type: the recorded ones are the last check's.)
    let varies = out.union_conflicts.contains(&e.id)
        || out
            .union_calls
            .get(&e.id)
            .is_some_and(|t| t.iter().any(|(_, m)| *m != t[0].1));
    if m.extension.is_some() || varies {
        return None;
    }
    let bi = &world.builtin;
    let nargs = if symbol.is_some() { 0 } else { call.args.len() };
    let shape = if m.owner == bi.int {
        match (m.name.as_str(), nargs) {
            ("times", 0) => Shape {
                kind: Kind::Times,
                source: None,
                symbol,
                words: None,
            },
            ("upto", 1) => Shape {
                kind: Kind::Upto,
                source: None,
                symbol,
                words: None,
            },
            _ => return None,
        }
    } else {
        let recv = call.recv.as_ref()?;
        if out.varied_types.contains(&recv.id) {
            return None;
        }
        let source = match out.node_types.get(&recv.id)? {
            Type::Class(id, _) if *id == bi.array => Source::Array,
            Type::Class(id, args) if *id == bi.range => {
                let int_range =
                    matches!(args.first(), Some(Type::Class(c, a)) if *c == bi.int && a.is_empty());
                let literal = matches!(
                    &recv.kind,
                    ExprKind::Range {
                        lo: Some(_),
                        hi: Some(_),
                        ..
                    }
                );
                if !int_range || !literal {
                    return None;
                }
                Source::Range
            }
            _ => return None,
        };
        let own = match source {
            Source::Array => bi.array,
            Source::Range => bi.range,
        };
        let kind = match (m.name.as_str(), nargs) {
            ("each", 0) if m.owner == own => Kind::Each,
            ("map", 0) if m.owner == own || m.owner == bi.enumerable => Kind::Map,
            ("select", 0) if m.owner == own || m.owner == bi.enumerable => Kind::Select,
            ("reject", 0) if m.owner == bi.enumerable => Kind::Reject,
            ("each_with_index", 0) if m.owner == bi.enumerable => Kind::EachWithIndex,
            ("reduce", 1) if m.owner == bi.enumerable => Kind::Reduce,
            ("count", 0) if m.owner == bi.enumerable => Kind::Count,
            ("any?", 0) if m.owner == bi.enumerable => Kind::Any,
            ("all?", 0) if m.owner == bi.enumerable => Kind::All,
            _ => return None,
        };
        let words = match (source, out.node_types.get(&recv.id)) {
            (Source::Array, Some(Type::Class(_, args))) => match args.first() {
                Some(Type::Class(c, a)) if *c == bi.int && a.is_empty() => Some(false),
                Some(Type::Class(c, a)) if *c == bi.float && a.is_empty() => Some(true),
                _ => None,
            },
            _ => None,
        };
        Shape {
            kind,
            source: Some(source),
            symbol,
            words,
        }
    };
    if symbol.is_some() {
        // One argument per element: not `each_with_index` or `reduce`.
        return (!matches!(shape.kind, Kind::EachWithIndex | Kind::Reduce)).then_some(shape);
    }
    // The block's variables must all be registers of the enclosing
    // function: nothing nested may capture them.
    let block = call.block.as_ref()?;
    let nparams = block.params.list.len() as u32;
    if !captured_slots(&block.body, &[], out, world, nparams).is_empty() {
        return None;
    }
    Some(shape)
}

/// Whether `call` is `recv.instance_exec(args) { ... }` with a block that
/// can run in place: the body is then lowered in the enclosing function
/// with `self` replaced by the receiver's register. A body that creates
/// a closure of its own is left alone (that closure must capture the
/// receiver as its `self`).
pub fn exec_shape(e: &Expr, call: &ast::Call, out: &Output, world: &World) -> Option<()> {
    if call.safe_nav {
        return None;
    }
    let block = call.block.as_ref()?;
    let simple_params = block
        .params
        .list
        .iter()
        .all(|p| p.kind == ParamKind::Positional && p.default.is_none());
    if !simple_params || out.block_destructure.contains_key(&e.id) {
        return None;
    }
    if !call.args.iter().all(|a| matches!(a, Arg::Positional(_))) {
        return None;
    }
    let Some(CallTarget::Method { method }) = out.calls.get(&e.id) else {
        return None;
    };
    let m = world.method(*method);
    if !(m.is_native && m.name == "instance_exec" && m.owner == world.builtin.object) {
        return None;
    }
    let nparams = block.params.list.len() as u32;
    if !captured_slots(&block.body, &[], out, world, nparams).is_empty() {
        return None;
    }
    if has_real_closure(&block.body, out, world) {
        return None;
    }
    Some(())
}
