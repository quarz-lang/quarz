//! Iteration calls whose block is lowered in place as a loop instead of
//! a block function: `n.times { }`, `array.each { }`, `(lo..hi).map { }`
//! and the like. The block body then runs in the enclosing function (no
//! closure, no call per element), with `break`/`next` as jumps.

use quarz_syntax::ast::{self, Arg, Expr, ExprKind, ParamKind};
use quarz_types::{CallTarget, Output, Type, World};

use crate::capture::captured_slots;

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
}

/// Whether `call` (expression `e`) is lowered in place, and how.
pub fn shape(e: &Expr, call: &ast::Call, out: &Output, world: &World) -> Option<Shape> {
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
    if m.extension.is_some() {
        return None;
    }
    let bi = &world.builtin;
    let nargs = call.args.len();
    let shape = if m.owner == bi.int {
        match (m.name.as_str(), nargs) {
            ("times", 0) => Shape {
                kind: Kind::Times,
                source: None,
            },
            ("upto", 1) => Shape {
                kind: Kind::Upto,
                source: None,
            },
            _ => return None,
        }
    } else {
        let recv = call.recv.as_ref()?;
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
        Shape {
            kind,
            source: Some(source),
        }
    };
    // The block's variables must all be registers of the enclosing
    // function: nothing nested may capture them.
    let nparams = block.params.list.len() as u32;
    if !captured_slots(&block.body, &[], out, world, nparams).is_empty() {
        return None;
    }
    Some(shape)
}
