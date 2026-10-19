//! Which local variable slots of a function are referenced from nested
//! blocks (and therefore live in a heap frame rather than a register).
//!
//! A block that is lowered in place as a loop (see `iter`) is not a
//! nested function: references from its body are references from the
//! enclosing function, and its own variables are registers there.

use std::collections::HashSet;

use quarz_syntax::ast::*;
use quarz_syntax::Span;
use quarz_types::{Output, VarRef, World};

/// A place where the checker recorded a variable reference, or an
/// implicit reference to every parameter (`super` without arguments).
#[derive(Clone, Copy, Debug)]
pub enum Site {
    Var(Span),
    ZSuper,
}

/// How deep a reference sits: `actual` counts every block level the way
/// the checker's `VarRef::depth` does, `real` only the levels that become
/// functions of their own.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Nest {
    pub actual: u32,
    pub real: u32,
}

impl Nest {
    const TOP: Nest = Nest { actual: 0, real: 0 };

    fn enter(self, inlined: bool) -> Nest {
        Nest {
            actual: self.actual + 1,
            real: if inlined { self.real } else { self.real + 1 },
        }
    }
}

pub struct Cx<'a> {
    pub out: &'a Output,
    pub world: &'a World,
    pub visit: &'a mut dyn FnMut(Site, Nest),
    /// How many blocks that become closures of their own were seen.
    pub real_blocks: u32,
}

/// Whether `body` creates a closure (a block or lambda that is not
/// lowered in place): such a closure would capture the wrong `self`
/// inside a block lowered in place with another receiver.
pub fn has_real_closure(body: &[Expr], out: &Output, world: &World) -> bool {
    let mut visit = |_: Site, _: Nest| {};
    let mut cx = Cx {
        out,
        world,
        visit: &mut visit,
        real_blocks: 0,
    };
    for e in body {
        walk_expr(e, Nest::TOP, &mut cx);
    }
    cx.real_blocks > 0
}

/// Slots of the function whose body is `body` (plus `extra` expressions
/// evaluated in the same frame, such as parameter defaults) that nested
/// blocks refer to.
pub fn captured_slots(
    body: &[Expr],
    extra: &[&Expr],
    out: &Output,
    world: &World,
    nparams: u32,
) -> HashSet<u32> {
    let mut captured = HashSet::new();
    let mut visit = |site: Site, nest: Nest| {
        if nest.real == 0 {
            return;
        }
        match site {
            Site::Var(span) => {
                if let Some(VarRef { depth, slot }) = out.var_refs.get(&span) {
                    if *depth == nest.actual {
                        captured.insert(*slot);
                    }
                }
            }
            Site::ZSuper => {
                for i in 0..nparams {
                    captured.insert(i);
                }
            }
        }
    };
    let mut cx = Cx {
        out,
        world,
        visit: &mut visit,
        real_blocks: 0,
    };
    for e in body {
        walk_expr(e, Nest::TOP, &mut cx);
    }
    for e in extra {
        walk_expr(e, Nest::TOP, &mut cx);
    }
    captured
}

pub fn walk_body(body: &[Expr], nest: Nest, cx: &mut Cx) {
    for e in body {
        walk_expr(e, nest, cx);
    }
}

fn walk_parts(parts: &[StrPart], nest: Nest, cx: &mut Cx) {
    for p in parts {
        if let StrPart::Interp(e) = p {
            walk_expr(e, nest, cx);
        }
    }
}

fn walk_args(args: &[Arg], nest: Nest, cx: &mut Cx) {
    for a in args {
        match a {
            Arg::Positional(e) | Arg::Splat(e) | Arg::DoubleSplat(e) | Arg::BlockPass(e) => {
                walk_expr(e, nest, cx)
            }
            Arg::Keyword { value, .. } => walk_expr(value, nest, cx),
        }
    }
}

fn walk_block(block: &Block, nest: Nest, cx: &mut Cx, inlined: bool) {
    if !inlined {
        cx.real_blocks += 1;
    }
    let inner = nest.enter(inlined);
    for p in &block.params.list {
        if let Some(d) = &p.default {
            walk_expr(d, inner, cx);
        }
    }
    walk_body(&block.body, inner, cx);
}

fn walk_lvalue(lv: &LValue, nest: Nest, cx: &mut Cx) {
    match lv {
        LValue::Local { span, .. } => (cx.visit)(Site::Var(*span), nest),
        LValue::IVar(_) | LValue::Const(_) => {}
        LValue::Attr { recv, .. } => walk_expr(recv, nest, cx),
        LValue::Index { recv, args } => {
            walk_expr(recv, nest, cx);
            walk_args(args, nest, cx);
        }
    }
}

fn walk_multi(targets: &[MultiTarget], nest: Nest, cx: &mut Cx) {
    for t in targets {
        match t {
            MultiTarget::Single(lv) | MultiTarget::Splat(Some(lv)) => walk_lvalue(lv, nest, cx),
            MultiTarget::Splat(None) => {}
            MultiTarget::Nested(ts) => walk_multi(ts, nest, cx),
        }
    }
}

pub fn walk_pattern(pat: &Pattern, nest: Nest, cx: &mut Cx) {
    match &pat.kind {
        PatternKind::Value(e) | PatternKind::Pin(e) => walk_expr(e, nest, cx),
        PatternKind::Bind(_) => (cx.visit)(Site::Var(pat.span), nest),
        PatternKind::Capture(inner, _) => {
            walk_pattern(inner, nest, cx);
            (cx.visit)(Site::Var(pat.span), nest);
        }
        PatternKind::Alt(alts) => {
            for a in alts {
                walk_pattern(a, nest, cx);
            }
        }
        PatternKind::Const(_) => {}
        PatternKind::ConstArray(_, ap) => walk_array_pattern(ap, pat.span, nest, cx),
        PatternKind::Array(ap) => walk_array_pattern(ap, pat.span, nest, cx),
        PatternKind::ConstHash(_, hp) => walk_hash_pattern(hp, pat.span, nest, cx),
        PatternKind::Hash(hp) => walk_hash_pattern(hp, pat.span, nest, cx),
        PatternKind::Find {
            pre_rest,
            middle,
            post_rest,
        } => {
            for p in middle {
                walk_pattern(p, nest, cx);
            }
            if pre_rest.is_some() {
                (cx.visit)(Site::Var(pat.span), nest);
            }
            if post_rest.is_some() {
                (cx.visit)(Site::Var(Span::empty(pat.span.end as usize)), nest);
            }
        }
        PatternKind::Range { lo, hi, .. } => {
            if let Some(e) = lo {
                walk_expr(e, nest, cx);
            }
            if let Some(e) = hi {
                walk_expr(e, nest, cx);
            }
        }
    }
}

fn walk_array_pattern(ap: &ArrayPattern, span: Span, nest: Nest, cx: &mut Cx) {
    for p in ap.pre.iter().chain(ap.post.iter()) {
        walk_pattern(p, nest, cx);
    }
    if let Some(Some(_)) = &ap.rest {
        (cx.visit)(Site::Var(span), nest);
    }
}

fn walk_hash_pattern(hp: &HashPattern, span: Span, nest: Nest, cx: &mut Cx) {
    for pair in &hp.pairs {
        match &pair.pattern {
            Some(p) => walk_pattern(p, nest, cx),
            None => (cx.visit)(Site::Var(pair.span), nest),
        }
    }
    if let Some(HashPatternRest::Bind(_)) = &hp.rest {
        (cx.visit)(Site::Var(span), nest);
    }
}

pub fn walk_expr(e: &Expr, nest: Nest, cx: &mut Cx) {
    use ExprKind::*;
    match &e.kind {
        Nil
        | True
        | False
        | SelfRef
        | Int(_)
        | Float(_)
        | Bytes(_)
        | Symbol(_)
        | Magic(_)
        | IVar(_)
        | Const(_)
        | TypeApp(_)
        | Retry
        | Using(_)
        | Require { .. } => {}
        Str(parts) | DSymbol(parts) | Regexp { parts, .. } => walk_parts(parts, nest, cx),
        Array(items) => walk_args(items, nest, cx),
        Hash(entries) => {
            for en in entries {
                match en {
                    HashEntry::Pair { key, value } => {
                        walk_expr(key, nest, cx);
                        walk_expr(value, nest, cx);
                    }
                    HashEntry::DoubleSplat(x) => walk_expr(x, nest, cx),
                }
            }
        }
        Range { lo, hi, .. } => {
            if let Some(x) = lo {
                walk_expr(x, nest, cx);
            }
            if let Some(x) = hi {
                walk_expr(x, nest, cx);
            }
        }
        Lambda(block) => walk_block(block, nest, cx, false),
        Local(_) => (cx.visit)(Site::Var(e.span), nest),
        Call(call) => {
            if let Some(r) = &call.recv {
                walk_expr(r, nest, cx);
            } else if cx.out.outer_self_calls.contains(&e.id) {
                // Reads an enclosing function's `self` from its hidden slot.
                (cx.visit)(Site::Var(e.span), nest);
            }
            walk_args(&call.args, nest, cx);
            if let Some(b) = &call.block {
                let inlined = crate::iter::shape(e, call, cx.out, cx.world).is_some()
                    || crate::iter::exec_shape(e, call, cx.out, cx.world).is_some();
                walk_block(b, nest, cx, inlined);
            }
        }
        MethodRef { recv, .. } => walk_expr(recv, nest, cx),
        Yield(args) => walk_args(args, nest, cx),
        Super { args, block } => {
            match args {
                Some(args) => walk_args(args, nest, cx),
                None => (cx.visit)(Site::ZSuper, nest),
            }
            if let Some(b) = block {
                walk_block(b, nest, cx, false);
            }
        }
        Assign { target, value } | OpAssign { target, value, .. } => {
            walk_lvalue(target, nest, cx);
            walk_expr(value, nest, cx);
        }
        MultiAssign { targets, value } => {
            walk_multi(targets, nest, cx);
            walk_expr(value, nest, cx);
        }
        TypedDecl { value, .. } => {
            (cx.visit)(Site::Var(e.span), nest);
            walk_expr(value, nest, cx);
        }
        And(a, b) | Or(a, b) => {
            walk_expr(a, nest, cx);
            walk_expr(b, nest, cx);
        }
        Not(a) => walk_expr(a, nest, cx),
        If { cond, then, els } => {
            walk_expr(cond, nest, cx);
            walk_body(then, nest, cx);
            if let Some(els) = els {
                walk_body(els, nest, cx);
            }
        }
        While { cond, body, .. } => {
            walk_expr(cond, nest, cx);
            walk_body(body, nest, cx);
        }
        Case {
            subject,
            whens,
            els,
        } => {
            if let Some(s) = subject {
                walk_expr(s, nest, cx);
            }
            for w in whens {
                walk_args(&w.conds, nest, cx);
                walk_body(&w.body, nest, cx);
            }
            if let Some(els) = els {
                walk_body(els, nest, cx);
            }
        }
        CaseIn { subject, arms, els } => {
            walk_expr(subject, nest, cx);
            for arm in arms {
                walk_pattern(&arm.pattern, nest, cx);
                if let Some(g) = &arm.guard {
                    walk_expr(&g.cond, nest, cx);
                }
                walk_body(&arm.body, nest, cx);
            }
            if let Some(els) = els {
                walk_body(els, nest, cx);
            }
        }
        MatchPattern { value, pattern, .. } => {
            walk_expr(value, nest, cx);
            walk_pattern(pattern, nest, cx);
        }
        Begin(block) => {
            walk_body(&block.body, nest, cx);
            for r in &block.rescues {
                if r.var.is_some() {
                    (cx.visit)(Site::Var(r.span), nest);
                }
                walk_body(&r.body, nest, cx);
            }
            if let Some(b) = &block.else_body {
                walk_body(b, nest, cx);
            }
            if let Some(b) = &block.ensure {
                walk_body(b, nest, cx);
            }
        }
        Return(v) | Break(v) | Next(v) => {
            if let Some(x) = v {
                walk_expr(x, nest, cx);
            }
        }
        Seq(exprs) => walk_body(exprs, nest, cx),
        ClassDef(_)
        | ModuleDef(_)
        | DataDef(_)
        | EnumDef(_)
        | ExtensionDef(_)
        | MethodDef(_)
        | FieldDecl(_)
        | AttrDecl { .. }
        | Mixin { .. }
        | Visibility { .. }
        | Alias { .. }
        | TypeAlias { .. }
        | ConstAssign { .. }
        | Extern { .. } => {}
    }
}
