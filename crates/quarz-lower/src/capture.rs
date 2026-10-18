//! Which local variable slots of a function are referenced from nested
//! blocks (and therefore live in a heap frame rather than a register).

use std::collections::HashSet;

use quarz_syntax::ast::*;
use quarz_syntax::Span;
use quarz_types::{Output, VarRef};

/// A place where the checker recorded a variable reference, or an
/// implicit reference to every parameter (`super` without arguments).
#[derive(Clone, Copy, Debug)]
pub enum Site {
    Var(Span),
    ZSuper,
}

/// Slots of the function whose body is `body` (plus `extra` expressions
/// evaluated in the same frame, such as parameter defaults) that nested
/// blocks refer to.
pub fn captured_slots(body: &[Expr], extra: &[&Expr], out: &Output, nparams: u32) -> HashSet<u32> {
    let mut captured = HashSet::new();
    let mut visit = |site: Site, nesting: u32| {
        if nesting == 0 {
            return;
        }
        match site {
            Site::Var(span) => {
                if let Some(VarRef { depth, slot }) = out.var_refs.get(&span) {
                    if *depth == nesting {
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
    for e in body {
        walk_expr(e, 0, &mut visit);
    }
    for e in extra {
        walk_expr(e, 0, &mut visit);
    }
    captured
}

pub fn walk_body(body: &[Expr], nesting: u32, f: &mut impl FnMut(Site, u32)) {
    for e in body {
        walk_expr(e, nesting, f);
    }
}

fn walk_parts(parts: &[StrPart], nesting: u32, f: &mut impl FnMut(Site, u32)) {
    for p in parts {
        if let StrPart::Interp(e) = p {
            walk_expr(e, nesting, f);
        }
    }
}

fn walk_args(args: &[Arg], nesting: u32, f: &mut impl FnMut(Site, u32)) {
    for a in args {
        match a {
            Arg::Positional(e) | Arg::Splat(e) | Arg::DoubleSplat(e) | Arg::BlockPass(e) => {
                walk_expr(e, nesting, f)
            }
            Arg::Keyword { value, .. } => walk_expr(value, nesting, f),
        }
    }
}

fn walk_block(block: &Block, nesting: u32, f: &mut impl FnMut(Site, u32)) {
    for p in &block.params.list {
        if let Some(d) = &p.default {
            walk_expr(d, nesting + 1, f);
        }
    }
    walk_body(&block.body, nesting + 1, f);
}

fn walk_lvalue(lv: &LValue, nesting: u32, f: &mut impl FnMut(Site, u32)) {
    match lv {
        LValue::Local { span, .. } => f(Site::Var(*span), nesting),
        LValue::IVar(_) | LValue::Const(_) => {}
        LValue::Attr { recv, .. } => walk_expr(recv, nesting, f),
        LValue::Index { recv, args } => {
            walk_expr(recv, nesting, f);
            walk_args(args, nesting, f);
        }
    }
}

fn walk_multi(targets: &[MultiTarget], nesting: u32, f: &mut impl FnMut(Site, u32)) {
    for t in targets {
        match t {
            MultiTarget::Single(lv) | MultiTarget::Splat(Some(lv)) => walk_lvalue(lv, nesting, f),
            MultiTarget::Splat(None) => {}
            MultiTarget::Nested(ts) => walk_multi(ts, nesting, f),
        }
    }
}

pub fn walk_pattern(pat: &Pattern, nesting: u32, f: &mut impl FnMut(Site, u32)) {
    match &pat.kind {
        PatternKind::Value(e) | PatternKind::Pin(e) => walk_expr(e, nesting, f),
        PatternKind::Bind(_) => f(Site::Var(pat.span), nesting),
        PatternKind::Capture(inner, _) => {
            walk_pattern(inner, nesting, f);
            f(Site::Var(pat.span), nesting);
        }
        PatternKind::Alt(alts) => {
            for a in alts {
                walk_pattern(a, nesting, f);
            }
        }
        PatternKind::Const(_) => {}
        PatternKind::ConstArray(_, ap) => walk_array_pattern(ap, pat.span, nesting, f),
        PatternKind::Array(ap) => walk_array_pattern(ap, pat.span, nesting, f),
        PatternKind::ConstHash(_, hp) => walk_hash_pattern(hp, pat.span, nesting, f),
        PatternKind::Hash(hp) => walk_hash_pattern(hp, pat.span, nesting, f),
        PatternKind::Find {
            pre_rest,
            middle,
            post_rest,
        } => {
            for p in middle {
                walk_pattern(p, nesting, f);
            }
            if pre_rest.is_some() {
                f(Site::Var(pat.span), nesting);
            }
            if post_rest.is_some() {
                f(Site::Var(Span::empty(pat.span.end as usize)), nesting);
            }
        }
        PatternKind::Range { lo, hi, .. } => {
            if let Some(e) = lo {
                walk_expr(e, nesting, f);
            }
            if let Some(e) = hi {
                walk_expr(e, nesting, f);
            }
        }
    }
}

fn walk_array_pattern(ap: &ArrayPattern, span: Span, nesting: u32, f: &mut impl FnMut(Site, u32)) {
    for p in ap.pre.iter().chain(ap.post.iter()) {
        walk_pattern(p, nesting, f);
    }
    if let Some(Some(_)) = &ap.rest {
        f(Site::Var(span), nesting);
    }
}

fn walk_hash_pattern(hp: &HashPattern, span: Span, nesting: u32, f: &mut impl FnMut(Site, u32)) {
    for pair in &hp.pairs {
        match &pair.pattern {
            Some(p) => walk_pattern(p, nesting, f),
            None => f(Site::Var(pair.span), nesting),
        }
    }
    if let Some(HashPatternRest::Bind(_)) = &hp.rest {
        f(Site::Var(span), nesting);
    }
}

pub fn walk_expr(e: &Expr, nesting: u32, f: &mut impl FnMut(Site, u32)) {
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
        Str(parts) | DSymbol(parts) | Regexp { parts, .. } => walk_parts(parts, nesting, f),
        Array(items) => walk_args(items, nesting, f),
        Hash(entries) => {
            for en in entries {
                match en {
                    HashEntry::Pair { key, value } => {
                        walk_expr(key, nesting, f);
                        walk_expr(value, nesting, f);
                    }
                    HashEntry::DoubleSplat(x) => walk_expr(x, nesting, f),
                }
            }
        }
        Range { lo, hi, .. } => {
            if let Some(x) = lo {
                walk_expr(x, nesting, f);
            }
            if let Some(x) = hi {
                walk_expr(x, nesting, f);
            }
        }
        Lambda(block) => walk_block(block, nesting, f),
        Local(_) => f(Site::Var(e.span), nesting),
        Call(call) => {
            if let Some(r) = &call.recv {
                walk_expr(r, nesting, f);
            }
            walk_args(&call.args, nesting, f);
            if let Some(b) = &call.block {
                walk_block(b, nesting, f);
            }
        }
        MethodRef { recv, .. } => walk_expr(recv, nesting, f),
        Yield(args) => walk_args(args, nesting, f),
        Super { args, block } => {
            match args {
                Some(args) => walk_args(args, nesting, f),
                None => f(Site::ZSuper, nesting),
            }
            if let Some(b) = block {
                walk_block(b, nesting, f);
            }
        }
        Assign { target, value } | OpAssign { target, value, .. } => {
            walk_lvalue(target, nesting, f);
            walk_expr(value, nesting, f);
        }
        MultiAssign { targets, value } => {
            walk_multi(targets, nesting, f);
            walk_expr(value, nesting, f);
        }
        TypedDecl { value, .. } => {
            f(Site::Var(e.span), nesting);
            walk_expr(value, nesting, f);
        }
        And(a, b) | Or(a, b) => {
            walk_expr(a, nesting, f);
            walk_expr(b, nesting, f);
        }
        Not(a) => walk_expr(a, nesting, f),
        If { cond, then, els } => {
            walk_expr(cond, nesting, f);
            walk_body(then, nesting, f);
            if let Some(els) = els {
                walk_body(els, nesting, f);
            }
        }
        While { cond, body, .. } => {
            walk_expr(cond, nesting, f);
            walk_body(body, nesting, f);
        }
        Case {
            subject,
            whens,
            els,
        } => {
            if let Some(s) = subject {
                walk_expr(s, nesting, f);
            }
            for w in whens {
                walk_args(&w.conds, nesting, f);
                walk_body(&w.body, nesting, f);
            }
            if let Some(els) = els {
                walk_body(els, nesting, f);
            }
        }
        CaseIn { subject, arms, els } => {
            walk_expr(subject, nesting, f);
            for arm in arms {
                walk_pattern(&arm.pattern, nesting, f);
                if let Some(g) = &arm.guard {
                    walk_expr(&g.cond, nesting, f);
                }
                walk_body(&arm.body, nesting, f);
            }
            if let Some(els) = els {
                walk_body(els, nesting, f);
            }
        }
        MatchPattern { value, pattern, .. } => {
            walk_expr(value, nesting, f);
            walk_pattern(pattern, nesting, f);
        }
        Begin(block) => {
            walk_body(&block.body, nesting, f);
            for r in &block.rescues {
                if r.var.is_some() {
                    f(Site::Var(r.span), nesting);
                }
                walk_body(&r.body, nesting, f);
            }
            if let Some(b) = &block.else_body {
                walk_body(b, nesting, f);
            }
            if let Some(b) = &block.ensure {
                walk_body(b, nesting, f);
            }
        }
        Return(v) | Break(v) | Next(v) => {
            if let Some(x) = v {
                walk_expr(x, nesting, f);
            }
        }
        Seq(exprs) => walk_body(exprs, nesting, f),
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
