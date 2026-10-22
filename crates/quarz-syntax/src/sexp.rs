//! A compact S-expression rendering of the AST, for debugging and tests.

use crate::ast::*;
use std::fmt::Write;

pub fn program_to_sexp(program: &Program) -> String {
    let mut out = String::new();
    for expr in &program.body {
        expr_to_sexp(expr, &mut out);
        out.push('\n');
    }
    out
}

pub fn expr_sexp(expr: &Expr) -> String {
    let mut out = String::new();
    expr_to_sexp(expr, &mut out);
    out
}

fn list(out: &mut String, head: &str, items: impl FnOnce(&mut String)) {
    out.push('(');
    out.push_str(head);
    items(out);
    out.push(')');
}

fn body(out: &mut String, exprs: &[Expr]) {
    for e in exprs {
        out.push(' ');
        expr_to_sexp(e, out);
    }
}

fn opt_body(out: &mut String, label: &str, exprs: &Option<Vec<Expr>>) {
    if let Some(exprs) = exprs {
        out.push(' ');
        list(out, label, |o| body(o, exprs));
    }
}

fn str_parts(out: &mut String, parts: &[StrPart]) {
    for part in parts {
        out.push(' ');
        match part {
            StrPart::Lit(s) => {
                let _ = write!(out, "{s:?}");
            }
            StrPart::Interp(e) => list(out, "interp", |o| {
                o.push(' ');
                expr_to_sexp(e, o)
            }),
        }
    }
}

fn args(out: &mut String, args: &[Arg]) {
    for arg in args {
        out.push(' ');
        match arg {
            Arg::Positional(e) => expr_to_sexp(e, out),
            Arg::Splat(e) => list(out, "splat", |o| {
                o.push(' ');
                expr_to_sexp(e, o)
            }),
            Arg::DoubleSplat(e) => list(out, "splat2", |o| {
                o.push(' ');
                expr_to_sexp(e, o)
            }),
            Arg::BlockPass(e) => list(out, "blockpass", |o| {
                o.push(' ');
                expr_to_sexp(e, o)
            }),
            Arg::Keyword { name, value, .. } => {
                let _ = write!(out, "{name}: ");
                expr_to_sexp(value, out);
            }
        }
    }
}

fn block(out: &mut String, b: &Block) {
    out.push(' ');
    list(out, "block", |o| {
        params(o, &b.params);
        body(o, &b.body);
    });
}

fn params(out: &mut String, ps: &Params) {
    out.push(' ');
    list(out, "params", |o| {
        for p in &ps.list {
            o.push(' ');
            let prefix = match p.kind {
                ParamKind::Positional => "",
                ParamKind::Rest => "*",
                ParamKind::KeywordOnly => "kw:",
                ParamKind::KeywordRest => "**",
                ParamKind::Block => "&",
            };
            let ivar = if p.assigns_ivar { "@" } else { "" };
            let _ = write!(o, "{prefix}{ivar}{}", p.name);
            if let Some(ty) = &p.ty {
                o.push(':');
                o.push_str(&type_sexp(ty));
            }
            if let Some(d) = &p.default {
                o.push('=');
                expr_to_sexp(d, o);
            }
        }
    });
}

pub fn type_sexp(ty: &TypeExpr) -> String {
    match &ty.kind {
        TypeExprKind::Named { path, args } => {
            let mut s = path.to_string();
            if !args.is_empty() {
                s.push('[');
                s.push_str(&args.iter().map(type_sexp).collect::<Vec<_>>().join(", "));
                s.push(']');
            }
            s
        }
        TypeExprKind::Nilable(t) => format!("{}?", type_sexp(t)),
        TypeExprKind::Union(ts) => ts.iter().map(type_sexp).collect::<Vec<_>>().join(" | "),
        TypeExprKind::Tuple(ts) => format!(
            "[{}]",
            ts.iter().map(type_sexp).collect::<Vec<_>>().join(", ")
        ),
        TypeExprKind::Proc {
            recv,
            params,
            ret,
            shareable,
        } => format!(
            "{}{}({}) -> {}",
            if *shareable { "shareable " } else { "" },
            recv.as_ref()
                .map(|r| format!("{}.", type_sexp(r)))
                .unwrap_or_default(),
            params.iter().map(type_sexp).collect::<Vec<_>>().join(", "),
            type_sexp(ret)
        ),
        TypeExprKind::SelfType => "self".to_string(),
        TypeExprKind::Nothing => "Nothing".to_string(),
    }
}

fn type_params(out: &mut String, tps: &[TypeParam]) {
    if tps.is_empty() {
        return;
    }
    out.push(' ');
    list(out, "tparams", |o| {
        for tp in tps {
            o.push(' ');
            match tp.variance {
                Variance::Covariant => o.push_str("out "),
                Variance::Contravariant => o.push_str("in "),
                Variance::Invariant => {}
            }
            o.push_str(&tp.name);
            if !tp.bounds.is_empty() {
                o.push(':');
                o.push_str(
                    &tp.bounds
                        .iter()
                        .map(type_sexp)
                        .collect::<Vec<_>>()
                        .join("&"),
                );
            }
        }
    });
}

fn lvalue(out: &mut String, lv: &LValue) {
    match lv {
        LValue::Local { name, .. } => out.push_str(name),
        LValue::IVar(n) => {
            let _ = write!(out, "@{n}");
        }
        LValue::Const(n) => out.push_str(n),
        LValue::Attr {
            recv,
            name,
            safe_nav,
        } => list(out, "attr", |o| {
            o.push(' ');
            expr_to_sexp(recv, o);
            let _ = write!(o, " {}{name}", if *safe_nav { "&." } else { "." });
        }),
        LValue::Index { recv, args: a } => list(out, "index", |o| {
            o.push(' ');
            expr_to_sexp(recv, o);
            args(o, a);
        }),
    }
}

fn multi_target(out: &mut String, t: &MultiTarget) {
    match t {
        MultiTarget::Single(lv) => lvalue(out, lv),
        MultiTarget::Splat(None) => out.push('*'),
        MultiTarget::Splat(Some(lv)) => {
            out.push('*');
            lvalue(out, lv);
        }
        MultiTarget::Nested(ts) => list(out, "nested", |o| {
            for t in ts {
                o.push(' ');
                multi_target(o, t);
            }
        }),
    }
}

pub fn pattern_sexp(pat: &Pattern) -> String {
    let mut out = String::new();
    pattern(&mut out, pat);
    out
}

fn pattern(out: &mut String, pat: &Pattern) {
    match &pat.kind {
        PatternKind::Value(e) => expr_to_sexp(e, out),
        PatternKind::Pin(e) => {
            out.push('^');
            expr_to_sexp(e, out);
        }
        PatternKind::Bind(n) => out.push_str(n),
        PatternKind::Capture(p, n) => list(out, "capture", |o| {
            o.push(' ');
            pattern(o, p);
            let _ = write!(o, " {n}");
        }),
        PatternKind::Alt(ps) => list(out, "alt", |o| {
            for p in ps {
                o.push(' ');
                pattern(o, p);
            }
        }),
        PatternKind::Const(path) => out.push_str(&path.to_string()),
        PatternKind::ConstArray(path, ap) => list(out, &path.to_string(), |o| array_pattern(o, ap)),
        PatternKind::ConstHash(path, hp) => list(out, &path.to_string(), |o| hash_pattern(o, hp)),
        PatternKind::Array(ap) => list(out, "arr", |o| array_pattern(o, ap)),
        PatternKind::Find {
            pre_rest,
            middle,
            post_rest,
        } => list(out, "find", |o| {
            let _ = write!(o, " *{}", pre_rest.as_deref().unwrap_or(""));
            for p in middle {
                o.push(' ');
                pattern(o, p);
            }
            let _ = write!(o, " *{}", post_rest.as_deref().unwrap_or(""));
        }),
        PatternKind::Hash(hp) => list(out, "hash", |o| hash_pattern(o, hp)),
        PatternKind::Range { lo, hi, exclusive } => list(out, "range", |o| {
            if let Some(lo) = lo {
                o.push(' ');
                expr_to_sexp(lo, o);
            }
            o.push_str(if *exclusive { " ... " } else { " .. " });
            if let Some(hi) = hi {
                expr_to_sexp(hi, o);
            }
        }),
    }
}

fn array_pattern(out: &mut String, ap: &ArrayPattern) {
    for p in &ap.pre {
        out.push(' ');
        pattern(out, p);
    }
    if let Some(rest) = &ap.rest {
        let _ = write!(out, " *{}", rest.as_deref().unwrap_or(""));
    }
    for p in &ap.post {
        out.push(' ');
        pattern(out, p);
    }
}

fn hash_pattern(out: &mut String, hp: &HashPattern) {
    for pair in &hp.pairs {
        let _ = write!(out, " {}:", pair.key);
        if let Some(p) = &pair.pattern {
            out.push(' ');
            pattern(out, p);
        }
    }
    match &hp.rest {
        Some(HashPatternRest::Bind(n)) => {
            let _ = write!(out, " **{n}");
        }
        Some(HashPatternRest::Nil) => out.push_str(" **nil"),
        None => {}
    }
}

fn method_def(out: &mut String, d: &MethodDef) {
    let head = if d.singleton { "defs" } else { "def" };
    list(out, head, |o| {
        if d.is_abstract {
            o.push_str(" abstract");
        }
        if d.is_override {
            o.push_str(" override");
        }
        if d.is_native {
            o.push_str(" native");
        }
        if let Some(v) = d.visibility {
            let _ = write!(o, " {v:?}");
        }
        let _ = write!(o, " {}", d.name);
        type_params(o, &d.type_params);
        params(o, &d.params);
        if let Some(ret) = &d.ret {
            let _ = write!(o, " -> {}", type_sexp(ret));
        }
        if let Some(b) = &d.body {
            body(o, b);
        }
    });
}

fn fields(out: &mut String, fs: &[FieldDecl]) {
    for f in fs {
        let _ = write!(out, " {}:{}", f.name, type_sexp(&f.ty));
        if let Some(d) = &f.default {
            out.push('=');
            expr_to_sexp(d, out);
        }
    }
}

pub fn expr_to_sexp(expr: &Expr, out: &mut String) {
    use ExprKind::*;
    match &expr.kind {
        // Shown as the comprehension it expands to.
        For(f) => expr_to_sexp(&f.comprehension, out),
        Nil => out.push_str("nil"),
        True => out.push_str("true"),
        False => out.push_str("false"),
        SelfRef => out.push_str("self"),
        Int(lit) => {
            if lit.base == 10 {
                out.push_str(&lit.digits);
            } else {
                let _ = write!(out, "{}r{}", lit.digits, lit.base);
            }
        }
        Float(f) => {
            let _ = write!(out, "{f:?}");
        }
        Str(parts) => list(out, "str", |o| str_parts(o, parts)),
        Bytes(bytes) => list(out, "bytes", |o| {
            o.push(' ');
            for b in bytes {
                let _ = write!(o, "{b:02x}");
            }
        }),
        Symbol(name) => {
            let simple = name
                .chars()
                .all(|c| c.is_alphanumeric() || c == '_' || c == '?' || c == '!' || c == '=');
            if simple {
                let _ = write!(out, ":{name}");
            } else {
                let _ = write!(out, ":{name:?}");
            }
        }
        DSymbol(parts) => list(out, "dsym", |o| str_parts(o, parts)),
        Regexp { parts, flags } => list(out, "regexp", |o| {
            str_parts(o, parts);
            if !flags.is_empty() {
                let _ = write!(o, " /{flags}");
            }
        }),
        Array(items) => list(out, "array", |o| args(o, items)),
        Hash(entries) => list(out, "hash", |o| {
            for e in entries {
                o.push(' ');
                match e {
                    HashEntry::Pair { key, value } => {
                        list(o, "pair", |o| {
                            o.push(' ');
                            expr_to_sexp(key, o);
                            o.push(' ');
                            expr_to_sexp(value, o);
                        });
                    }
                    HashEntry::DoubleSplat(e) => list(o, "splat2", |o| {
                        o.push(' ');
                        expr_to_sexp(e, o)
                    }),
                }
            }
        }),
        Range { lo, hi, exclusive } => list(out, "range", |o| {
            if let Some(lo) = lo {
                o.push(' ');
                expr_to_sexp(lo, o);
            }
            o.push_str(if *exclusive { " ... " } else { " .. " });
            if let Some(hi) = hi {
                expr_to_sexp(hi, o);
            }
        }),
        Lambda(b) => list(out, "lambda", |o| {
            params(o, &b.params);
            body(o, &b.body);
        }),
        Magic(m) => {
            let _ = write!(out, "{m:?}");
        }
        Local(name) => out.push_str(name),
        IVar(name) => {
            let _ = write!(out, "@{name}");
        }
        Const(path) => out.push_str(&path.to_string()),
        TypeApp(ty) => list(out, "type", |o| {
            o.push(' ');
            o.push_str(&type_sexp(ty));
        }),
        Call(call) => {
            let head = if call.safe_nav { "call&." } else { "call" };
            list(out, head, |o| {
                o.push(' ');
                match &call.recv {
                    Some(r) => expr_to_sexp(r, o),
                    None => o.push('_'),
                }
                let _ = write!(o, " {}", call.name);
                if !call.type_args.is_empty() {
                    o.push('[');
                    o.push_str(
                        &call
                            .type_args
                            .iter()
                            .map(type_sexp)
                            .collect::<Vec<_>>()
                            .join(", "),
                    );
                    o.push(']');
                }
                args(o, &call.args);
                if let Some(b) = &call.block {
                    block(o, b);
                }
            });
        }
        MethodRef { recv, name } => list(out, "methodref", |o| {
            o.push(' ');
            expr_to_sexp(recv, o);
            let _ = write!(o, " {name}");
        }),
        Yield(a) => list(out, "yield", |o| args(o, a)),
        Super { args: a, block: b } => list(out, "super", |o| {
            match a {
                Some(a) => args(o, a),
                None => o.push_str(" zsuper"),
            }
            if let Some(b) = b {
                block(o, b);
            }
        }),
        Assign { target, value } => list(out, "=", |o| {
            o.push(' ');
            lvalue(o, target);
            o.push(' ');
            expr_to_sexp(value, o);
        }),
        OpAssign { target, op, value } => list(out, op.as_str(), |o| {
            o.push(' ');
            lvalue(o, target);
            o.push(' ');
            expr_to_sexp(value, o);
        }),
        MultiAssign { targets, value } => list(out, "masgn", |o| {
            o.push(' ');
            list(o, "targets", |o| {
                for t in targets {
                    o.push(' ');
                    multi_target(o, t);
                }
            });
            o.push(' ');
            expr_to_sexp(value, o);
        }),
        TypedDecl { name, ty, value } => list(out, "decl", |o| {
            let _ = write!(o, " {name}:{} ", type_sexp(ty));
            expr_to_sexp(value, o);
        }),
        And(a, b) => list(out, "and", |o| {
            o.push(' ');
            expr_to_sexp(a, o);
            o.push(' ');
            expr_to_sexp(b, o);
        }),
        Or(a, b) => list(out, "or", |o| {
            o.push(' ');
            expr_to_sexp(a, o);
            o.push(' ');
            expr_to_sexp(b, o);
        }),
        Not(a) => list(out, "not", |o| {
            o.push(' ');
            expr_to_sexp(a, o);
        }),
        If { cond, then, els } => list(out, "if", |o| {
            o.push(' ');
            expr_to_sexp(cond, o);
            o.push(' ');
            list(o, "then", |o| body(o, then));
            opt_body(o, "else", els);
        }),
        While {
            cond,
            body: b,
            negate,
            do_while,
        } => {
            let head = match (negate, do_while) {
                (false, false) => "while",
                (true, false) => "until",
                (false, true) => "do-while",
                (true, true) => "do-until",
            };
            list(out, head, |o| {
                o.push(' ');
                expr_to_sexp(cond, o);
                body(o, b);
            })
        }
        Case {
            subject,
            whens,
            els,
        } => list(out, "case", |o| {
            o.push(' ');
            match subject {
                Some(s) => expr_to_sexp(s, o),
                None => o.push('_'),
            }
            for w in whens {
                o.push(' ');
                list(o, "when", |o| {
                    o.push(' ');
                    list(o, "conds", |o| args(o, &w.conds));
                    body(o, &w.body);
                });
            }
            opt_body(o, "else", els);
        }),
        CaseIn { subject, arms, els } => list(out, "case-in", |o| {
            o.push(' ');
            expr_to_sexp(subject, o);
            for arm in arms {
                o.push(' ');
                list(o, "in ", |o| {
                    pattern(o, &arm.pattern);
                    if let Some(g) = &arm.guard {
                        o.push(' ');
                        list(o, if g.negate { "unless" } else { "if" }, |o| {
                            o.push(' ');
                            expr_to_sexp(&g.cond, o);
                        });
                    }
                    body(o, &arm.body);
                });
            }
            opt_body(o, "else", els);
        }),
        MatchPattern {
            value,
            pattern: p,
            raises,
        } => list(out, if *raises { "=>" } else { "in" }, |o| {
            o.push(' ');
            expr_to_sexp(value, o);
            o.push(' ');
            pattern(o, p);
        }),
        Begin(b) => list(out, "begin", |o| {
            body(o, &b.body);
            for r in &b.rescues {
                o.push(' ');
                list(o, "rescue", |o| {
                    for c in &r.classes {
                        let _ = write!(o, " {}", type_sexp(c));
                    }
                    if let Some(v) = &r.var {
                        let _ = write!(o, " => {v}");
                    }
                    body(o, &r.body);
                });
            }
            opt_body(o, "else", &b.else_body);
            opt_body(o, "ensure", &b.ensure);
        }),
        Return(v) => list(out, "return", |o| {
            if let Some(v) = v {
                o.push(' ');
                expr_to_sexp(v, o);
            }
        }),
        Break(v) => list(out, "break", |o| {
            if let Some(v) = v {
                o.push(' ');
                expr_to_sexp(v, o);
            }
        }),
        Next(v) => list(out, "next", |o| {
            if let Some(v) = v {
                o.push(' ');
                expr_to_sexp(v, o);
            }
        }),
        Retry => out.push_str("(retry)"),
        Seq(es) => list(out, "seq", |o| body(o, es)),
        ClassDef(c) => list(
            out,
            if c.is_abstract {
                "abstract-class"
            } else {
                "class"
            },
            |o| {
                let _ = write!(o, " {}", c.name);
                type_params(o, &c.type_params);
                if let Some(sup) = &c.superclass {
                    let _ = write!(o, " < {}", type_sexp(sup));
                }
                body(o, &c.body);
            },
        ),
        ModuleDef(m) => list(out, "module", |o| {
            let _ = write!(o, " {}", m.name);
            type_params(o, &m.type_params);
            body(o, &m.body);
        }),
        DataDef(d) => list(out, "data", |o| {
            let _ = write!(o, " {}", d.name);
            type_params(o, &d.type_params);
            o.push(' ');
            list(o, "fields", |o| fields(o, &d.fields));
            body(o, &d.body);
        }),
        EnumDef(e) => list(out, "enum", |o| {
            let _ = write!(o, " {}", e.name);
            type_params(o, &e.type_params);
            for v in &e.variants {
                o.push(' ');
                list(o, &v.name, |o| fields(o, &v.fields));
            }
            body(o, &e.body);
        }),
        ExtensionDef(e) => list(out, "extension", |o| {
            let _ = write!(o, " {}", type_sexp(&e.target));
            type_params(o, &e.type_params);
            body(o, &e.body);
        }),
        MethodDef(d) => method_def(out, d),
        FieldDecl(f) => list(out, if f.mutable { "var" } else { "field" }, |o| {
            fields(o, std::slice::from_ref(f))
        }),
        AttrDecl { kind, names } => list(out, &format!("attr_{kind:?}").to_lowercase(), |o| {
            for n in names {
                let _ = write!(o, " {n}");
            }
        }),
        Mixin { kind, types } => list(out, &format!("{kind:?}").to_lowercase(), |o| {
            for t in types {
                let _ = write!(o, " {}", type_sexp(t));
            }
        }),
        Visibility { visibility, names } => {
            list(out, &format!("{visibility:?}").to_lowercase(), |o| {
                for n in names {
                    let _ = write!(o, " {n}");
                }
            })
        }
        Alias { new_name, old_name } => {
            let _ = write!(out, "(alias {new_name} {old_name})");
        }
        TypeAlias {
            name,
            type_params: tps,
            ty,
        } => list(out, "type", |o| {
            let _ = write!(o, " {name}");
            type_params(o, tps);
            let _ = write!(o, " {}", type_sexp(ty));
        }),
        ConstAssign { name, value } => list(out, "const", |o| {
            let _ = write!(o, " {name} ");
            expr_to_sexp(value, o);
        }),
        Using(path) => {
            let _ = write!(out, "(using {path})");
        }
        Require { path, relative } => {
            let _ = write!(
                out,
                "({} {path:?})",
                if *relative {
                    "require_relative"
                } else {
                    "require"
                }
            );
        }
        Extern { abi, decls } => list(out, "extern", |o| {
            let _ = write!(o, " {abi:?}");
            for d in decls {
                o.push(' ');
                method_def(o, d);
            }
        }),
    }
}
