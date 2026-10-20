//! Definite initialization of fields.
//!
//! A *required* field (a declared type that does not admit `nil`, and no
//! default) must be assigned on every path through `initialize`, and the
//! new object must not be used before all of them are: no `self`, no
//! call on the implicit receiver that may run user code, no read of a
//! field that is not assigned yet. A subclass assigns its own required
//! fields before `super`, which assigns the inherited ones (so a method
//! the superclass's `initialize` calls, and the subclass overrides, sees
//! them). Hence a field's value always has the field's declared type,
//! which compiled code relies on.

use std::collections::{BTreeSet, HashSet};

use quarz_syntax::ast::*;
use quarz_syntax::Span;

use crate::check::CallTarget;
use crate::types::MethodId;

/// Assigned fields at a point; `None` once control cannot reach it.
type St = Option<BTreeSet<String>>;

pub struct InitCheck<'a> {
    /// Every required field, own and inherited.
    pub required: &'a BTreeSet<String>,
    /// The class's own required fields.
    pub own: &'a BTreeSet<String>,
    pub calls: &'a dyn Fn(NodeId) -> Option<CallTarget>,
    /// Whether calling `method` on the implicit receiver may run user
    /// code that sees the object (a native, or a `Kernel` function,
    /// does not).
    pub runs_user_code: &'a dyn Fn(MethodId) -> bool,
    pub errors: Vec<(String, Span)>,
    /// One "used before" error is enough.
    reported: HashSet<&'static str>,
}

impl<'a> InitCheck<'a> {
    pub fn new(
        required: &'a BTreeSet<String>,
        own: &'a BTreeSet<String>,
        calls: &'a dyn Fn(NodeId) -> Option<CallTarget>,
        runs_user_code: &'a dyn Fn(MethodId) -> bool,
    ) -> Self {
        InitCheck {
            required,
            own,
            calls,
            runs_user_code,
            errors: Vec::new(),
            reported: HashSet::new(),
        }
    }

    /// Check `initialize`: `params` are its parameters in order (a
    /// default to evaluate, the field a `@x` parameter assigns).
    pub fn method(
        &mut self,
        params: &[(Option<&Expr>, Option<String>)],
        body: &[Expr],
        span: Span,
    ) {
        let mut st: St = Some(BTreeSet::new());
        for (default, field) in params {
            if let Some(d) = default {
                st = self.expr(d, st);
            }
            if let (Some(f), Some(s)) = (field, st.as_mut()) {
                s.insert(f.clone());
            }
        }
        let st = self.body(body, st);
        self.check_complete(
            &st,
            span,
            "is not assigned on every path through `initialize`",
        );
    }

    /// Check a field's default, run when the fields in `set` are.
    pub fn default(&mut self, e: &Expr, set: &[String]) {
        self.expr(e, Some(set.iter().cloned().collect()));
    }

    fn missing(&self, st: &St, of: &BTreeSet<String>) -> Option<String> {
        let s = st.as_ref()?;
        of.iter().find(|f| !s.contains(*f)).cloned()
    }

    fn check_complete(&mut self, st: &St, span: Span, what: &str) {
        if let Some(f) = self.missing(st, self.required) {
            self.errors.push((format!("field `@{f}` {what}"), span));
        }
    }

    fn self_use(&mut self, st: &St, span: Span) {
        if self.reported.contains("self") {
            return;
        }
        if let Some(f) = self.missing(st, self.required) {
            self.reported.insert("self");
            self.errors.push((
                format!("the object is used before field `@{f}` is assigned"),
                span,
            ));
        }
    }

    fn body(&mut self, es: &[Expr], mut st: St) -> St {
        for e in es {
            st = self.expr(e, st);
        }
        st
    }

    fn args(&mut self, args: &[Arg], mut st: St) -> St {
        for a in args {
            st = match a {
                Arg::Positional(e)
                | Arg::Splat(e)
                | Arg::DoubleSplat(e)
                | Arg::BlockPass(e)
                | Arg::Keyword { value: e, .. } => self.expr(e, st),
            };
        }
        st
    }

    fn parts(&mut self, parts: &[StrPart], mut st: St) -> St {
        for p in parts {
            if let StrPart::Interp(e) = p {
                st = self.expr(e, st);
            }
        }
        st
    }

    /// A block may run at any later time, or never: what it uses is
    /// checked against the state where it is written, what it assigns
    /// does not count.
    fn block(&mut self, b: &Block, st: &St) {
        let mut inner = st.clone();
        for p in &b.params.list {
            if let Some(d) = &p.default {
                inner = self.expr(d, inner);
            }
        }
        self.body(&b.body, inner);
    }

    fn join(a: St, b: St) -> St {
        match (a, b) {
            (None, x) | (x, None) => x,
            (Some(a), Some(b)) => Some(a.intersection(&b).cloned().collect()),
        }
    }

    fn assign(&mut self, target: &LValue, st: St) -> St {
        match target {
            LValue::IVar(name) => st.map(|mut s| {
                s.insert(name.clone());
                s
            }),
            LValue::Attr { recv, .. } => self.expr(recv, st),
            LValue::Index { recv, args } => {
                let st = self.expr(recv, st);
                self.args(args, st)
            }
            LValue::Local { .. } | LValue::Const(_) => st,
        }
    }

    fn multi(&mut self, targets: &[MultiTarget], mut st: St) -> St {
        for t in targets {
            st = match t {
                MultiTarget::Single(l) | MultiTarget::Splat(Some(l)) => self.assign(l, st),
                MultiTarget::Splat(None) => st,
                MultiTarget::Nested(ts) => self.multi(ts, st),
            };
        }
        st
    }

    fn expr(&mut self, e: &Expr, st: St) -> St {
        match &e.kind {
            ExprKind::Nil
            | ExprKind::True
            | ExprKind::False
            | ExprKind::Int(_)
            | ExprKind::Float(_)
            | ExprKind::Bytes(_)
            | ExprKind::Symbol(_)
            | ExprKind::Magic(_)
            | ExprKind::Local(_)
            | ExprKind::Const(_)
            | ExprKind::TypeApp(_)
            | ExprKind::Retry
            | ExprKind::ClassDef(_)
            | ExprKind::ModuleDef(_)
            | ExprKind::DataDef(_)
            | ExprKind::EnumDef(_)
            | ExprKind::ExtensionDef(_)
            | ExprKind::MethodDef(_)
            | ExprKind::FieldDecl(_)
            | ExprKind::AttrDecl { .. }
            | ExprKind::Mixin { .. }
            | ExprKind::Visibility { .. }
            | ExprKind::Alias { .. }
            | ExprKind::TypeAlias { .. }
            | ExprKind::Using(_)
            | ExprKind::Require { .. }
            | ExprKind::Extern { .. } => st,
            ExprKind::SelfRef => {
                self.self_use(&st, e.span);
                st
            }
            ExprKind::IVar(name) => {
                if self.required.contains(name)
                    && st.as_ref().is_some_and(|s| !s.contains(name))
                    && self.reported.insert("read")
                {
                    self.errors.push((
                        format!("field `@{name}` is read before it is assigned"),
                        e.span,
                    ));
                }
                st
            }
            ExprKind::Str(parts) | ExprKind::DSymbol(parts) => self.parts(parts, st),
            ExprKind::Regexp { parts, .. } => self.parts(parts, st),
            ExprKind::Array(items) => self.args(items, st),
            ExprKind::Hash(entries) => {
                let mut st = st;
                for h in entries {
                    st = match h {
                        HashEntry::Pair { key, value } => {
                            let st = self.expr(key, st);
                            self.expr(value, st)
                        }
                        HashEntry::DoubleSplat(e) => self.expr(e, st),
                    };
                }
                st
            }
            ExprKind::Range { lo, hi, .. } => {
                let mut st = st;
                for x in [lo, hi].into_iter().flatten() {
                    st = self.expr(x, st);
                }
                st
            }
            ExprKind::Lambda(b) => {
                self.block(b, &st);
                st
            }
            ExprKind::Call(call) => {
                let st = match &call.recv {
                    Some(r) => self.expr(r, st),
                    None => st,
                };
                let st = self.args(&call.args, st);
                if call.recv.is_none() {
                    let user = match (self.calls)(e.id) {
                        Some(CallTarget::Method { method }) => (self.runs_user_code)(method),
                        _ => false,
                    };
                    if user {
                        self.self_use(&st, e.span);
                    }
                }
                if let Some(b) = &call.block {
                    self.block(b, &st);
                }
                st
            }
            ExprKind::MethodRef { recv, .. } => self.expr(recv, st),
            ExprKind::Yield(args) => self.args(args, st),
            ExprKind::Super { args, block } => {
                let st = match args {
                    Some(a) => self.args(a, st),
                    None => st,
                };
                if let Some(f) = self.missing(&st, self.own) {
                    self.errors.push((
                        format!("field `@{f}` must be assigned before `super`"),
                        e.span,
                    ));
                }
                if let Some(b) = block {
                    self.block(b, &st);
                }
                // The superclass's `initialize` assigned the rest.
                st.map(|mut s| {
                    s.extend(self.required.iter().cloned());
                    s
                })
            }
            ExprKind::Assign { target, value } => {
                let st = self.expr(value, st);
                self.assign(target, st)
            }
            ExprKind::OpAssign { target, value, .. } => {
                let st = match &**target {
                    LValue::IVar(name) => self.expr(
                        &Expr {
                            id: e.id,
                            span: e.span,
                            kind: ExprKind::IVar(name.clone()),
                        },
                        st,
                    ),
                    _ => st,
                };
                let st = self.expr(value, st);
                self.assign(target, st)
            }
            ExprKind::MultiAssign { targets, value } => {
                let st = self.expr(value, st);
                self.multi(targets, st)
            }
            ExprKind::TypedDecl { value, .. } => self.expr(value, st),
            ExprKind::And(a, b) | ExprKind::Or(a, b) => {
                let st = self.expr(a, st);
                let after_b = self.expr(b, st.clone());
                Self::join(st, after_b)
            }
            ExprKind::Not(a) => self.expr(a, st),
            ExprKind::If { cond, then, els } => {
                let st = self.expr(cond, st);
                let t = self.body(then, st.clone());
                let f = match els {
                    Some(els) => self.body(els, st),
                    None => st,
                };
                Self::join(t, f)
            }
            ExprKind::While {
                cond,
                body,
                do_while,
                ..
            } => {
                if *do_while {
                    let st = self.body(body, st);
                    self.expr(cond, st)
                } else {
                    // The body may not run at all, and a `break` leaves
                    // it with no less than the state after the test.
                    let st = self.expr(cond, st);
                    self.body(body, st.clone());
                    st
                }
            }
            ExprKind::Case {
                subject,
                whens,
                els,
            } => {
                let mut st = match subject {
                    Some(s) => self.expr(s, st),
                    None => st,
                };
                let mut out: St = None;
                for w in whens {
                    st = self.args(&w.conds, st);
                    let b = self.body(&w.body, st.clone());
                    out = Self::join(out, b);
                }
                let e = match els {
                    Some(els) => self.body(els, st),
                    None => st,
                };
                Self::join(out, e)
            }
            ExprKind::CaseIn { subject, arms, els } => {
                let st = self.expr(subject, st);
                let mut out: St = None;
                for arm in arms {
                    let mut a = st.clone();
                    if let Some(g) = &arm.guard {
                        a = self.expr(&g.cond, a);
                    }
                    let b = self.body(&arm.body, a);
                    out = Self::join(out, b);
                }
                // No arm matching raises unless there is an `else`.
                match els {
                    Some(els) => {
                        let e = self.body(els, st);
                        Self::join(out, e)
                    }
                    None => out,
                }
            }
            ExprKind::MatchPattern { value, .. } => self.expr(value, st),
            ExprKind::Begin(b) => {
                let entry = st.clone();
                let mut end = self.body(&b.body, st);
                if let Some(els) = &b.else_body {
                    end = self.body(els, end);
                }
                for r in &b.rescues {
                    // Raised from anywhere in the body.
                    let rescued = self.body(&r.body, entry.clone());
                    end = Self::join(end, rescued);
                }
                if let Some(ens) = &b.ensure {
                    // Runs on every exit, possibly right after the entry.
                    let at_ensure = self.body(ens, entry);
                    if let (Some(e), Some(a)) = (end.as_mut(), at_ensure) {
                        e.extend(a);
                    }
                }
                end
            }
            ExprKind::Return(v) => {
                let st = match v {
                    Some(v) => self.expr(v, st),
                    None => st,
                };
                self.check_complete(&st, e.span, "is not assigned when `initialize` returns");
                None
            }
            ExprKind::Break(v) | ExprKind::Next(v) => {
                let st = match v {
                    Some(v) => self.expr(v, st),
                    None => st,
                };
                // Control continues after the loop (or the block's
                // call) with no less than the state there.
                let _ = st;
                None
            }
            ExprKind::Seq(es) => self.body(es, st),
            ExprKind::ConstAssign { value, .. } => self.expr(value, st),
        }
    }
}
