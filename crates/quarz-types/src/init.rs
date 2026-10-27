//! Definite initialization of fields.
//!
//! A *required* field (a declared type that does not admit `nil`, and no
//! default) must be assigned on every path through `initialize`, and the
//! new object must not be used before all of them are: no `self`, no
//! call on the implicit receiver (but to a built-in `Kernel` function,
//! which takes no `self`: a native method on `self` may read its fields
//! too),
//! no read of a field that is not assigned yet. `raise`, and a call of a
//! method whose result type is `Nothing` (`exit`, `abort`; not one `&.`
//! may skip), ends a path. A
//! field's default does not use the object at all. A subclass assigns
//! its own required fields before `super`, which assigns the inherited
//! ones (so a method the superclass's `initialize` calls, and the
//! subclass overrides, sees them). Hence a field's value always has the
//! field's declared type, which compiled code relies on.

use rustc_hash::FxHashSet as HashSet;
use std::collections::BTreeSet;

use quarz_syntax::ast::*;
use quarz_syntax::token::OpAssign;
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
    /// Whether calling `method` on the implicit receiver uses the object
    /// (anything but a built-in `Kernel` function).
    pub uses_self: &'a dyn Fn(MethodId) -> bool,
    /// Whether `method`'s result type is `Nothing`: control does not get
    /// past a call of it.
    pub diverges: &'a dyn Fn(MethodId) -> bool,
    pub errors: Vec<(String, Span)>,
    /// The assignments and `super` calls after which the object becomes
    /// usable (every required field assigned) on some path, and whether
    /// it is from the start (after the parameters).
    pub usable_after: Vec<NodeId>,
    pub usable_on_entry: bool,
    /// Checking a field's default, where the object is not usable.
    in_default: bool,
    /// For each enclosing loop or block (innermost last): the states
    /// where a `break` or `next` leaves it (joined).
    exits: Vec<St>,
    /// One "used before" error is enough.
    reported: HashSet<&'static str>,
}

impl<'a> InitCheck<'a> {
    pub fn new(
        required: &'a BTreeSet<String>,
        own: &'a BTreeSet<String>,
        calls: &'a dyn Fn(NodeId) -> Option<CallTarget>,
        uses_self: &'a dyn Fn(MethodId) -> bool,
        diverges: &'a dyn Fn(MethodId) -> bool,
    ) -> Self {
        InitCheck {
            required,
            own,
            calls,
            uses_self,
            diverges,
            errors: Vec::new(),
            usable_after: Vec::new(),
            usable_on_entry: false,
            in_default: false,
            exits: Vec::new(),
            reported: HashSet::default(),
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
        // A default runs only when its argument is left out: what it
        // assigns does not count, nor is the object usable after it (it
        // runs before `initialize` proper, as Swift's default arguments).
        // The `@x` parameters are assigned after all the parameters.
        let noted = self.usable_after.len();
        for (default, _) in params {
            if let Some(d) = default {
                self.expr(d, st.clone());
            }
        }
        self.usable_after.truncate(noted);
        if let Some(s) = st.as_mut() {
            s.extend(params.iter().filter_map(|(_, f)| f.clone()));
        }
        self.usable_on_entry = self.complete(&st);
        let st = self.body(body, st);
        self.check_complete(
            &st,
            span,
            "is not assigned on every path through `initialize`",
        );
    }

    /// Check a field's default, run when the fields in `set` are: it may
    /// read those, and not use the object otherwise (docs/01 §3), even
    /// once it has assigned every field.
    pub fn default(&mut self, e: &Expr, set: &[String]) {
        self.in_default = true;
        self.expr(e, Some(set.iter().cloned().collect()));
    }

    /// Whether every required field is assigned (at a point control
    /// reaches).
    fn complete(&self, st: &St) -> bool {
        st.is_some() && self.missing(st, self.required).is_none()
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
        if self.in_default {
            if st.is_some() {
                self.reported.insert("self");
                self.errors
                    .push(("a field's default cannot use the object".to_string(), span));
            }
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
        // Its `next` and `break` leave the block, not a loop around it.
        self.exits.push(None);
        self.block_body(b, st);
        self.exits.pop();
    }

    fn block_body(&mut self, b: &Block, st: &St) {
        let mut inner = st.clone();
        for p in &b.params.list {
            if let Some(d) = &p.default {
                inner = self.expr(d, inner);
            }
        }
        self.body(&b.body, inner);
    }

    /// The expressions a pattern evaluates (values, pins, bounds) are
    /// checked against `st`; they assign nothing that counts.
    fn pattern(&mut self, p: &Pattern, st: &St) {
        match &p.kind {
            PatternKind::Value(e) | PatternKind::Pin(e) => {
                self.expr(e, st.clone());
            }
            PatternKind::Range { lo, hi, .. } => {
                for e in [lo, hi].into_iter().flatten() {
                    self.expr(e, st.clone());
                }
            }
            PatternKind::Capture(p, _) => self.pattern(p, st),
            PatternKind::Alt(ps) | PatternKind::Find { middle: ps, .. } => {
                for p in ps {
                    self.pattern(p, st);
                }
            }
            PatternKind::ConstArray(_, a) => self.array_pattern(a, st),
            PatternKind::Array(a) => self.array_pattern(a, st),
            PatternKind::ConstHash(_, h) => self.hash_pattern(h, st),
            PatternKind::Hash(h) => self.hash_pattern(h, st),
            PatternKind::Bind(_) | PatternKind::Const(_) => {}
        }
    }

    fn array_pattern(&mut self, a: &ArrayPattern, st: &St) {
        for p in a.pre.iter().chain(&a.post) {
            self.pattern(p, st);
        }
    }

    fn hash_pattern(&mut self, h: &HashPattern, st: &St) {
        for pair in &h.pairs {
            if let Some(p) = &pair.pattern {
                self.pattern(p, st);
            }
        }
    }

    fn join(a: St, b: St) -> St {
        match (a, b) {
            (None, x) | (x, None) => x,
            (Some(a), Some(b)) => Some(a.intersection(&b).cloned().collect()),
        }
    }

    fn assign(&mut self, target: &LValue, st: St) -> St {
        let st = self.operands(target, st);
        Self::set(target, st)
    }

    /// What a target evaluates before the value it is given (the
    /// receiver, the index): `recv[i] = v` runs `recv`, `i`, then `v`.
    fn operands(&mut self, target: &LValue, st: St) -> St {
        match target {
            LValue::Attr { recv, .. } => self.expr(recv, st),
            LValue::Index { recv, args } => {
                let st = self.expr(recv, st);
                self.args(args, st)
            }
            LValue::IVar(_) | LValue::Local { .. } | LValue::Const(_) => st,
        }
    }

    /// The assignment itself, once the operands and the value ran.
    fn set(target: &LValue, st: St) -> St {
        match target {
            LValue::IVar(name) => st.map(|mut s| {
                s.insert(name.clone());
                s
            }),
            _ => st,
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

    /// The state after `e`. Each expression after which it becomes
    /// complete is noted (an assignment, `super`, a `begin` whose `ensure`
    /// assigns the rest, and what encloses them, since a path may become
    /// complete only there): the object is usable after it.
    fn expr(&mut self, e: &Expr, st: St) -> St {
        let before = self.complete(&st);
        let after = self.expr_inner(e, st);
        if !before && self.complete(&after) {
            self.usable_after.push(e.id);
        }
        after
    }

    fn expr_inner(&mut self, e: &Expr, st: St) -> St {
        match &e.kind {
            // Both expansions assign the same.
            ExprKind::For(f) => self.expr(&f.comprehension, st),
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
                // `recv&.m(args)` runs nothing more on a nil receiver.
                let skipped = call.safe_nav.then(|| st.clone());
                let st = self.args(&call.args, st);
                // `raise` (the special form, docs/02): control does not
                // get past it.
                if call.recv.is_none() && call.name == "raise" {
                    return None;
                }
                if call.recv.is_none() {
                    let uses = match (self.calls)(e.id) {
                        Some(CallTarget::Method { method }) => (self.uses_self)(method),
                        _ => false,
                    };
                    if uses {
                        self.self_use(&st, e.span);
                    }
                }
                if let Some(b) = &call.block {
                    self.block(b, &st);
                }
                if let Some(CallTarget::Method { method }) = (self.calls)(e.id) {
                    // (Unless `recv&.m` skipped it.)
                    if (self.diverges)(method) {
                        return skipped.unwrap_or(None);
                    }
                }
                match skipped {
                    Some(nil) => Self::join(st, nil),
                    None => st,
                }
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
            ExprKind::Assign { target, value } => match &**target {
                // `recv&.x = value`: no value on a nil receiver.
                LValue::Attr {
                    recv,
                    safe_nav: true,
                    ..
                } => {
                    let st = self.expr(recv, st);
                    let after = self.expr(value, st.clone());
                    Self::join(st, after)
                }
                _ => {
                    let st = self.operands(target, st);
                    let st = self.expr(value, st);
                    Self::set(target, st)
                }
            },
            ExprKind::OpAssign { target, op, value } => {
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
                let st = self.operands(target, st);
                // `x ||= v` and `x &&= v` may leave `v` unevaluated.
                let skipped = matches!(op, OpAssign::OrOr | OpAssign::AndAnd).then(|| st.clone());
                let st = self.expr(value, st);
                let st = Self::set(target, st);
                match skipped {
                    Some(kept) => Self::join(st, kept),
                    None => st,
                }
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
                    // A `next` goes to the test and a `break` out of the
                    // loop, with what was assigned where they are.
                    self.exits.push(None);
                    let end = self.body(body, st);
                    let exits = self.exits.pop().flatten();
                    let tested = self.expr(cond, Self::join(end, exits.clone()));
                    Self::join(tested, exits)
                } else {
                    // The body may not run at all, and a `break` leaves
                    // it with no less than the state after the test.
                    let st = self.expr(cond, st);
                    self.exits.push(None);
                    self.body(body, st.clone());
                    self.exits.pop();
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
                    // The body runs after whichever condition matched.
                    let mut matched: St = None;
                    for c in &w.conds {
                        st = self.args(std::slice::from_ref(c), st);
                        matched = Self::join(matched, st.clone());
                    }
                    let b = self.body(&w.body, matched.or_else(|| st.clone()));
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
                    self.pattern(&arm.pattern, &st);
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
            ExprKind::MatchPattern { value, pattern, .. } => {
                let st = self.expr(value, st);
                self.pattern(pattern, &st);
                st
            }
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
                // Control continues at the loop's test or after it (or
                // after the block's call), with no less than the state
                // there: a do-while loop joins it (`exits`).
                if let Some(top) = self.exits.last_mut() {
                    *top = Self::join(top.take(), st);
                }
                None
            }
            ExprKind::Seq(es) => self.body(es, st),
            ExprKind::ConstAssign { value, .. } => self.expr(value, st),
        }
    }
}
