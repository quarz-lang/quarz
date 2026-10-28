//! Pattern checking: variable binding, narrowing and coverage.

use quarz_syntax::ast::*;
use quarz_syntax::Span;

use crate::check::Checker;
use crate::types::*;
use crate::world::*;

impl Checker {
    /// Check a pattern against the type of the matched value, declaring the
    /// variables it binds. Returns the type the value is narrowed to when
    /// the pattern matches.
    pub(crate) fn check_pattern(&mut self, pattern: &Pattern, value_ty: &Type) -> Type {
        let value_ty = self.resolve_ty(value_ty);
        match &pattern.kind {
            PatternKind::Bind(name) => {
                self.declare_pattern_var(name, value_ty.clone(), pattern.span);
                value_ty
            }
            PatternKind::Capture(inner, name) => {
                let narrowed = self.check_pattern(inner, &value_ty);
                self.declare_pattern_var(name, narrowed.clone(), pattern.span);
                narrowed
            }
            PatternKind::Alt(alts) => {
                let mut result = Type::Nothing;
                for a in alts {
                    let t = self.check_pattern(a, &value_ty);
                    result = self.join_types(&result, &t);
                }
                result
            }
            PatternKind::Pin(expr) => {
                self.check_expr_pub(expr, None);
                value_ty
            }
            PatternKind::Value(expr) => {
                let t = self.check_expr_pub(expr, None);
                let t = self.resolve_ty(&t);
                // `1 === 1.0`: a value of a type not decided yet is not
                // narrowed to the literal's class.
                if Self::undecided(&value_ty) {
                    return value_ty;
                }
                let t = self.numeric_widen(&t);
                let (yes, _) = self.split_by_type(&value_ty, &t);
                if yes.is_nothing() {
                    self.warn(
                        format!(
                            "pattern of type {} never matches {}",
                            self.type_name(&t),
                            self.type_name(&value_ty)
                        ),
                        pattern.span,
                    );
                }
                yes
            }
            PatternKind::Range { lo, hi, .. } => {
                let mut t = Type::Nothing;
                for side in [lo, hi].into_iter().flatten() {
                    let st = self.check_expr_pub(side, None);
                    t = self.join_types(&t, &st);
                }
                if Self::undecided(&value_ty) {
                    return value_ty;
                }
                let t = self.numeric_widen(&t);
                let (yes, _) = self.split_by_type(&value_ty, &t);
                yes
            }
            PatternKind::Const(path) => match self.resolve_pattern_class(path, pattern.span) {
                Some(cid) => {
                    let target = self.open_class(cid);
                    let (yes, _) = self.split_by_type(&value_ty, &target);
                    if yes.is_nothing() {
                        self.warn(
                            format!(
                                "{} never matches {}",
                                self.type_name(&target),
                                self.type_name(&value_ty)
                            ),
                            pattern.span,
                        );
                        return self.dead_arm_type(cid, &value_ty);
                    }
                    yes
                }
                None => Type::Nothing,
            },
            PatternKind::ConstArray(path, ap) => {
                let Some(cid) = self.resolve_pattern_class(path, pattern.span) else {
                    return Type::Nothing;
                };
                let target = self.open_class(cid);
                let (yes, _) = self.split_by_type(&value_ty, &target);
                let narrowed = if yes.is_nothing() {
                    self.dead_arm_type(cid, &value_ty)
                } else {
                    yes
                };
                // Positional deconstruction of data/variant fields.
                let fields = self.deconstruct_fields(&narrowed, pattern.span);
                let mut field_types: Vec<Type> = fields.iter().map(|(_, t)| t.clone()).collect();
                if fields.is_empty() {
                    // Reported: bind the elements without another error.
                    field_types = vec![Type::Nothing; ap.pre.len() + ap.post.len()];
                }
                self.check_array_pattern_elems(ap, &Type::Tuple(field_types), pattern.span);
                narrowed
            }
            PatternKind::ConstHash(path, hp) => {
                let Some(cid) = self.resolve_pattern_class(path, pattern.span) else {
                    return Type::Nothing;
                };
                let target = self.open_class(cid);
                let (yes, _) = self.split_by_type(&value_ty, &target);
                let narrowed = if yes.is_nothing() {
                    self.dead_arm_type(cid, &value_ty)
                } else {
                    yes
                };
                let fields = self.deconstruct_fields(&narrowed, pattern.span);
                for pair in &hp.pairs {
                    let Some((_, fty)) = fields.iter().find(|(n, _)| *n == pair.key) else {
                        if fields.is_empty() {
                            continue; // reported by deconstruct_fields
                        }
                        self.report(
                            format!("{} has no field `{}`", self.type_name(&narrowed), pair.key),
                            pair.span,
                        );
                        continue;
                    };
                    let fty = fty.clone();
                    match &pair.pattern {
                        Some(p) => {
                            self.check_pattern(p, &fty);
                        }
                        None => self.declare_pattern_var(&pair.key, fty, pair.span),
                    }
                }
                if let Some(HashPatternRest::Bind(name)) = &hp.rest {
                    let t = self.world.hash_of(self.world.symbol(), self.world.object());
                    self.declare_pattern_var(name, t, pattern.span);
                }
                narrowed
            }
            PatternKind::Array(ap) => {
                let array_like = self.array_like(&value_ty);
                let narrowed = match &array_like {
                    Some(t) => t.clone(),
                    None => {
                        self.report(
                            format!("array pattern cannot match {}", self.type_name(&value_ty)),
                            pattern.span,
                        );
                        return Type::Nothing;
                    }
                };
                self.check_array_pattern_elems(ap, &narrowed, pattern.span);
                narrowed
            }
            PatternKind::Find {
                pre_rest,
                middle,
                post_rest,
            } => {
                let Some(narrowed) = self.array_like(&value_ty) else {
                    self.report(
                        format!("find pattern cannot match {}", self.type_name(&value_ty)),
                        pattern.span,
                    );
                    return Type::Nothing;
                };
                let elem = self.array_elem(&narrowed);
                if let Some(name) = pre_rest {
                    let t = self.world.array_of(elem.clone());
                    self.declare_pattern_var(name, t, pattern.span);
                }
                if let Some(name) = post_rest {
                    let t = self.world.array_of(elem.clone());
                    // Keyed by the empty span at the pattern's end.
                    self.declare_pattern_var(name, t, Span::empty(pattern.span.end as usize));
                }
                for m in middle {
                    self.check_pattern(m, &elem);
                }
                narrowed
            }
            PatternKind::Hash(hp) => {
                // A hash with symbol keys, or a data/variant by field names.
                let members = self.expand_members(&value_ty);
                let mut hash_members: Vec<Type> = members
                    .iter()
                    .filter(|m| matches!(m, Type::Class(id, _) if *id == self.world.builtin.hash))
                    .cloned()
                    .collect();
                // An `Object` subject may be any hash.
                if members.iter().any(|m| self.world.is_object(m)) {
                    hash_members.push(self.world.hash_of(self.world.symbol(), self.world.object()));
                }
                let data_members: Vec<Type> = members
                    .iter()
                    .filter(|m| matches!(m, Type::Class(id, _) if matches!(self.world.class(*id).kind, ClassKind::Data | ClassKind::Variant)))
                    .cloned()
                    .collect();
                if hash_members.is_empty() && data_members.is_empty() {
                    self.report(
                        format!("hash pattern cannot match {}", self.type_name(&value_ty)),
                        pattern.span,
                    );
                    return Type::Nothing;
                }
                let mut narrowed = Type::Nothing;
                for m in hash_members.iter().chain(data_members.iter()) {
                    narrowed = self.join_types(&narrowed, m);
                }
                for pair in &hp.pairs {
                    let mut fty = Type::Nothing;
                    for m in &hash_members {
                        if let Type::Class(_, args) = m {
                            if args.len() == 2 {
                                let v = args[1].clone();
                                fty = self.join_types(&fty, &v);
                            }
                        }
                    }
                    for m in &data_members {
                        let fields = self.deconstruct_fields(m, pattern.span);
                        if let Some((_, t)) = fields.iter().find(|(n, _)| *n == pair.key) {
                            let t = t.clone();
                            fty = self.join_types(&fty, &t);
                        }
                    }
                    match &pair.pattern {
                        Some(p) => {
                            self.check_pattern(p, &fty);
                        }
                        None => self.declare_pattern_var(&pair.key, fty, pair.span),
                    }
                }
                if let Some(HashPatternRest::Bind(name)) = &hp.rest {
                    let t = self.world.hash_of(self.world.symbol(), self.world.object());
                    self.declare_pattern_var(name, t, pattern.span);
                }
                narrowed
            }
        }
    }

    fn resolve_pattern_class(&mut self, path: &ConstPath, span: Span) -> Option<ClassId> {
        let ns = self.current_namespace();
        let member = self.resolve_path_pub(ns, path, span);
        match member.map(|m| self.world.through_alias(m)) {
            Some(Member::Class(cid)) => {
                self.out.pattern_classes.insert(span, cid);
                Some(cid)
            }
            Some(_) => {
                self.report(format!("`{path}` is not a class"), span);
                None
            }
            None => None,
        }
    }

    /// Whether `cid` with Object for its type arguments is a supertype of
    /// all its instances for what a pattern does with it: a `data` type or
    /// variant (whose fields cannot be set) whose parameters have no
    /// bounds (Object would not meet them) and occur in its fields only
    /// covariantly (not in `(A) -> R` or an invariant `Cell[A]`, which
    /// would accept wrong values).
    fn object_args_safe(&self, cid: ClassId) -> bool {
        let class = self.world.class(cid);
        matches!(class.kind, ClassKind::Data | ClassKind::Variant)
            && class.type_params.iter().all(|p| p.bounds.is_empty())
            && (0..class.type_params.len()).all(|i| self.param_safe(cid, i, &mut Vec::new()))
    }

    /// Whether the `i`th type parameter of the `data` type, variant or
    /// enum `cid` has no bound and occurs in its immutable fields only
    /// covariantly.
    /// Classes being checked count as safe (a recursive `data Node[A] =
    /// (v: A, rest: Node[A]?)` is).
    fn param_safe(&self, cid: ClassId, i: usize, visiting: &mut Vec<(ClassId, usize)>) -> bool {
        if visiting.contains(&(cid, i)) {
            return true;
        }
        let class = self.world.class(cid);
        // A bound Object does not meet: its methods use the parameter
        // through it.
        let Some(id) = class
            .type_params
            .get(i)
            .filter(|p| p.bounds.is_empty())
            .map(|p| p.id)
        else {
            return false;
        };
        let holders: Vec<ClassId> = match class.kind {
            ClassKind::Data | ClassKind::Variant => vec![cid],
            ClassKind::Enum => class.variants.clone(),
            _ => return false,
        };
        visiting.push((cid, i));
        let ok = holders.iter().all(|&h| {
            let hc = self.world.class(h);
            let params: Vec<Type> = hc.type_params.iter().map(|p| Type::Param(p.id)).collect();
            let subst = self.world.class_subst(h, &params);
            self.world.all_fields(h).iter().all(|(f, fsubst)| {
                let ty = f.ty.subst(fsubst).subst(&subst);
                !f.mutable && self.only_covariant(&ty, id, true, visiting)
            })
        });
        visiting.pop();
        ok
    }

    /// Whether the type parameter `id` occurs in `t` only where a wider
    /// type is a supertype (`pos`: in a covariant position so far).
    fn only_covariant(
        &self,
        t: &Type,
        id: TypeParamId,
        pos: bool,
        visiting: &mut Vec<(ClassId, usize)>,
    ) -> bool {
        match t {
            Type::Param(p) => *p != id || pos,
            Type::Var(_) | Type::Nothing | Type::Void => true,
            Type::Union(ms) | Type::Tuple(ms) => {
                ms.iter().all(|m| self.only_covariant(m, id, pos, visiting))
            }
            Type::Class(c, args) => {
                let vs: Vec<Variance> = self
                    .world
                    .class(*c)
                    .type_params
                    .iter()
                    .map(|p| p.variance)
                    .collect();
                args.iter().enumerate().all(|(i, a)| {
                    if !a.mentions_param(id) {
                        return true;
                    }
                    match vs.get(i) {
                        Some(Variance::Covariant) => self.only_covariant(a, id, pos, visiting),
                        Some(Variance::Contravariant) => self.only_covariant(a, id, !pos, visiting),
                        // An invariant parameter of a `data` type or enum
                        // that only holds it covariantly acts covariant.
                        _ => {
                            self.param_safe(*c, i, visiting)
                                && self.only_covariant(a, id, pos, visiting)
                        }
                    }
                })
            }
            Type::ClassObject(_, args) => args.iter().all(|a| !a.mentions_param(id)),
            Type::Proc(rc, ps, r, _) => {
                rc.as_ref()
                    .is_none_or(|t| self.only_covariant(t, id, !pos, visiting))
                    && ps
                        .iter()
                        .all(|p| self.only_covariant(p, id, !pos, visiting))
                    && self.only_covariant(r, id, pos, visiting)
            }
        }
    }

    /// What a value or range pattern of type `t` matches: a number
    /// pattern matches equal numbers of the other number classes too
    /// (`1 === 1.0`, `(1..5) === 2.5`).
    fn numeric_widen(&self, t: &Type) -> Type {
        let b = &self.world.builtin;
        let numbers = [b.int, b.integer, b.float];
        let all_numeric = !t.is_nothing()
            && t.members()
                .iter()
                .all(|m| matches!(m, Type::Class(id, _) if numbers.contains(id)));
        if all_numeric {
            Type::union_of(numbers.iter().map(|id| Type::class(*id)).collect())
        } else {
            t.clone()
        }
    }

    /// Whether a member of `t` is an inference variable not decided yet.
    fn undecided(t: &Type) -> bool {
        t.members().iter().any(|m| matches!(m, Type::Var(_)))
    }

    /// `cid` as a test's target: a generic class without its arguments,
    /// which `split_by_type` takes from what it narrows.
    fn open_class(&self, cid: ClassId) -> Type {
        if self.world.class(cid).type_params.is_empty() {
            Type::class(cid)
        } else {
            Type::Class(cid, vec![])
        }
    }

    /// The type of an arm that never matches (it does not run): `cid`
    /// with the arguments a member of `value_ty` gives (a sibling variant
    /// of an enum), else Object.
    fn dead_arm_type(&self, cid: ClassId, value_ty: &Type) -> Type {
        self.expand_members(value_ty)
            .iter()
            .find_map(|m| self.class_type_from(cid, m))
            .unwrap_or_else(|| self.object_args(cid))
    }

    fn object_args(&self, cid: ClassId) -> Type {
        let n = self.world.class(cid).type_params.len();
        Type::Class(cid, (0..n).map(|_| self.world.object()).collect())
    }

    /// The instance type of `cid` that a value of type `m` is when it is a
    /// `cid`, with the type arguments `m` gives: `m` itself, `m`'s
    /// arguments for a variant of the enum `m`, or those of `m`'s ancestor
    /// `cid`. `None` when `m` does not tell them.
    pub(crate) fn class_type_from(&self, cid: ClassId, m: &Type) -> Option<Type> {
        let class = self.world.class(cid);
        if class.type_params.is_empty() {
            return Some(Type::class(cid));
        }
        let Type::Class(mid, args) = m else {
            return None;
        };
        if *mid == cid {
            return Some(m.clone());
        }
        if class.variant_of == Some(*mid) {
            return Some(Type::Class(cid, args.clone()));
        }
        // A subclass of a generic class: find the ancestor. For a variant,
        // the arguments come from the enum (a sibling variant shares them).
        let wanted = class.variant_of.unwrap_or(cid);
        self.world
            .ancestors(*mid, args)
            .into_iter()
            .find(|(anc, _)| *anc == wanted)
            .map(|(_, anc_args)| Type::Class(cid, anc_args))
    }

    /// `cid` with Object for type arguments not known, when that admits
    /// no wrong value: every parameter covariant with bounds `Object`
    /// meets (as `is_a?` allows, `World::param_admits_object`), or a
    /// `data` type or variant that only holds them so
    /// (`object_args_safe`).
    pub(crate) fn guessed_args(&self, cid: ClassId) -> Option<Type> {
        let class = self.world.class(cid);
        let covariant =
            (0..class.type_params.len()).all(|i| self.world.param_admits_object(cid, i));
        // The built-in immutable collections are run by natives that take
        // any value where they take a `T` (`Hash#[]`, `Range#cover?`).
        let b = &self.world.builtin;
        let builtin = [b.array, b.hash, b.set, b.range].contains(&cid);
        (covariant || builtin || self.object_args_safe(cid)).then(|| self.object_args(cid))
    }

    /// Fields of a data type or enum variant (name and type), for
    /// `Const(...)` patterns.
    fn deconstruct_fields(&mut self, t: &Type, span: Span) -> Vec<(String, Type)> {
        // A member whose arguments are not known (a type not decided yet,
        // or an `Object` a generic class test could not narrow) would
        // leave its fields out of the join: refused.
        // A `T` narrowed to a class deconstructs as that class.
        let t = &Type::union_of(
            self.expand_members(t)
                .into_iter()
                .map(|m| match m {
                    Type::Param(p) => self.world.narrowed_class(p).unwrap_or(m),
                    m => m,
                })
                .collect(),
        );
        let unknown = self.expand_members(t).into_iter().any(|m| match &m {
            Type::Class(cid, _) => !matches!(
                self.world.class(*cid).kind,
                ClassKind::Data | ClassKind::Variant | ClassKind::Class
            ),
            _ => true,
        });
        if unknown {
            self.report(
                if Self::undecided(t) {
                    "cannot deconstruct a value whose type is not yet known; add a type annotation"
                        .to_string()
                } else {
                    format!(
                        "cannot deconstruct a value of type {}: its type arguments are not known here; add a type annotation",
                        self.type_name(t)
                    )
                },
                span,
            );
            return Vec::new();
        }
        let mut out: Vec<(String, Type)> = Vec::new();
        for m in self.expand_members(t) {
            let Type::Class(cid, args) = &m else { continue };
            let mut subst = self.world.class_subst(*cid, args);
            // A field of type `Self` is of the value's own type.
            subst.insert(crate::declare::SELF_PARAM, m.clone());
            for (f, fsubst) in self.world.all_fields(*cid) {
                let ty = f.ty.subst(&fsubst).subst(&subst);
                match out.iter_mut().find(|(n, _)| *n == f.name) {
                    Some((_, existing)) => {
                        let j = self.join_types(existing, &ty);
                        *existing = j;
                    }
                    None => out.push((f.name.clone(), ty)),
                }
            }
        }
        if out.is_empty() {
            self.report(
                format!(
                    "{} cannot be deconstructed (it has no fields)",
                    self.type_name(t)
                ),
                span,
            );
        }
        out
    }

    /// The array or tuple part of a type (for array patterns).
    fn array_like(&mut self, t: &Type) -> Option<Type> {
        let mut result = Type::Nothing;
        for m in self.expand_members(t) {
            match &m {
                Type::Class(id, _) if *id == self.world.builtin.array => {
                    result = self.join_types(&result, &m);
                }
                Type::Tuple(_) => result = self.join_types(&result, &m),
                Type::Class(id, _) if *id == self.world.builtin.object => {
                    let arr = self.world.array_of(self.world.object());
                    result = self.join_types(&result, &arr);
                }
                _ => {}
            }
        }
        if result.is_nothing() {
            None
        } else {
            Some(result)
        }
    }

    fn array_elem(&self, t: &Type) -> Type {
        match t {
            Type::Class(_, args) if args.len() == 1 => args[0].clone(),
            Type::Tuple(ts) => Type::union_of(ts.clone()),
            Type::Union(ms) => Type::union_of(ms.iter().map(|m| self.array_elem(m)).collect()),
            _ => self.world.object(),
        }
    }

    fn check_array_pattern_elems(&mut self, ap: &ArrayPattern, value_ty: &Type, span: Span) {
        let tuple: Option<Vec<Type>> = match value_ty {
            Type::Tuple(ts) => Some(ts.clone()),
            _ => None,
        };
        let elem = self.array_elem(value_ty);
        if let Some(ts) = &tuple {
            let fixed = ap.pre.len() + ap.post.len();
            if ap.rest.is_none() && fixed != ts.len() {
                self.report(
                    format!(
                        "pattern has {} element(s) but the tuple has {}",
                        fixed,
                        ts.len()
                    ),
                    span,
                );
            } else if fixed > ts.len() {
                self.report(
                    format!(
                        "pattern needs at least {} element(s) but the tuple has {}",
                        fixed,
                        ts.len()
                    ),
                    span,
                );
            }
        }
        for (i, p) in ap.pre.iter().enumerate() {
            let t = tuple
                .as_ref()
                .and_then(|ts| ts.get(i).cloned())
                .unwrap_or_else(|| elem.clone());
            self.check_pattern(p, &t);
        }
        if let Some(Some(name)) = &ap.rest {
            let rest_elem = match &tuple {
                Some(ts) => {
                    let end = ts.len().saturating_sub(ap.post.len());
                    let start = ap.pre.len().min(end);
                    Type::union_of(ts[start..end].to_vec())
                }
                None => elem.clone(),
            };
            let t = self.world.array_of(rest_elem);
            self.declare_pattern_var(name, t, span);
        }
        for (i, p) in ap.post.iter().enumerate() {
            let t = tuple
                .as_ref()
                .and_then(|ts| {
                    ts.get(ts.len().wrapping_sub(ap.post.len()).wrapping_add(i))
                        .cloned()
                })
                .unwrap_or_else(|| elem.clone());
            self.check_pattern(p, &t);
        }
    }

    /// Whether the pattern matches every value of `member` (used for
    /// exhaustiveness). Conservative: `false` when unsure.
    pub(crate) fn pattern_covers(&self, pattern: &Pattern, member: &Type) -> bool {
        match &pattern.kind {
            PatternKind::Bind(_) => true,
            PatternKind::Capture(inner, _) => self.pattern_covers(inner, member),
            PatternKind::Alt(alts) => alts.iter().any(|a| self.pattern_covers(a, member)),
            PatternKind::Value(e) => match (&e.kind, member) {
                (ExprKind::Nil, Type::Class(id, _)) => *id == self.world.builtin.nil,
                _ => false,
            },
            PatternKind::Const(_) | PatternKind::ConstArray(..) | PatternKind::ConstHash(..) => {
                let Some(cid) = self.out.pattern_classes.get(&pattern.span) else {
                    return false;
                };
                let Type::Class(mid, _) = member else {
                    return false;
                };
                if !self.world.class_is_a(*mid, *cid) {
                    return false;
                }
                match &pattern.kind {
                    PatternKind::Const(_) => true,
                    PatternKind::ConstArray(_, ap) => {
                        ap.post.is_empty()
                            && ap
                                .pre
                                .iter()
                                .all(|p| matches!(p.kind, PatternKind::Bind(_)))
                    }
                    PatternKind::ConstHash(_, hp) => hp.pairs.iter().all(|p| match &p.pattern {
                        None => true,
                        Some(sub) => self.field_pattern_irrefutable(sub, *mid, &p.key),
                    }),
                    _ => false,
                }
            }
            // `[a, b]` against a tuple `[A, B]`: of the right length, and
            // each element pattern covers its element type.
            PatternKind::Array(ap) => {
                let Type::Tuple(ts) = member else {
                    return false;
                };
                let fixed = ap.pre.len() + ap.post.len();
                let fits = match ap.rest {
                    None => fixed == ts.len(),
                    Some(_) => fixed <= ts.len(),
                };
                fits && ap
                    .pre
                    .iter()
                    .zip(ts.iter())
                    .all(|(p, t)| self.covers_all(p, t))
                    && ap
                        .post
                        .iter()
                        .zip(ts[ts.len() - ap.post.len()..].iter())
                        .all(|(p, t)| self.covers_all(p, t))
            }
            _ => false,
        }
    }

    /// Whether the pattern covers every member of `t` (a union or not).
    fn covers_all(&self, pattern: &Pattern, t: &Type) -> bool {
        t.members().iter().all(|m| self.pattern_covers(pattern, m))
    }

    fn field_pattern_irrefutable(&self, pattern: &Pattern, cid: ClassId, field: &str) -> bool {
        match &pattern.kind {
            PatternKind::Bind(_) => true,
            PatternKind::Capture(inner, _) => self.field_pattern_irrefutable(inner, cid, field),
            PatternKind::Const(_) => {
                // `Circle(center: Point)`: irrefutable if the field type is
                // exactly that class.
                let Some(pcid) = self.out.pattern_classes.get(&pattern.span) else {
                    return false;
                };
                match self.world.find_field(cid, field) {
                    Some((f, _)) => match &f.ty {
                        Type::Class(fid, _) => self.world.class_is_a(*fid, *pcid),
                        _ => false,
                    },
                    None => false,
                }
            }
            _ => false,
        }
    }
}
