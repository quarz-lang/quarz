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
                let (yes, _) = self.split_by_type(&value_ty, &t);
                yes
            }
            PatternKind::Const(path) => match self.resolve_pattern_class(path, pattern.span) {
                Some(cid) => {
                    let target = self.class_type_for(cid, &value_ty);
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
                        return target;
                    }
                    yes
                }
                None => Type::Nothing,
            },
            PatternKind::ConstArray(path, ap) => {
                let Some(cid) = self.resolve_pattern_class(path, pattern.span) else {
                    return Type::Nothing;
                };
                let target = self.class_type_for(cid, &value_ty);
                let (yes, _) = self.split_by_type(&value_ty, &target);
                let narrowed = if yes.is_nothing() {
                    target.clone()
                } else {
                    yes
                };
                // Positional deconstruction of data/variant fields.
                let fields = self.deconstruct_fields(&narrowed, pattern.span);
                let field_types: Vec<Type> = fields.iter().map(|(_, t)| t.clone()).collect();
                self.check_array_pattern_elems(ap, &Type::Tuple(field_types), pattern.span);
                narrowed
            }
            PatternKind::ConstHash(path, hp) => {
                let Some(cid) = self.resolve_pattern_class(path, pattern.span) else {
                    return Type::Nothing;
                };
                let target = self.class_type_for(cid, &value_ty);
                let (yes, _) = self.split_by_type(&value_ty, &target);
                let narrowed = if yes.is_nothing() {
                    target.clone()
                } else {
                    yes
                };
                let fields = self.deconstruct_fields(&narrowed, pattern.span);
                for pair in &hp.pairs {
                    let Some((_, fty)) = fields.iter().find(|(n, _)| *n == pair.key) else {
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
                for name in [pre_rest, post_rest].into_iter().flatten() {
                    let t = self.world.array_of(elem.clone());
                    self.declare_pattern_var(name, t, pattern.span);
                }
                for m in middle {
                    self.check_pattern(m, &elem);
                }
                narrowed
            }
            PatternKind::Hash(hp) => {
                // A hash with symbol keys, or a data/variant by field names.
                let members = self.expand_members(&value_ty);
                let hash_members: Vec<Type> = members
                    .iter()
                    .filter(|m| matches!(m, Type::Class(id, _) if *id == self.world.builtin.hash))
                    .cloned()
                    .collect();
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
        match self.resolve_path_pub(ns, path, span) {
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

    /// The instance type of `cid`, taking type arguments from the matched
    /// value's type when it is the same class or an enum of the variant.
    fn class_type_for(&self, cid: ClassId, value_ty: &Type) -> Type {
        let class = self.world.class(cid);
        if class.type_params.is_empty() {
            return Type::class(cid);
        }
        for m in self.expand_members(value_ty) {
            if let Type::Class(mid, args) = &m {
                if *mid == cid {
                    return m.clone();
                }
                if class.variant_of == Some(*mid) {
                    return Type::Class(cid, args.clone());
                }
                // A subclass of a generic class: find the ancestor. For a
                // variant, the arguments come from the enum (a sibling
                // variant shares them).
                let wanted = class.variant_of.unwrap_or(cid);
                for (anc, anc_args) in self.world.ancestors(*mid, args) {
                    if anc == wanted {
                        return Type::Class(cid, anc_args);
                    }
                }
            }
        }
        // Unknown arguments: use the parameters themselves as placeholders.
        Type::Class(
            cid,
            class
                .type_params
                .iter()
                .map(|_| self.world.object())
                .collect(),
        )
    }

    /// Fields of a data type or enum variant (name and type), for
    /// `Const(...)` patterns.
    fn deconstruct_fields(&mut self, t: &Type, span: Span) -> Vec<(String, Type)> {
        let mut out: Vec<(String, Type)> = Vec::new();
        for m in self.expand_members(t) {
            let Type::Class(cid, args) = &m else { continue };
            let kind = self.world.class(*cid).kind;
            if !matches!(
                kind,
                ClassKind::Data | ClassKind::Variant | ClassKind::Class
            ) {
                continue;
            }
            let subst = self.world.class_subst(*cid, args);
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
            _ => false,
        }
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
