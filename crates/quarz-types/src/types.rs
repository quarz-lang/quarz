//! The representation of types.

use rustc_hash::FxHashMap as HashMap;

pub type ClassId = u32;
pub type MethodId = u32;
pub type TypeParamId = u32;
pub type InferVar = u32;
pub type ConstId = u32;
pub type ExtensionId = u32;

#[derive(Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum Type {
    /// The bottom type: `raise`, `return`, an empty loop.
    Nothing,
    /// An instance of a class, module, data, enum or enum variant, with its
    /// type arguments. Primitive types (`Int`, `Nil`, ...) are classes too.
    Class(ClassId, Vec<Type>),
    /// A class used as a value (`Point` in `Point.new`): `Type[Point]`.
    ClassObject(ClassId, Vec<Type>),
    /// `Type[T]` for a `T` that is not (yet) a class: a type parameter or
    /// an inference variable, or a union a parameter was bound to. Once
    /// the inner type is a class, `Type::type_of` makes it a
    /// `ClassObject`.
    TypeOf(Box<Type>),
    /// Normalized: flattened, deduplicated, at least two members, no
    /// `Nothing`.
    Union(Vec<Type>),
    Tuple(Vec<Type>),
    /// A block or lambda: `(A, B) -> R`.
    /// A procedure: the receiver (`self` inside, for `Recv.(A) -> R`),
    /// the parameters, the result, and whether it is Shareable
    /// (`shareable (A) -> R`: it captured Shareable values by copy, so any
    /// task may call it), and its keyword-only parameters (`(A, *, k: B)
    /// -> R`), sorted by name.
    Proc(Option<Box<Type>>, Vec<Type>, Box<Type>, bool, Box<[ProcKw]>),
    /// A generic type parameter of the enclosing class or method.
    Param(TypeParamId),
    /// An inference variable, bound by unification during checking.
    Var(InferVar),
    /// `-> Void`: the result of a method or procedure whose body's value
    /// is discarded. Only a result is `Void` (never a value's type: a
    /// call's is `Nil`), and it compares as `Nil`.
    Void,
}

/// A keyword-only parameter of a procedure type (docs/02 §9): `k: T`.
/// A written type lists required ones only; a block's or a lambda's own
/// type has its keywords with a default as optional (`required: false`),
/// which a call may leave out.
#[derive(Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct ProcKw {
    pub name: String,
    pub ty: Type,
    pub required: bool,
}

impl ProcKw {
    /// Keywords sorted by name, as a procedure type keeps them.
    pub fn sorted(mut kws: Vec<ProcKw>) -> Box<[ProcKw]> {
        kws.sort_by(|a, b| a.name.cmp(&b.name));
        kws.into_boxed_slice()
    }

    /// The same keywords with each type mapped.
    pub fn map(kws: &[ProcKw], mut f: impl FnMut(&Type) -> Type) -> Box<[ProcKw]> {
        kws.iter()
            .map(|k| ProcKw {
                name: k.name.clone(),
                ty: f(&k.ty),
                required: k.required,
            })
            .collect()
    }

    /// Whether a procedure with keywords `v` can be called as one with
    /// keywords `t` (docs/02 §9): every keyword `t` lists is one `v`
    /// takes (optional in `v` where it is in `t`), and every keyword `v`
    /// requires is listed by `t`. The pairs (`v`'s type, `t`'s type) to
    /// compare, contravariantly, or `None`.
    pub fn accepts<'a>(v: &'a [ProcKw], t: &'a [ProcKw]) -> Option<Vec<(&'a Type, &'a Type)>> {
        let mut pairs = Vec::new();
        for tk in t {
            let vk = v.iter().find(|k| k.name == tk.name)?;
            if vk.required && !tk.required {
                return None;
            }
            pairs.push((&vk.ty, &tk.ty));
        }
        if v.iter()
            .any(|vk| vk.required && !t.iter().any(|tk| tk.name == vk.name))
        {
            return None;
        }
        Some(pairs)
    }
}

impl Type {
    /// A procedure type without keywords.
    pub fn proc_(
        recv: Option<Box<Type>>,
        params: Vec<Type>,
        ret: Box<Type>,
        shareable: bool,
    ) -> Type {
        Type::Proc(recv, params, ret, shareable, Box::default())
    }

    pub fn class(id: ClassId) -> Type {
        Type::Class(id, Vec::new())
    }

    /// `Type[inner]`: a `ClassObject` when `inner` is a class.
    pub fn type_of(inner: Type) -> Type {
        match inner {
            Type::Class(id, args) => Type::ClassObject(id, args),
            t => Type::TypeOf(Box::new(t)),
        }
    }

    /// The instances of a class object: `Point` for `Type[Point]`.
    pub fn instance_of(&self) -> Option<Type> {
        match self {
            Type::ClassObject(id, args) => Some(Type::Class(*id, args.clone())),
            Type::TypeOf(t) => Some((**t).clone()),
            _ => None,
        }
    }

    pub fn is_nothing(&self) -> bool {
        matches!(self, Type::Nothing)
    }

    /// Build a union, flattening nested unions, dropping `Nothing` and
    /// duplicates. Subtype absorption is done by `World::simplify_union`.
    pub fn union_of(members: Vec<Type>) -> Type {
        let mut out: Vec<Type> = Vec::new();
        fn push(out: &mut Vec<Type>, t: Type) {
            match t {
                Type::Nothing => {}
                Type::Union(ms) => {
                    for m in ms {
                        push(out, m);
                    }
                }
                t => {
                    if !out.contains(&t) {
                        out.push(t);
                    }
                }
            }
        }
        for m in members {
            push(&mut out, m);
        }
        match out.len() {
            0 => Type::Nothing,
            1 => out.pop().unwrap(),
            _ => Type::Union(out),
        }
    }

    /// The members of a union, or the type itself.
    pub fn members(&self) -> Vec<Type> {
        match self {
            Type::Union(ms) => ms.clone(),
            t => vec![t.clone()],
        }
    }

    /// Substitute type parameters.
    pub fn subst(&self, map: &HashMap<TypeParamId, Type>) -> Type {
        if map.is_empty() {
            return self.clone();
        }
        match self {
            Type::Nothing => Type::Nothing,
            Type::Void => Type::Void,
            Type::Class(id, args) => Type::Class(*id, args.iter().map(|a| a.subst(map)).collect()),
            Type::ClassObject(id, args) => {
                Type::ClassObject(*id, args.iter().map(|a| a.subst(map)).collect())
            }
            Type::TypeOf(t) => Type::type_of(t.subst(map)),
            Type::Union(ms) => Type::union_of(ms.iter().map(|m| m.subst(map)).collect()),
            Type::Tuple(ts) => Type::Tuple(ts.iter().map(|t| t.subst(map)).collect()),
            Type::Proc(rc, ps, r, sh, kws) => Type::Proc(
                rc.as_ref().map(|t| Box::new(t.subst(map))),
                ps.iter().map(|p| p.subst(map)).collect(),
                Box::new(r.subst(map)),
                *sh,
                ProcKw::map(kws, |t| t.subst(map)),
            ),
            Type::Param(id) => match map.get(id) {
                Some(t) => t.clone(),
                None => Type::Param(*id),
            },
            Type::Var(v) => Type::Var(*v),
        }
    }

    /// This type with every inference variable replaced by `with`.
    pub fn fill_vars(&self, with: &Type) -> Type {
        match self {
            Type::Var(_) => with.clone(),
            Type::Class(id, args) => {
                Type::Class(*id, args.iter().map(|a| a.fill_vars(with)).collect())
            }
            Type::ClassObject(id, args) => {
                Type::ClassObject(*id, args.iter().map(|a| a.fill_vars(with)).collect())
            }
            Type::TypeOf(t) => Type::type_of(t.fill_vars(with)),
            Type::Union(ms) => Type::union_of(ms.iter().map(|m| m.fill_vars(with)).collect()),
            Type::Tuple(ts) => Type::Tuple(ts.iter().map(|t| t.fill_vars(with)).collect()),
            Type::Proc(rc, ps, r, sh, kws) => Type::Proc(
                rc.as_ref().map(|t| Box::new(t.fill_vars(with))),
                ps.iter().map(|p| p.fill_vars(with)).collect(),
                Box::new(r.fill_vars(with)),
                *sh,
                ProcKw::map(kws, |t| t.fill_vars(with)),
            ),
            other => other.clone(),
        }
    }

    pub fn has_vars(&self) -> bool {
        match self {
            Type::Var(_) => true,
            Type::Nothing | Type::Void | Type::Param(_) => false,
            Type::Class(_, args) | Type::ClassObject(_, args) => args.iter().any(Type::has_vars),
            Type::TypeOf(t) => t.has_vars(),
            Type::Union(ms) | Type::Tuple(ms) => ms.iter().any(Type::has_vars),
            Type::Proc(rc, ps, r, _, kws) => {
                rc.as_ref().is_some_and(|t| t.has_vars())
                    || ps.iter().any(Type::has_vars)
                    || r.has_vars()
                    || kws.iter().any(|k| k.ty.has_vars())
            }
        }
    }

    /// Whether the inference variable `v` occurs in the type.
    pub fn mentions_var(&self, v: u32) -> bool {
        match self {
            Type::Var(w) => *w == v,
            Type::Nothing | Type::Void | Type::Param(_) => false,
            Type::Class(_, args) | Type::ClassObject(_, args) => {
                args.iter().any(|a| a.mentions_var(v))
            }
            Type::TypeOf(t) => t.mentions_var(v),
            Type::Union(ms) | Type::Tuple(ms) => ms.iter().any(|m| m.mentions_var(v)),
            Type::Proc(rc, ps, r, _, kws) => {
                rc.as_ref().is_some_and(|t| t.mentions_var(v))
                    || ps.iter().any(|p| p.mentions_var(v))
                    || r.mentions_var(v)
                    || kws.iter().any(|k| k.ty.mentions_var(v))
            }
        }
    }

    /// Whether any type parameter occurs in the type.
    pub fn mentions_any_param(&self) -> bool {
        match self {
            Type::Param(_) => true,
            Type::Var(_) | Type::Nothing | Type::Void => false,
            Type::Class(_, args) | Type::ClassObject(_, args) => {
                args.iter().any(Type::mentions_any_param)
            }
            Type::TypeOf(t) => t.mentions_any_param(),
            Type::Union(ms) | Type::Tuple(ms) => ms.iter().any(Type::mentions_any_param),
            Type::Proc(rc, ps, r, _, kws) => {
                rc.as_ref().is_some_and(|t| t.mentions_any_param())
                    || ps.iter().any(Type::mentions_any_param)
                    || r.mentions_any_param()
                    || kws.iter().any(|k| k.ty.mentions_any_param())
            }
        }
    }

    /// Whether the type parameter `id` occurs in the type.
    pub fn mentions_param(&self, id: TypeParamId) -> bool {
        match self {
            Type::Param(p) => *p == id,
            Type::Var(_) | Type::Nothing | Type::Void => false,
            Type::Class(_, args) | Type::ClassObject(_, args) => {
                args.iter().any(|a| a.mentions_param(id))
            }
            Type::TypeOf(t) => t.mentions_param(id),
            Type::Union(ms) | Type::Tuple(ms) => ms.iter().any(|m| m.mentions_param(id)),
            Type::Proc(rc, ps, r, _, kws) => {
                rc.as_ref().is_some_and(|t| t.mentions_param(id))
                    || ps.iter().any(|p| p.mentions_param(id))
                    || r.mentions_param(id)
                    || kws.iter().any(|k| k.ty.mentions_param(id))
            }
        }
    }

    pub fn has_params(&self) -> bool {
        match self {
            Type::Param(_) => true,
            Type::Nothing | Type::Void | Type::Var(_) => false,
            Type::Class(_, args) | Type::ClassObject(_, args) => args.iter().any(Type::has_params),
            Type::TypeOf(t) => t.has_params(),
            Type::Union(ms) | Type::Tuple(ms) => ms.iter().any(Type::has_params),
            Type::Proc(rc, ps, r, _, kws) => {
                rc.as_ref().is_some_and(|t| t.has_params())
                    || ps.iter().any(Type::has_params)
                    || r.has_params()
                    || kws.iter().any(|k| k.ty.has_params())
            }
        }
    }

    pub fn for_each_var(&self, f: &mut dyn FnMut(InferVar)) {
        match self {
            Type::Var(v) => f(*v),
            Type::Nothing | Type::Void | Type::Param(_) => {}
            Type::Class(_, args) | Type::ClassObject(_, args) => {
                args.iter().for_each(|a| a.for_each_var(f))
            }
            Type::TypeOf(t) => t.for_each_var(f),
            Type::Union(ms) | Type::Tuple(ms) => ms.iter().for_each(|m| m.for_each_var(f)),
            Type::Proc(rc, ps, r, _, kws) => {
                if let Some(t) = rc {
                    t.for_each_var(f);
                }
                ps.iter().for_each(|p| p.for_each_var(f));
                r.for_each_var(f);
                kws.iter().for_each(|k| k.ty.for_each_var(f));
            }
        }
    }

    /// `T?` → `T` (remove `Nil` from a union), given the id of `Nil`.
    pub fn without_nil(&self, nil: ClassId) -> Type {
        match self {
            Type::Union(ms) => Type::union_of(
                ms.iter()
                    .filter(|m| !matches!(m, Type::Class(id, _) if *id == nil))
                    .cloned()
                    .collect(),
            ),
            Type::Class(id, _) if *id == nil => Type::Nothing,
            t => t.clone(),
        }
    }

    pub fn class_id(&self) -> Option<ClassId> {
        match self {
            Type::Class(id, _) => Some(*id),
            _ => None,
        }
    }
}
