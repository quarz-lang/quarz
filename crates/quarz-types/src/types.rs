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
    /// A class used as a value (`Point` in `Point.new`).
    ClassObject(ClassId, Vec<Type>),
    /// Normalized: flattened, deduplicated, at least two members, no
    /// `Nothing`.
    Union(Vec<Type>),
    Tuple(Vec<Type>),
    /// A block or lambda: `(A, B) -> R`.
    /// A procedure: the receiver (`self` inside, for `Recv.(A) -> R`),
    /// the parameters, the result, and whether it is Shareable
    /// (`shareable (A) -> R`: it captured Shareable values by copy, so any
    /// task may call it).
    Proc(Option<Box<Type>>, Vec<Type>, Box<Type>, bool),
    /// A generic type parameter of the enclosing class or method.
    Param(TypeParamId),
    /// An inference variable, bound by unification during checking.
    Var(InferVar),
}

impl Type {
    pub fn class(id: ClassId) -> Type {
        Type::Class(id, Vec::new())
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
            Type::Class(id, args) => Type::Class(*id, args.iter().map(|a| a.subst(map)).collect()),
            Type::ClassObject(id, args) => {
                Type::ClassObject(*id, args.iter().map(|a| a.subst(map)).collect())
            }
            Type::Union(ms) => Type::union_of(ms.iter().map(|m| m.subst(map)).collect()),
            Type::Tuple(ts) => Type::Tuple(ts.iter().map(|t| t.subst(map)).collect()),
            Type::Proc(rc, ps, r, sh) => Type::Proc(
                rc.as_ref().map(|t| Box::new(t.subst(map))),
                ps.iter().map(|p| p.subst(map)).collect(),
                Box::new(r.subst(map)),
                *sh,
            ),
            Type::Param(id) => match map.get(id) {
                Some(t) => t.clone(),
                None => Type::Param(*id),
            },
            Type::Var(v) => Type::Var(*v),
        }
    }

    pub fn has_vars(&self) -> bool {
        match self {
            Type::Var(_) => true,
            Type::Nothing | Type::Param(_) => false,
            Type::Class(_, args) | Type::ClassObject(_, args) => args.iter().any(Type::has_vars),
            Type::Union(ms) | Type::Tuple(ms) => ms.iter().any(Type::has_vars),
            Type::Proc(rc, ps, r, _) => {
                rc.as_ref().is_some_and(|t| t.has_vars())
                    || ps.iter().any(Type::has_vars)
                    || r.has_vars()
            }
        }
    }

    /// Whether the inference variable `v` occurs in the type.
    pub fn mentions_var(&self, v: u32) -> bool {
        match self {
            Type::Var(w) => *w == v,
            Type::Nothing | Type::Param(_) => false,
            Type::Class(_, args) | Type::ClassObject(_, args) => {
                args.iter().any(|a| a.mentions_var(v))
            }
            Type::Union(ms) | Type::Tuple(ms) => ms.iter().any(|m| m.mentions_var(v)),
            Type::Proc(rc, ps, r, _) => {
                rc.as_ref().is_some_and(|t| t.mentions_var(v))
                    || ps.iter().any(|p| p.mentions_var(v))
                    || r.mentions_var(v)
            }
        }
    }

    /// Whether any type parameter occurs in the type.
    pub fn mentions_any_param(&self) -> bool {
        match self {
            Type::Param(_) => true,
            Type::Var(_) | Type::Nothing => false,
            Type::Class(_, args) | Type::ClassObject(_, args) => {
                args.iter().any(Type::mentions_any_param)
            }
            Type::Union(ms) | Type::Tuple(ms) => ms.iter().any(Type::mentions_any_param),
            Type::Proc(rc, ps, r, _) => {
                rc.as_ref().is_some_and(|t| t.mentions_any_param())
                    || ps.iter().any(Type::mentions_any_param)
                    || r.mentions_any_param()
            }
        }
    }

    /// Whether the type parameter `id` occurs in the type.
    pub fn mentions_param(&self, id: TypeParamId) -> bool {
        match self {
            Type::Param(p) => *p == id,
            Type::Var(_) | Type::Nothing => false,
            Type::Class(_, args) | Type::ClassObject(_, args) => {
                args.iter().any(|a| a.mentions_param(id))
            }
            Type::Union(ms) | Type::Tuple(ms) => ms.iter().any(|m| m.mentions_param(id)),
            Type::Proc(rc, ps, r, _) => {
                rc.as_ref().is_some_and(|t| t.mentions_param(id))
                    || ps.iter().any(|p| p.mentions_param(id))
                    || r.mentions_param(id)
            }
        }
    }

    pub fn has_params(&self) -> bool {
        match self {
            Type::Param(_) => true,
            Type::Nothing | Type::Var(_) => false,
            Type::Class(_, args) | Type::ClassObject(_, args) => args.iter().any(Type::has_params),
            Type::Union(ms) | Type::Tuple(ms) => ms.iter().any(Type::has_params),
            Type::Proc(rc, ps, r, _) => {
                rc.as_ref().is_some_and(|t| t.has_params())
                    || ps.iter().any(Type::has_params)
                    || r.has_params()
            }
        }
    }

    pub fn for_each_var(&self, f: &mut dyn FnMut(InferVar)) {
        match self {
            Type::Var(v) => f(*v),
            Type::Nothing | Type::Param(_) => {}
            Type::Class(_, args) | Type::ClassObject(_, args) => {
                args.iter().for_each(|a| a.for_each_var(f))
            }
            Type::Union(ms) | Type::Tuple(ms) => ms.iter().for_each(|m| m.for_each_var(f)),
            Type::Proc(rc, ps, r, _) => {
                if let Some(t) = rc {
                    t.for_each_var(f);
                }
                ps.iter().for_each(|p| p.for_each_var(f));
                r.for_each_var(f);
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
