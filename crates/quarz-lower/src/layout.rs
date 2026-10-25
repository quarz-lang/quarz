//! Object layouts: where each declared field of a class lives among the
//! object's physical fields. A field whose type is a small immutable
//! data type (`data Vec2 = (x: Float, y: Float)`: fields that are all
//! `Int`/`Float`/`Bool` or such data, no type parameters, no user
//! equality) is stored *by value*: its data class's physical fields are
//! laid out in place, so storing a `Vec2` into the field copies two
//! words and reading the field builds a `Vec2` only when the value is
//! used as one (a read whose only use is its fields never allocates,
//! thanks to scalar replacement).

use quarz_ir::{ClassId, MethodId};
use quarz_types::{ClassKind, Synth, Type, World};

#[derive(Clone, Debug)]
pub struct Ivar {
    pub name: String,
    pub ty: Type,
    /// The first physical field.
    pub slot: u32,
    /// The data class stored by value here, if any.
    pub flat: Option<ClassId>,
}

#[derive(Clone, Debug)]
pub struct Slot {
    pub name: String,
    pub ty: Type,
}

#[derive(Clone, Debug, Default)]
pub struct Layout {
    pub ivars: Vec<Ivar>,
    pub slots: Vec<Slot>,
    /// The data constructor (takes the physical fields), for data types.
    pub init: Option<MethodId>,
}

/// The layouts of every class, by class id.
pub fn compute(world: &World) -> Vec<Layout> {
    let n = world.classes.len();
    let mut memo: Vec<Option<Layout>> = vec![None; n];
    for id in 0..n {
        ensure(world, id as ClassId, &mut memo, &mut Vec::new());
    }
    memo.into_iter().map(|l| l.unwrap_or_default()).collect()
}

fn ensure(world: &World, cid: ClassId, memo: &mut Vec<Option<Layout>>, stack: &mut Vec<ClassId>) {
    if memo[cid as usize].is_some() || stack.contains(&cid) {
        return;
    }
    stack.push(cid);
    let mut ivars = Vec::new();
    let mut slots: Vec<Slot> = Vec::new();
    for (f, subst) in world.all_fields(cid) {
        // A field a superclass declares is laid out as there (its code
        // reads it so), whatever type arguments this class gives it
        // (`class Sub < Box[Int]` keeps `@v: T` a value, not a word).
        let ty = f.ty.clone();
        let flat = flat_class(world, &ty, stack).filter(|d| {
            ensure(world, *d, memo, stack);
            memo[*d as usize].is_some()
        });
        ivars.push(Ivar {
            name: f.name.clone(),
            ty: f.ty.subst(&subst),
            slot: slots.len() as u32,
            flat,
        });
        match flat {
            Some(d) => {
                let inner: Vec<Slot> = memo[d as usize]
                    .as_ref()
                    .map(|l| l.slots.clone())
                    .unwrap_or_default();
                for s in inner {
                    slots.push(Slot {
                        name: format!("{}.{}", f.name, s.name),
                        ty: s.ty,
                    });
                }
            }
            None => slots.push(Slot { name: f.name, ty }),
        }
    }
    let init = world.class(cid).methods.get("initialize").and_then(|ms| {
        ms.iter()
            .copied()
            .find(|m| world.method(*m).synth == Synth::DataInit)
    });
    stack.pop();
    memo[cid as usize] = Some(Layout { ivars, slots, init });
}

fn is_scalar(world: &World, ty: &Type) -> bool {
    let b = &world.builtin;
    matches!(ty, Type::Class(id, args) if args.is_empty() && (*id == b.int || *id == b.float || *id == b.bool_))
}

/// The data class a field of type `ty` can hold by value.
fn flat_class(world: &World, ty: &Type, stack: &[ClassId]) -> Option<ClassId> {
    let Type::Class(d, args) = ty else {
        return None;
    };
    if !args.is_empty() || stack.contains(d) {
        return None;
    }
    let c = world.class(*d);
    if c.kind != ClassKind::Data || !c.type_params.is_empty() || c.fields.is_empty() {
        return None;
    }
    // Equality, hashing and identity of the containing object are
    // structural over the physical fields: a data type with its own
    // notion of equality keeps its box.
    const OWN: [&str; 5] = ["==", "!=", "hash", "eql?", "equal?"];
    // Decided where the type is defined: an extension's `==` is resolved
    // statically where it is visible and takes no part in dispatch (a
    // `Hash` compares with the type's own), so it changes nothing here.
    if OWN.iter().any(|n| c.methods.contains_key(*n)) {
        return None;
    }
    let mut inner = stack.to_vec();
    inner.push(*d);
    let all = c
        .fields
        .iter()
        .all(|f| is_scalar(world, &f.ty) || flat_class(world, &f.ty, &inner).is_some());
    all.then_some(*d)
}
