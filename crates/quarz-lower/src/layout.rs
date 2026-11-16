//! Object layouts: where each declared field of a class lives among the
//! object's physical fields. A field whose type is a small immutable
//! data type (`data Vec2 = (x: Float, y: Float)`: fields that are all
//! `Int`/`Float`/`Bool` or such data, no type parameters, no `==`, `!=`
//! or `hash` of the program's, `World::user_method`) is stored *by
//! value*: its data class's physical fields are laid out in place, so
//! storing a `Vec2` into the field copies two words and reading the field
//! builds a `Vec2` only when the value is used as one (a read whose only
//! use is its fields never allocates, thanks to scalar replacement).

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
        of(world, id as ClassId, &mut memo);
    }
    memo.into_iter().map(|l| l.unwrap_or_default()).collect()
}

/// Class `cid`'s layout into `memo` (by class id), with those of the
/// `data` types it holds by value, which it reads from `memo` when there
/// already: `compute`'s step for one class.
pub fn of(world: &World, cid: ClassId, memo: &mut Vec<Option<Layout>>) {
    ensure(world, cid, memo, &mut Vec::new());
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

/// What a change of the world did to the layouts that existed: the first
/// class of `before` (by id) that `after` lays out otherwise, with the
/// first of its declared fields placed otherwise (another first physical
/// field, or another `data` type held in place there; past the shorter
/// list when only the number of fields or of physical fields differs).
/// A class `after` adds is not compared. The checks that a layout cannot
/// change under code lowered with it (#809: a later unit's declarations)
/// call it on the layouts before and after.
pub fn first_change(before: &[Layout], after: &[Layout]) -> Option<(ClassId, usize)> {
    for (id, (b, a)) in before.iter().zip(after).enumerate() {
        let differs = b
            .ivars
            .iter()
            .zip(&a.ivars)
            .position(|(x, y)| x.name != y.name || x.slot != y.slot || x.flat != y.flat);
        if let Some(i) = differs {
            return Some((id as ClassId, i));
        }
        if b.ivars.len() != a.ivars.len() || b.slots.len() != a.slots.len() {
            return Some((id as ClassId, b.ivars.len().min(a.ivars.len())));
        }
    }
    None
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
    // structural over the physical fields: a data type compared or hashed
    // by methods of the program's keeps its box. Those are what the
    // runtime's lookup finds (`World::user_method`): the type's own, a
    // module's it includes, or one an unconditional extension includes;
    // not an extension's own method, which is resolved statically where
    // it is visible and takes no part in dispatch (#809). A method of the
    // name that a comparison or a hash does not call (`hash(seed: Int)`,
    // an abstract `==` the built-in one meets) does not count, as it did
    // when the type's own table was read: such a type is held in place.
    // (`equal?` is identity and cannot be redefined; `eql?` is not Quarz's.)
    const OWN: [(&str, usize); 3] = [("==", 1), ("!=", 1), ("hash", 0)];
    if OWN
        .iter()
        .any(|(n, argc)| world.user_method(*d, n, *argc).is_some())
    {
        return None;
    }
    // A read rebuilds the value with the generated `initialize`: one of
    // the body's own (which replaces it, docs/01 §4) keeps the box.
    let generated_init = c
        .methods
        .get("initialize")
        .is_some_and(|ms| ms.iter().any(|m| world.method(*m).synth == Synth::DataInit));
    if !generated_init {
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
