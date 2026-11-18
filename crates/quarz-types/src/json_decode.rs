//! `JSON.decode[T]` (std/json.qz): which types JSON decodes into, and the
//! descriptor of `T` that the lowering bakes at the call for the native
//! (`natives/json.rs`), so that decoding needs no reflection.
//!
//! A descriptor is `PREFIX` and a list of nodes separated by `;`, the root
//! first; a node refers to others by their index:
//!
//! - `i` `Int`, `I` `Integer`, `f` `Float`, `s` `String`, `b` `Bool`,
//!   `y` `Symbol`, `n` `Nil`, `t` `Time`, `DC` `Date` (the prelude's,
//!   class `C`, from an ISO 8601 date string), `B` `Bytes`, `v`
//!   `JSON::Value`;
//! - `?N` nil or node N; `aN` an `Array`, `eN` a `Set` of node N; `hN`,
//!   `HN` a `Hash` of `String` or `Symbol` keys to node N;
//! - `dC:N,N,...` a `data` type: its class id, and its fields' nodes in
//!   the order of the class's fields. The tree shake keeps the classes a
//!   descriptor names (`class_ids`): the native builds their values;
//! - `uKN,KN,...` a union of members other than nil: for each kind of JSON
//!   value it takes (`s` string, `n` number, `b` bool, `a` array, `o`
//!   object, in that order), the member's node. This function decides
//!   which member a kind picks (`Builder::union`); the native only looks
//!   the value's kind up.
//!
//! A type met again (a recursive `data` type) refers to its node.
//!
//! In a block given to `def_method` and its kin, `T` may mention a type
//! parameter the generated method carries (docs/14 §5): the lowering then
//! bakes a marker (`DEFERRED`), which the runner turns into the
//! descriptor of `T` with the classes the statement gives, at the
//! statement (an error there when it does not decode), and the generated
//! method's lowering puts in its place (`Generated::decode`).

use rustc_hash::FxHashMap as HashMap;

use crate::types::{ClassId, Type, TypeParamId};
use crate::world::{ClassKind, MethodInfo, World};

/// Whether `m` is `JSON.decode` or `JSON.decode?` (std/json.qz), whose
/// call is given `T`'s descriptor.
pub fn is_decode(world: &World, m: &MethodInfo) -> bool {
    m.singleton
        && matches!(m.name.as_str(), "decode" | "decode?")
        && world.std_files.contains(&m.file)
        && world.class(m.owner).name == "JSON"
}

/// How many times a `data` type may be met inside itself with other type
/// arguments (`W[W[Int]]` twice) before it counts as recursing without
/// end.
const MAX_NESTING: usize = 16;

/// What a descriptor's text starts with (a string constant the tree
/// shake recognizes): `quarz_ir::JSON_TYPE_PREFIX`, which this crate does
/// not see (quarz-lower tests they agree).
pub const PREFIX: &str = "\u{1}json-type:";

/// A deferred descriptor's marker, in its own constant (found by its
/// index, not its text).
pub const DEFERRED: &str = "\u{1}json-type-deferred";

/// The descriptor of `t`, or why it cannot be decoded, naming the type at
/// fault (`` `Foo` is a class ``).
pub fn descriptor(world: &World, t: &Type) -> Result<String, String> {
    describe_with(world, t, &|_| false)
}

/// Whether `t` decodes, a type parameter for which `carried` holds
/// counting as one that will (decided when it is known, `deferred`).
pub fn check_with(
    world: &World,
    t: &Type,
    carried: &dyn Fn(TypeParamId) -> bool,
) -> Result<(), String> {
    describe_with(world, t, carried).map(|_| ())
}

fn describe_with(
    world: &World,
    t: &Type,
    carried: &dyn Fn(TypeParamId) -> bool,
) -> Result<String, String> {
    let mut b = Builder {
        world,
        nodes: Vec::new(),
        seen: HashMap::default(),
        within: Vec::new(),
        carried,
    };
    b.node(t)?;
    Ok(format!("{PREFIX}{}", b.nodes.join(";")))
}

struct Builder<'a> {
    world: &'a World,
    nodes: Vec<String>,
    seen: HashMap<Type, usize>,
    /// The `data` classes being described, outermost first.
    within: Vec<ClassId>,
    /// The type parameters to take as decodable (`check_with`).
    carried: &'a dyn Fn(TypeParamId) -> bool,
}

impl Builder<'_> {
    fn node(&mut self, t: &Type) -> Result<usize, String> {
        if let Some(&i) = self.seen.get(t) {
            return Ok(i);
        }
        let i = self.nodes.len();
        self.nodes.push(String::new());
        self.seen.insert(t.clone(), i);
        let s = self.describe(t)?;
        self.nodes[i] = s;
        Ok(i)
    }

    fn describe(&mut self, t: &Type) -> Result<String, String> {
        let w = self.world;
        let b = &w.builtin;
        let refuse = |why: &str| Err(format!("`{}` {why}", w.type_name(t)));
        match t {
            Type::Union(ms) => {
                let nil = Type::Class(b.nil, Vec::new());
                let others: Vec<&Type> = ms.iter().filter(|m| **m != nil).collect();
                // (`JSON::Value` holds `null` itself: `Value?` would read it
                // as nil, and not give back what `generate` wrote.)
                if others.len() == 1
                    && matches!(others[0], Type::Class(v, _) if w.class(*v).name == "JSON::Value")
                {
                    return refuse("is nullable, but `JSON::Value` holds `null` already (`JSON::Value::Null`): write `JSON::Value`");
                }
                if others.len() < ms.len() {
                    let n = match others.as_slice() {
                        [one] => self.node(one)?,
                        _ => self.node(&Type::Union(others.into_iter().cloned().collect()))?,
                    };
                    return Ok(format!("?{n}"));
                }
                self.union(t, &others)
            }
            Type::Class(id, args) => {
                let id = *id;
                let simple = [
                    (b.int, "i"),
                    (b.integer, "I"),
                    (b.float, "f"),
                    (b.string, "s"),
                    (b.bool_, "b"),
                    (b.symbol, "y"),
                    (b.nil, "n"),
                    (b.time, "t"),
                    (b.bytes, "B"),
                ];
                if let Some((_, c)) = simple.iter().find(|(c, _)| *c == id) {
                    return Ok(c.to_string());
                }
                if is_date(w, id) {
                    return Ok(format!("D{id}"));
                }
                if id == b.array || id == b.set {
                    let Some(e) = args.first() else {
                        return refuse("has no element type");
                    };
                    let n = self.node(e)?;
                    return Ok(format!("{}{n}", if id == b.array { "a" } else { "e" }));
                }
                if id == b.hash {
                    let (Some(k), Some(v)) = (args.first(), args.get(1)) else {
                        return refuse("has no key and value types");
                    };
                    let kind = match k {
                        Type::Class(k, _) if *k == b.string => "h",
                        Type::Class(k, _) if *k == b.symbol => "H",
                        _ => return refuse("has keys that are neither `String` nor `Symbol`"),
                    };
                    let n = self.node(v)?;
                    return Ok(format!("{kind}{n}"));
                }
                let class = w.class(id);
                if class.name == "JSON::Value" {
                    return Ok("v".to_string());
                }
                match class.kind {
                    ClassKind::Data => {
                        // (Met again and again with other type arguments,
                        // inside itself: `P[T]` holding a `P[Array[T]]`
                        // would need a descriptor without end. A nesting
                        // written out, `W[W[Int]]`, stops long before.)
                        if self.within.iter().filter(|c| **c == id).count() >= MAX_NESTING {
                            return Err(format!(
                                "`{}` holds itself with other type arguments, without end",
                                class.name
                            ));
                        }
                        self.within.push(id);
                        let own = w.class_subst(id, args);
                        let mut kids = Vec::new();
                        for (f, sub) in w.all_fields(id) {
                            let ty = f.ty.subst(&sub).subst(&own);
                            match self.node(&ty) {
                                Ok(n) => kids.push(n.to_string()),
                                Err(e) => {
                                    self.within.pop();
                                    return Err(e);
                                }
                            }
                        }
                        self.within.pop();
                        Ok(format!("d{id}:{}", kids.join(",")))
                    }
                    ClassKind::Enum | ClassKind::Variant => {
                        refuse("is an enum: only `data` types are decoded from objects")
                    }
                    ClassKind::Module => refuse("is a module"),
                    _ => refuse("is a class: only `data` types are decoded from objects"),
                }
            }
            // (Its descriptor is made where it is known: `deferred`.)
            Type::Param(p) if (self.carried)(*p) => Ok("v".to_string()),
            Type::Param(_) | Type::Var(_) => {
                refuse("is a type parameter: the type must be written at the call")
            }
            Type::Proc(..) => refuse("is a procedure"),
            _ => refuse("cannot be decoded from JSON"),
        }
    }

    /// A union of members other than nil (`u` followed by `K=N` entries):
    /// each member is decoded from the JSON values of one kind, and no two
    /// members from the same kind, so the value's kind picks the member.
    fn union(&mut self, t: &Type, members: &[&Type]) -> Result<String, String> {
        let w = self.world;
        let mut by_kind: Vec<(JsonKind, &Type, usize)> = Vec::new();
        for m in members {
            let n = self.node(m)?;
            let kind = match self.kind(m) {
                // (Decided at the statement, where its descriptor is made:
                // `check_with` keeps only the verdict of this one.)
                Kind::Carried => continue,
                Kind::Unexpected => {
                    return Err(format!(
                        "internal error: `{}` described as a union's member, but of no JSON kind",
                        w.type_name(m)
                    ))
                }
                Kind::Any => {
                    return Err(format!(
                        "`{}` is a union JSON cannot tell apart: `{}` is decoded from any JSON value: write `JSON::Value`",
                        w.type_name(t),
                        w.type_name(m)
                    ))
                }
                Kind::Of(k) => k,
            };
            if let Some((_, other, _)) = by_kind.iter().find(|(k, ..)| *k == kind) {
                return Err(format!(
                    "`{}` is a union JSON cannot tell apart: `{}` and `{}` are both decoded from {}",
                    w.type_name(t),
                    w.type_name(other),
                    w.type_name(m),
                    kind.noun()
                ));
            }
            by_kind.push((kind, m, n));
        }
        by_kind.sort_by_key(|(k, ..)| *k);
        let entries: Vec<String> = by_kind
            .iter()
            .map(|(k, _, n)| format!("{}{n}", k.code()))
            .collect();
        Ok(format!("u{}", entries.join(",")))
    }

    /// The kind of JSON value a member of a union is decoded from (the
    /// member itself decodes: `node` described it).
    fn kind(&self, t: &Type) -> Kind {
        let w = self.world;
        let b = &w.builtin;
        match t {
            Type::Param(_) => Kind::Carried,
            Type::Class(id, _) => {
                let id = *id;
                if [b.string, b.symbol, b.time, b.bytes].contains(&id) || is_date(w, id) {
                    Kind::Of(JsonKind::String)
                } else if [b.int, b.integer, b.float].contains(&id) {
                    Kind::Of(JsonKind::Number)
                } else if id == b.bool_ {
                    Kind::Of(JsonKind::Bool)
                } else if id == b.array || id == b.set {
                    Kind::Of(JsonKind::Array)
                } else if w.class(id).name == "JSON::Value" {
                    Kind::Any
                } else {
                    // A `Hash` or a `data` type.
                    Kind::Of(JsonKind::Object)
                }
            }
            // (`node` refused every other type, and a union's members are
            // no unions: `Type::union_of` flattens them.)
            _ => Kind::Unexpected,
        }
    }
}

/// Whether class `id` is the prelude's `Date` (#884), decoded from its
/// ISO 8601 text, not as a `data` type's object.
fn is_date(w: &World, id: ClassId) -> bool {
    let c = w.class(id);
    c.name == "Date" && c.file == 0
}

/// What a union's member is decoded from.
enum Kind {
    Of(JsonKind),
    /// Every JSON value: `JSON::Value`.
    Any,
    /// Not known yet: a type parameter the generated method carries.
    Carried,
    /// None: a type `node` does not describe (an internal error).
    Unexpected,
}

/// The kinds of JSON values other than `null`, in the order a union's
/// entries are written.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum JsonKind {
    String,
    Number,
    Bool,
    Array,
    Object,
}

impl JsonKind {
    /// Its letter in a union's entries.
    fn code(self) -> char {
        match self {
            JsonKind::String => 's',
            JsonKind::Number => 'n',
            JsonKind::Bool => 'b',
            JsonKind::Array => 'a',
            JsonKind::Object => 'o',
        }
    }

    fn noun(self) -> &'static str {
        match self {
            JsonKind::String => "a string",
            JsonKind::Number => "a number",
            JsonKind::Bool => "`true` or `false`",
            JsonKind::Array => "an array",
            JsonKind::Object => "an object",
        }
    }
}
