//! `JSON.decode[T]` (std/json.qz): which types JSON decodes into, and the
//! descriptor of `T` that the lowering bakes at the call for the native
//! (`natives/json.rs`), so that decoding needs no reflection.
//!
//! A descriptor is a list of nodes separated by `;`, the root first; a
//! node refers to others by their index:
//!
//! - `i` `Int`, `I` `Integer`, `f` `Float`, `s` `String`, `b` `Bool`,
//!   `y` `Symbol`, `n` `Nil`, `t` `Time`, `B` `Bytes`, `v` `JSON::Value`;
//! - `?N` nil or node N; `aN` an `Array`, `eN` a `Set` of node N; `hN`,
//!   `HN` a `Hash` of `String` or `Symbol` keys to node N;
//! - `dC:N,N,...` a `data` type: its class, the `C`-th of the descriptor's
//!   classes (passed along as class values, so that the tree shake keeps
//!   them: the native builds their values), and its fields' nodes in the
//!   order of the class's fields.
//!
//! A type met again (a recursive `data` type) refers to its node.

use rustc_hash::FxHashMap as HashMap;

use crate::types::{ClassId, Type};
use crate::world::{ClassKind, MethodInfo, World};

/// Whether `m` is `JSON.decode` or `JSON.decode?` (std/json.qz), whose
/// call is given `T`'s descriptor.
pub fn is_decode(world: &World, m: &MethodInfo) -> bool {
    m.singleton
        && matches!(m.name.as_str(), "decode" | "decode?")
        && world.std_files.contains(&m.file)
        && world.class(m.owner).name == "JSON"
}

/// A type's descriptor: its text, and the `data` classes it names.
pub struct Descriptor {
    pub text: String,
    pub classes: Vec<ClassId>,
}

/// The descriptor of `t`, or why it cannot be decoded, naming the type at
/// fault (`` `Foo` is a class ``).
pub fn descriptor(world: &World, t: &Type) -> Result<Descriptor, String> {
    let mut b = Builder {
        world,
        nodes: Vec::new(),
        seen: HashMap::default(),
        classes: Vec::new(),
    };
    b.node(t)?;
    Ok(Descriptor {
        text: b.nodes.join(";"),
        classes: b.classes,
    })
}

struct Builder<'a> {
    world: &'a World,
    nodes: Vec<String>,
    seen: HashMap<Type, usize>,
    classes: Vec<ClassId>,
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
                if others.len() == 1 && others.len() < ms.len() {
                    let n = self.node(others[0])?;
                    return Ok(format!("?{n}"));
                }
                refuse("is a union: only a type or nil (`T?`) is decoded")
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
                        let own = w.class_subst(id, args);
                        let mut kids = Vec::new();
                        for (f, sub) in w.all_fields(id) {
                            let ty = f.ty.subst(&sub).subst(&own);
                            kids.push(self.node(&ty)?.to_string());
                        }
                        let c = match self.classes.iter().position(|c| *c == id) {
                            Some(c) => c,
                            None => {
                                self.classes.push(id);
                                self.classes.len() - 1
                            }
                        };
                        Ok(format!("d{c}:{}", kids.join(",")))
                    }
                    ClassKind::Enum | ClassKind::Variant => {
                        refuse("is an enum: only `data` types are decoded from objects")
                    }
                    ClassKind::Module => refuse("is a module"),
                    _ => refuse("is a class: only `data` types are decoded from objects"),
                }
            }
            Type::Param(_) | Type::Var(_) => {
                refuse("is a type parameter: the type must be written at the call")
            }
            Type::Proc(..) => refuse("is a procedure"),
            _ => refuse("cannot be decoded from JSON"),
        }
    }
}
