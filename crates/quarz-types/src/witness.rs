//! Conformance witnesses (#536 step 3): the one computation of "what runs
//! in place of a module's method for a class that conforms to the module
//! through an extension", on the instance side and on the class side.
//! `World::witnesses` builds the table from the declarations alone (never
//! from the extensions active where it is asked); the declarer checks its
//! rows, the checker reads it (`World::witness`), the lowering ships it
//! (`RtWorld::witnesses`) and the runtime looks a row up, with no rule of
//! its own.

use std::rc::Rc;

use rustc_hash::FxHashMap as HashMap;

use crate::types::*;
use crate::world::*;

/// Where a row of the witness table comes from.
#[derive(Clone, Debug, PartialEq)]
pub enum WitnessSource {
    /// A conformance: include number `include` of extension `ext`, which
    /// targets `target` (a class of the row's class's chain, or a module
    /// it has), makes the class conform to the row's module.
    Include {
        ext: ExtensionId,
        include: usize,
        target: ClassId,
    },
    /// No conformance: the class has the module (or abstract class) by
    /// its own declarations, nothing in its lookup order implements the
    /// abstract method, and an own method of extension `ext` (one of the
    /// prelude's, or a top-level one of the class's group, which includes
    /// nothing for it) does (docs/01 §7).
    Method { ext: ExtensionId },
    /// No extension: an abstract method of the class's own ancestors (an
    /// abstract superclass's stub, a module's) implemented by a method the
    /// walk of the override table does not reach: one further up the
    /// lookup order than the abstract method's owner, or the one of the
    /// signature past an overload of the name. A fact of the override
    /// relation, kept here because the record this table replaces kept it
    /// (#536 step 4 may fold it into the override table).
    Inherited,
}

/// What implements an abstract method of a class's own ancestors
/// (`World::implementation_for`).
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Implementation {
    /// Nothing: the class must implement it.
    Missing,
    /// A method where dispatch finds it (the override table).
    Own(MethodId),
    /// An extension's own method (`WitnessSource::Method`).
    Extension(ExtensionId, MethodId),
    /// `WitnessSource::Inherited`.
    Inherited(MethodId),
}

/// A row of the witness table (`World::witnesses`): for values of `class`
/// (instance side) or for the class object `class` (class side), `by`
/// runs in place of `method`, a method of `module`.
#[derive(Clone, Debug, PartialEq)]
pub struct Witness {
    pub class: ClassId,
    /// The module instantiation the class conforms to (`args` in the
    /// class's own parameters): `method`'s owner.
    pub module: ClassId,
    pub args: Vec<Type>,
    pub source: WitnessSource,
    /// The module's method, of either side (`MethodInfo::singleton`).
    pub method: MethodId,
    /// What runs: `method` itself for a default nothing replaces, and for
    /// an abstract one nothing implements (it raises, #600, #555).
    pub by: MethodId,
}

/// The witness table, with its index by (class, method).
#[derive(Debug, Default)]
pub struct WitnessTable {
    /// The rows, those of one class together.
    pub rows: Vec<Witness>,
    index: HashMap<(ClassId, MethodId), u32>,
    /// Where each class's rows are in `rows`.
    ranges: HashMap<ClassId, (u32, u32)>,
}

impl WitnessTable {
    pub fn get(&self, class: ClassId, method: MethodId) -> Option<&Witness> {
        self.index
            .get(&(class, method))
            .map(|i| &self.rows[*i as usize])
    }

    /// A number that changes when a row does (its class, method or what
    /// runs): for "did the table change" between two inputs of the REPL,
    /// which the number of rows does not say (a nearer conformance changes
    /// a subclass's rows without adding one).
    pub fn fingerprint(&self) -> u64 {
        use std::hash::{Hash, Hasher};
        let mut h = rustc_hash::FxHasher::default();
        for w in &self.rows {
            (w.class, w.method, w.by).hash(&mut h);
        }
        h.finish()
    }

    /// The rows of class `class`.
    pub fn of(&self, class: ClassId) -> &[Witness] {
        match self.ranges.get(&class) {
            Some((from, to)) => &self.rows[*from as usize..*to as usize],
            None => &[],
        }
    }

    /// (Called class by class.)
    fn push(&mut self, w: Witness) {
        let key = (w.class, w.method);
        if !self.index.contains_key(&key) {
            let at = self.rows.len() as u32;
            self.index.insert(key, at);
            self.ranges.entry(w.class).or_insert((at, at)).1 = at + 1;
            self.rows.push(w);
        }
    }
}

/// The table remembered for a state of the declarations
/// (`World::witnesses`).
#[derive(Debug, Default)]
pub struct WitnessMemo {
    table: std::cell::RefCell<Option<(WitnessKey, Rc<WitnessTable>)>>,
}

/// What the table is computed from grows with these (a method, a class,
/// an extension or a file added): a copy of the world starts without one.
type WitnessKey = (usize, usize, usize, usize);

impl Clone for WitnessMemo {
    fn clone(&self) -> Self {
        WitnessMemo::default()
    }
}

impl WitnessMemo {
    pub fn clear(&mut self) {
        *self.table.get_mut() = None;
    }
}

/// A conformance of a class through an extension's include
/// (`World::extension_conformances`).
#[derive(Clone, Debug)]
pub struct ExtConformance {
    pub ext: ExtensionId,
    /// The include of `ext` that brings the module, and the module it
    /// names (which is the module, or includes it).
    pub include: usize,
    /// The extension's target, with its arguments in the class's
    /// parameters.
    pub target: ClassId,
    pub target_args: Vec<Type>,
    /// The entry of the class's declared order the conformance hangs
    /// from: the target, or (the target being a module only another
    /// extension brings) the entry that one hangs from.
    pub root: ClassId,
    pub module: ClassId,
    /// The module's arguments in the class's parameters, and in the
    /// extension's.
    pub args: Vec<Type>,
    pub ext_args: Vec<Type>,
}

impl World {
    /// The witness table (#536 step 3; docs/01 §7): the one computation of
    /// the conformance witnesses, from the declarations alone.
    ///
    /// A row exists for a class `K` and a method `r` of a module `M` that
    /// `K` has only through an extension: `M` is not in `K`'s declared
    /// order (`View::Declared`, `RtClass::class_side`); on the instance
    /// side also where `K`'s own include of `M` does nothing, a superclass
    /// having it already through an extension in dispatch's order
    /// (`shadowed_includes`; the class side goes by the declared order,
    /// #504). `E` is the
    /// extension whose include brings `M` (`extension_conformances`: the
    /// nearest target up `K`'s declared order, the first declared
    /// extension there; bounds are not consulted, a class value carrying
    /// no type arguments), `C` the class of `K`'s chain it hangs from. For
    /// a module `K` has itself, ordinary dispatch holds (the override
    /// table, #536 step 1) and the extension's method of the name is an
    /// extension method, chosen statically.
    ///
    /// Instance side (a call through a value typed `M`; #536 step 1's
    /// decisions (3) and (4): the class's own methods and own includes
    /// override any extension's module, a subclass's too):
    /// 1. below `C`, the first method of `K`'s lookup order
    ///    (`View::Lookup`) that replaces `r` (`World::replaces_seen`): a
    ///    subclass's own, or one of a module it includes itself;
    /// 2. `E`'s own method of the name that takes `r`'s calls (the same
    ///    signature first);
    /// 3. the first method of `C`'s own part of the lookup order (`C`,
    ///    the modules it includes itself and those of its top-level
    ///    unconditional extensions) in front of `M` that replaces `r`;
    /// 4. a method of a module `E` includes after the one bringing `M`,
    ///    the last included first (#523), that replaces `r`;
    /// 5. the nearest method, in the included module's own ancestry in
    ///    front of `M`, that replaces `r`;
    /// 6. `r` itself when it has a body. An abstract `r` is implemented
    ///    by what follows `M` in the order, as for a class's own include:
    ///    a module `E` includes before it, then the rest of `C`'s lookup
    ///    order (an inherited method), then a module another extension
    ///    makes the class conform to (#522); in 1, 3 and here, where a class
    ///    gives no method and `E` is itself active where the class is
    ///    declared (a prelude extension, a top-level one of the class's
    ///    group), also by an own method of such an extension that targets
    ///    the class (`WitnessSource::Method`'s rule). One that nothing
    ///    implements stays in the row and raises when called (#600,
    ///    #555).
    ///
    /// Each class's rows are asked as seen where the class is declared
    /// (`declaration_view`: what the pairing rule's subtyping and the
    /// bounds read), so the table does not depend on the extensions
    /// active where it is asked for.
    ///
    /// Class side (a call through `Type[M]` or `T <: M`; #504): witnesses
    /// are fixed, the row of `C` serves `C` and every class below it (no
    /// step 1). Steps 2, 4, 5 and 6 alike; step 3 is `C`'s own or a
    /// superclass's own class method only, not one of a module they
    /// include (#601); an abstract `r` has no later implementation.
    ///
    /// Two more kinds of row, for a concrete class and an abstract
    /// instance method of its declared ancestors (`implementation_for`,
    /// which the declarer's conformance check asks too, over the same
    /// order): `WitnessSource::Method`, where no method of its lookup
    /// order implements it, the own method of a prelude extension or of a
    /// top-level extension of the class's group (the nearest target
    /// first) that does; `WitnessSource::Inherited`, the implementation
    /// when it is not where the override table's walk finds it (an
    /// abstract superclass's stub over an inherited body, the choice by
    /// signature past an overload): a fact of the override relation, kept
    /// here as the record this table replaces kept it.
    ///
    /// The gated sends of natives (`Interp::find_method`) still look the
    /// name up first (#599).
    pub fn witnesses(&self) -> Rc<WitnessTable> {
        let key: WitnessKey = (
            self.classes.len(),
            self.methods.len(),
            self.extensions.len(),
            self.file_groups.len(),
        );
        if let Some((k, t)) = self.witness_memo.table.borrow().as_ref() {
            if *k == key {
                return t.clone();
            }
        }
        let table = Rc::new(self.build_witnesses());
        *self.witness_memo.table.borrow_mut() = Some((key, table.clone()));
        table
    }

    /// What runs in place of `method` for class `k`, when the table has a
    /// row for them.
    pub fn witness(&self, k: ClassId, method: MethodId) -> Option<MethodId> {
        self.witnesses().get(k, method).map(|w| w.by)
    }

    /// The conformances class `k` has through extensions' includes, one
    /// for each module that is not in its declared order
    /// (`View::Declared`): going up that order, for each entry the
    /// extensions that target it in declaration order, each one's
    /// includes from the last (with what each brings, and the extensions
    /// of the modules brought, before the next). Bounds are not
    /// consulted: the run time cannot see a value's type arguments, and a
    /// row no value reaches is harmless.
    pub fn extension_conformances(&self, k: ClassId) -> Vec<ExtConformance> {
        let declared = self.resolution(k, &self.own_args(k), View::Declared);
        let mut seen: Vec<ClassId> = declared.iter().map(|(c, _)| *c).collect();
        let mut out = Vec::new();
        for (a, aargs) in &declared {
            self.conformances_from(*a, aargs, *a, &mut seen, &mut out);
        }
        out
    }

    fn conformances_from(
        &self,
        target: ClassId,
        targs: &[Type],
        root: ClassId,
        seen: &mut Vec<ClassId>,
        out: &mut Vec<ExtConformance>,
    ) {
        for e in &self.extensions {
            if e.target != target || e.includes.is_empty() {
                continue;
            }
            let esubst = self.extension_subst(e, targs);
            for (i, inc) in e.includes.iter().enumerate().rev() {
                let Type::Class(m, eargs) = inc else { continue };
                let margs: Vec<Type> = eargs.iter().map(|t| t.subst(&esubst)).collect();
                let here = self.resolution(*m, &margs, View::Declared);
                let there = self.resolution(*m, eargs, View::Declared);
                let mut new = Vec::new();
                for ((x, xargs), (_, xeargs)) in here.into_iter().zip(there) {
                    if self.class(x).kind != ClassKind::Module || seen.contains(&x) {
                        continue;
                    }
                    seen.push(x);
                    out.push(ExtConformance {
                        ext: e.id,
                        include: i,
                        target,
                        target_args: targs.to_vec(),
                        root,
                        module: x,
                        args: xargs.clone(),
                        ext_args: xeargs,
                    });
                    new.push((x, xargs));
                }
                for (x, xargs) in new {
                    self.conformances_from(x, &xargs, root, seen, out);
                }
            }
        }
    }

    /// The modules class `k` includes itself (in its declared order) that
    /// are, in dispatch's order (`View::Runtime`, the order
    /// `RtClass::ancestors` ships), in the part of a class further up its
    /// chain: a superclass has the module already through an extension
    /// whose modules keep their place in the walk (a top-level one), so
    /// the class's own include does nothing (docs/01 §6, as Ruby). Each
    /// with its arguments in `k`'s parameters and that class. (A scoped
    /// extension's module at a superclass does not move an own include.)
    /// `World::resolution` alone decides it: the module's place in two of
    /// its views is compared, the rule of includes is not derived again
    /// from the declarations.
    fn shadowed_includes(&self, k: ClassId) -> Vec<(ClassId, Vec<Type>, ClassId)> {
        let declared = self.resolution(k, &self.own_args(k), View::Declared);
        if !declared
            .iter()
            .any(|(m, _)| self.class(*m).kind == ClassKind::Module)
        {
            return Vec::new();
        }
        let runtime: Vec<ClassId> = self
            .resolution(k, &[], View::Runtime)
            .into_iter()
            .map(|(c, _)| c)
            .collect();
        let ids: Vec<ClassId> = declared.iter().map(|(c, _)| *c).collect();
        let part = |order: &[ClassId], m: ClassId| -> Option<ClassId> {
            let at = order.iter().position(|c| *c == m)?;
            order[..at]
                .iter()
                .rev()
                .copied()
                .find(|c| self.class(*c).kind != ClassKind::Module)
        };
        declared
            .iter()
            .filter(|(m, _)| self.class(*m).kind == ClassKind::Module)
            .filter_map(|(m, margs)| {
                let (dp, rp) = (part(&ids, *m)?, part(&runtime, *m)?);
                (dp != rp && ids.iter().position(|c| *c == rp) > ids.iter().position(|c| *c == dp))
                    .then(|| (*m, margs.clone(), rp))
            })
            .collect()
    }

    /// The class of `k`'s superclass chain whose own part of the declared
    /// order (the class and the modules it brings itself) holds `entry`.
    fn part_class(&self, k: ClassId, entry: ClassId) -> ClassId {
        let declared = self.resolution(k, &self.own_args(k), View::Declared);
        let at = declared
            .iter()
            .position(|(c, _)| *c == entry)
            .unwrap_or_else(|| {
                panic!(
                    "internal error: `{}` is not in `{}`'s declared order",
                    self.class(entry).name,
                    self.class(k).name
                )
            });
        declared[..=at]
            .iter()
            .rev()
            .map(|(c, _)| *c)
            .find(|c| self.class(*c).kind != ClassKind::Module)
            .unwrap_or(k)
    }

    fn build_witnesses(&self) -> WitnessTable {
        let mut table = WitnessTable::default();
        // (The rows of a conformance at the class it hangs from, found
        // once for the classes below.)
        let mut at_root: HashMap<(ClassId, ExtensionId, ClassId, MethodId), MethodId> =
            HashMap::default();
        for k in 0..self.classes.len() as ClassId {
            if self.class(k).kind == ClassKind::Module {
                continue;
            }
            // (Each class's rows as seen where the class is declared: the
            // table does not depend on the extensions active where it is
            // asked for.)
            self.with_view(self.declaration_view(k), || {
                self.class_witnesses(k, &mut table, &mut at_root)
            });
        }
        table
    }

    /// The rows of class `k` (`witnesses`), asked under `k`'s
    /// `declaration_view`.
    fn class_witnesses(
        &self,
        k: ClassId,
        table: &mut WitnessTable,
        at_root: &mut HashMap<(ClassId, ExtensionId, ClassId, MethodId), MethodId>,
    ) {
        let kind = self.class(k).kind;
        let own = self.own_args(k);
        let lookup = self.resolution(k, &own, View::Lookup);
        // (The conformances are enumerated here, the run-time membership
        // by `resolution`: every module a value of the class is by
        // membership and the class does not declare has its rows.)
        #[cfg(debug_assertions)]
        {
            let declared: Vec<ClassId> = self
                .resolution(k, &own, View::Declared)
                .into_iter()
                .map(|(c, _)| c)
                .collect();
            let confs: Vec<ClassId> = self
                .extension_conformances(k)
                .into_iter()
                .map(|c| c.module)
                .collect();
            for (m, _) in self.resolution(k, &[], View::Runtime) {
                assert!(
                    self.class(m).kind != ClassKind::Module
                        || declared.contains(&m)
                        || confs.contains(&m),
                    "internal error: `{}` is a `{}` at run time by no conformance the witness table knows",
                    self.class(k).name,
                    self.class(m).name
                );
            }
        }
        for conf in self.extension_conformances(k) {
            let c = self.part_class(k, conf.root);
            let source = WitnessSource::Include {
                ext: conf.ext,
                include: conf.include,
                target: conf.target,
            };
            let module = self.class(conf.module);
            let instance: Vec<MethodId> = module.methods.values().flatten().copied().collect();
            let class_side: Vec<MethodId> = module
                .singleton_methods
                .values()
                .flatten()
                .copied()
                .collect();
            for r in instance.into_iter().chain(class_side) {
                let info = self.method(r);
                if info.owner != conf.module {
                    continue;
                }
                let below = (c != k && !info.singleton)
                    .then(|| self.witness_below(k, c, &lookup, &conf, r))
                    .flatten();
                let by = below.unwrap_or_else(|| {
                    *at_root
                        .entry((c, conf.ext, conf.module, r))
                        .or_insert_with(|| self.conformance_witness(c, r))
                });
                table.push(Witness {
                    class: k,
                    module: conf.module,
                    args: conf.args.clone(),
                    source: source.clone(),
                    method: r,
                    by,
                });
            }
        }
        // A module the class includes itself that a superclass has
        // already, through an extension, in dispatch's order (the own
        // include then does nothing, docs/01 §6): on the instance side
        // the superclass's conformance holds, the class's own part of
        // the order in front of it (step 1).
        for (m, margs, p) in self.shadowed_includes(k) {
            let Some(at_p) = self
                .extension_conformances(p)
                .into_iter()
                .find(|x| x.module == m)
            else {
                continue;
            };
            let c = self.part_class(k, at_p.root);
            let conf = ExtConformance {
                args: margs,
                ..at_p
            };
            let methods: Vec<MethodId> =
                self.class(m).methods.values().flatten().copied().collect();
            for r in methods {
                let info = self.method(r);
                if info.owner != m || info.singleton {
                    continue;
                }
                let by = self
                    .witness_below(k, c, &lookup, &conf, r)
                    .unwrap_or_else(|| {
                        *at_root
                            .entry((c, conf.ext, conf.module, r))
                            .or_insert_with(|| self.conformance_witness(c, r))
                    });
                table.push(Witness {
                    class: k,
                    module: m,
                    args: conf.args.clone(),
                    source: WitnessSource::Include {
                        ext: conf.ext,
                        include: conf.include,
                        target: conf.target,
                    },
                    method: r,
                    by,
                });
            }
        }
        // The other kinds: an abstract method of the class's declared
        // ancestors.
        let concrete = match kind {
            ClassKind::Class => !self.class(k).is_abstract,
            ClassKind::Data | ClassKind::Variant => true,
            ClassKind::Module | ClassKind::Enum | ClassKind::Main => false,
        };
        if !concrete {
            return;
        }
        for (d, dargs) in self.resolution(k, &own, View::Declared) {
            let abstracts: Vec<MethodId> = self
                .class(d)
                .methods
                .values()
                .flatten()
                .copied()
                .filter(|&r| {
                    let m = self.method(r);
                    m.is_abstract && m.owner == d && !m.singleton
                })
                .collect();
            for r in abstracts {
                let (source, by) = match self.implementation_for(k, &lookup, d, r) {
                    Implementation::Extension(ext, by) => (WitnessSource::Method { ext }, by),
                    Implementation::Inherited(by) => (WitnessSource::Inherited, by),
                    Implementation::Missing | Implementation::Own(_) => continue,
                };
                table.push(Witness {
                    class: k,
                    module: d,
                    args: dargs.clone(),
                    source,
                    method: r,
                    by,
                });
            }
        }
    }

    /// What implements the abstract instance method `r`, declared by `d`,
    /// for class `k`, going up `order`, `k`'s lookup order with its
    /// arguments (`View::Lookup`): the one answer the declarer's
    /// conformance check (what the class must implement) and the table
    /// (its rows of the kinds `Method` and `Inherited`) both take. The
    /// first entry's own method that takes what `r`'s callers pass
    /// (`implements`), or, an entry having none, the own method of an
    /// extension of the prelude or of `k`'s group that targets it
    /// (`group_gives`). A method of an entry after `d` is `Inherited`; one
    /// in front of `d` must be the one of the signature
    /// (`implementation_by_signature`: another of the name is an overload,
    /// and the one of the signature may come further up, `Inherited` then;
    /// none: missing).
    pub fn implementation_for(
        &self,
        k: ClassId,
        order: &[(ClassId, Vec<Type>)],
        d: ClassId,
        r: MethodId,
    ) -> Implementation {
        let name = &self.method(r).name;
        let at = |c: ClassId| order.iter().position(|(e, _)| *e == c);
        for (e, _) in order {
            if let Some(ids) = self.class(*e).methods.get(name) {
                if let Some(&i) = ids.iter().find(|i| self.implements(**i, r)) {
                    if at(self.method(i).owner) > at(d) {
                        return Implementation::Inherited(i);
                    }
                    return match self.implementation_by_signature(order, d, r) {
                        None => Implementation::Missing,
                        Some(j) if j != i => Implementation::Inherited(j),
                        Some(_) => Implementation::Own(i),
                    };
                }
            }
            if let Some((ext, i)) = self.group_gives(k, *e, r) {
                return Implementation::Extension(ext, i);
            }
        }
        Implementation::Missing
    }

    /// The method that implements the abstract `abs` (of the ancestor
    /// `anc`) by signature, going up `typed` (the ancestors with their
    /// arguments): the first that takes every call `abs` takes there
    /// (`World::takes_calls_of`), or of the same signature for the
    /// runtime (a method's own type parameters).
    fn implementation_by_signature(
        &self,
        typed: &[(ClassId, Vec<Type>)],
        anc: ClassId,
        abs: MethodId,
    ) -> Option<MethodId> {
        let (_, aargs) = typed.iter().find(|(c, _)| *c == anc)?;
        let asubst = self.class_subst(anc, aargs);
        let a = self.method(abs);
        for (k, kargs) in typed {
            let Some(ids) = self.class(*k).methods.get(&a.name) else {
                continue;
            };
            let ksubst = self.class_subst(*k, kargs);
            for &j in ids {
                let jm = self.method(j);
                if jm.is_abstract || jm.singleton != a.singleton {
                    continue;
                }
                let fits = if jm.type_params.is_empty() && a.type_params.is_empty() {
                    self.takes_calls_of(jm, &ksubst, a, &asubst)
                } else {
                    self.same_signature_at_run_time(j, abs)
                };
                if fits {
                    return Some(j);
                }
            }
        }
        None
    }

    /// The own method of an extension that implements the abstract method
    /// `r` for the class or module `entry` of class `k`'s lookup order,
    /// wherever the value goes: an extension of the prelude, or one at
    /// the top level of the group of `k`'s file (active where `k` is
    /// declared), targeting `entry`, in declaration order.
    fn group_gives(
        &self,
        k: ClassId,
        entry: ClassId,
        r: MethodId,
    ) -> Option<(ExtensionId, MethodId)> {
        let group = self.file_groups.get(&self.class(k).file);
        self.extensions
            .iter()
            .filter(|e| {
                e.target == entry
                    && (e.always_active || (group.is_some() && e.group.as_ref() == group))
            })
            .find_map(|e| self.extension_method_for(e, r).map(|i| (e.id, i)))
    }

    /// The own method of extension `e` that stands for the abstract
    /// method `abs`: one that takes what its callers pass (`implements`),
    /// of the same signature first. It is then checked as an override.
    pub fn extension_method_for(&self, e: &ExtensionInfo, abs: MethodId) -> Option<MethodId> {
        let a = self.method(abs);
        let ids = e.methods.get(&a.name)?;
        let side = |i: &&MethodId| self.method(**i).singleton == a.singleton;
        ids.iter()
            .filter(side)
            .find(|i| self.implements(**i, abs) && self.same_signature_at_run_time(**i, abs))
            .or_else(|| ids.iter().filter(side).find(|i| self.implements(**i, abs)))
            .copied()
    }

    /// Whether a concrete method of the same name whose arity covers the
    /// abstract one's counts as its implementation (types are checked
    /// with the pair, as an override).
    pub fn implements(&self, candidate: MethodId, abstract_id: MethodId) -> bool {
        let (c, a) = (self.method(candidate), self.method(abstract_id));
        if c.is_abstract || c.name != a.name {
            return false;
        }
        let (cmin, cmax) = c.positional_arity();
        let (amin, amax) = a.positional_arity();
        cmin <= amin
            && cmax >= amax
            && c.block.is_some() == a.block.is_some()
            && c.keywords_accept(a)
    }

    /// The method of class or module `entry` (its own, on `r`'s side)
    /// that replaces `r`, each seen through its substitution.
    fn entry_replaces(
        &self,
        entry: ClassId,
        esubst: &HashMap<TypeParamId, Type>,
        r: MethodId,
        rsubst: &HashMap<TypeParamId, Type>,
    ) -> Option<MethodId> {
        let info = self.method(r);
        let class = self.class(entry);
        let table = if info.singleton {
            &class.singleton_methods
        } else {
            &class.methods
        };
        table.get(&info.name)?.iter().copied().find(|&i| {
            let im = self.method(i);
            im.owner == entry
                && !im.is_abstract
                && im.singleton == info.singleton
                && i != r
                && self.replaces_seen(i, esubst, r, rsubst)
        })
    }

    /// Step 1 of the instance side (`witnesses`): for class `k` below the
    /// class `c` its conformance hangs from, the first method of `k`'s
    /// lookup order in front of `c` that replaces `r`, seen from `k`; for
    /// an abstract `r`, also the extension's method `group_gives` finds
    /// for an entry.
    fn witness_below(
        &self,
        k: ClassId,
        c: ClassId,
        lookup: &[(ClassId, Vec<Type>)],
        conf: &ExtConformance,
        r: MethodId,
    ) -> Option<MethodId> {
        let rsubst = self.class_subst(conf.module, &conf.args);
        let abstract_ = self.method(r).is_abstract;
        let grouped = self.active_where_declared(k, conf.ext);
        // (The module's own ancestry gives `r` nothing: it is behind it.)
        let behind: Vec<ClassId> = self
            .resolution(conf.module, &conf.args, View::Declared)
            .into_iter()
            .map(|(m, _)| m)
            .collect();
        for (e, eargs) in lookup.iter().take_while(|(e, _)| *e != c) {
            if behind.contains(e) {
                continue;
            }
            if let Some(i) = self.entry_replaces(*e, &self.class_subst(*e, eargs), r, &rsubst) {
                return Some(i);
            }
            if abstract_ && grouped {
                if let Some((_, i)) = self.group_gives(k, *e, r) {
                    return Some(i);
                }
            }
        }
        None
    }

    /// The witness of method `r` for class `c` itself, the class its
    /// conformance to `r`'s module hangs from: steps 2 to 6 of
    /// `witnesses`. `r` itself when nothing else is found.
    pub fn conformance_witness(&self, c: ClassId, r: MethodId) -> MethodId {
        let owner = self.method(r).owner;
        let Some(conf) = self
            .extension_conformances(c)
            .into_iter()
            .find(|x| x.module == owner)
        else {
            return r;
        };
        // (Seen where `c` is declared, whichever class's rows ask.)
        self.with_view(self.declaration_view(c), || {
            self.witness_at(c, &conf, r).unwrap_or(r)
        })
    }

    /// `conformance_witness` for extension `ext`'s include number
    /// `include`, as if no other extension made its target conform: what
    /// the declarer checks at the extension, also for one that is not the
    /// first to bring the module (#517). The methods of the modules the
    /// include brings that the target does not have itself, each with its
    /// witness for the target (`None`: an abstract one nothing
    /// implements).
    pub fn include_witnesses(
        &self,
        ext: ExtensionId,
        include: usize,
    ) -> Vec<(ExtConformance, MethodId, Option<MethodId>)> {
        // (Seen where the target is declared, as its rows are.)
        let target = self.extensions[ext as usize].target;
        self.with_view(self.declaration_view(target), || {
            self.include_witnesses_at(ext, include)
        })
    }

    fn include_witnesses_at(
        &self,
        ext: ExtensionId,
        include: usize,
    ) -> Vec<(ExtConformance, MethodId, Option<MethodId>)> {
        let e = &self.extensions[ext as usize];
        let Some(Type::Class(m, eargs)) = e.includes.get(include) else {
            return Vec::new();
        };
        let target = e.target;
        let targs = self.own_args(target);
        let declared: Vec<ClassId> = self
            .resolution(target, &targs, View::Declared)
            .into_iter()
            .map(|(c, _)| c)
            .collect();
        let esubst = self.extension_subst(e, &targs);
        let margs: Vec<Type> = eargs.iter().map(|t| t.subst(&esubst)).collect();
        let here = self.resolution(*m, &margs, View::Declared);
        let there = self.resolution(*m, eargs, View::Declared);
        let mut out = Vec::new();
        for ((x, xargs), (_, xeargs)) in here.into_iter().zip(there) {
            if self.class(x).kind != ClassKind::Module || declared.contains(&x) {
                continue;
            }
            let conf = ExtConformance {
                ext,
                include,
                target,
                target_args: targs.clone(),
                root: target,
                module: x,
                args: xargs,
                ext_args: xeargs,
            };
            let class = self.class(x);
            let methods: Vec<MethodId> = class
                .methods
                .values()
                .flatten()
                .chain(class.singleton_methods.values().flatten())
                .copied()
                .filter(|&r| self.method(r).owner == x)
                .collect();
            // (A module target has no class of its own to answer for: the
            // classes including it do, each from its own rows.)
            let c = if self.class(target).kind == ClassKind::Module {
                None
            } else {
                Some(target)
            };
            for r in methods {
                let by = match c {
                    Some(c) => self.witness_at(c, &conf, r),
                    None => self.witness_at(target, &conf, r),
                };
                out.push((conf.clone(), r, by));
            }
        }
        out
    }

    /// Steps 2 to 6 for `conf`, a conformance class `c` has from its own
    /// part of the declared order; `None` for an abstract `r` nothing
    /// implements.
    fn witness_at(&self, c: ClassId, conf: &ExtConformance, r: MethodId) -> Option<MethodId> {
        let info = self.method(r);
        let e = &self.extensions[conf.ext as usize];
        if info.singleton {
            return self.class_witness_at(c, conf, r);
        }
        let x = conf.module;
        // (Seen from `c`, and from the extension for its own methods and
        // its modules'.)
        let rsubst = self.class_subst(x, &conf.args);
        let rsubst_e = self.class_subst(x, &conf.ext_args);
        let none = HashMap::default();
        let lookup = self.resolution(c, &self.own_args(c), View::Lookup);
        // (An extension's own method for an abstract `r`, `group_gives`:
        // only where the conformance's extension is itself active where
        // the class is declared, so that the class's conformance check
        // sees the module and checks the pair, as for a module the class
        // includes itself.)
        let grouped = self.active_where_declared(c, conf.ext);
        // (`c`'s own part of the order in front of the conformance: for a
        // module target `c` includes itself, what comes before it.)
        let root_at = lookup.iter().position(|(k, _)| *k == conf.root);
        // 2. The extension's own method.
        let own = if info.is_abstract {
            self.extension_method_for(e, r)
        } else {
            e.methods.get(&info.name).and_then(|ids| {
                ids.iter().copied().find(|&i| {
                    let im = self.method(i);
                    !im.is_abstract && !im.singleton && self.replaces_seen(i, &none, r, &rsubst_e)
                })
            })
        };
        // (In front of the extension's own, what `c` has before a module
        // target of its own: the class's own methods and own includes
        // override any extension's module.)
        if let Some(at) = root_at {
            for (k, kargs) in &lookup[..at] {
                if let Some(i) = self.entry_replaces(*k, &self.class_subst(*k, kargs), r, &rsubst) {
                    return Some(i);
                }
            }
        }
        if own.is_some() {
            return own;
        }
        // The module's own ancestry, which gives `r` nothing: its methods
        // are behind `r` (the module overrides them).
        let behind: Vec<ClassId> = self
            .resolution(x, &conf.args, View::Declared)
            .into_iter()
            .map(|(k, _)| k)
            .collect();
        // 3. `c`'s own part of the lookup order in front of the module:
        // from the conformance's root to the next class, up to the module
        // itself where a top-level unconditional extension puts it there.
        let from = root_at.unwrap_or(0);
        let part_end = lookup[from + 1..]
            .iter()
            .position(|(k, _)| self.class(*k).kind != ClassKind::Module)
            .map_or(lookup.len(), |p| from + 1 + p);
        let x_at = lookup.iter().position(|(k, _)| *k == x);
        let front_end = x_at.filter(|p| *p < part_end).unwrap_or(part_end);
        for (k, kargs) in &lookup[from..front_end] {
            if behind.contains(k) {
                continue;
            }
            if let Some(i) = self.entry_replaces(*k, &self.class_subst(*k, kargs), r, &rsubst) {
                return Some(i);
            }
            if info.is_abstract && grouped {
                if let Some((_, i)) = self.group_gives(c, *k, r) {
                    return Some(i);
                }
            }
        }
        // 4. A module the extension includes after the one that brings the
        // module, the last included first.
        let brought = |inc: &Type| -> Vec<(ClassId, Vec<Type>)> {
            match inc {
                Type::Class(m, margs) => self
                    .resolution(*m, margs, View::Declared)
                    .into_iter()
                    .filter(|(k, _)| self.class(*k).kind == ClassKind::Module)
                    .collect(),
                _ => Vec::new(),
            }
        };
        for inc in e.includes[conf.include + 1..].iter().rev() {
            for (k, kargs) in brought(inc) {
                if behind.contains(&k) {
                    continue;
                }
                if let Some(i) = self.entry_replaces(k, &self.class_subst(k, &kargs), r, &rsubst_e)
                {
                    return Some(i);
                }
            }
        }
        // 5. The included module's own ancestry in front of the module.
        for (k, kargs) in brought(&e.includes[conf.include]) {
            if k == x {
                break;
            }
            if let Some(i) = self.entry_replaces(k, &self.class_subst(k, &kargs), r, &rsubst_e) {
                return Some(i);
            }
        }
        // 6. The module's own; an abstract one is implemented by what
        // follows it: the modules the extension includes before it, then
        // the rest of the lookup order.
        if !info.is_abstract {
            return Some(r);
        }
        for inc in e.includes[..conf.include].iter().rev() {
            for (k, kargs) in brought(inc) {
                if behind.contains(&k) {
                    continue;
                }
                if let Some(i) = self.entry_replaces(k, &self.class_subst(k, &kargs), r, &rsubst_e)
                {
                    return Some(i);
                }
            }
        }
        for (k, kargs) in &lookup[front_end..] {
            if behind.contains(k) {
                continue;
            }
            if let Some(i) = self.entry_replaces(*k, &self.class_subst(*k, kargs), r, &rsubst) {
                return Some(i);
            }
            if grouped {
                if let Some((_, i)) = self.group_gives(c, *k, r) {
                    return Some(i);
                }
            }
        }
        // (And by a module another extension makes the class conform to,
        // whichever is declared first: an abstract declaration gives no
        // method beside another's body, #522.)
        for other in self.extension_conformances(c) {
            if behind.contains(&other.module) {
                continue;
            }
            let osubst = self.class_subst(other.module, &other.args);
            if let Some(i) = self.entry_replaces(other.module, &osubst, r, &rsubst) {
                return Some(i);
            }
        }
        None
    }

    /// The class side of `witness_at` (#504): the extension's own `def
    /// self.`, else the class's own or a superclass's own class method
    /// (not a module's, #601), else a module the extension includes after
    /// it (the last first, #523), else the nearest in the included
    /// module's own ancestry, else the module's default.
    fn class_witness_at(&self, c: ClassId, conf: &ExtConformance, r: MethodId) -> Option<MethodId> {
        let info = self.method(r);
        let e = &self.extensions[conf.ext as usize];
        let x = conf.module;
        let in_class: Vec<(ClassId, Vec<Type>)> = self
            .resolution(c, &self.own_args(c), View::Declared)
            .into_iter()
            .chain(std::iter::once((x, conf.args.clone())))
            .collect();
        let own: Vec<MethodId> = e
            .methods
            .get(&info.name)
            .into_iter()
            .flatten()
            .copied()
            .filter(|&i| self.method(i).singleton)
            .collect();
        // A witness takes every call the module's method takes, with the
        // module's arguments substituted (`d(x: Int)` for `M[Int]`'s `d(x:
        // T)`); an abstract one is checked as an override at the
        // extension.
        // (`isubst`: how the candidate's owner is seen; `in_ext`: with the
        // module's arguments in the extension's parameters, for the
        // extension's own methods and its modules'.)
        let fits = |i: MethodId, isubst: &HashMap<TypeParamId, Type>, in_ext: bool| {
            if !self.implements(i, r) {
                return false;
            }
            if info.is_abstract || self.same_signature_at_run_time(i, r) {
                return true;
            }
            let rsubst = if in_ext {
                self.class_subst(x, &conf.ext_args)
            } else {
                self.class_subst(x, &conf.args)
            };
            self.takes_calls_of(self.method(i), isubst, info, &rsubst)
        };
        let of = |k: ClassId, kargs: Option<&[Type]>, in_ext: bool, concrete: bool| {
            let isubst = kargs.map(|a| self.class_subst(k, a)).unwrap_or_default();
            self.class(k)
                .singleton_methods
                .get(&info.name)
                .and_then(|ids| {
                    ids.iter().copied().find(|&i| {
                        let im = self.method(i);
                        im.owner == k && (!concrete || !im.is_abstract) && fits(i, &isubst, in_ext)
                    })
                })
        };
        let none = HashMap::default();
        if let Some(i) = own.iter().copied().find(|&i| fits(i, &none, true)) {
            return Some(i);
        }
        if let Some(i) = self.superclass_chain(c).into_iter().find_map(|k| {
            let kargs = in_class
                .iter()
                .find(|(e, _)| *e == k)
                .map(|(_, a)| a.as_slice());
            of(k, kargs, false, false)
        }) {
            return Some(i);
        }
        let modules = |inc: &Type| -> Vec<(ClassId, Vec<Type>)> {
            match inc {
                Type::Class(m, margs) => self
                    .resolution(*m, margs, View::Declared)
                    .into_iter()
                    .filter(|(k, _)| self.class(*k).kind == ClassKind::Module)
                    .collect(),
                _ => Vec::new(),
            }
        };
        let behind: Vec<ClassId> = modules(&Type::Class(x, conf.ext_args.clone()))
            .into_iter()
            .map(|(k, _)| k)
            .collect();
        for inc in e.includes[conf.include + 1..].iter().rev() {
            for (k, kargs) in modules(inc) {
                if behind.contains(&k) {
                    continue;
                }
                if let Some(i) = of(k, Some(&kargs), true, true) {
                    return Some(i);
                }
            }
        }
        for (k, kargs) in modules(&e.includes[conf.include]) {
            if k == x {
                break;
            }
            if let Some(i) = of(k, Some(&kargs), true, true) {
                return Some(i);
            }
        }
        (!info.is_abstract).then_some(r)
    }
}
