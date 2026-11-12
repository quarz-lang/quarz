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

/// The override table's pairs (#536 step 1) as the table's walk reads
/// them, remembered for one build: `World::overrides` of a method, as
/// seen where its class is declared; the pairs of
/// `World::include_overrides_of` a class has, as (overridden, by),
/// likewise; and a class's run-time order.
/// The modules an extension brings, with their arguments in its
/// parameters (`World::brought_modules`).
type Brought = Rc<Vec<(ClassId, Vec<Type>)>>;

#[derive(Default)]
struct Pairs {
    overrides: HashMap<MethodId, Rc<Vec<MethodId>>>,
    includes: HashMap<ClassId, Rc<Vec<(MethodId, MethodId)>>>,
    runtime: HashMap<ClassId, Rc<Vec<ClassId>>>,
    brought: HashMap<ExtensionId, Brought>,
}

impl Pairs {
    fn overrides(&mut self, world: &World, m: MethodId) -> Rc<Vec<MethodId>> {
        self.overrides
            .entry(m)
            .or_insert_with(|| {
                let owner = world.method(m).owner;
                Rc::new(world.with_view(world.declaration_view(owner), || world.overrides(m)))
            })
            .clone()
    }

    fn include(&mut self, world: &World, c: ClassId) -> Rc<Vec<(MethodId, MethodId)>> {
        self.includes
            .entry(c)
            .or_insert_with(|| {
                Rc::new(world.with_view(world.declaration_view(c), || {
                    world
                        .include_overrides_of(c)
                        .into_iter()
                        .map(|o| (o.overridden, o.by))
                        .collect()
                }))
            })
            .clone()
    }

    fn brought(&mut self, world: &World, e: ExtensionId) -> Brought {
        self.brought
            .entry(e)
            .or_insert_with(|| Rc::new(world.brought_modules(&world.extensions[e as usize])))
            .clone()
    }

    fn runtime(&mut self, world: &World, c: ClassId) -> Rc<Vec<ClassId>> {
        self.runtime
            .entry(c)
            .or_insert_with(|| {
                Rc::new(
                    world
                        .resolution(c, &[], View::Runtime)
                        .into_iter()
                        .map(|(k, _)| k)
                        .collect(),
                )
            })
            .clone()
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
    /// #504). For a module `K` has itself, ordinary dispatch holds (the
    /// override table, #536 step 1) and an extension's method of the name
    /// is an extension method, chosen statically. Bounds are not
    /// consulted for a row's existence, a class value carrying no type
    /// arguments.
    ///
    /// The invariant: a row's witness is the module's own method, or the
    /// own method of an extension, or a method the override table pairs
    /// with the module's method for a class of `K`'s run-time order, or
    /// what `implementation_for` finds for the class under a conformance
    /// active where it is declared. The table adds no pair of its own
    /// (`row_is_a_checked_pair`), so each pair is one a check of the
    /// declarer covers: an extension's method at the extension, in its
    /// parameters (`Declarer::check_extension_own_witnesses`); a pair of
    /// `World::overrides` or `World::include_overrides_of` where the
    /// override table is checked; `implementation_for`'s with the class
    /// (`Declarer::check_conformance_of`).
    ///
    /// Instance side (a call through a value typed `M`; #536 step 1's
    /// decisions (3) and (4): the class's own methods and own includes
    /// override any extension's module, a subclass's too): going up `K`'s
    /// run-time order (`View::Runtime`: dispatch's, then the modules of
    /// the scoped and conditional extensions), at each entry
    /// 1. the own method of an extension targeting the entry that brings
    ///    `M` (the first declared), which takes `r`'s calls
    ///    (`extension_own_witness`);
    /// 2. else the entry's own method that the override table pairs with
    ///    `r`: a class's own method or a subclass's, one of a module they
    ///    include themselves, a module's over the one it includes, an
    ///    abstract `r` with what the table says implements it;
    ///
    /// and the walk ends at `M` when `r` has a body (the module's own
    /// runs). Before the walk, for an abstract `r` under a conformance
    /// whose extension is active where `K` is declared (the class's
    /// conformance check then sees the module): what the rule of the
    /// class's own abstract methods finds when the walk would not, the
    /// own method of an extension that includes nothing for it, or a
    /// method further up than the module (`implementation_for`; the
    /// replaced record had both), checked with the class. An abstract `r` nothing implements stays in the row and
    /// raises when called (#600, #555). What the override table does not
    /// pair is no witness yet: a method the class inherits, a module the
    /// same extension includes beside `M` (#557), a module another
    /// extension brings, beyond the pairs `include_overrides_of` has
    /// (#605).
    ///
    /// Class side (a call through `Type[M]` or `T <: M`; #504): witnesses
    /// are fixed, the row of the class the conformance hangs from serves
    /// it and every class below it: the extension's own `def self.`, else
    /// the class's own or a superclass's own class method (not one of a
    /// module they include, #601), else a module the extension includes
    /// after it (the last first, #523), else the nearest in the included
    /// module's own ancestry, else the module's default; each checked at
    /// the extension (`Declarer::check_extension_class_side`).
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
    /// Each class's rows are asked as seen where the class is declared
    /// (`declaration_view`), each pair of the override table where its
    /// class is, an extension's own method where the extension is: the
    /// table does not depend on the extensions active where it is asked
    /// for.
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
        let mut pairs = Pairs::default();
        for k in 0..self.classes.len() as ClassId {
            if self.class(k).kind == ClassKind::Module {
                continue;
            }
            // (Each class's rows as seen where the class is declared: the
            // table does not depend on the extensions active where it is
            // asked for.)
            self.with_view(self.declaration_view(k), || {
                self.class_witnesses(k, &mut table, &mut at_root, &mut pairs)
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
        pairs: &mut Pairs,
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
        // A conformance through an extension, and a module the class
        // includes itself that a superclass has already, through an
        // extension, in dispatch's order (the own include then does
        // nothing, docs/01 §6): on the instance side the superclass's
        // conformance holds.
        let mut confs: Vec<(ExtConformance, bool)> = self
            .extension_conformances(k)
            .into_iter()
            .map(|c| (c, true))
            .collect();
        for (m, margs, p) in self.shadowed_includes(k) {
            if let Some(at_p) = self
                .extension_conformances(p)
                .into_iter()
                .find(|x| x.module == m)
            {
                confs.push((
                    ExtConformance {
                        args: margs,
                        ..at_p
                    },
                    false,
                ));
            }
        }
        for (conf, class_side) in confs {
            let source = WitnessSource::Include {
                ext: conf.ext,
                include: conf.include,
                target: conf.target,
            };
            let module = self.class(conf.module);
            let methods: Vec<MethodId> = module
                .methods
                .values()
                .flatten()
                .chain(module.singleton_methods.values().flatten())
                .copied()
                .filter(|&r| self.method(r).owner == conf.module)
                .collect();
            for r in methods {
                let by = if self.method(r).singleton {
                    if !class_side {
                        continue;
                    }
                    // (Fixed, #504: the row of the class the conformance
                    // hangs from.)
                    let c = self.part_class(k, conf.root);
                    *at_root
                        .entry((c, conf.ext, conf.module, r))
                        .or_insert_with(|| self.class_conformance_witness(c, r))
                } else {
                    self.instance_witness(k, &lookup, &conf, r, pairs)
                };
                let w = Witness {
                    class: k,
                    module: conf.module,
                    args: conf.args.clone(),
                    source: source.clone(),
                    method: r,
                    by,
                };
                debug_assert!(
                    self.row_is_a_checked_pair(&w),
                    "internal error: the witness table pairs `{}` with `{}#{}` for `{}` by no check",
                    self.method(by).name,
                    self.class(conf.module).name,
                    self.method(r).name,
                    self.class(k).name
                );
                table.push(w);
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
        let found: Vec<(ExtensionId, MethodId)> = self
            .extensions
            .iter()
            .filter(|e| {
                e.target == entry
                    && (e.always_active || (group.is_some() && e.group.as_ref() == group))
            })
            .filter_map(|e| self.extension_method_for(e, r).map(|i| (e.id, i)))
            .collect();
        // (Of several, one whose extension brings the method's module
        // itself: `extension Box[T <: String]; include PS; def parse` for
        // `PS#parse`, not another extension's `parse` written for the
        // module that one includes, #529. Else the first declared, #605.)
        let module = self.method(r).owner;
        found
            .iter()
            .copied()
            .find(|(e, _)| {
                self.brought_args(&self.extensions[*e as usize], module)
                    .is_some()
            })
            .or_else(|| found.first().copied())
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

    /// The instance-side row for class `k` and method `r` of a module it
    /// has through the conformance `conf` (`witnesses`): going up `k`'s
    /// run-time order, at each entry the own method of an extension
    /// targeting it that brings the module (`extension_own_witness`), else
    /// the entry's method that the override table pairs with `r`
    /// (`Pairs`); ending at the module when `r` has a body. `r` itself
    /// when nothing is found.
    fn instance_witness(
        &self,
        k: ClassId,
        lookup: &[(ClassId, Vec<Type>)],
        conf: &ExtConformance,
        r: MethodId,
        pairs: &mut Pairs,
    ) -> MethodId {
        let info = self.method(r);
        let x = conf.module;
        // An abstract `r` under a conformance active where `k` is declared
        // (the class's conformance check sees the module): what the rule
        // of the class's own abstract methods finds when it is not where
        // the walk below finds it, an extension's own method that includes
        // nothing or a method further up than the module
        // (`implementation_for`: the replaced record had these too).
        if info.is_abstract && self.active_where_declared(k, conf.ext) {
            match self.implementation_for(k, lookup, x, r) {
                Implementation::Extension(_, i) | Implementation::Inherited(i) => return i,
                Implementation::Own(_) | Implementation::Missing => {}
            }
        }
        let order = pairs.runtime(self, k);
        for &a in order.iter() {
            if a == x && !info.is_abstract {
                return r;
            }
            // (A file's top-level `def`s are functions, no methods here.)
            if self.class(a).kind == ClassKind::Main {
                continue;
            }
            for e in &self.extensions {
                if e.target != a || e.includes.is_empty() || !e.methods.contains_key(&info.name) {
                    continue;
                }
                let brought = pairs.brought(self, e.id);
                if let Some((_, args)) = brought.iter().find(|(m, _)| *m == x) {
                    if let Some(i) = self.extension_own_witness_with(e, x, args, r) {
                        return i;
                    }
                }
            }
            let class = self.class(a);
            if let Some(ids) = class.methods.get(&info.name) {
                let candidates: Vec<MethodId> = ids
                    .iter()
                    .copied()
                    .filter(|&i| {
                        let im = self.method(i);
                        im.owner == a && !im.is_abstract && !im.singleton && i != r
                    })
                    .collect();
                // (A module's method over it where a class of the
                // receiver's includes the module, then what the method's
                // own entry says: the two parts of the override table.)
                if let Some(&i) = candidates.iter().find(|&&i| {
                    order
                        .iter()
                        .any(|&c| pairs.include(self, c).contains(&(r, i)))
                }) {
                    return i;
                }
                if let Some(&i) = candidates
                    .iter()
                    .find(|&&i| pairs.overrides(self, i).contains(&r))
                {
                    return i;
                }
            }
        }
        r
    }

    /// The own method of extension `ext` that runs in place of method `r`
    /// of module `x`, when the extension brings `x` (`brought_modules`):
    /// for an abstract `r`, the method that takes what
    /// its callers pass, of the same signature first
    /// (`extension_method_for`); for one with a body, the method that
    /// replaces it (`World::replaces_seen`), `x`'s arguments as the
    /// extension includes it. Asked as seen where the extension is
    /// declared, whoever asks: the table for every class the extension
    /// reaches, and the declarer, which checks the pair at the extension.
    pub fn extension_own_witness(
        &self,
        ext: ExtensionId,
        x: ClassId,
        r: MethodId,
    ) -> Option<MethodId> {
        let e = &self.extensions[ext as usize];
        let args = self.brought_args(e, x)?;
        self.extension_own_witness_with(e, x, &args, r)
    }

    /// `extension_own_witness`, `x`'s arguments as the extension brings it
    /// given.
    fn extension_own_witness_with(
        &self,
        e: &ExtensionInfo,
        x: ClassId,
        args: &[Type],
        r: MethodId,
    ) -> Option<MethodId> {
        let info = self.method(r);
        let ids = e.methods.get(&info.name)?;
        if info.is_abstract {
            return self.extension_method_for(e, r);
        }
        let rsubst = self.class_subst(x, args);
        let none = HashMap::default();
        self.with_view(self.extension_view(e), || {
            ids.iter().copied().find(|&i| {
                let im = self.method(i);
                !im.is_abstract
                    && im.singleton == info.singleton
                    && self.replaces_seen(i, &none, r, &rsubst)
            })
        })
    }

    /// The modules extension `e` brings (what its includes are, what they
    /// include, and what extensions make those conform to), each with its
    /// arguments in the extension's parameters, the last include's first;
    /// as seen where the extension is declared.
    pub fn brought_modules(&self, e: &ExtensionInfo) -> Vec<(ClassId, Vec<Type>)> {
        self.with_view(self.extension_view(e), || {
            let mut out: Vec<(ClassId, Vec<Type>)> = Vec::new();
            for inc in e.includes.iter().rev() {
                let Type::Class(m, margs) = inc else { continue };
                for (x, xargs) in self.resolution(*m, margs, View::Override) {
                    if self.class(x).kind == ClassKind::Module && !out.iter().any(|(k, _)| *k == x)
                    {
                        out.push((x, xargs));
                    }
                }
            }
            out
        })
    }

    /// Whether extension `e` brings module `x` (`brought_modules`), and
    /// with which arguments in the extension's parameters.
    pub fn brought_args(&self, e: &ExtensionInfo, x: ClassId) -> Option<Vec<Type>> {
        self.brought_modules(e)
            .into_iter()
            .find(|(k, _)| *k == x)
            .map(|(_, a)| a)
    }

    /// The extensions active where extension `e` is declared, whoever
    /// asks: the prelude's and the top-level ones of its group.
    pub fn extension_view(&self, e: &ExtensionInfo) -> Vec<ExtensionId> {
        let group = self.file_groups.get(&e.file);
        self.extensions
            .iter()
            .filter(|o| o.always_active || (group.is_some() && o.group.as_ref() == group))
            .map(|o| o.id)
            .collect()
    }

    /// The invariant of the table (#536 step 3): a row's witness is the
    /// module's own method, an own method of an extension, or a method the
    /// override table pairs with the module's for a class of the row's
    /// class's run-time order; the table adds no pair of its own, so every
    /// pair is one a check of the declarer covers (an extension's method
    /// at the extension or with the class it implements the method for,
    /// the override table's pairs where that table is checked). The class
    /// side's witnesses are checked at the extension, each conformance
    /// (`Declarer::check_extension_class_side`). Asked again here from the
    /// relations themselves, not from what the walk remembered.
    fn row_is_a_checked_pair(&self, w: &Witness) -> bool {
        let (r, by) = (w.method, w.by);
        if by == r || self.method(r).singleton || self.method(by).extension.is_some() {
            return true;
        }
        // (The record rule, under a conformance active where the class is
        // declared: checked with the class, `check_conformance_of`.)
        if let WitnessSource::Include { ext, .. } = w.source {
            if self.method(r).is_abstract && self.active_where_declared(w.class, ext) {
                let lookup = self.resolution(w.class, &self.own_args(w.class), View::Lookup);
                if self.implementation_for(w.class, &lookup, w.module, r)
                    == Implementation::Inherited(by)
                {
                    return true;
                }
            }
        }
        let owner = self.method(by).owner;
        if self
            .with_view(self.declaration_view(owner), || self.overrides(by))
            .contains(&r)
        {
            return true;
        }
        self.resolution(w.class, &[], View::Runtime)
            .into_iter()
            .any(|(c, _)| {
                self.with_view(self.declaration_view(c), || self.include_overrides_of(c))
                    .iter()
                    .any(|o| o.overridden == r && o.by == by)
            })
    }

    /// The class-side witness of method `r` for class `c` itself, the
    /// class its conformance to `r`'s module hangs from (`witnesses`). `r`
    /// itself when nothing else is found.
    fn class_conformance_witness(&self, c: ClassId, r: MethodId) -> MethodId {
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
            self.class_witness_at(c, &conf, r).unwrap_or(r)
        })
    }

    /// The witnesses of extension `ext`'s include number `include` for its
    /// target, as if no other extension made the target conform: what the
    /// declarer checks at the extension, also for one that is not the
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
        let mut pairs = Pairs::default();
        let lookup = self.resolution(target, &targs, View::Lookup);
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
            for r in methods {
                let by = if self.method(r).singleton {
                    self.class_witness_at(target, &conf, r)
                } else {
                    let by = self.instance_witness(target, &lookup, &conf, r, &mut pairs);
                    (by != r || !self.method(r).is_abstract).then_some(by)
                };
                out.push((conf.clone(), r, by));
            }
        }
        out
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
