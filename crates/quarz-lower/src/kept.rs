//! The tables the declarations decide, kept across the lowering's rounds
//! (#717, M2): the classes' and methods' rows of `RtWorld`, the override
//! table, the include pairs, the witness record and the rows over them,
//! the layouts and the overridden set. A `static` statement only adds
//! members (`World::static_events`), so a round rebuilds the rows of the
//! classes its events reach and keeps the others; a change of the class
//! graph (another program, a REPL input that declared classes or
//! extensions, a rollback) builds everything again.
//!
//! What each event reaches is the table on #717 ("M2 note, refreshed"):
//!
//! - **D(X)**: the classes whose ancestors hold `X` in any view a row
//!   reads (`ancestor_views`: the run-time ancestors, every extension's
//!   include; the override view, `own_ancestors`, which also has the
//!   modules of conditional extensions with their bounds assumed; the
//!   lookup and dispatch orders; the static view), closed transitively
//!   (an ancestor's ancestors in any view are the class's: a subclass of
//!   `Box[T]` with arguments a conditional extension's bound refuses still
//!   reads the rows of `Box`'s methods, which read that extension's
//!   module), `X` itself too. So a class outside D(X) reads no row of a
//!   class inside it.
//! - **H(X)**: the classes holding a field whose type names `X`
//!   (`ClassInfo::fields`, own or inherited, so with their D), and the
//!   holders of those that are `data` types, enums or variants (held in
//!   turn), transitively: a layout lays a flat `data` field out in place,
//!   and a `data` type's shareability reads its fields' types. Only a
//!   `data` type's flatness names take it (row 8, #796); a field or a
//!   recheck changes no holder's row or layout (`Kept::sync` says why;
//!   debug builds check it, `Kept::assert_holders_kept`).
//! - **T**: the classes whose instance methods a class object answers
//!   (`RtWorld::type_side_owners`): an instance method into one of them
//!   would change the override row of every class method of its name and
//!   the class-side keys of every class. No statement generates one
//!   (`Kept::sync` says why, and asserts it).
//!
//! Every invalidation set is a superset; a row kept stale is a soundness
//! bug, which the oracle (`QUARZ_VERIFY_STATIC_TABLES`, `verify`)
//! compares every round against the tables built from nothing.

use quarz_ir::*;
use quarz_types::{self as types, ClassKind, StaticEvent, Type, World};
use rustc_hash::FxHashSet as HashSet;

use crate::layout::{self, Layout};
use crate::rtworld;

/// What the kept tables were built for: the class graph and the
/// declarations. Classes and modules are not reopened, and a new include
/// needs a new class or extension, so the counts tell a graph change; a
/// method declared rather than generated (a REPL input's function, which
/// goes into an existing class, the file's top level) changes the count of
/// methods no `StaticEvent::Method` added.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct GraphKey {
    classes: usize,
    extensions: usize,
    declared_methods: usize,
}

impl GraphKey {
    fn of(world: &World) -> GraphKey {
        let generated = world
            .static_events
            .iter()
            .filter(|e| matches!(e, StaticEvent::Method(_)))
            .count();
        GraphKey {
            classes: world.classes.len(),
            extensions: world.extensions.len(),
            declared_methods: world.methods.len().saturating_sub(generated),
        }
    }
}

/// The tables, and what the next sync starts from.
pub(crate) struct Kept {
    key: GraphKey,
    /// The events read (`World::static_events`), and the sizes of what
    /// grows with them.
    cursor: usize,
    methods: usize,
    ext_impls: usize,
    class_ext_impls: usize,
    /// The checker's constructor choices the class rows were made with
    /// (`Output::inherited_inits`, which `class_row` reads): written by
    /// the check of a `new` site's class (`Checker::
    /// check_inherited_constructors`, after a file's statements), with no
    /// event, so compared at each sync.
    inherited: Vec<(ClassId, Option<MethodId>, MethodId)>,
    /// The declared tables, assembled (`rtworld::declared`'s value).
    pub(crate) rt: RtWorld,
    /// The override table, by method (`World::overrides`).
    table: Vec<Vec<MethodId>>,
    /// Per class: `World::include_overrides_of`,
    /// `class_include_overrides_of`, `rtworld::witness_record_of`, and the
    /// rows over them (`RtWorld::witness_rows_of`,
    /// `rtworld::class_override_rows_of`).
    pairs: Vec<Vec<(ClassId, MethodId, MethodId)>>,
    class_pairs: Vec<Vec<(ClassId, MethodId, MethodId)>>,
    record: Vec<Vec<(ClassId, MethodId, Option<MethodId>)>>,
    override_rows: Vec<Vec<(ClassId, MethodId, MethodId)>>,
    witness_rows: Vec<Vec<(ClassId, MethodId, Option<MethodId>)>>,
    class_rows: Vec<Vec<(ClassId, MethodId, MethodId)>>,
    /// `World::overridden_methods_over` the kept table and pairs.
    pub(crate) overridden: HashSet<MethodId>,
    graph: Graph,
    /// Each sync's number and the classes it rebuilt (`None`: all), for
    /// the readers that keep rows of their own (`changed_since`).
    epoch: u64,
    log: Vec<(u64, Option<Vec<ClassId>>)>,
}

/// The class graph's inversions, made once per graph.
struct Graph {
    /// D(X) by class, `X` first.
    below: Vec<Vec<ClassId>>,
    /// The classes declaring a field whose type names each class.
    holders: HashMap<ClassId, Vec<ClassId>>,
    /// T, sorted (`RtWorld::type_side_owners`).
    type_side_owners: Vec<ClassId>,
    /// Each class's methods, by owner.
    owned: Vec<Vec<MethodId>>,
    /// Each class's superclass and includes when the graph was made
    /// (debug builds assert they do not change, #717's P1).
    #[cfg(debug_assertions)]
    heads: Vec<(Option<Type>, Vec<Type>)>,
}

/// What one sync rebuilt, for the statistics (`QUARZ_STATIC_TABLES_STATS`).
#[derive(Default, Debug)]
pub(crate) struct SyncStats {
    pub full: bool,
    pub classes: usize,
    pub methods: usize,
    pub events: usize,
    /// Which edges of the table the events took: H for a `data` type's
    /// equality (row 8, #796), a recheck (rows 1/10), a deferred
    /// conformance (rows 5/7), a field (rows 1/2/8/9/10).
    pub data_eq: bool,
    pub rechecked: bool,
    pub conformance: bool,
    pub fields: bool,
    pub news: bool,
    pub inits: bool,
}

/// The names a `data` type's flatness reads (`layout::flat_class`): a
/// method of one of them generated into a `data` type may change the
/// layouts of its holders (#796; the edge goes if flatness is decided
/// from the written declarations).
const FLATNESS_NAMES: [&str; 4] = ["==", "!=", "hash", "initialize"];

impl Kept {
    /// Every table from nothing, the layouts (`layout::compute`) into
    /// `layouts`, at `epoch` (after every epoch earlier tables reached).
    pub(crate) fn build(
        world: &World,
        out: &types::Output,
        layouts: &mut Vec<Layout>,
        epoch: u64,
    ) -> Kept {
        let (rt, table) = rtworld::declared_with(world, out, rtworld::witness_record(world));
        let n = world.classes.len();
        let by_class = |c: ClassId| c as usize;
        let pairs = group(&rt.include_overrides, n, |r| by_class(r.0));
        let record = group(&rt.witness_record, n, |r| by_class(r.0));
        let override_rows = group(&rt.override_rows, n, |r| by_class(r.0));
        let witness_rows = group(&rt.witness_rows, n, |r| by_class(r.0));
        let class_rows = group(&rt.class_override_rows, n, |r| by_class(r.0));
        let class_pairs: Vec<Vec<(ClassId, MethodId, MethodId)>> = (0..n as ClassId)
            .map(|c| class_pairs_of(world, c))
            .collect();
        let flat: Vec<(ClassId, MethodId, MethodId)> =
            class_pairs.iter().flatten().copied().collect();
        let overridden = world.overridden_methods_over(&table, &rt.include_overrides, &flat);
        let graph = Graph::build(world, &rt);
        *layouts = layout::compute(world);
        Kept {
            key: GraphKey::of(world),
            cursor: world.static_events.len(),
            methods: world.methods.len(),
            ext_impls: world.ext_impls.len(),
            class_ext_impls: world.class_ext_impls.len(),
            inherited: out.inherited_inits.clone(),
            rt,
            table,
            pairs,
            class_pairs,
            record,
            override_rows,
            witness_rows,
            class_rows,
            overridden,
            graph,
            epoch,
            log: vec![(epoch, None)],
        }
    }

    /// Whether these tables are for `world`'s class graph and have not
    /// read past its events (a rolled-back REPL input shortens them).
    pub(crate) fn fits(&self, world: &World) -> bool {
        self.key == GraphKey::of(world) && self.cursor <= world.static_events.len()
    }

    /// The classes rebuilt by the syncs after `epoch`, or `None` when one
    /// of them rebuilt everything (or the log does not reach back).
    pub(crate) fn changed_since(&self, epoch: u64) -> Option<Vec<ClassId>> {
        if epoch == 0 || self.log.first().is_none_or(|(e, _)| *e > epoch + 1) {
            return None;
        }
        // (From the newest back: a reader asks for the syncs since its own
        // last one, a few entries.)
        let mut out: Vec<ClassId> = Vec::new();
        for (e, cs) in self.log.iter().rev() {
            if *e <= epoch {
                break;
            }
            out.extend(cs.as_ref()?.iter().copied());
        }
        out.sort_unstable();
        out.dedup();
        Some(out)
    }

    pub(crate) fn epoch(&self) -> u64 {
        self.epoch
    }

    /// Whether every event of `world` was read.
    pub(crate) fn synced(&self, world: &World) -> bool {
        self.cursor == world.static_events.len()
    }

    /// Read the events since the last sync and rebuild the rows they
    /// reach.
    pub(crate) fn sync(
        &mut self,
        world: &World,
        out: &types::Output,
        layouts: &mut Vec<Layout>,
    ) -> SyncStats {
        #[cfg(debug_assertions)]
        self.graph.assert_heads(world);
        let mut stats = SyncStats::default();
        let events = &world.static_events[self.cursor..];
        stats.events = events.len();
        let added = events
            .iter()
            .filter(|e| matches!(e, StaticEvent::Method(_)))
            .count();
        assert_eq!(
            self.methods + added,
            world.methods.len(),
            "internal error: methods were added to the world without their events (#717)"
        );
        // R0's witnesses (`World::ext_impls`, `class_ext_impls`) are
        // recorded by the declaration of an extension
        // (`Declarer::check_extension_conformance`,
        // `check_extension_static`) and by nothing a `static` statement
        // runs (`recheck_classes` and `recheck_conformance` read them):
        // a new extension changes the graph key, which builds everything
        // again. So between two syncs of one graph they do not grow.
        assert!(
            world.ext_impls.len() == self.ext_impls
                && world.class_ext_impls.len() == self.class_ext_impls,
            "internal error: R0's witnesses changed during a static phase (#717)"
        );
        let mut dirty: Vec<ClassId> = Vec::new();
        // (The owners of the methods generated so far in this sync, for
        // `New`'s check.)
        let mut generated_into: HashSet<ClassId> = HashSet::default();
        // (The classes whose holders' rows and layouts debug builds check
        // unchanged, `assert_holders_kept`.)
        #[cfg(debug_assertions)]
        let mut held: Vec<ClassId> = Vec::new();
        for event in events {
            match event {
                // (Rows 1, 2, 3(a), 4, 5, 7, 10, 12 for D(owner); row 8
                // through H for a `data` type's flatness names.)
                //
                // Never an extension's method, nor an instance method of a
                // class of T, which would change rows of every class (row
                // 3(b) and 7): a statement generates into the class it
                // runs on (`self`), never an extension, and runs on a
                // class only through a `static def` the class has (its
                // body's statements, or another class's statement calling
                // it); the classes of T are the prelude's, which have
                // none, and a module with `static def`s is never included
                // by an extension (`check_extension_static`), the only way
                // a user's module joins T. Both would have to change for
                // this to fail.
                StaticEvent::Method(m) => {
                    let mi = world.method(*m);
                    let x = mi.owner;
                    assert!(
                        mi.extension.is_none()
                            && (mi.singleton
                                || self.graph.type_side_owners.binary_search(&x).is_err()),
                        "internal error: a statement generated `{}` into an extension or a class of the type side (#717)",
                        mi.name
                    );
                    generated_into.insert(x);
                    dirty.extend(self.graph.below(x));
                    if is_data(world, x) && FLATNESS_NAMES.contains(&mi.name.as_str()) {
                        stats.data_eq = true;
                        dirty.extend(self.graph.held_by(world, x));
                    }
                }
                // (Rows 1, 2 (field indices), 8, 9, 10 for D(X).) Not H(X):
                // a field is generated into a class only
                // (`Checker::add_generated_field`), which a holder keeps by
                // reference: no holder's layout moves, and a class's
                // shareability is its written `Shareable` (an include, which
                // no statement adds), so no `data` holder's changes.
                StaticEvent::Field(x) => {
                    stats.fields = true;
                    dirty.extend(self.graph.below(*x));
                    self.graph.add_holder(world, *x);
                    #[cfg(debug_assertions)]
                    held.push(*x);
                }
                // (Row 1's inherited constructors.) The `Method` event of
                // the method that builds the instance, into the same class,
                // comes before it in the same sync (`static_run::Runner`
                // calls `StaticHost::generated_new` right after
                // `add_generated` declared it): its D is this one's.
                StaticEvent::New(x) => {
                    stats.news = true;
                    assert!(
                        generated_into.contains(x),
                        "internal error: a generated constructor of `{}` came without its method's event (#717)",
                        world.class(*x).name
                    );
                }
                // (A body's captures: no row reads them.)
                StaticEvent::Captures(_) => {}
                // (The shareable promise reset: rows 1 and 10.) Not H: a
                // recheck finds the shareability it reset unchanged, as
                // no statement adds an include or a field to a `data`
                // type, enum or variant (see `Field`), the only things a
                // derived shareability reads.
                StaticEvent::Rechecked(cs) => {
                    stats.rechecked = true;
                    for c in cs {
                        dirty.extend(self.graph.below(*c));
                        #[cfg(debug_assertions)]
                        held.push(*c);
                    }
                }
                StaticEvent::Conformance(cs) => {
                    stats.conformance = true;
                    for c in cs {
                        dirty.extend(self.graph.below(*c));
                    }
                }
            }
        }
        // Constructor choices changed since (no event: see `inherited`):
        // the class rows of their classes.
        if out.inherited_inits != self.inherited {
            stats.inits = true;
            for e in out
                .inherited_inits
                .iter()
                .filter(|e| !self.inherited.contains(e))
            {
                dirty.push(e.0);
            }
            for e in self
                .inherited
                .iter()
                .filter(|e| !out.inherited_inits.contains(e))
            {
                dirty.push(e.0);
            }
            self.inherited = out.inherited_inits.clone();
        }
        for m in self.methods..world.methods.len() {
            let owner = world.method(m as MethodId).owner;
            self.graph.owned[owner as usize].push(m as MethodId);
        }
        dirty.sort_unstable();
        dirty.dedup();
        self.rebuild(world, out, &dirty, layouts);
        #[cfg(debug_assertions)]
        self.assert_holders_kept(world, out, &held, &dirty, layouts);
        self.cursor = world.static_events.len();
        self.methods = world.methods.len();
        self.ext_impls = world.ext_impls.len();
        self.class_ext_impls = world.class_ext_impls.len();
        self.epoch += 1;
        stats.classes = dirty.len();
        stats.methods = dirty
            .iter()
            .map(|c| self.graph.owned[*c as usize].len())
            .sum();
        self.log.push((self.epoch, Some(dirty)));
        stats
    }

    /// Debug builds: the holders (H) of the classes a field was generated
    /// into or rechecked, outside `dirty` (sorted), have the class rows and
    /// layouts they would have if rebuilt (`sync`'s `Field` and
    /// `Rechecked`: why no event rebuilds them).
    #[cfg(debug_assertions)]
    fn assert_holders_kept(
        &self,
        world: &World,
        out: &types::Output,
        xs: &[ClassId],
        dirty: &[ClassId],
        layouts: &[Layout],
    ) {
        let mut hs: Vec<ClassId> = xs
            .iter()
            .flat_map(|x| self.graph.held_by(world, *x))
            .filter(|h| dirty.binary_search(h).is_err())
            .collect();
        hs.sort_unstable();
        hs.dedup();
        if hs.is_empty() {
            return;
        }
        let mut memo: Vec<Option<Layout>> = layouts.iter().cloned().map(Some).collect();
        for &h in &hs {
            memo[h as usize] = None;
        }
        for &h in &hs {
            assert!(
                rtworld::class_row(world, out, h) == self.rt.classes[h as usize],
                "internal error: the class row of `{}` changed with a class it holds (#717)",
                world.class(h).name
            );
            layout::of(world, h, &mut memo);
            assert_eq!(
                format!("{:?}", memo[h as usize]),
                format!("{:?}", layouts.get(h as usize)),
                "internal error: the layout of `{}` changed with a class it holds (#717)",
                world.class(h).name
            );
        }
    }

    /// The rows of `dirty` (sorted), and their methods', built again; the
    /// assembled tables, the overridden set and the layouts after them.
    fn rebuild(
        &mut self,
        world: &World,
        out: &types::Output,
        dirty: &[ClassId],
        layouts: &mut Vec<Layout>,
    ) {
        if self.rt.methods.len() < world.methods.len() {
            self.table.resize(world.methods.len(), Vec::new());
        }
        for &c in dirty {
            self.rt.classes[c as usize] = rtworld::class_row(world, out, c);
            self.pairs[c as usize] = world
                .include_overrides_of(c)
                .into_iter()
                .map(|o| (o.class, o.overridden, o.by))
                .collect();
            self.class_pairs[c as usize] = class_pairs_of(world, c);
            self.record[c as usize] = rtworld::witness_record_of(world, c);
        }
        // The methods of the classes rebuilt (new ones among them): their
        // rows may list a method generated above or below them.
        for &c in dirty {
            for &m in &self.graph.owned[c as usize] {
                self.table[m as usize] = world.overrides(m);
                let row = rtworld::method_row(world, m, &self.table[m as usize]);
                if (m as usize) < self.rt.methods.len() {
                    self.rt.methods[m as usize] = row;
                } else {
                    debug_assert_eq!(m as usize, self.rt.methods.len());
                    self.rt.methods.push(row);
                }
            }
        }
        assert_eq!(
            self.rt.methods.len(),
            world.methods.len(),
            "internal error: a new method's owner was not rebuilt (#717)"
        );
        self.rt.include_overrides = self.pairs.iter().flatten().copied().collect();
        self.rt.witness_record = self.record.iter().flatten().copied().collect();
        // The rows over them (they read the tables just assembled).
        for &c in dirty {
            let (rows, witnesses) = self.rt.witness_rows_of(c);
            self.override_rows[c as usize] = sorted(rows);
            self.witness_rows[c as usize] = sorted(witnesses);
        }
        for &c in dirty {
            self.class_rows[c as usize] = rtworld::class_override_rows_of(
                world,
                &self.rt,
                &self.table,
                &self.graph.type_side_owners,
                c,
            );
        }
        self.rt.override_rows = self.override_rows.iter().flatten().copied().collect();
        self.rt.witness_rows = self.witness_rows.iter().flatten().copied().collect();
        self.rt.class_override_rows = self.class_rows.iter().flatten().copied().collect();
        let class_pairs: Vec<(ClassId, MethodId, MethodId)> =
            self.class_pairs.iter().flatten().copied().collect();
        self.overridden =
            world.overridden_methods_over(&self.table, &self.rt.include_overrides, &class_pairs);
        // The layouts of the classes rebuilt, the others' read where one
        // holds a `data` type by value.
        let mut memo: Vec<Option<Layout>> = std::mem::take(layouts).into_iter().map(Some).collect();
        for &c in dirty {
            memo[c as usize] = None;
        }
        for &c in dirty {
            layout::of(world, c, &mut memo);
        }
        *layouts = memo.into_iter().map(|l| l.unwrap_or_default()).collect();
    }
}

impl Graph {
    fn build(world: &World, rt: &RtWorld) -> Graph {
        let n = world.classes.len();
        let mut below: Vec<Vec<ClassId>> = (0..n as ClassId).map(|c| vec![c]).collect();
        let direct: Vec<Vec<ClassId>> = (0..n as ClassId)
            .map(|c| ancestor_views(world, c))
            .collect();
        let views = transitive(&direct);
        for c in 0..n as ClassId {
            for &a in &views[c as usize] {
                if a != c && !below[a as usize].contains(&c) {
                    below[a as usize].push(c);
                }
            }
        }
        let mut holders: HashMap<ClassId, Vec<ClassId>> = HashMap::default();
        for c in &world.classes {
            for f in &c.fields {
                for k in classes_named(&f.ty) {
                    let hs = holders.entry(k).or_default();
                    if !hs.contains(&c.id) {
                        hs.push(c.id);
                    }
                }
            }
        }
        let mut owned: Vec<Vec<MethodId>> = vec![Vec::new(); n];
        for m in &world.methods {
            owned[m.owner as usize].push(m.id);
        }
        let mut type_side_owners = rt.type_side_owners();
        type_side_owners.sort_unstable();
        Graph {
            below,
            holders,
            type_side_owners,
            owned,
            #[cfg(debug_assertions)]
            heads: heads(world),
        }
    }

    /// D(x).
    fn below(&self, x: ClassId) -> impl Iterator<Item = ClassId> + '_ {
        self.below[x as usize].iter().copied()
    }

    /// H(x): the holders of `x` with their D, and the holders of those
    /// that are `data` types, enums or variants, transitively.
    fn held_by(&self, world: &World, x: ClassId) -> Vec<ClassId> {
        let mut out: Vec<ClassId> = Vec::new();
        let mut todo: Vec<ClassId> = vec![x];
        let mut seen: Vec<ClassId> = vec![x];
        while let Some(y) = todo.pop() {
            for &h in self.holders.get(&y).into_iter().flatten() {
                for d in self.below(h) {
                    if !out.contains(&d) {
                        out.push(d);
                    }
                }
                if is_data(world, h) && !seen.contains(&h) {
                    seen.push(h);
                    todo.push(h);
                }
            }
        }
        out
    }

    /// Class `x`'s last field, just generated: it holds what its type
    /// names.
    fn add_holder(&mut self, world: &World, x: ClassId) {
        if let Some(f) = world.class(x).fields.last() {
            for k in classes_named(&f.ty) {
                let hs = self.holders.entry(k).or_default();
                if !hs.contains(&x) {
                    hs.push(x);
                }
            }
        }
    }

    /// #717's P1: no class's superclass or includes changed since the
    /// graph was made.
    #[cfg(debug_assertions)]
    fn assert_heads(&self, world: &World) {
        assert!(
            heads(world) == self.heads,
            "internal error: a class's superclass or includes changed during a static phase (#717)"
        );
    }
}

#[cfg(debug_assertions)]
fn heads(world: &World) -> Vec<(Option<Type>, Vec<Type>)> {
    world
        .classes
        .iter()
        .map(|c| (c.superclass.clone(), c.includes.clone()))
        .collect()
}

/// Class `c`'s ancestors in every view a kept row reads, sorted: what
/// D is the inversion of (#717). The run-time ancestors (`RtClass::
/// ancestors`), the override view (`World::own_ancestors`: the override
/// table, the include pairs, the safety net's frames), the lookup and
/// dispatch orders (`RtClass::lookup`, `class_side`, the witness record)
/// and the static view (`World::ancestors`, the reflection).
fn ancestor_views(world: &World, c: ClassId) -> Vec<ClassId> {
    let mut out: Vec<ClassId> = world
        .runtime_ancestors(c)
        .into_iter()
        .chain(world.own_ancestors(c))
        .chain(world.ancestors(c, &[]))
        .map(|(k, _)| k)
        .chain(world.lookup_ancestors(c))
        .chain(world.class_dispatch_order(c))
        .collect();
    out.sort_unstable();
    out.dedup();
    out
}

/// Each class's ancestors in `direct`, with their ancestors', and so on:
/// the transitive closure (the ancestry has no cycle), sorted.
fn transitive(direct: &[Vec<ClassId>]) -> Vec<Vec<ClassId>> {
    let n = direct.len();
    let mut done: Vec<Option<Vec<ClassId>>> = vec![None; n];
    // (A class on the way: not entered again, should the declarer ever
    // let a cycle through.)
    let mut on_way: Vec<bool> = vec![false; n];
    for start in 0..n {
        // (Depth first, each class's closure after its ancestors'.)
        let mut stack: Vec<(usize, bool)> = vec![(start, false)];
        while let Some((c, expanded)) = stack.pop() {
            if done[c].is_some() {
                continue;
            }
            if !expanded {
                if on_way[c] {
                    continue;
                }
                on_way[c] = true;
                stack.push((c, true));
                for &a in &direct[c] {
                    if a as usize != c && done[a as usize].is_none() && !on_way[a as usize] {
                        stack.push((a as usize, false));
                    }
                }
                continue;
            }
            let mut all: Vec<ClassId> = direct[c].clone();
            for &a in &direct[c] {
                if a as usize != c {
                    if let Some(more) = &done[a as usize] {
                        all.extend(more.iter().copied());
                    }
                }
            }
            all.sort_unstable();
            all.dedup();
            on_way[c] = false;
            done[c] = Some(all);
        }
    }
    done.into_iter().map(|v| v.unwrap_or_default()).collect()
}

fn is_data(world: &World, c: ClassId) -> bool {
    matches!(
        world.class(c).kind,
        ClassKind::Data | ClassKind::Enum | ClassKind::Variant
    )
}

/// Class `c`'s class-side include pairs, as `class_include_overrides`
/// lists them.
fn class_pairs_of(world: &World, c: ClassId) -> Vec<(ClassId, MethodId, MethodId)> {
    world
        .class_include_overrides_of(c)
        .into_iter()
        .map(|o| (o.class, o.overridden, o.by))
        .collect()
}

/// The classes a type names, anywhere in it.
fn classes_named(t: &Type) -> Vec<ClassId> {
    fn walk(t: &Type, out: &mut Vec<ClassId>) {
        match t {
            Type::Class(c, args) | Type::ClassObject(c, args) => {
                out.push(*c);
                for a in args {
                    walk(a, out);
                }
            }
            Type::TypeOf(t) => walk(t, out),
            Type::Union(ts) | Type::Tuple(ts) => ts.iter().for_each(|t| walk(t, out)),
            Type::Proc(r, ps, ret, _, kws) => {
                r.iter().for_each(|t| walk(t, out));
                ps.iter().for_each(|t| walk(t, out));
                kws.iter().for_each(|k| walk(&k.ty, out));
                walk(ret, out);
            }
            Type::Nothing | Type::Void | Type::Param(_) | Type::Var(_) => {}
        }
    }
    let mut out = Vec::new();
    walk(t, &mut out);
    out
}

/// `rows` (sorted by class) split by class.
fn group<R: Copy>(rows: &[R], n: usize, class: impl Fn(&R) -> usize) -> Vec<Vec<R>> {
    let mut out: Vec<Vec<R>> = vec![Vec::new(); n];
    let mut last = 0;
    for r in rows {
        let c = class(r);
        debug_assert!(c >= last, "internal error: rows not by class (#717)");
        last = c;
        out[c].push(*r);
    }
    out
}

fn sorted<R: Ord>(mut rows: Vec<R>) -> Vec<R> {
    rows.sort_unstable();
    rows.dedup();
    rows
}

/// Whether the oracle runs (`QUARZ_VERIFY_STATIC_TABLES`, set by
/// `.cargo/config.toml` for `cargo test` and `cargo run`): every sync's
/// tables compared with the tables built from nothing. Read at run time,
/// as `QUARZ_VERIFY=moves` is, so a release build runs it too when asked
/// (and through `cargo run --release`); an installed `quarz` or
/// `target/release/quarz` run directly does not.
pub(crate) fn verify_enabled() -> bool {
    use std::sync::OnceLock;
    static ON: OnceLock<bool> = OnceLock::new();
    *ON.get_or_init(|| {
        std::env::var("QUARZ_VERIFY_STATIC_TABLES").is_ok_and(|v| !v.is_empty() && v != "0")
    })
}

/// The oracle (#717): the kept tables against `rtworld::declared`, the
/// layouts against `layout::compute` and the overridden set against
/// `World::overridden_methods` over the override table. A difference is
/// an internal error: a row kept stale, which the invalidation missed.
pub(crate) fn verify(world: &World, out: &types::Output, k: &Kept, layouts: &[Layout]) {
    let (full, table) = rtworld::declared_with(world, out, rtworld::witness_record(world));
    let fail = |what: String| -> ! {
        panic!("internal error (QUARZ_VERIFY_STATIC_TABLES): the kept tables differ from the tables built from nothing: {what} (#717)")
    };
    if k.rt != full {
        for (i, (a, b)) in k.rt.classes.iter().zip(&full.classes).enumerate() {
            if a != b {
                fail(format!(
                    "the row of class `{}`: kept {a:?}, built {b:?}",
                    world.class(i as ClassId).name
                ));
            }
        }
        for (i, (a, b)) in k.rt.methods.iter().zip(&full.methods).enumerate() {
            if a != b {
                let m = world.method(i as MethodId);
                fail(format!(
                    "the row of method `{}` of `{}`: kept {a:?}, built {b:?}",
                    m.name,
                    world.class(m.owner).name
                ));
            }
        }
        let tables: [(&str, String, String); 6] = [
            (
                "include_overrides",
                format!("{:?}", k.rt.include_overrides),
                format!("{:?}", full.include_overrides),
            ),
            (
                "witness_record",
                format!("{:?}", k.rt.witness_record),
                format!("{:?}", full.witness_record),
            ),
            (
                "override_rows",
                format!("{:?}", k.rt.override_rows),
                format!("{:?}", full.override_rows),
            ),
            (
                "witness_rows",
                format!("{:?}", k.rt.witness_rows),
                format!("{:?}", full.witness_rows),
            ),
            (
                "class_override_rows",
                format!("{:?}", k.rt.class_override_rows),
                format!("{:?}", full.class_override_rows),
            ),
            (
                "sizes",
                format!("{} {}", k.rt.classes.len(), k.rt.methods.len()),
                format!("{} {}", full.classes.len(), full.methods.len()),
            ),
        ];
        for (name, a, b) in tables {
            if a != b {
                fail(format!("`{name}`: kept {a}, built {b}"));
            }
        }
        fail("another table (extensions, top-level names, built-ins, file mains)".to_string());
    }
    if k.table != table {
        fail("the override table".to_string());
    }
    let built = layout::compute(world);
    for (i, (a, b)) in layouts.iter().zip(&built).enumerate() {
        if format!("{a:?}") != format!("{b:?}") {
            fail(format!(
                "the layout of `{}`: kept {a:?}, built {b:?}",
                world.class(i as ClassId).name
            ));
        }
    }
    if layouts.len() != built.len() {
        fail("the number of layouts".to_string());
    }
    if k.overridden != world.overridden_methods(&table) {
        fail("the overridden set".to_string());
    }
    VERIFIED.with(|n| n.set(n.get() + 1));
}

thread_local! {
    /// Syncs the oracle compared, for the statistics.
    static VERIFIED: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

/// One line per sync on the file `QUARZ_STATIC_TABLES_STATS` names: what
/// the sync rebuilt and which edges of the table its events took (#717's
/// coverage report).
pub(crate) fn record_stats(s: &SyncStats) {
    let Some(path) = std::env::var_os("QUARZ_STATIC_TABLES_STATS") else {
        return;
    };
    use std::io::Write;
    let line = format!(
        "sync full={} classes={} methods={} events={} data_eq={} rechecked={} conformance={} fields={} news={} inits={} verified={}\n",
        s.full as u8,
        s.classes,
        s.methods,
        s.events,
        s.data_eq as u8,
        s.rechecked as u8,
        s.conformance as u8,
        s.fields as u8,
        s.news as u8,
        s.inits as u8,
        verify_enabled() as u8,
    );
    if let Ok(mut f) = std::fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(path)
    {
        let _ = f.write_all(line.as_bytes());
    }
}
