//! Scalar replacement of data objects that do not escape: a `data`
//! value built in a function and only ever read field by field (after
//! inlining, `Vec2.new(x * k, y * k)` consumed by `+`) is never
//! allocated; each field read becomes a move from the register that
//! held the constructor argument.
//!
//! Registers are mutable, so the pass works on reaching definitions: a
//! use of a register is attributed to the construction only when that
//! construction is the one definition reaching it, and the argument
//! registers must still hold their values there.

use std::cell::RefCell;

use rustc_hash::{FxHashMap as HashMap, FxHashSet as HashSet};

use quarz_ir::*;

/// Replace what can be replaced in every function.
pub fn scalar_replace(functions: &mut [Function], methods: &[RtMethod], classes: &[RtClass]) {
    for f in functions.iter_mut() {
        replace_in(f, methods, classes);
    }
}

/// A definition site: instruction `inst` of block `block`.
pub(crate) type Site = (usize, usize);

/// The sites that may have written a register last, in order (a few at
/// most).
pub(crate) type Sites = Vec<Site>;

/// Reaching definitions, found on demand: from a read, the walk goes
/// back through the predecessors to the writes of the register on each
/// path. A table of every register at every block's entry would grow as
/// blocks times registers, which a long method makes quadratic in time
/// and memory; a read is mostly near its writes.
pub(crate) struct Reaching {
    preds: Vec<Vec<usize>>,
    /// Blocks entered from an exception: nothing definite is known there.
    handlers: HashSet<usize>,
    /// Each register's writes (`written`), in order.
    writes: Vec<Vec<Site>>,
    /// Where each register is read: by instructions, in order (once per
    /// operand), and by terminators (their blocks).
    pub(crate) uses: Vec<Vec<Site>>,
    pub(crate) term_uses: Vec<Vec<usize>>,
    /// Whether a read of a register may see anything (`UNKNOWN`).
    unknown: RefCell<HashMap<Reg, bool>>,
    /// The definitions entering a block, by block and register.
    entry: RefCell<HashMap<(usize, Reg), Sites>>,
}

impl Reaching {
    /// The writes of `r` in block `bi` before instruction `ii`.
    fn writes_before(&self, r: Reg, bi: usize, ii: usize) -> &[Site] {
        let w = &self.writes[r as usize];
        let lo = w.partition_point(|s| s.0 < bi);
        let hi = w.partition_point(|s| *s < (bi, ii));
        &w[lo..hi]
    }

    /// Whether one of `regs` is written in block `bi` between
    /// instructions `from` and `to` (both excluded).
    fn written_between(&self, regs: &[Reg], bi: usize, from: usize, to: usize) -> bool {
        regs.iter().any(|r| {
            self.writes_before(*r, bi, to)
                .last()
                .is_some_and(|s| s.1 > from)
        })
    }

    /// Whether one of `regs` is written in block `bi` before instruction
    /// `to`.
    fn written_before(&self, regs: &[Reg], bi: usize, to: usize) -> bool {
        regs.iter()
            .any(|r| !self.writes_before(*r, bi, to).is_empty())
    }

    /// The reads of `r` that its write at `site` may reach (`defs_at`
    /// there includes `site`): instructions in order and terminators,
    /// found walking forward from `site` up to the next writes. A read
    /// at a write is before it. A handler's entry is `UNKNOWN`: the walk
    /// stops there.
    pub(crate) fn reads_of(&self, f: &Function, site: Site, r: Reg) -> (Vec<Site>, Vec<usize>) {
        let writes = &self.writes[r as usize];
        let uses = &self.uses[r as usize];
        let mut reads = Vec::new();
        let mut terms = Vec::new();
        let mut seen: HashSet<usize> = HashSet::default();
        // Breadth first: the reads are mostly near, and once all are found
        // the walk stops.
        let mut queue = std::collections::VecDeque::from([(site.0, site.1 + 1)]);
        while let Some((b, from)) = queue.pop_front() {
            let next = writes
                .get(writes.partition_point(|w| *w < (b, from)))
                .filter(|w| w.0 == b)
                .map(|w| w.1);
            let lo = uses.partition_point(|u| *u < (b, from));
            let hi = uses.partition_point(|u| *u <= (b, next.unwrap_or(usize::MAX)));
            reads.extend_from_slice(&uses[lo..hi]);
            if next.is_some() {
                continue;
            }
            if self.term_uses[r as usize].binary_search(&b).is_ok() {
                terms.push(b);
            }
            // Every read found: the rest of the function reads it no more
            // (a temporary written once).
            if reads.len() + terms.len() == uses.len() + self.term_uses[r as usize].len() {
                break;
            }
            for s in successors(&f.blocks[b]) {
                let s = s as usize;
                if !self.handlers.contains(&s) && seen.insert(s) {
                    queue.push_back((s, 0));
                }
            }
        }
        reads.sort_unstable();
        terms.sort_unstable();
        (reads, terms)
    }

    /// Whether some read of `r` may see anything (`UNKNOWN`: in a
    /// handler, or after one).
    pub(crate) fn read_unknown(&self, f: &Function, r: Reg) -> bool {
        if self.handlers.is_empty() {
            return false;
        }
        if let Some(unknown) = self.unknown.borrow().get(&r) {
            return *unknown;
        }
        let unknown = self.uses[r as usize]
            .iter()
            .any(|&(bi, ii)| defs_at(self, bi, ii, r).contains(&UNKNOWN))
            || self.term_uses[r as usize]
                .iter()
                .any(|&bi| defs_at(self, bi, f.blocks[bi].insts.len(), r).contains(&UNKNOWN));
        self.unknown.borrow_mut().insert(r, unknown);
        unknown
    }

    /// The definitions of `r` entering block `b` (not a handler).
    fn entering(&self, b: usize, r: Reg) -> Sites {
        if let Some(sites) = self.entry.borrow().get(&(b, r)) {
            return sites.clone();
        }
        let mut sites = Sites::new();
        let mut seen: HashSet<usize> = one(b);
        let mut stack = vec![b];
        while let Some(x) = stack.pop() {
            for &p in &self.preds[x] {
                // What leaves `p`: its last write, anything from a handler,
                // or what enters it.
                if let Some(site) = self.writes_before(r, p, usize::MAX).last() {
                    sites.push(*site);
                } else if self.handlers.contains(&p) {
                    sites.push(UNKNOWN);
                } else if seen.insert(p) {
                    // Known already: what enters it is all its paths give.
                    match self.entry.borrow().get(&(p, r)) {
                        Some(known) => sites.extend_from_slice(known),
                        None => stack.push(p),
                    }
                }
            }
        }
        sites.sort_unstable();
        sites.dedup();
        self.entry.borrow_mut().insert((b, r), sites.clone());
        sites
    }
}

/// The set of one element.
pub(crate) fn one<T: std::hash::Hash + Eq>(x: T) -> HashSet<T> {
    let mut s = HashSet::default();
    s.insert(x);
    s
}

pub(crate) fn successors(b: &Block) -> Vec<BlockId> {
    let mut v = match &b.term {
        Term::Jump(t) => vec![*t],
        Term::Branch { then, els, .. } => vec![*then, *els],
        _ => vec![],
    };
    if let Some(h) = b.handler {
        v.push(h.block);
    }
    v
}

/// The "any definition" marker: a handler block may be entered from the
/// middle of its region, so nothing definite is known there.
pub(crate) const UNKNOWN: Site = (usize::MAX, usize::MAX);

/// What an instruction writes, for the reaching definitions: its
/// defined registers, and the array an `ArrayPush` or `ArrayPushWord`
/// appends to (changed in place, so a copy taken before no longer equals
/// it).
pub(crate) fn written(inst: &Inst) -> Vec<Reg> {
    let mut v = inst.defs();
    if let Inst::ArrayPush { arr, .. } | Inst::ArrayPushWord { arr, .. } = inst {
        v.push(*arr);
    }
    v
}

pub(crate) fn reaching(f: &Function) -> Reaching {
    let mut preds: Vec<Vec<usize>> = vec![Vec::new(); f.blocks.len()];
    let mut writes: Vec<Vec<Site>> = vec![Vec::new(); f.nregs as usize];
    let mut uses: Vec<Vec<Site>> = vec![Vec::new(); f.nregs as usize];
    let mut term_uses: Vec<Vec<usize>> = vec![Vec::new(); f.nregs as usize];
    for (bi, blk) in f.blocks.iter().enumerate() {
        for s in successors(blk) {
            preds[s as usize].push(bi);
        }
        if let Some(r) = blk.term.uses() {
            term_uses[r as usize].push(bi);
        }
        for (ii, inst) in blk.insts.iter().enumerate() {
            for r in inst.uses() {
                uses[r as usize].push((bi, ii));
            }
            for r in written(inst) {
                let w = &mut writes[r as usize];
                if w.last() != Some(&(bi, ii)) {
                    w.push((bi, ii));
                }
            }
        }
    }
    let handlers = f
        .blocks
        .iter()
        .filter_map(|b| b.handler.map(|h| h.block as usize))
        .collect();
    Reaching {
        preds,
        handlers,
        writes,
        uses,
        term_uses,
        unknown: RefCell::default(),
        entry: RefCell::default(),
    }
}

/// Where what `site` made (a copy, `dst <- src`; an object built from
/// argument registers) still holds: on every path from `site`, none of
/// `regs` was written again, and no path from the function's entry or a
/// handler gets there without passing `site`. Reaching definitions
/// cannot tell this across a loop: a use reached by `site` in the
/// previous pass, while one of `regs` was written again by the same
/// instruction in this one, has the same definitions as at `site`, but
/// not the same values. Found on demand, as the reaching definitions
/// are, by blocks.
pub(crate) struct Holds<'r> {
    reach: &'r Reaching,
    site: Site,
    regs: Vec<Reg>,
    entry: HashMap<usize, bool>,
}

impl<'r> Holds<'r> {
    pub(crate) fn new(reach: &'r Reaching, site: Site, regs: &[Reg]) -> Holds<'r> {
        Holds {
            reach,
            site,
            regs: regs.to_vec(),
            entry: HashMap::default(),
        }
    }

    /// Whether it still holds before instruction `ii` of block `bi`
    /// (`ii` the instruction count: before the terminator).
    pub(crate) fn at(&mut self, bi: usize, ii: usize) -> bool {
        let (sb, si) = self.site;
        if sb == bi && si < ii {
            return !self.reach.written_between(&self.regs, bi, si, ii);
        }
        !self.reach.written_before(&self.regs, bi, ii) && self.on_entry(bi)
    }

    /// Whether it holds on entry to block `b`: walking back, every path
    /// meets a block that makes it (`site`, nothing of `regs` written
    /// after it there) before one that ends it (writes one of `regs`) or
    /// the entry of the function, a handler or a block nothing enters.
    /// A loop that does neither adds no path.
    fn on_entry(&mut self, b: usize) -> bool {
        if let Some(holds) = self.entry.get(&b) {
            return *holds;
        }
        let reach = self.reach;
        let (sb, si) = self.site;
        let mut holds = true;
        let mut seen: HashSet<usize> = one(b);
        let mut stack = vec![b];
        'walk: while let Some(x) = stack.pop() {
            if x == 0 || reach.handlers.contains(&x) || reach.preds[x].is_empty() {
                holds = false;
                break;
            }
            for &p in &reach.preds[x] {
                let makes = p == sb && !reach.written_between(&self.regs, p, si, usize::MAX);
                if makes {
                    continue;
                }
                let ends = if p == sb {
                    true
                } else {
                    reach.written_before(&self.regs, p, usize::MAX)
                };
                if ends {
                    holds = false;
                    break 'walk;
                }
                if seen.insert(p) {
                    stack.push(p);
                }
            }
        }
        self.entry.insert(b, holds);
        holds
    }
}

/// The definitions of `r` reaching instruction `ii` of block `bi`
/// (none = never written on this path, i.e. still nil).
pub(crate) fn defs_at(reach: &Reaching, bi: usize, ii: usize, r: Reg) -> Sites {
    // The last write before `ii` in the block, else what enters it.
    if let Some(site) = reach.writes_before(r, bi, ii).last() {
        return vec![*site];
    }
    if reach.handlers.contains(&bi) {
        vec![UNKNOWN]
    } else {
        reach.entering(bi, r)
    }
}

fn replace_in(f: &mut Function, methods: &[RtMethod], classes: &[RtClass]) {
    // Candidate constructions.
    let mut sites: Vec<(Site, ClassId, Vec<Reg>, Reg)> = Vec::new();
    for (bi, blk) in f.blocks.iter().enumerate() {
        for (ii, inst) in blk.insts.iter().enumerate() {
            if let Inst::Call {
                dst,
                kind:
                    CallKind::Construct {
                        class,
                        init: Some(init),
                    },
                args,
                splat: false,
                kw,
                kw_splat: None,
                block: None,
                ..
            } = inst
            {
                let Some(m) = methods.get(*init as usize) else {
                    continue;
                };
                let Some(c) = classes.get(*class as usize) else {
                    continue;
                };
                if kw.is_empty()
                    && m.synth == RtSynth::DataInit
                    && matches!(c.kind, RtClassKind::Data | RtClassKind::Variant)
                    && args.len() == c.fields.len()
                    && blk.handler.is_none()
                {
                    sites.push(((bi, ii), *class, args.clone(), *dst));
                }
            }
        }
    }
    if sites.is_empty() {
        return;
    }
    let reach = reaching(f);
    let mut delete: HashSet<Site> = HashSet::default();
    let mut rewrite: HashMap<Site, Inst> = HashMap::default();
    for (site, class, args, dst) in sites {
        let arg_defs: Vec<Sites> = args
            .iter()
            .map(|a| defs_at(&reach, site.0, site.1, *a))
            .collect();
        // Aliases of the object: the register each definition writes.
        let mut aliases: Vec<(Reg, Site)> = vec![(dst, site)];
        let mut holds: Vec<Holds> = args
            .iter()
            .map(|a| Holds::new(&reach, site, &[*a]))
            .collect();
        let mut seen: HashSet<Site> = one(site);
        let mut to_delete: Vec<Site> = vec![site];
        let mut to_rewrite: Vec<(Site, Inst)> = Vec::new();
        let mut ok = true;
        let mut k = 0;
        while ok && k < aliases.len() {
            let (q, def) = aliases[k];
            k += 1;
            // A use in a handler (entered from anywhere in its region:
            // `UNKNOWN`) may see the object; so does a terminator.
            let (reads, terms) = reach.reads_of(f, def, q);
            if !terms.is_empty() || reach.read_unknown(f, q) {
                ok = false;
                break;
            }
            for (ubi, uii) in reads {
                let here = defs_at(&reach, ubi, uii, q);
                if here.len() != 1 {
                    ok = false;
                    break;
                }
                match &f.blocks[ubi].insts[uii] {
                    Inst::Move { dst: m, src } if *src == q => {
                        if seen.insert((ubi, uii)) {
                            aliases.push((*m, (ubi, uii)));
                            to_delete.push((ubi, uii));
                        }
                    }
                    Inst::FieldGet {
                        dst: d,
                        obj,
                        index,
                        class: c,
                    } if *obj == q && *c == class && (*index as usize) < args.len() => {
                        let a = args[*index as usize];
                        // The argument still holds what the object was
                        // built from: same definitions, and not written
                        // since on any path (a pass of a loop may write
                        // it and leave before building again).
                        if defs_at(&reach, ubi, uii, a) != arg_defs[*index as usize]
                            || !holds[*index as usize].at(ubi, uii)
                        {
                            ok = false;
                            break;
                        }
                        to_rewrite.push(((ubi, uii), Inst::Move { dst: *d, src: a }));
                    }
                    _ => {
                        ok = false;
                        break;
                    }
                }
            }
        }
        if ok {
            delete.extend(to_delete);
            rewrite.extend(to_rewrite);
        }
    }
    if delete.is_empty() {
        return;
    }
    for (bi, blk) in f.blocks.iter_mut().enumerate() {
        let insts = std::mem::take(&mut blk.insts);
        let lines = std::mem::take(&mut blk.lines);
        for (ii, (inst, line)) in insts.into_iter().zip(lines).enumerate() {
            if delete.contains(&(bi, ii)) {
                continue;
            }
            let inst = rewrite.remove(&(bi, ii)).unwrap_or(inst);
            blk.insts.push(inst);
            blk.lines.push(line);
        }
    }
}
