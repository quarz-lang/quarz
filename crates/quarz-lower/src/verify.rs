//! A checker of the QIR the passes leave (docs/05 §3): after each pass of
//! `lower_checked`, the invariants of the instructions and of the values
//! flowing through registers that later passes and both back ends rely
//! on. A violation is a bug in the pass that just ran: lowering stops
//! there, with the function and the place, rather than let a back end
//! run code whose meaning is lost.
//!
//! On by default in a debug build, off in a release one; `QUARZ_VERIFY_IR`
//! (`0` or `1`) overrides either.

use std::sync::OnceLock;

use quarz_ir::{
    BlockId, CallKind, FuncKind, Function, HandlerKind, Inst, Reg, RtWorld, Term, INLINE_LINE_FLAG,
};

use crate::sroa::{successors, written};

/// The pass after which the functions are checked: what holds grows with
/// the passes run (moves exist only after `mark_moves`, borrows after
/// `mark_borrows`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Stage {
    Lowered,
    Cha,
    Devirt,
    Inline,
    Sroa,
    Copyprop,
    Release,
    Borrow,
    Regshare,
    Moves,
}

impl Stage {
    fn name(self) -> &'static str {
        match self {
            Stage::Lowered => "lowering",
            Stage::Cha => "cha",
            Stage::Devirt => "devirt",
            Stage::Inline => "inline",
            Stage::Sroa => "sroa",
            Stage::Copyprop => "copyprop",
            Stage::Release => "release",
            Stage::Borrow => "borrow",
            Stage::Regshare => "regshare",
            Stage::Moves => "mark_moves",
        }
    }
}

/// An invariant a function breaks: where (`inst` is `None` for the
/// block's terminator or the block itself) and what.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Violation {
    pub block: BlockId,
    pub inst: Option<usize>,
    pub line: u32,
    pub what: String,
}

/// Whether the checks run (`QUARZ_VERIFY_IR`, read once).
pub fn enabled() -> bool {
    static ON: OnceLock<bool> = OnceLock::new();
    *ON.get_or_init(|| match std::env::var("QUARZ_VERIFY_IR").as_deref() {
        Ok("0") => false,
        Ok(_) => true,
        Err(_) => cfg!(debug_assertions),
    })
}

/// Check every function after `stage`; panic at the first one breaking
/// an invariant, with the function's QIR.
pub fn check(functions: &[Function], world: &RtWorld, stage: Stage) {
    if !enabled() {
        return;
    }
    for (id, f) in functions.iter().enumerate() {
        let found = verify(f, world, functions.len(), stage);
        if let Some(v) = found.first() {
            let mut dump = String::new();
            quarz_ir::dump::dump_function(&mut dump, id as u32, f);
            let at = match v.inst {
                Some(i) => format!("block {} inst {i}", v.block),
                None => format!("block {}", v.block),
            };
            panic!(
                "QIR verifier: {} after {}: {at} (line {}): {}\n{dump}",
                f.name,
                stage.name(),
                v.line,
                v.what
            );
        }
    }
}

/// The invariants `f` breaks after `stage` (`nfuncs` functions in all).
pub fn verify(f: &Function, world: &RtWorld, nfuncs: usize, stage: Stage) -> Vec<Violation> {
    let mut v = Checker {
        f,
        world,
        out: Vec::new(),
    };
    v.structure(nfuncs, stage);
    // The value flow is checked on sound structure only.
    if v.out.is_empty() {
        v.words();
        v.resumes();
        if stage >= Stage::Release {
            v.moves(stage);
        }
        if stage >= Stage::Moves {
            v.read_once();
        }
    }
    v.out
}

struct Checker<'a> {
    f: &'a Function,
    world: &'a RtWorld,
    out: Vec<Violation>,
}

impl Checker<'_> {
    fn report(&mut self, block: usize, inst: Option<usize>, what: String) {
        let b = &self.f.blocks[block];
        let line = match inst {
            Some(i) => b.lines.get(i).copied().unwrap_or(0),
            None => b.term_line,
        };
        let line = match line & INLINE_LINE_FLAG {
            0 => line,
            _ => self
                .f
                .inlined
                .get((line & !INLINE_LINE_FLAG) as usize)
                .map_or(0, |o| o.call_line & !INLINE_LINE_FLAG),
        };
        self.out.push(Violation {
            block: block as BlockId,
            inst,
            line,
            what,
        });
    }

    /// A (structure): targets, registers, lines and indices in range,
    /// handler-only instructions in their handlers, the marks of later
    /// passes absent before them (F: `nregs` covers every register).
    fn structure(&mut self, nfuncs: usize, stage: Stage) {
        let f = self.f;
        let nblocks = f.blocks.len();
        let nregs = f.nregs;
        // The kind of handler each block is the entry of.
        let mut handler_of: Vec<Option<HandlerKind>> = vec![None; nblocks];
        for (bi, b) in f.blocks.iter().enumerate() {
            if let Some(h) = b.handler {
                if h.block as usize >= nblocks {
                    self.report(bi, None, format!("handler block {} out of range", h.block));
                    continue;
                }
                if h.block as usize == bi {
                    self.report(bi, None, "the block is its own handler".into());
                }
                handler_of[h.block as usize] = Some(h.kind);
            }
        }
        for (bi, b) in f.blocks.iter().enumerate() {
            if b.lines.len() != b.insts.len() {
                self.report(
                    bi,
                    None,
                    format!("{} lines for {} instructions", b.lines.len(), b.insts.len()),
                );
            }
            for (ii, inst) in b.insts.iter().enumerate() {
                if let Some(&l) = b.lines.get(ii) {
                    if l & INLINE_LINE_FLAG != 0
                        && (l & !INLINE_LINE_FLAG) as usize >= f.inlined.len()
                    {
                        self.report(
                            bi,
                            Some(ii),
                            format!("inlined line {} out of range", l & !INLINE_LINE_FLAG),
                        );
                    }
                }
                for r in inst.defs().into_iter().chain(inst.uses()) {
                    if r >= nregs {
                        self.report(bi, Some(ii), format!("r{r} past the {nregs} registers"));
                    }
                }
                if let Inst::ClearRegs { from, to } = inst {
                    if from > to || *to > nregs {
                        self.report(
                            bi,
                            Some(ii),
                            format!("ClearRegs {from}..{to} of {nregs} registers"),
                        );
                    }
                }
                self.indices(bi, ii, inst, nfuncs);
                match inst {
                    Inst::CatchException { .. } if handler_of[bi] != Some(HandlerKind::Rescue) => {
                        self.report(
                            bi,
                            Some(ii),
                            "CatchException outside a rescue handler".into(),
                        )
                    }
                    Inst::CatchAny { .. } if handler_of[bi] != Some(HandlerKind::Ensure) => {
                        self.report(bi, Some(ii), "CatchAny outside an ensure handler".into())
                    }
                    Inst::Take { .. } if stage < Stage::Moves => {
                        self.report(bi, Some(ii), "Take before mark_moves".into())
                    }
                    Inst::Call { moved, .. } if *moved != 0 && stage < Stage::Moves => {
                        self.report(bi, Some(ii), "moved operands before mark_moves".into())
                    }
                    Inst::OwnedCall { unused: true, .. } if stage < Stage::Moves => {
                        self.report(bi, Some(ii), "an unused OwnedCall before mark_moves".into())
                    }
                    Inst::ArrayGetReg { borrow: true, .. } if stage < Stage::Borrow => self.report(
                        bi,
                        Some(ii),
                        "a borrowed element before mark_borrows".into(),
                    ),
                    _ => {}
                }
            }
            match &b.term {
                Term::Jump(t) if *t as usize >= nblocks => {
                    self.report(bi, None, format!("jump to block {t} out of range"))
                }
                Term::Branch { then, els, .. }
                    if *then as usize >= nblocks || *els as usize >= nblocks =>
                {
                    self.report(
                        bi,
                        None,
                        format!("branch to block {then}/{els} out of range"),
                    )
                }
                _ => {}
            }
            if let Some(r) = b.term.uses() {
                if r >= nregs {
                    self.report(bi, None, format!("r{r} past the {nregs} registers"));
                }
            }
        }
    }

    /// The indices an instruction holds into the function's and the
    /// program's tables.
    fn indices(&mut self, bi: usize, ii: usize, inst: &Inst, nfuncs: usize) {
        let f = self.f;
        let w = self.world;
        let nmethods = w.methods.len() as u32;
        let nclasses = w.classes.len() as u32;
        let mut bad: Vec<String> = Vec::new();
        let method = |m: u32, bad: &mut Vec<String>| {
            if m >= nmethods {
                bad.push(format!("method {m} out of range"));
            }
        };
        let class = |c: u32, bad: &mut Vec<String>| {
            if c >= nclasses {
                bad.push(format!("class {c} out of range"));
            }
        };
        match inst {
            Inst::LoadConst { idx, .. } if *idx as usize >= f.consts.len() => {
                bad.push(format!("constant {idx} out of range"))
            }
            // (A function without a frame of its own uses its creator's.)
            Inst::FrameGet { depth: 0, slot, .. } | Inst::FrameSet { depth: 0, slot, .. }
                if f.frame_size > 0 && *slot >= f.frame_size =>
            {
                bad.push(format!("frame slot {slot} of {}", f.frame_size))
            }
            Inst::FieldGet {
                class: c, index, ..
            }
            | Inst::FieldSet {
                class: c, index, ..
            } if *c != u32::MAX => {
                if *c >= nclasses {
                    bad.push(format!("class {c} out of range"));
                } else if *index as usize >= w.classes[*c as usize].fields.len() {
                    bad.push(format!(
                        "field {index} of {}'s {}",
                        w.classes[*c as usize].name,
                        w.classes[*c as usize].fields.len()
                    ));
                }
            }
            Inst::Call { kind, .. } => match kind {
                CallKind::Method(m) | CallKind::Super(m) => method(*m, &mut bad),
                CallKind::Construct { class: c, init }
                | CallKind::ConstructRecv { class: c, init } => {
                    class(*c, &mut bad);
                    if let Some(m) = init {
                        method(*m, &mut bad);
                    }
                }
                _ => {}
            },
            Inst::OwnedCall { method: m, .. } => method(*m, &mut bad),
            Inst::BinOp {
                method: Some(m), ..
            } => method(*m, &mut bad),
            Inst::ClassRef { class: c, .. }
            | Inst::ClassIsA { class: c, .. }
            | Inst::ClassIs { class: c, .. }
            | Inst::VariantSingleton { class: c, .. } => class(*c, &mut bad),
            Inst::MakeBlock { func, .. } if *func as usize >= nfuncs => {
                bad.push(format!("function {func} out of range"))
            }
            Inst::ConstGet { id, .. } if *id as usize >= w.consts.len() => {
                bad.push(format!("constant {id} out of the program's"))
            }
            Inst::Arg { index, .. } | Inst::HasArg { index, .. } => {
                let n = match f.kind {
                    FuncKind::Method(m) => w.methods.get(m as usize).map(|m| m.params.len()),
                    FuncKind::Block => Some(f.param_kinds.len()),
                    _ => None,
                };
                if let Some(n) = n {
                    if *index as usize >= n {
                        bad.push(format!("parameter {index} of {n}"));
                    }
                }
            }
            _ => {}
        }
        for what in bad {
            self.report(bi, Some(ii), what);
        }
    }

    /// B (value flow): what a word read or append works on was made for
    /// it, and no borrowed element is updated in place.
    fn words(&mut self) {
        let f = self.f;
        let insts = || f.blocks.iter().flat_map(|b| &b.insts);
        let words =
            insts().any(|i| matches!(i, Inst::ArrayGetWord { .. } | Inst::ArrayPushWord { .. }));
        // (Only a function borrowing elements can update one.)
        let borrows = insts().any(|i| matches!(i, Inst::ArrayGetReg { borrow: true, .. }));
        if !words && !borrows {
            return;
        }
        let defs = Defs::new(f);
        for (bi, b) in f.blocks.iter().enumerate() {
            for (ii, inst) in b.insts.iter().enumerate() {
                match inst {
                    Inst::ArrayGetWord { arr, float, .. } => {
                        let ok =
                            |i: &Inst| matches!(i, Inst::ArrayWords { float: g, .. } if g == float);
                        if let Some(what) = self.made_by(&defs, bi, ii, *arr, &ok, true) {
                            self.report(bi, Some(ii), format!("ArrayGetWord reads r{arr}, {what}"));
                        }
                    }
                    Inst::ArrayPushWord { arr, float, .. } => {
                        let ok = |i: &Inst| matches!(i, Inst::ArrayNewWords { float: g, .. } if g == float);
                        // (Its own array: no copy refers to it.)
                        if let Some(what) = self.made_by(&defs, bi, ii, *arr, &ok, false) {
                            self.report(bi, Some(ii), format!("ArrayPushWord on r{arr}, {what}"));
                        }
                    }
                    _ => {}
                }
                let updated = match inst {
                    _ if !borrows => None,
                    Inst::ArrayPush { arr, .. } => Some(*arr),
                    Inst::OwnedCall {
                        recv: quarz_ir::VarLoc::Reg(r),
                        ..
                    } => Some(*r),
                    _ => None,
                };
                if let Some(r) = updated {
                    for (sb, si) in defs.at(bi, ii, r).into_iter().flatten() {
                        if matches!(
                            f.blocks[sb].insts[si],
                            Inst::ArrayGetReg { borrow: true, .. }
                        ) {
                            self.report(
                                bi,
                                Some(ii),
                                format!("updates r{r}, a borrowed element (block {sb} inst {si})"),
                            );
                        }
                    }
                }
            }
        }
    }

    /// `None` when every definition of `r` reaching instruction `ii` of
    /// block `bi` is one `ok` accepts, or a copy (`Move`/`Take`) of such
    /// a register; else what reaches instead.
    fn made_by(
        &self,
        defs: &Defs,
        bi: usize,
        ii: usize,
        r: Reg,
        ok: &dyn Fn(&Inst) -> bool,
        copies: bool,
    ) -> Option<String> {
        let f = self.f;
        let mut seen: Vec<((usize, usize), Reg)> = Vec::new();
        let mut todo: Vec<(usize, usize, Reg)> = vec![(bi, ii, r)];
        while let Some((b, i, r)) = todo.pop() {
            for site in defs.at(b, i, r) {
                let Some(site) = site else {
                    return Some(format!("nil on entry (r{r} not written on some path)"));
                };
                if seen.contains(&(site, r)) {
                    continue;
                }
                seen.push((site, r));
                let inst = &f.blocks[site.0].insts[site.1];
                match inst {
                    i if ok(i) => {}
                    Inst::Move { src, .. } | Inst::Take { src, .. } if copies => {
                        todo.push((site.0, site.1, *src))
                    }
                    // An append changes the array in place (a write for
                    // the definitions): what it appended to.
                    Inst::ArrayPushWord { arr, .. } if *arr == r => {
                        todo.push((site.0, site.1, *arr))
                    }
                    other => {
                        return Some(format!(
                            "made by {} at block {} inst {}",
                            inst_name(other),
                            site.0,
                            site.1
                        ))
                    }
                }
            }
        }
        None
    }

    /// A5: what a `Resume` continues was caught by a `CatchAny`.
    fn resumes(&mut self) {
        let f = self.f;
        if !f.blocks.iter().any(|b| matches!(b.term, Term::Resume(_))) {
            return;
        }
        let defs = Defs::new(f);
        for (bi, b) in f.blocks.iter().enumerate() {
            if let Term::Resume(r) = b.term {
                let caught = defs.at(bi, b.insts.len(), r).iter().all(|site| {
                    site.is_some_and(|(sb, si)| {
                        matches!(f.blocks[sb].insts[si], Inst::CatchAny { .. })
                    })
                });
                if !caught {
                    self.report(
                        bi,
                        None,
                        format!("Resume of r{r}, not what a CatchAny caught"),
                    );
                }
            }
        }
    }
}

impl Checker<'_> {
    /// C9: no register is read after its value moved out of it (`Take`,
    /// a moved operand, once `mark_moves` ran) or its scope ended
    /// (`Release`) before something wrote it again: a forward dataflow
    /// of each register's "moved" state, joined by "moved on some path",
    /// handlers entered from every point of the blocks they cover.
    fn moves(&mut self, stage: Stage) {
        let f = self.f;
        let n = f.nregs as usize;
        let nblocks = f.blocks.len();
        let moves = stage >= Stage::Moves;
        let releases = f.blocks.iter().flat_map(|b| &b.insts).any(|i| {
            matches!(i, Inst::Release { .. })
                || (moves && matches!(i, Inst::Take { .. } | Inst::Call { moved: 1.., .. }))
        });
        if !releases {
            return;
        }
        // What an instruction leaves moved, after its writes.
        // What an instruction moves out of its operands (done before it
        // writes its results: a call's result may go to an operand it
        // moved, and is there when it raises).
        let moved_out = |inst: &Inst, state: &mut [bool]| match inst {
            Inst::Take { src, .. } if moves => state[*src as usize] = true,
            Inst::Call {
                recv, args, moved, ..
            } if moves && *moved != 0 => {
                for (i, a) in args.iter().enumerate().take(15) {
                    if moved & (1 << i) != 0 {
                        state[*a as usize] = true;
                    }
                }
                if let Some(r) = recv.filter(|_| moved & (1 << 15) != 0) {
                    state[r as usize] = true;
                }
            }
            _ => {}
        };
        let transfer = |inst: &Inst, state: &mut [bool]| {
            moved_out(inst, state);
            for r in inst.defs() {
                state[r as usize] = false;
            }
            if let Inst::Release { src } = inst {
                state[*src as usize] = true;
            }
        };
        let mut entry: Vec<Vec<bool>> = vec![vec![false; n]; nblocks];
        let mut done = vec![false; nblocks];
        let mut todo: Vec<usize> = vec![0];
        let or_into = |to: &mut Vec<bool>, from: &[bool]| -> bool {
            let mut changed = false;
            for (t, v) in to.iter_mut().zip(from) {
                if *v && !*t {
                    *t = true;
                    changed = true;
                }
            }
            changed
        };
        // To a fixed point: each block's entry state, from its
        // predecessors' exits and, for a handler, every point of what it
        // covers.
        while let Some(b) = todo.pop() {
            let blk = &f.blocks[b];
            let mut state = entry[b].clone();
            // What a handler of the block may see: the state where
            // something raises (before an instruction that may, or at a
            // terminator that leaves with a flow).
            let mut any = vec![false; n];
            for inst in &blk.insts {
                if may_raise(f, inst) {
                    // What it moved out is gone when it raises; what it
                    // writes is not written.
                    let mut raised = state.clone();
                    moved_out(inst, &mut raised);
                    or_into(&mut any, &raised);
                }
                transfer(inst, &mut state);
            }
            // A terminator leaving with a flow: an exception reaches any
            // handler, `break`/`return` out of a block only an ensure one.
            let ensure = blk.handler.is_some_and(|h| h.kind == HandlerKind::Ensure);
            match blk.term {
                Term::Raise(_) | Term::Resume(_) => or_into(&mut any, &state),
                Term::BreakOut(_) | Term::ReturnOut(_) if ensure => or_into(&mut any, &state),
                _ => false,
            };
            let mut targets: Vec<(usize, &[bool])> = Vec::new();
            for s in crate::sroa::successors(blk) {
                if blk.handler.is_some_and(|h| h.block == s) {
                    targets.push((s as usize, &any));
                } else {
                    targets.push((s as usize, &state));
                }
            }
            for (s, st) in targets {
                if or_into(&mut entry[s], st) || !done[s] {
                    done[s] = true;
                    todo.push(s);
                }
            }
        }
        // The reads, against the fixed point.
        for (bi, blk) in f.blocks.iter().enumerate() {
            if !done[bi] && bi != 0 {
                continue;
            }
            let mut state = entry[bi].clone();
            for (ii, inst) in blk.insts.iter().enumerate() {
                for r in inst.uses() {
                    if state[r as usize] {
                        self.report(bi, Some(ii), format!("reads r{r}, {}", self.why_moved()));
                    }
                }
                transfer(inst, &mut state);
            }
            if let Some(r) = blk.term.uses() {
                if state[r as usize] {
                    self.report(bi, None, format!("reads r{r}, {}", self.why_moved()));
                }
            }
        }
    }

    fn why_moved(&self) -> &'static str {
        "moved out or released before (on some path)"
    }

    /// C10, C11: a `Take` moves to another register; an operand moved
    /// into a call is read by it once and is not a borrowed element; the
    /// result of an `OwnedCall` marked unused is not read.
    fn read_once(&mut self) {
        let f = self.f;
        let borrowed = quarz_ir::live::borrowed_regs(f);
        let mut live: Option<Vec<Vec<Vec<bool>>>> = None;
        for (bi, blk) in f.blocks.iter().enumerate() {
            for (ii, inst) in blk.insts.iter().enumerate() {
                match inst {
                    Inst::Take { dst, src } if dst == src => {
                        self.report(bi, Some(ii), format!("Take of r{src} into itself"))
                    }
                    Inst::Call {
                        recv,
                        args,
                        kw,
                        kw_splat,
                        block,
                        moved,
                        ..
                    } if *moved != 0 => {
                        let mut operands: Vec<Reg> = recv.iter().copied().collect();
                        operands.extend(args.iter().copied());
                        operands.extend(kw.iter().map(|(_, r)| *r));
                        operands.extend(kw_splat.iter().copied());
                        operands.extend(block.iter().copied());
                        let mut moved_regs: Vec<Reg> = args
                            .iter()
                            .enumerate()
                            .take(15)
                            .filter(|(i, _)| moved & (1 << i) != 0)
                            .map(|(_, r)| *r)
                            .collect();
                        moved_regs.extend(recv.filter(|_| moved & (1 << 15) != 0));
                        for r in moved_regs {
                            let n = operands.iter().filter(|o| **o == r).count();
                            if n != 1 {
                                self.report(
                                    bi,
                                    Some(ii),
                                    format!("moves r{r}, which it reads {n} times"),
                                );
                            }
                            if borrowed[r as usize] {
                                self.report(
                                    bi,
                                    Some(ii),
                                    format!("moves r{r}, a borrowed element"),
                                );
                            }
                        }
                    }
                    Inst::OwnedCall {
                        dst, unused: true, ..
                    } => {
                        let live = live.get_or_insert_with(|| quarz_ir::live::liveness(f));
                        if live[bi][ii + 1][*dst as usize] {
                            self.report(
                                bi,
                                Some(ii),
                                format!("an unused OwnedCall's r{dst} is read"),
                            );
                        }
                    }
                    _ => {}
                }
            }
        }
    }
}

/// Reaching definitions, one register at a time, with handler edges: a
/// handler is entered from any point of the blocks it covers, so what
/// enters it is what any of them held anywhere (unlike `sroa`'s, which
/// gives up there).
struct Defs<'a> {
    f: &'a Function,
    /// The blocks jumping or branching to each block.
    preds: Vec<Vec<usize>>,
    /// The blocks each handler block covers.
    covered: Vec<Vec<usize>>,
}

impl<'a> Defs<'a> {
    fn new(f: &'a Function) -> Defs<'a> {
        let n = f.blocks.len();
        let mut preds = vec![Vec::new(); n];
        let mut covered = vec![Vec::new(); n];
        for (bi, b) in f.blocks.iter().enumerate() {
            for s in successors(b) {
                if b.handler.is_some_and(|h| h.block == s) {
                    covered[s as usize].push(bi);
                } else {
                    preds[s as usize].push(bi);
                }
            }
        }
        Defs { f, preds, covered }
    }

    /// The writes of `r` reaching instruction `ii` of block `bi` (`ii`
    /// the instruction count: the terminator), `None` for the nil it
    /// holds on entry to the function along some path.
    fn at(&self, bi: usize, ii: usize, r: Reg) -> Vec<Option<(usize, usize)>> {
        let mut out = Vec::new();
        let mut entered = vec![false; self.f.blocks.len()];
        let mut todo: Vec<(usize, usize)> = vec![(bi, ii)];
        while let Some((b, end)) = todo.pop() {
            let insts = &self.f.blocks[b].insts;
            if let Some(k) = (0..end.min(insts.len()))
                .rev()
                .find(|&k| written(&insts[k]).contains(&r))
            {
                out.push(Some((b, k)));
                continue;
            }
            // What enters `b`.
            if entered[b] {
                continue;
            }
            entered[b] = true;
            if b == 0 {
                out.push(None);
            }
            for &p in &self.preds[b] {
                todo.push((p, self.f.blocks[p].insts.len()));
            }
            // A handler: any write in a block it covers, or what entered it.
            for &p in &self.covered[b] {
                for (k, inst) in self.f.blocks[p].insts.iter().enumerate() {
                    if written(inst).contains(&r) {
                        out.push(Some((p, k)));
                    }
                }
                todo.push((p, 0));
            }
        }
        out.sort_unstable();
        out.dedup();
        out
    }
}

/// Whether running `inst` may end in a flow a handler catches: anything
/// but the moves of values between registers and the like.
fn may_raise(f: &Function, inst: &Inst) -> bool {
    if let Inst::LoadConst { idx, .. } = inst {
        // Only a regexp is compiled (and may fail) when loaded.
        return matches!(
            f.consts.get(*idx as usize),
            Some(quarz_ir::Constant::Regexp { .. })
        );
    }
    !matches!(
        inst,
        Inst::Move { .. }
            | Inst::Take { .. }
            | Inst::Release { .. }
            | Inst::ClearRegs { .. }
            | Inst::SelfRef { .. }
            | Inst::Arg { .. }
            | Inst::HasArg { .. }
            | Inst::BlockParam { .. }
            | Inst::IsNil { .. }
            | Inst::Not { .. }
            | Inst::ClassRef { .. }
            | Inst::ClassIs { .. }
            | Inst::ClassIsA { .. }
            | Inst::IsA { .. }
            | Inst::IsArray { .. }
            | Inst::IsHash { .. }
            | Inst::IsObject { .. }
            | Inst::Len { .. }
            | Inst::MakeBlock { .. }
            | Inst::SymbolProc { .. }
            | Inst::CatchAny { .. }
            | Inst::Rescuing { .. }
    )
}

/// The instruction's kind, for messages.
fn inst_name(inst: &Inst) -> String {
    let s = format!("{inst:?}");
    s.split([' ', '{', '(']).next().unwrap_or("").to_string()
}
