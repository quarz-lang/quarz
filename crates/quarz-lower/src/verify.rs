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

use rustc_hash::{FxHashMap as HashMap, FxHashSet as HashSet};

use quarz_ir::{
    BlockId, CallKind, FuncId, FuncKind, Function, HandlerKind, Inst, Reg, RtWorld, Term,
    INLINE_LINE_FLAG,
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
    check_from(functions, 0, world, stage);
}

/// `check` for functions numbered from `base` (a REPL round's, after
/// the functions of the rounds before it).
pub fn check_from(functions: &[Function], base: FuncId, world: &RtWorld, stage: Stage) {
    if !enabled() {
        return;
    }
    let nfuncs = base as usize + functions.len();
    for (i, f) in functions.iter().enumerate() {
        let id = base as usize + i;
        let found = verify(f, world, nfuncs, stage);
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
        early: Vec::new(),
    };
    v.structure(nfuncs, stage);
    // The value flow is checked on sound structure only (marks of a later
    // pass found early do not make it unsound).
    if v.out.is_empty() {
        v.words();
        v.resumes();
        if stage >= Stage::Release {
            v.moves(stage);
        }
        if stage >= Stage::Moves {
            v.read_once();
        }
        // (Not after mark_moves for now: `own_dying_receivers` may then
        // update the array in place at a borrowed element's last read.)
        if (Stage::Borrow..Stage::Moves).contains(&stage) {
            v.borrows();
        }
    }
    let mut out = v.early;
    out.append(&mut v.out);
    out
}

struct Checker<'a> {
    f: &'a Function,
    world: &'a RtWorld,
    out: Vec<Violation>,
    /// The marks of a later pass found before it (A6).
    early: Vec<Violation>,
}

impl Checker<'_> {
    fn report_early(&mut self, block: usize, inst: usize, what: String) {
        self.report(block, Some(inst), what);
        let v = self.out.pop().expect("the violation");
        self.early.push(v);
    }

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
                        self.report_early(bi, ii, "Take before mark_moves".into())
                    }
                    Inst::Call { moved, .. } if *moved != 0 && stage < Stage::Moves => {
                        self.report_early(bi, ii, "moved operands before mark_moves".into())
                    }
                    Inst::OwnedCall { unused: true, .. } if stage < Stage::Moves => {
                        self.report_early(bi, ii, "an unused OwnedCall before mark_moves".into())
                    }
                    Inst::ArrayGetReg { borrow: true, .. } if stage < Stage::Borrow => {
                        self.report_early(bi, ii, "a borrowed element before mark_borrows".into())
                    }
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
            | Inst::VariantSingleton { class: c, .. }
            | Inst::UnitSelf { class: c, .. } => class(*c, &mut bad),
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
            // handler, `break`/`return` out of a block only an ensure one
            // (past the rescues, which the ensure covers: through them,
            // as an approximation).
            let ensure = quarz_ir::flow_handler(&f.blocks, blk).is_some();
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

impl Checker<'_> {
    /// D13: a borrowed element register (`ArrayGetReg` with `borrow`)
    /// still meets what `borrow::mark_in` required of it: written only by
    /// borrowed reads of one array, `Release` and `ClearRegs`; never moved
    /// out, returned, raised or updated in place; the array live and
    /// unchanged wherever it is; no handler in the function.
    fn borrows(&mut self) {
        let f = self.f;
        let mut arrays: Vec<Option<Reg>> = vec![None; f.nregs as usize];
        let mut any = false;
        for blk in &f.blocks {
            for inst in &blk.insts {
                if let Inst::ArrayGetReg {
                    dst,
                    arr,
                    borrow: true,
                    ..
                } = inst
                {
                    arrays[*dst as usize] = Some(*arr);
                    any = true;
                }
            }
        }
        if !any {
            return;
        }
        if let Some(bi) = f.blocks.iter().position(|b| b.handler.is_some()) {
            self.report(
                bi,
                None,
                "a borrowed element in a function with handlers".into(),
            );
            return;
        }
        for (bi, blk) in f.blocks.iter().enumerate() {
            for (ii, inst) in blk.insts.iter().enumerate() {
                let written: Vec<Reg> = match inst {
                    Inst::ArrayGetReg {
                        dst,
                        arr,
                        borrow: true,
                        ..
                    } => {
                        if arrays[*dst as usize] != Some(*arr) {
                            self.report(
                                bi,
                                Some(ii),
                                format!("r{dst} borrows elements of two arrays"),
                            );
                        }
                        Vec::new()
                    }
                    Inst::Release { .. } | Inst::ClearRegs { .. } => Vec::new(),
                    _ => inst.defs().to_vec(),
                };
                for r in written {
                    if arrays[r as usize].is_some() {
                        self.report(
                            bi,
                            Some(ii),
                            format!("writes r{r}, a borrowed element's register"),
                        );
                    }
                }
                let consumed: Vec<Reg> = match inst {
                    Inst::Take { src, .. } => vec![*src],
                    Inst::ArrayPush { arr, .. } => vec![*arr],
                    Inst::OwnedCall {
                        recv: quarz_ir::VarLoc::Reg(r),
                        ..
                    } => vec![*r],
                    Inst::Call {
                        recv, args, moved, ..
                    } => {
                        let mut v: Vec<Reg> = args
                            .iter()
                            .enumerate()
                            .take(15)
                            .filter(|(i, _)| moved & (1 << i) != 0)
                            .map(|(_, r)| *r)
                            .collect();
                        v.extend(recv.filter(|_| moved & (1 << 15) != 0));
                        v
                    }
                    _ => Vec::new(),
                };
                for r in consumed {
                    if arrays[r as usize].is_some() {
                        self.report(
                            bi,
                            Some(ii),
                            format!("moves or updates r{r}, a borrowed element"),
                        );
                    }
                }
            }
            if let Term::Return(r)
            | Term::Raise(r)
            | Term::BreakOut(r)
            | Term::ReturnOut(r)
            | Term::Resume(r) = blk.term
            {
                if arrays[r as usize].is_some() {
                    self.report(
                        bi,
                        None,
                        format!("r{r}, a borrowed element, leaves the function"),
                    );
                }
            }
        }
        // The array holds the element wherever the element is live.
        let live = quarz_ir::live::liveness(f);
        for (bi, blk) in f.blocks.iter().enumerate() {
            for (ii, here) in live[bi].iter().enumerate() {
                let inst = blk.insts.get(ii);
                for (e, a) in arrays.iter().enumerate() {
                    let Some(a) = *a else { continue };
                    if !here[e] {
                        continue;
                    }
                    let changes = inst.is_some_and(|i| {
                        i.defs().contains(&a)
                            || matches!(i, Inst::ArrayPush { arr, .. } if *arr == a)
                            || matches!(i, Inst::OwnedCall { recv: quarz_ir::VarLoc::Reg(r), .. } if *r == a)
                    });
                    if !here[a as usize] || changes {
                        let inst = (ii < blk.insts.len()).then_some(ii);
                        self.report(
                            bi,
                            inst,
                            format!("r{e} borrows from r{a}, which does not hold it here"),
                        );
                        return;
                    }
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
            | Inst::MarkUsable { .. }
    )
}

/// The instruction's kind, for messages.
fn inst_name(inst: &Inst) -> String {
    let s = format!("{inst:?}");
    s.split([' ', '{', '(']).next().unwrap_or("").to_string()
}

/// E14: check what register sharing did to each function it renumbered
/// (`maps`, from `regshare::share_registers`, against the functions
/// `before` it); panic as `check` does.
pub fn check_regshare(
    before: &[Function],
    after: &[Function],
    maps: &[Option<Vec<Reg>>],
    world: &RtWorld,
) {
    for (id, ((old, new), map)) in before.iter().zip(after).zip(maps).enumerate() {
        let Some(map) = map else { continue };
        let found = regshare(old, new, map, world);
        if let Some(v) = found.first() {
            let mut dump = String::new();
            quarz_ir::dump::dump_function(&mut dump, id as u32, old);
            panic!(
                "QIR verifier: {} after regshare: block {} (line {}): {}\nbefore it:\n{dump}",
                old.name, v.block, v.line, v.what
            );
        }
    }
}

/// What register sharing must keep, `old` renumbered by `map` into
/// `new`: counted and non-counted registers apart, and a borrowed
/// element's register to itself; a result apart from its operands; and
/// every register a `ClearRegs` cleared that is read after it or may
/// hold a counted value still cleared.
pub fn regshare(old: &Function, new: &Function, map: &[Reg], world: &RtWorld) -> Vec<Violation> {
    let mut out = Vec::new();
    let mut report = |block: usize, what: String| {
        out.push(Violation {
            block: block as BlockId,
            inst: None,
            line: 0,
            what,
        })
    };
    let heap = quarz_ir::live::heap_possible(old, &world.methods);
    let borrowed = quarz_ir::live::borrowed_regs(old);
    // The registers `old` mentions, by new number.
    let mut mentioned = vec![false; old.nregs as usize];
    for b in &old.blocks {
        for i in &b.insts {
            for r in i.uses().into_iter().chain(i.defs()) {
                mentioned[r as usize] = true;
            }
        }
        if let Some(r) = b.term.uses() {
            mentioned[r as usize] = true;
        }
    }
    let mut kinds: Vec<Option<(bool, Option<Reg>)>> = vec![None; new.nregs as usize];
    for r in 0..old.nregs {
        if !mentioned[r as usize] {
            continue;
        }
        let n = map[r as usize] as usize;
        let kind = (heap[r as usize], borrowed[r as usize].then_some(r));
        match kinds[n] {
            None => kinds[n] = Some(kind),
            Some((h, _)) if h != kind.0 => report(
                0,
                format!("r{n} holds a counted and a non-counted register (r{r})"),
            ),
            Some((_, b)) if b.is_some() || kind.1.is_some() => report(
                0,
                format!("r{n} holds a borrowed element's register and another (r{r})"),
            ),
            _ => {}
        }
    }
    let live = quarz_ir::live::liveness(old);
    let m = |r: Reg| map[r as usize];
    for (bi, (ob, nb)) in old.blocks.iter().zip(&new.blocks).enumerate() {
        let mut j = 0;
        let mut i = 0;
        while i < ob.insts.len() {
            let inst = &ob.insts[i];
            if let Inst::ClearRegs { .. } = inst {
                // A run of clears renumbered into a run of clears.
                // (Moves between them that sharing dropped do not end it.)
                let start = i;
                while i < ob.insts.len()
                    && match ob.insts[i] {
                        Inst::ClearRegs { .. } => true,
                        Inst::Move { dst, src } | Inst::Take { dst, src } => m(dst) == m(src),
                        _ => false,
                    }
                {
                    i += 1;
                }
                let mut cleared: Vec<Reg> = Vec::new();
                while j < nb.insts.len() {
                    let Inst::ClearRegs { from, to } = nb.insts[j] else {
                        break;
                    };
                    cleared.extend(from..to);
                    j += 1;
                }
                // Nor more: a number cleared is not one an old register
                // live after the run has, unless the run cleared it.
                let old_cleared: Vec<Reg> = ob.insts[start..i]
                    .iter()
                    .flat_map(|inst| match inst {
                        Inst::ClearRegs { from, to } => *from..*to,
                        _ => 0..0,
                    })
                    .collect();
                for r in 0..old.nregs {
                    if live[bi][i][r as usize]
                        && cleared.contains(&m(r))
                        && !old_cleared.contains(&r)
                    {
                        report(bi, format!("clears r{} (r{r}), live after it", m(r)));
                    }
                }
                for k in start..i {
                    let Inst::ClearRegs { from, to } = ob.insts[k] else {
                        continue;
                    };
                    for r in from..to {
                        let kept = live[bi][k + 1][r as usize] || heap[r as usize];
                        if kept && !cleared.contains(&m(r)) {
                            report(bi, format!("no longer clears r{r} (now r{})", m(r)));
                        }
                    }
                }
                continue;
            }
            i += 1;
            if let Inst::Move { dst, src } | Inst::Take { dst, src } = inst {
                if m(*dst) == m(*src) {
                    continue;
                }
            }
            let renumbered = crate::inline::rewrite_with(inst, &m, &|c| c);
            if nb.insts.get(j) != Some(&renumbered) {
                report(
                    bi,
                    format!("instruction {} is not renumbered as it was", i - 1),
                );
                return out;
            }
            j += 1;
            if !matches!(inst, Inst::Move { .. } | Inst::Take { .. }) {
                let uses = inst.uses();
                let defs = inst.defs();
                for (k, a) in defs.iter().enumerate() {
                    for b in &defs[k + 1..] {
                        if a != b && m(*a) == m(*b) {
                            report(
                                bi,
                                format!("instruction {}'s results r{a} and r{b} share", i - 1),
                            );
                        }
                    }
                }
                for d in defs {
                    for u in &uses {
                        if d != *u && m(d) == m(*u) {
                            report(
                                bi,
                                format!(
                                    "instruction {}'s result r{d} shares with its operand r{u}",
                                    i - 1
                                ),
                            );
                        }
                    }
                }
            }
        }
        if j != nb.insts.len() {
            report(bi, "instructions added".into());
        }
        let mut term = ob.term.clone();
        term.map_uses(&mut |r| m(r));
        if nb.term != term || nb.handler != ob.handler {
            report(
                bi,
                "the terminator or handler is not renumbered as it was".into(),
            );
        }
    }
    if old.blocks.len() != new.blocks.len() {
        report(0, "blocks added or removed".into());
    }
    // (d) Interference. The pairs a dropped move joins hold one value
    // where both are live (exempted everywhere); any other two registers
    // live at one point hold different numbers, and a register written
    // takes no number another live after the write has. A handler's live
    // set counts throughout its block. Live in an unreachable block (the
    // code after a `rescue` ending in `return`, say) is not live, nor are
    // two registers no path to a point has written (both nil): sharing
    // only separates a register written from those live after the write.
    let joined = |a: Reg, b: Reg, at: &Inst| {
        matches!(at, Inst::Move { dst, src } | Inst::Take { dst, src }
            if (*dst, *src) == (a, b) || (*dst, *src) == (b, a))
    };
    let mut dropped: HashSet<(Reg, Reg)> = HashSet::default();
    for b in &old.blocks {
        for inst in &b.insts {
            if let Inst::Move { dst, src } | Inst::Take { dst, src } = inst {
                if dst != src && m(*dst) == m(*src) {
                    dropped.insert((*dst.min(src), *dst.max(src)));
                }
            }
        }
    }
    let written = maybe_written(old);
    let mut reachable = vec![false; old.blocks.len()];
    let mut work = vec![0usize];
    while let Some(b) = work.pop() {
        if !std::mem::replace(&mut reachable[b], true) {
            work.extend(
                quarz_ir::live::successors(&old.blocks[b])
                    .into_iter()
                    .map(|s| s as usize),
            );
        }
    }
    for (bi, ob) in old.blocks.iter().enumerate() {
        let handler = ob
            .handler
            .filter(|_| !ob.insts.is_empty())
            .map(|h| &live[h.block as usize][0]);
        let at = |k: usize| -> Vec<Reg> {
            (0..old.nregs)
                .filter(|r| live[bi][k][*r as usize] || handler.is_some_and(|l| l[*r as usize]))
                .collect()
        };
        let unwritten = |k: usize, r: Reg| !written[bi][k][r as usize];
        for k in 0..=ob.insts.len() {
            let regs = if reachable[bi] { at(k) } else { Vec::new() };
            let mut by_number: HashMap<Reg, Vec<Reg>> = HashMap::default();
            for r in regs.iter().copied() {
                let sharing = by_number.entry(m(r)).or_default();
                for &q in sharing.iter() {
                    if !dropped.contains(&(q.min(r), q.max(r)))
                        && !(unwritten(k, q) && unwritten(k, r))
                    {
                        report(
                            bi,
                            format!(
                                "r{q} and r{r}, both live at instruction {k}, share r{}",
                                m(r)
                            ),
                        );
                    }
                }
                sharing.push(r);
            }
            let Some(inst) = ob.insts.get(k) else {
                continue;
            };
            let after = at(k + 1);
            let writes: Vec<Reg> = match inst {
                // A clear writes only what it keeps.
                Inst::ClearRegs { from, to } => (*from..*to)
                    .filter(|r| live[bi][k + 1][*r as usize] || heap[*r as usize])
                    .collect(),
                _ => inst.defs().to_vec(),
            };
            for d in writes {
                for &l in &after {
                    if l != d && m(l) == m(d) && !joined(d, l, inst) {
                        report(
                            bi,
                            format!(
                                "instruction {k} writes r{d} while r{l}, live after it, shares r{}",
                                m(d)
                            ),
                        );
                    }
                }
            }
        }
    }
    // What the back end reads of the new function agrees.
    let new_heap = quarz_ir::live::heap_possible(new, &world.methods);
    for (n, kind) in kinds.iter().enumerate() {
        if let Some((h, _)) = kind {
            if new_heap.get(n).copied().unwrap_or(false) != *h {
                report(
                    0,
                    format!("r{n}'s registers and the new function disagree on counting"),
                );
            }
        }
    }
    out
}

/// For each point (`result[b][i]`, as `live::liveness` numbers them), the
/// registers some path from the entry writes before it. A handler is
/// entered with what its region may have written.
fn maybe_written(f: &Function) -> Vec<Vec<Vec<bool>>> {
    let n = f.nregs as usize;
    let nblocks = f.blocks.len();
    let mut entry = vec![vec![false; n]; nblocks];
    let out_of = |bi: usize, entry: &[Vec<bool>]| {
        let mut w = entry[bi].clone();
        for inst in &f.blocks[bi].insts {
            for r in inst.defs() {
                w[r as usize] = true;
            }
        }
        w
    };
    let mut changed = true;
    while changed {
        changed = false;
        for bi in 0..nblocks {
            let out = out_of(bi, &entry);
            for s in quarz_ir::live::successors(&f.blocks[bi]) {
                for (e, o) in entry[s as usize].iter_mut().zip(&out) {
                    if *o && !*e {
                        *e = true;
                        changed = true;
                    }
                }
            }
        }
    }
    f.blocks
        .iter()
        .enumerate()
        .map(|(bi, b)| {
            let mut w = entry[bi].clone();
            let mut points = vec![w.clone()];
            for inst in &b.insts {
                for r in inst.defs() {
                    w[r as usize] = true;
                }
                points.push(w.clone());
            }
            points
        })
        .collect()
}

/// E15: check what copy propagation did to each function (against the
/// functions `before` it); panic as `check` does.
pub fn check_copyprop(before: &[Function], after: &[Function]) {
    for (id, (old, new)) in before.iter().zip(after).enumerate() {
        let found = copyprop(old, new);
        if let Some(v) = found.first() {
            let mut dump = String::new();
            quarz_ir::dump::dump_function(&mut dump, id as u32, old);
            panic!(
                "QIR verifier: {} after copyprop: block {} inst {} (line {}): {}\nbefore it:\n{dump}",
                old.name,
                v.block,
                v.inst.unwrap_or(0),
                v.line,
                v.what
            );
        }
    }
}

/// What copy propagation must keep of `old`'s releases in `new`: each
/// `Release` of a register `d` stays, goes with a copy into `d` it
/// removed (the source still holds the value), or releases the source
/// `s` of such a copy (a chain of them) when that copy was all that read
/// `s`. A release redirected to another variable would end a scope
/// whose release can be observed somewhere else.
pub fn copyprop(old: &Function, new: &Function) -> Vec<Violation> {
    let mut out = Vec::new();
    let mut report = |block: usize, inst: Option<usize>, what: String| {
        let line = inst
            .and_then(|i| old.blocks[block].lines.get(i).copied())
            .unwrap_or(0);
        out.push(Violation {
            block: block as BlockId,
            inst,
            line,
            what,
        })
    };
    if old.blocks.len() != new.blocks.len() {
        report(0, None, "blocks added or removed".into());
        return out;
    }
    let flexible = |i: &Inst| matches!(i, Inst::Move { .. } | Inst::Release { .. });
    // Align each block's instructions: copy propagation only removes
    // moves and releases, and changes what instructions read. Between
    // two other instructions, the new moves and releases are some of the
    // old ones, in order.
    let mut removed: HashMap<Reg, Vec<Reg>> = HashMap::default();
    let mut deleted: HashSet<(usize, usize)> = HashSet::default();
    // Each run's releases: (block, old indices, new sources).
    let mut runs: Vec<(usize, Vec<usize>, Vec<Reg>)> = Vec::new();
    for (bi, (ob, nb)) in old.blocks.iter().zip(&new.blocks).enumerate() {
        let (mut i, mut j) = (0, 0);
        while i < ob.insts.len() || j < nb.insts.len() {
            let (i0, j0) = (i, j);
            while i < ob.insts.len() && flexible(&ob.insts[i]) {
                i += 1;
            }
            while j < nb.insts.len() && flexible(&nb.insts[j]) {
                j += 1;
            }
            // Moves: each new one is the next old one into its register
            // (from the same source, if one is: the first may be a dead
            // copy removed).
            let mut k = i0;
            for n in &nb.insts[j0..j] {
                let Inst::Move { dst: d, src: ns } = n else {
                    continue;
                };
                let same = (k..i).find(
                    |k| matches!(ob.insts[*k], Inst::Move { dst, src } if dst == *d && src == *ns),
                );
                let target = same.or_else(|| {
                    (k..i).find(|k| matches!(ob.insts[*k], Inst::Move { dst, .. } if dst == *d))
                });
                while k < i && Some(k) != target {
                    if let Inst::Move { dst, src } = ob.insts[k] {
                        removed.entry(dst).or_default().push(src);
                        deleted.insert((bi, k));
                    }
                    k += 1;
                }
                if k == i {
                    report(bi, None, format!("a move into r{d} added"));
                    return out;
                }
                k += 1;
            }
            for k in k..i {
                if let Inst::Move { dst, src } = ob.insts[k] {
                    removed.entry(dst).or_default().push(src);
                    deleted.insert((bi, k));
                }
            }
            let old_rel: Vec<usize> = (i0..i)
                .filter(|k| matches!(ob.insts[*k], Inst::Release { .. }))
                .collect();
            let new_rel: Vec<Reg> = nb.insts[j0..j]
                .iter()
                .filter_map(|n| match n {
                    Inst::Release { src } => Some(*src),
                    _ => None,
                })
                .collect();
            runs.push((bi, old_rel, new_rel));
            match (ob.insts.get(i), nb.insts.get(j)) {
                (Some(o), Some(n)) if std::mem::discriminant(o) == std::mem::discriminant(n) => {
                    i += 1;
                    j += 1;
                }
                (None, None) => {}
                (Some(o), _) => {
                    report(bi, Some(i), format!("{} is not as it was", inst_name(o)));
                    return out;
                }
                (None, Some(_)) => {
                    report(bi, None, "instructions added".into());
                    return out;
                }
            }
        }
    }
    // Whether something besides the removed copies reads each register,
    // before the pass and after it. Releases do not count (the pass may
    // have removed or redirected them in an earlier round), and a read
    // counts only when it is there on both sides: a round sees reads that
    // an earlier one redirected away, or onto the source.
    let reads_in = |f: &Function, skip: &dyn Fn(usize, usize) -> bool| {
        let mut reads = vec![false; old.nregs as usize];
        for (bi, b) in f.blocks.iter().enumerate() {
            for (ii, i) in b.insts.iter().enumerate() {
                if !skip(bi, ii) && !matches!(i, Inst::Release { .. }) {
                    for r in i.uses() {
                        if let Some(x) = reads.get_mut(r as usize) {
                            *x = true;
                        }
                    }
                }
            }
            if let Some(x) = b.term.uses().and_then(|r| reads.get_mut(r as usize)) {
                *x = true;
            }
        }
        reads
    };
    let before = reads_in(old, &|bi, ii| deleted.contains(&(bi, ii)));
    let after = reads_in(new, &|_, _| false);
    let kept_reads: Vec<bool> = before.iter().zip(&after).map(|(a, b)| *a && *b).collect();
    // Whether `to` is the source of a chain of removed copies into `d`,
    // nothing else reading it. (Weaker than the pass's condition: a copy
    // of `to` it removed earlier, or a release of `to`, is not counted;
    // nor is it checked that the copy removed is the one reaching the
    // release.)
    let from_source = |d: Reg, to: Reg| -> bool {
        let mut work = vec![d];
        let mut seen: HashSet<Reg> = HashSet::default();
        while let Some(r) = work.pop() {
            if !seen.insert(r) {
                continue;
            }
            for &s in removed.get(&r).into_iter().flatten() {
                if s == to && !kept_reads[s as usize] {
                    return true;
                }
                work.push(s);
            }
        }
        false
    };
    for (bi, old_rel, new_rel) in runs {
        let src_of = |k: usize| match old.blocks[bi].insts[k] {
            Inst::Release { src } => src,
            _ => unreachable!(),
        };
        // Each new release is the next old one it may stand for (one of
        // the same register first); the old ones passed over were removed.
        let mut at = 0;
        let mut dropped: Vec<usize> = Vec::new();
        for s in new_rel {
            let found = old_rel[at..]
                .iter()
                .position(|k| src_of(*k) == s)
                .or_else(|| {
                    old_rel[at..]
                        .iter()
                        .position(|k| from_source(src_of(*k), s))
                });
            let Some(p) = found else {
                let first = old_rel.get(at).copied();
                let what = match first {
                    Some(k) => format!("releases r{s} instead of r{}", src_of(k)),
                    None => format!("a release of r{s} added"),
                };
                report(bi, first, what);
                return out;
            };
            dropped.extend(&old_rel[at..at + p]);
            at += p + 1;
        }
        dropped.extend(&old_rel[at..]);
        for k in dropped {
            let d = src_of(k);
            if !removed.contains_key(&d) {
                report(
                    bi,
                    Some(k),
                    format!("the release of r{d} is removed, with no copy into it"),
                );
            }
        }
    }
    out
}

/// `f` with each register `r` renumbered `map[r]` (as register sharing
/// does, but dropping no move): for tests of `regshare`.
pub fn renumber(f: &Function, map: &[Reg]) -> Function {
    let mut g = f.clone();
    // (A clear's end may be one past the last register.)
    let m = |r: Reg| map.get(r as usize).copied().unwrap_or(r);
    for b in &mut g.blocks {
        for inst in &mut b.insts {
            *inst = crate::inline::rewrite_with(inst, &m, &|c| c);
        }
        b.term.map_uses(&mut |r| m(r));
    }
    g
}
