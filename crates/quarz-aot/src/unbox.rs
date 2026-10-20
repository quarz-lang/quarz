//! Which registers hold an unboxed number at each point of a function.
//!
//! Every register has a boxed home in memory that is always up to date
//! (stores write through). On top of that, a register whose value is
//! statically known to be an `Int` that fits a machine word, a `Float`
//! or a `Bool` is also kept in an SSA variable, so arithmetic on it needs
//! no tag test, no overflow-into-BigInt handling beyond a check, and no
//! release of the old value. The knowledge comes from constants, from the
//! overload the lowering recorded for an operator (`Int#+(Int)` says both
//! operands are Ints: an operand whose state is unknown is checked once
//! at run time, and the function falls back to the interpreter if the
//! check fails), and from copies. A forward dataflow analysis over the
//! basic blocks gives the state at each block's entry; the generator then
//! tracks it instruction by instruction with the same transfer function.

use quarz_ir::*;

/// What is known about a register's current value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum State {
    /// Anything: only the boxed home is valid.
    Unknown,
    /// Nil, a boolean or a number: no release needed on overwrite.
    NonHeap,
    Bool,
    Int,
    Float,
}

impl State {
    pub fn meet(self, other: State) -> State {
        if self == other {
            self
        } else if self != State::Unknown && other != State::Unknown {
            State::NonHeap
        } else {
            State::Unknown
        }
    }

    pub fn needs_release(self) -> bool {
        self == State::Unknown
    }
}

/// The static types of a binary operation's operands and result.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Num {
    Int,
    Float,
}

#[derive(Clone, Copy, Debug)]
pub struct BinTypes {
    pub lhs: Num,
    pub rhs: Num,
    /// `None` for a comparison (the result is a Bool).
    pub result: Option<Num>,
}

/// The operand types of a `BinOp` whose overload is known to be one of
/// Int's or Float's arithmetic or comparison methods.
pub fn bin_types(inst: &Inst, methods: &[RtMethod], builtin: &RtBuiltin) -> Option<BinTypes> {
    let Inst::BinOp {
        op,
        method: Some(mid),
        ..
    } = inst
    else {
        return None;
    };
    let m = methods.get(*mid as usize)?;
    let lhs = if m.owner == builtin.int {
        Num::Int
    } else if m.owner == builtin.float {
        Num::Float
    } else {
        return None;
    };
    let rhs = match m.params.first().and_then(|p| p.ty.as_deref()) {
        Some("Int") => Num::Int,
        Some("Float") => Num::Float,
        _ => return None,
    };
    let result = match op {
        FastOp::Add | FastOp::Sub | FastOp::Mul | FastOp::Div | FastOp::Mod => {
            if lhs == Num::Int && rhs == Num::Int {
                Some(Num::Int)
            } else {
                Some(Num::Float)
            }
        }
        FastOp::Lt | FastOp::Le | FastOp::Gt | FastOp::Ge | FastOp::Eq | FastOp::Ne => None,
        _ => return None,
    };
    Some(BinTypes { lhs, rhs, result })
}

/// The registers an instruction may write.
pub fn defs(inst: &Inst) -> Vec<Reg> {
    inst.defs()
}

/// The registers an instruction reads.
pub fn uses(inst: &Inst) -> Vec<Reg> {
    inst.uses()
}

/// The register a terminator reads, if any.
pub fn term_uses(term: &Term) -> Option<Reg> {
    term.uses()
}

/// Instructions whose generated code reads no register's home except
/// through the states (so unboxed registers need no write-back first).
pub fn reads_no_home(inst: &Inst) -> bool {
    matches!(
        inst,
        Inst::LoadConst { .. }
            | Inst::Move { .. }
            | Inst::SelfRef { .. }
            | Inst::Arg { .. }
            | Inst::BlockParam { .. }
            | Inst::FrameGet { .. }
            | Inst::FieldGet { .. }
            | Inst::ClassRef { .. }
            | Inst::MakeBlock { .. }
            | Inst::Not { .. }
            | Inst::ClassIs { .. }
            | Inst::IsNil { .. }
            | Inst::CatchException { .. }
            | Inst::CatchAny { .. }
            | Inst::ClearRegs { .. }
    )
}

/// Of those, the ones that may still unwind to the block's handler
/// (which reads the homes).
pub fn may_unwind(inst: &Inst) -> bool {
    matches!(
        inst,
        Inst::BlockParam { .. }
            | Inst::FrameGet { .. }
            | Inst::FieldGet { .. }
            | Inst::MakeBlock { .. }
    )
}

fn successors(b: &Block) -> Vec<BlockId> {
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

/// Liveness: `result[b][i][r]` says whether register `r` may be read
/// before being written from instruction `i` of block `b` on (index
/// `insts.len()` stands for the terminator). A block's handler can be
/// entered from any of its instructions, so what the handler reads is
/// live throughout the block.
pub fn liveness(f: &Function) -> Vec<Vec<Vec<bool>>> {
    let nregs = f.nregs as usize;
    let nblocks = f.blocks.len();
    let mut live_in: Vec<Vec<bool>> = vec![vec![false; nregs]; nblocks];
    let uses_defs: Vec<Vec<(Vec<Reg>, Vec<Reg>)>> = f
        .blocks
        .iter()
        .map(|blk| blk.insts.iter().map(|i| (uses(i), defs(i))).collect())
        .collect();
    let or_into = |live: &mut [bool], other: &[bool]| {
        for (l, v) in live.iter_mut().zip(other) {
            *l |= *v;
        }
    };
    // The live set at the end of a block, then stepping backwards.
    let walk = |bi: usize, live_in: &[Vec<bool>], visit: &mut dyn FnMut(&[bool])| {
        let blk = &f.blocks[bi];
        let mut live = vec![false; nregs];
        for s in successors(blk) {
            or_into(&mut live, &live_in[s as usize]);
        }
        if let Some(r) = term_uses(&blk.term) {
            live[r as usize] = true;
        }
        let handler: Option<&Vec<bool>> = blk.handler.map(|h| &live_in[h.block as usize]);
        visit(&live);
        for (u, d) in uses_defs[bi].iter().rev() {
            for r in d {
                live[*r as usize] = false;
            }
            for r in u {
                live[*r as usize] = true;
            }
            if let Some(h) = handler {
                or_into(&mut live, h);
            }
            visit(&live);
        }
    };
    let mut changed = true;
    while changed {
        changed = false;
        for bi in (0..nblocks).rev() {
            let mut last = vec![false; nregs];
            walk(bi, &live_in, &mut |l| last.clone_from_slice(l));
            if last != live_in[bi] {
                live_in[bi] = last;
                changed = true;
            }
        }
    }
    (0..nblocks)
        .map(|bi| {
            let mut per_inst = Vec::with_capacity(f.blocks[bi].insts.len() + 1);
            walk(bi, &live_in, &mut |l| per_inst.push(l.to_vec()));
            per_inst.reverse();
            per_inst
        })
        .collect()
}

/// The shape of a function's typed entry: parameters and result passed
/// as machine values (see `Gen::typed`).
#[derive(Clone, Debug)]
pub struct TypedSig {
    pub params: Vec<Num>,
    pub ret: Num,
}

/// The functions that get a typed entry, by id: a method whose
/// positional, non-defaulted parameters (at most six) and result are
/// all declared `Int`/`Float`, with no block, no frame of its own and
/// nothing in the body that reads the argument list.
pub fn typed_sigs(functions: &[Function], methods: &[RtMethod]) -> Vec<Option<TypedSig>> {
    functions
        .iter()
        .enumerate()
        .map(|(fid, f)| {
            let FuncKind::Method(mid) = f.kind else {
                return None;
            };
            let m = methods.get(mid as usize)?;
            if m.func != Some(fid as FuncId)
                || m.has_block
                || m.is_abstract
                || m.native_key.is_some()
                || m.synth != RtSynth::None
                || m.params.len() > 6
                || f.frame_size != 0
            {
                return None;
            }
            let params: Vec<Num> = m
                .params
                .iter()
                .map(|p| {
                    if p.kind == RtParamKind::Positional && !p.has_default {
                        num_of(p.ty.as_deref())
                    } else {
                        None
                    }
                })
                .collect::<Option<_>>()?;
            let ret = num_of(m.ret.as_deref())?;
            let plain = f.blocks.iter().all(|b| {
                b.insts.iter().all(|i| {
                    !matches!(
                        i,
                        Inst::MakeBlock { .. }
                            | Inst::BlockParam { .. }
                            | Inst::HasArg { .. }
                            | Inst::Call {
                                kind: CallKind::Yield,
                                ..
                            }
                    )
                })
            });
            plain.then_some(TypedSig { params, ret })
        })
        .collect()
}

/// The result type of a call that goes through a typed entry: a direct
/// call (bound to one body) of a function that has one.
pub fn call_num(inst: &Inst, methods: &[RtMethod], typed: &[Option<TypedSig>]) -> Option<Num> {
    let Inst::Call {
        kind: CallKind::Method(mid),
        args,
        splat: false,
        kw,
        kw_splat: None,
        block: None,
        ..
    } = inst
    else {
        return None;
    };
    if !kw.is_empty() {
        return None;
    }
    let m = methods.get(*mid as usize)?;
    if m.native_key.is_some()
        || (m.overridden && !m.singleton && !m.is_extension)
        || m.synth != RtSynth::None
    {
        return None;
    }
    let fid = m.func?;
    let sig = typed.get(fid as usize)?.as_ref()?;
    (sig.params.len() == args.len()).then_some(sig.ret)
}

/// A call to `Int#to_f` with an unboxed receiver: the conversion is
/// done inline (the receiver and the result register).
pub fn int_to_f(inst: &Inst, methods: &[RtMethod], st: &[State]) -> Option<(Reg, Reg)> {
    let Inst::Call {
        dst,
        kind: CallKind::Method(mid),
        recv: Some(recv),
        args,
        splat: false,
        kw,
        kw_splat: None,
        block: None,
    } = inst
    else {
        return None;
    };
    let m = methods.get(*mid as usize)?;
    (args.is_empty()
        && kw.is_empty()
        && m.native_key.as_deref() == Some("Int#to_f")
        && st[*recv as usize] == State::Int)
        .then_some((*recv, *dst))
}

/// The declared type of a method's positional, non-defaulted parameter,
/// when it is Int or Float.
pub fn param_num(f: &Function, methods: &[RtMethod], index: u32) -> Option<Num> {
    let FuncKind::Method(mid) = f.kind else {
        return None;
    };
    let p = methods.get(mid as usize)?.params.get(index as usize)?;
    if p.kind != RtParamKind::Positional || p.has_default {
        return None;
    }
    num_of(p.ty.as_deref())
}

/// The declared type of a field, when it is Int or Float.
pub fn field_num(classes: &[RtClass], class: ClassId, index: u32) -> Option<Num> {
    let field = classes.get(class as usize)?.fields.get(index as usize)?;
    num_of(field.ty.as_deref())
}

fn num_of(name: Option<&str>) -> Option<Num> {
    match name {
        Some("Int") => Some(Num::Int),
        Some("Float") => Some(Num::Float),
        _ => None,
    }
}

/// Apply an instruction's effect on the states (the generator emits code
/// that matches this exactly).
pub fn transfer(
    inst: &Inst,
    st: &mut [State],
    f: &Function,
    methods: &[RtMethod],
    classes: &[RtClass],
    builtin: &RtBuiltin,
    typed: &[Option<TypedSig>],
) {
    match inst {
        // A call through a typed entry leaves its result unboxed (the
        // caller falls back to the interpreter when it does not fit).
        Inst::Call { dst, .. } if call_num(inst, methods, typed).is_some() => {
            st[*dst as usize] = num_state(call_num(inst, methods, typed).unwrap_or(Num::Int));
        }
        Inst::Call { dst, .. } if int_to_f(inst, methods, st).is_some() => {
            st[*dst as usize] = State::Float;
        }
        Inst::ClearRegs { from, to } => {
            for r in *from..*to {
                st[r as usize] = State::NonHeap;
            }
        }
        // A parameter or field of a numeric type is checked once and
        // then known (the check fails into the interpreter).
        Inst::Arg { dst, index } => {
            st[*dst as usize] = match param_num(f, methods, *index) {
                Some(n) => num_state(n),
                None => State::Unknown,
            };
        }
        Inst::FieldGet {
            dst, class, index, ..
        } => {
            st[*dst as usize] = match field_num(classes, *class, *index) {
                Some(n) => num_state(n),
                None => State::Unknown,
            };
        }
        Inst::LoadConst { dst, idx } => {
            st[*dst as usize] = match f.consts[*idx as usize] {
                Constant::Int(_) => State::Int,
                Constant::Float(_) => State::Float,
                Constant::Bool(_) => State::Bool,
                Constant::Nil => State::NonHeap,
                _ => State::Unknown,
            };
        }
        Inst::Move { dst, src } => st[*dst as usize] = st[*src as usize],
        Inst::BinOp { dst, lhs, rhs, .. } => match bin_types(inst, methods, builtin) {
            Some(t) if !(t.result == Some(Num::Float) && float_mod(inst)) => {
                // The operands are checked (or already known) on the
                // fast path; the slow path leaves the function.
                st[*lhs as usize] = num_state(t.lhs);
                st[*rhs as usize] = num_state(t.rhs);
                st[*dst as usize] = match t.result {
                    Some(n) => num_state(n),
                    None => State::Bool,
                };
            }
            _ => st[*dst as usize] = State::Unknown,
        },
        Inst::Not { dst, .. }
        | Inst::IsNil { dst, .. }
        | Inst::HasArg { dst, .. }
        | Inst::Equal { dst, .. }
        | Inst::CaseEq { dst, .. }
        | Inst::IsArray { dst, .. }
        | Inst::IsHash { dst, .. }
        | Inst::IsObject { dst, .. }
        | Inst::ClassIsA { dst, .. }
        | Inst::ClassIs { dst, .. }
        | Inst::IsA { dst, .. } => st[*dst as usize] = State::Bool,
        // A length is always a machine-word Int.
        Inst::Len { dst, .. } => st[*dst as usize] = State::Int,
        _ => {
            for r in defs(inst) {
                st[r as usize] = State::Unknown;
            }
        }
    }
}

/// A `Float` remainder has no inline form; it stays on the generic path.
pub fn float_mod(inst: &Inst) -> bool {
    matches!(
        inst,
        Inst::BinOp {
            op: FastOp::Mod,
            ..
        }
    )
}

pub fn num_state(n: Num) -> State {
    match n {
        Num::Int => State::Int,
        Num::Float => State::Float,
    }
}

/// The state of every register at the entry of every block.
pub fn analyze(
    f: &Function,
    methods: &[RtMethod],
    classes: &[RtClass],
    builtin: &RtBuiltin,
    typed: &[Option<TypedSig>],
) -> Vec<Vec<State>> {
    let nregs = f.nregs as usize;
    let nblocks = f.blocks.len();
    // Unreached until proven otherwise: the meet identity is "all
    // known", represented by `None`.
    let mut entry: Vec<Option<Vec<State>>> = vec![None; nblocks];
    entry[0] = Some(vec![State::NonHeap; nregs]);
    // Handler blocks are entered from an unwind with only the boxed homes
    // valid.
    for blk in &f.blocks {
        if let Some(h) = blk.handler {
            entry[h.block as usize] = Some(vec![State::Unknown; nregs]);
        }
    }
    let mut changed = true;
    while changed {
        changed = false;
        for (i, blk) in f.blocks.iter().enumerate() {
            let Some(start) = entry[i].clone() else {
                continue;
            };
            let mut st = start;
            for inst in &blk.insts {
                transfer(inst, &mut st, f, methods, classes, builtin, typed);
            }
            let targets: Vec<BlockId> = match &blk.term {
                Term::Jump(t) => vec![*t],
                Term::Branch { then, els, .. } => vec![*then, *els],
                _ => vec![],
            };
            for t in targets {
                let slot = &mut entry[t as usize];
                let merged = match slot {
                    None => st.clone(),
                    Some(old) => old.iter().zip(&st).map(|(a, b)| a.meet(*b)).collect(),
                };
                if slot.as_ref() != Some(&merged) {
                    *slot = Some(merged);
                    changed = true;
                }
            }
        }
    }
    entry
        .into_iter()
        .map(|e| e.unwrap_or_else(|| vec![State::Unknown; nregs]))
        .collect()
}
