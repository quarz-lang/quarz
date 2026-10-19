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
    match inst {
        Inst::LoadConst { dst, .. }
        | Inst::Move { dst, .. }
        | Inst::SelfRef { dst }
        | Inst::Arg { dst, .. }
        | Inst::HasArg { dst, .. }
        | Inst::BlockParam { dst }
        | Inst::FrameGet { dst, .. }
        | Inst::FieldGet { dst, .. }
        | Inst::FieldGetByName { dst, .. }
        | Inst::ConstGet { dst, .. }
        | Inst::ClassRef { dst, .. }
        | Inst::VariantSingleton { dst, .. }
        | Inst::Call { dst, .. }
        | Inst::IsNil { dst, .. }
        | Inst::BinOp { dst, .. }
        | Inst::Not { dst, .. }
        | Inst::CaseEq { dst, .. }
        | Inst::Equal { dst, .. }
        | Inst::ClassIsA { dst, .. }
        | Inst::IsA { dst, .. }
        | Inst::As { dst, .. }
        | Inst::MakeBlock { dst, .. }
        | Inst::MethodRef { dst, .. }
        | Inst::SymbolProc { dst, .. }
        | Inst::MakeArray { dst, .. }
        | Inst::MakeHash { dst, .. }
        | Inst::MakeRange { dst, .. }
        | Inst::MakeRegexp { dst, .. }
        | Inst::Interpolate { dst, .. }
        | Inst::ToSym { dst, .. }
        | Inst::IsArray { dst, .. }
        | Inst::IsHash { dst, .. }
        | Inst::IsObject { dst, .. }
        | Inst::ToArray { dst, .. }
        | Inst::Len { dst, .. }
        | Inst::ArrayGet { dst, .. }
        | Inst::ArrayGetReg { dst, .. }
        | Inst::ArraySlice { dst, .. }
        | Inst::ArraySliceReg { dst, .. }
        | Inst::ObjectFields { dst, .. }
        | Inst::HashGetSym { dst, .. }
        | Inst::HashRest { dst, .. }
        | Inst::CatchException { dst }
        | Inst::CatchAny { dst } => vec![*dst],
        Inst::OwnedCall { dst, recv, .. } => match recv {
            VarLoc::Reg(r) => vec![*dst, *r],
            VarLoc::Frame { .. } => vec![*dst],
        },
        Inst::FrameSet { .. } | Inst::FieldSet { .. } | Inst::NoMatch { .. } => vec![],
    }
}

/// Apply an instruction's effect on the states (the generator emits code
/// that matches this exactly).
pub fn transfer(
    inst: &Inst,
    st: &mut [State],
    f: &Function,
    methods: &[RtMethod],
    builtin: &RtBuiltin,
) {
    match inst {
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
        | Inst::IsA { dst, .. } => st[*dst as usize] = State::Bool,
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
pub fn analyze(f: &Function, methods: &[RtMethod], builtin: &RtBuiltin) -> Vec<Vec<State>> {
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
                transfer(inst, &mut st, f, methods, builtin);
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
