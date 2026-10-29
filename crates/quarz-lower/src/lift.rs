//! A block lifted to a method (docs/14 §5): the body of a method a
//! `static` statement generated with `Meta::ClassDef#def_method` is a
//! copy of the block's function, with the values the block captured
//! baked in where it read them (`Generated::captures`), and the same for
//! the blocks made inside it. The checker keeps such a block from
//! assigning what it captures, leaving the enclosing method (`return`,
//! `break`), yielding to its block and using its `self`; `check` tells
//! whether a function tree obeys that, for the runner to refuse the
//! generation otherwise, and `lift` assumes it.

use quarz_ir::*;
use quarz_types::world::Baked;
use quarz_types::Generated;

use crate::Lowerer;

/// A reader of a captured slot: `FrameGet { depth, slot }` in a function
/// `skip` frames below the block's, with `own` the block function's own
/// frame, reads slot `slot` of the frame `depth - own - skip` above the
/// block's chain (as `captured_slots` counts in the runtime).
fn captured(depth: u32, own: u32, skip: u32) -> Option<u32> {
    depth.checked_sub(own + skip)
}

/// Whether the block function `root` (and the blocks it makes) can be a
/// method's body: the frame slots it reads outside itself, or why not.
pub fn check(functions: &[Function], root: FuncId) -> Result<Vec<(u32, u32)>, String> {
    let mut reads: Vec<(u32, u32)> = Vec::new();
    let mut work: Vec<(FuncId, u32)> = vec![(root, 0)];
    while let Some((fid, skip)) = work.pop() {
        let Some(f) = functions.get(fid as usize) else {
            return Err("the block's function is not lowered".to_string());
        };
        let own = u32::from(f.frame_size > 0);
        for b in &f.blocks {
            for inst in &b.insts {
                match inst {
                    Inst::FrameGet { depth, slot, .. } => {
                        if let Some(d) = captured(*depth, own, skip) {
                            if !reads.contains(&(d, *slot)) {
                                reads.push((d, *slot));
                            }
                        }
                    }
                    Inst::FrameSet { depth, .. } if captured(*depth, own, skip).is_some() => {
                        return Err("the block assigns a variable of the enclosing method".into());
                    }
                    Inst::OwnedCall {
                        recv: VarLoc::Frame { depth, .. },
                        ..
                    } if captured(*depth, own, skip).is_some() => {
                        return Err("the block assigns a variable of the enclosing method".into());
                    }
                    Inst::BlockParam { .. } => {
                        return Err("the block uses the enclosing method's block".into());
                    }
                    Inst::Call {
                        kind: CallKind::Yield,
                        ..
                    } => {
                        return Err("the block yields to the enclosing method's block".into());
                    }
                    Inst::MakeBlock { func, .. } => work.push((*func, skip + own)),
                    _ => {}
                }
            }
            match b.term {
                Term::ReturnOut(_) => {
                    return Err("the block returns from the enclosing method".into());
                }
                Term::BreakOut(_) if fid == root => {
                    return Err("the block breaks out of the enclosing method".into());
                }
                _ => {}
            }
        }
    }
    Ok(reads)
}

impl Lowerer {
    /// The function of a generated method: the block's, copied with its
    /// captures baked in, and its own blocks likewise.
    pub(crate) fn lift(&mut self, mid: MethodId, name: String, g: &Generated) -> FuncId {
        // New ids for the block function and the blocks it makes, first.
        let mut copies: Vec<(FuncId, FuncId, u32)> = Vec::new();
        let mut work: Vec<(FuncId, u32)> = vec![(g.func, 0)];
        while let Some((old, skip)) = work.pop() {
            let new = self.alloc_func();
            copies.push((old, new, skip));
            let f = &self.done[old as usize];
            let own = u32::from(f.frame_size > 0);
            for b in &f.blocks {
                for inst in &b.insts {
                    if let Inst::MakeBlock { func, .. } = inst {
                        work.push((*func, skip + own));
                    }
                }
            }
        }
        let renamed = |old: FuncId| -> FuncId {
            copies
                .iter()
                .find(|(o, _, _)| *o == old)
                .map(|(_, n, _)| *n)
                .expect("block function copied")
        };
        for &(old, new, skip) in &copies {
            let mut f = self.done[old as usize].clone();
            let own = u32::from(f.frame_size > 0);
            if old == g.func {
                f.kind = FuncKind::Method(mid);
                f.name = name.clone();
            }
            let mut baker = Baker {
                layouts: &self.layouts,
                nregs: f.nregs,
                consts: std::mem::take(&mut f.consts),
            };
            for b in &mut f.blocks {
                let insts = std::mem::take(&mut b.insts);
                let lines = std::mem::take(&mut b.lines);
                for (inst, line) in insts.into_iter().zip(lines) {
                    let before = b.insts.len();
                    match inst {
                        Inst::FrameGet { dst, depth, slot } => match captured(depth, own, skip) {
                            Some(d) => {
                                let value = g
                                    .captures
                                    .iter()
                                    .find(|(cd, cs, _)| (*cd, *cs) == (d, slot))
                                    .map(|(_, _, v)| v)
                                    .expect("captured value recorded");
                                baker.bake(&mut b.insts, dst, value);
                            }
                            None => b.insts.push(Inst::FrameGet { dst, depth, slot }),
                        },
                        Inst::MakeBlock {
                            dst,
                            func,
                            destructure,
                            is_lambda,
                        } => b.insts.push(Inst::MakeBlock {
                            dst,
                            func: renamed(func),
                            destructure,
                            is_lambda,
                        }),
                        other => b.insts.push(other),
                    }
                    b.lines
                        .extend(std::iter::repeat_n(line, b.insts.len() - before));
                }
            }
            f.nregs = baker.nregs;
            f.consts = baker.consts;
            self.set_func(new, f);
        }
        renamed(g.func)
    }
}

/// Emits the instructions that make a baked value.
pub(crate) struct Baker<'a> {
    layouts: &'a [crate::layout::Layout],
    nregs: u32,
    consts: Vec<Constant>,
}

impl<'a> Baker<'a> {
    /// For a function with `nregs` registers so far and no constants.
    pub(crate) fn new(layouts: &'a [crate::layout::Layout], nregs: u32) -> Baker<'a> {
        Baker {
            layouts,
            nregs,
            consts: Vec::new(),
        }
    }

    /// The registers used and the constants made.
    pub(crate) fn finish(self) -> (u32, Vec<Constant>) {
        (self.nregs, self.consts)
    }

    fn reg(&mut self) -> Reg {
        let r = self.nregs;
        self.nregs += 1;
        r
    }

    fn constant(&mut self, out: &mut Vec<Inst>, dst: Reg, c: Constant) {
        let idx = match self.consts.iter().position(|k| *k == c) {
            Some(i) => i as u32,
            None => {
                self.consts.push(c);
                self.consts.len() as u32 - 1
            }
        };
        out.push(Inst::LoadConst { dst, idx });
    }

    pub(crate) fn bake(&mut self, out: &mut Vec<Inst>, dst: Reg, v: &Baked) {
        match v {
            Baked::Nil => self.constant(out, dst, Constant::Nil),
            Baked::Bool(b) => self.constant(out, dst, Constant::Bool(*b)),
            Baked::Int(i) => self.constant(out, dst, Constant::Int(*i)),
            Baked::BigInt { digits, base } => self.constant(
                out,
                dst,
                Constant::BigInt {
                    digits: digits.clone(),
                    base: *base,
                },
            ),
            Baked::Float(f) => self.constant(out, dst, Constant::Float(*f)),
            Baked::Str(s) => self.constant(out, dst, Constant::Str(s.clone())),
            Baked::Symbol(s) => self.constant(out, dst, Constant::Symbol(s.clone())),
            Baked::Regexp { source, flags } => self.constant(
                out,
                dst,
                Constant::Regexp {
                    source: source.clone(),
                    flags: flags.clone(),
                },
            ),
            Baked::Bytes(b) => self.constant(out, dst, Constant::Bytes(b.clone())),
            Baked::Class(class) => out.push(Inst::ClassRef { dst, class: *class }),
            Baked::Variant(class) => out.push(Inst::VariantSingleton { dst, class: *class }),
            Baked::Array(items) => {
                let items = items
                    .iter()
                    .map(|item| {
                        let reg = self.reg();
                        self.bake(out, reg, item);
                        ArrayItem { reg, splat: false }
                    })
                    .collect();
                out.push(Inst::MakeArray { dst, items });
            }
            Baked::Hash(pairs) => {
                let items = pairs
                    .iter()
                    .map(|(k, v)| {
                        let (kr, vr) = (self.reg(), self.reg());
                        self.bake(out, kr, k);
                        self.bake(out, vr, v);
                        HashItem::Pair(kr, vr)
                    })
                    .collect();
                out.push(Inst::MakeHash { dst, items });
            }
            Baked::Range { lo, hi, exclusive } => {
                let mut bound = |b: &Option<Box<Baked>>, out: &mut Vec<Inst>| {
                    b.as_ref().map(|b| {
                        let r = self.reg();
                        self.bake(out, r, b);
                        r
                    })
                };
                let lo = bound(lo, out);
                let hi = bound(hi, out);
                out.push(Inst::MakeRange {
                    dst,
                    lo,
                    hi,
                    exclusive: *exclusive,
                });
            }
            Baked::Data(class, fields) => {
                // The data constructor given every physical field copies
                // them in, without running code (`Interp::construct`). A
                // data type whose body has its own `initialize` has none:
                // the value is allocated without one and its physical
                // fields stored, still without running code (docs/14 §5).
                let args: Vec<Reg> = fields
                    .iter()
                    .map(|f| {
                        let r = self.reg();
                        self.bake(out, r, f);
                        r
                    })
                    .collect();
                let init = self.layouts.get(*class as usize).and_then(|l| l.init);
                let stores = if init.is_some() {
                    Vec::new()
                } else {
                    args.clone()
                };
                out.push(Inst::Call {
                    dst,
                    kind: CallKind::Construct {
                        class: *class,
                        init,
                    },
                    recv: None,
                    args: if init.is_some() { args } else { Vec::new() },
                    splat: false,
                    kw: Vec::new(),
                    kw_splat: None,
                    block: None,
                    moved: 0,
                });
                for (index, src) in stores.into_iter().enumerate() {
                    out.push(Inst::FieldSet {
                        obj: dst,
                        index: index as u32,
                        src,
                        class: *class,
                    });
                }
            }
        }
    }
}
