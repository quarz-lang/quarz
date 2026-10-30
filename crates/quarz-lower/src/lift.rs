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

/// The captured slots of the block function `root` (and the blocks it
/// makes) that hold a field handle `set` is called on (docs/14 §5): a
/// handle must name a `var` field for them. `set` is `Meta::FieldRef#set`.
pub fn handle_sets(functions: &[Function], root: FuncId, set: MethodId) -> Vec<(u32, u32)> {
    let mut out: Vec<(u32, u32)> = Vec::new();
    let mut work: Vec<(FuncId, u32)> = vec![(root, 0)];
    while let Some((fid, skip)) = work.pop() {
        let Some(f) = functions.get(fid as usize) else {
            continue;
        };
        let own = u32::from(f.frame_size > 0);
        // (Over the whole function, as `handle_registers`: a register a
        // captured `FrameGet` alone writes.)
        let mut loaded: Vec<(Reg, (u32, u32))> = Vec::new();
        let mut other: Vec<Reg> = Vec::new();
        for b in &f.blocks {
            for inst in &b.insts {
                match inst {
                    Inst::FrameGet { dst, depth, slot }
                        if captured(*depth, own, skip).is_some() =>
                    {
                        let d = captured(*depth, own, skip).unwrap();
                        loaded.push((*dst, (d, *slot)));
                    }
                    Inst::MakeBlock { func, .. } => {
                        other.extend(inst.defs());
                        work.push((*func, skip + own));
                    }
                    // (An inlined block clears its registers before it
                    // loads them: not a write of a handle register.)
                    Inst::ClearRegs { .. } => {}
                    _ => other.extend(inst.defs()),
                }
            }
        }
        loaded.retain(|(r, _)| !other.contains(r));
        for b in &f.blocks {
            for inst in &b.insts {
                if let Inst::Call {
                    kind: CallKind::Method(m),
                    recv: Some(r),
                    ..
                } = inst
                {
                    if *m == set {
                        if let Some((_, at)) = loaded.iter().find(|(l, _)| l == r) {
                            if !out.contains(at) {
                                out.push(*at);
                            }
                        }
                    }
                }
            }
        }
    }
    out
}

impl Lowerer {
    /// The function of a generated method: the block's, copied with its
    /// captures baked in, and its own blocks likewise.
    pub(crate) fn lift(
        &mut self,
        world: &quarz_types::World,
        mid: MethodId,
        name: String,
        g: &Generated,
    ) -> FuncId {
        // A handle's `get`/`set`/`bind` (docs/14 §5): the field access or
        // the bound method, in place of the call, where the handle is
        // baked.
        let handle_methods = |class: ClassId, n: &str| -> Option<MethodId> {
            world
                .class(class)
                .methods
                .get(n)
                .and_then(|ids| ids.first().copied())
        };
        let field_ref = world.builtin.meta_field_ref;
        let (get, set) = (
            handle_methods(field_ref, "get"),
            handle_methods(field_ref, "set"),
        );
        let bind = handle_methods(world.builtin.meta_method, "bind");
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
            // The registers holding a baked handle, with what it names, in
            // the whole function: a register
            // the captured `FrameGet` alone writes (the lowering gives each
            // value its own).
            let handles = handle_registers(&f, own, skip, g, world);
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
                        Inst::Call {
                            dst,
                            kind: CallKind::Method(m),
                            recv: Some(r),
                            ref args,
                            ..
                        } if (Some(m) == get || Some(m) == set || Some(m) == bind)
                            && handles.iter().any(|(h, _)| *h == r) =>
                        {
                            match &handles.iter().find(|(h, _)| *h == r).unwrap().1 {
                                Handle::Field(class, index) if Some(m) == get => {
                                    baker.field_get(&mut b.insts, dst, args[0], *class, *index);
                                }
                                Handle::Field(class, index) => {
                                    baker.field_set(&mut b.insts, args[0], *class, *index, args[1]);
                                    baker.constant(&mut b.insts, dst, Constant::Nil);
                                }
                                Handle::Method(method, name) => {
                                    let name = baker.const_index(Constant::Str(name.clone()));
                                    b.insts.push(Inst::MethodRef {
                                        dst,
                                        recv: args[0],
                                        name,
                                        method: Some(*method),
                                    });
                                }
                            }
                        }
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

/// What a baked handle names (docs/14 §5).
enum Handle {
    /// A field: its class and declared index.
    Field(ClassId, u32),
    /// A method, resolved when its statement had run, and its name.
    Method(MethodId, String),
}

/// The registers of block function `f` (`own`, `skip` as in `lift`) that
/// hold a baked handle, with what it names: written by a captured
/// `FrameGet` of a handle and by nothing else.
fn handle_registers(
    f: &Function,
    own: u32,
    skip: u32,
    g: &Generated,
    world: &quarz_types::World,
) -> Vec<(Reg, Handle)> {
    let mut found: Vec<(Reg, Handle)> = Vec::new();
    let mut other: Vec<Reg> = Vec::new();
    for b in &f.blocks {
        for inst in &b.insts {
            if let Inst::FrameGet { dst, depth, slot } = inst {
                if let Some(d) = captured(*depth, own, skip) {
                    let value = g
                        .captures
                        .iter()
                        .find(|(cd, cs, _)| (*cd, *cs) == (d, *slot))
                        .map(|(_, _, v)| v);
                    if let Some(h) = value.and_then(|v| handle_of(world, v)) {
                        found.push((*dst, h));
                        continue;
                    }
                }
            }
            // (An inlined block clears its registers before it loads them.)
            if !matches!(inst, Inst::ClearRegs { .. }) {
                other.extend(inst.defs());
            }
        }
    }
    found.retain(|(r, _)| !other.contains(r));
    found
}

/// What a baked `Meta::FieldRef` or `Meta::Method` names (docs/14 §5):
/// a field when its class has it, a method once resolved.
fn handle_of(world: &quarz_types::World, v: &Baked) -> Option<Handle> {
    let Baked::Data(c, fields) = v else {
        return None;
    };
    let (Some(Baked::Class(owner)), Some(Baked::Symbol(name))) = (fields.first(), fields.get(1))
    else {
        return None;
    };
    if *c == world.builtin.meta_field_ref {
        let index = world.field_index(*owner, name)?;
        Some(Handle::Field(*owner, index as u32))
    } else if *c == world.builtin.meta_method {
        // (Its class's `k`th method of that name,
        // `Runner::resolve_method_handles`.)
        let (Some(Baked::Bool(singleton)), Some(Baked::Int(k)), Some(Baked::Class(at))) =
            (fields.get(3), fields.get(4), fields.get(5))
        else {
            return None;
        };
        let class = world.class(*at);
        let table = if *singleton {
            &class.singleton_methods
        } else {
            &class.methods
        };
        let m = table
            .get(name)?
            .get(usize::try_from(*k).ok()?.checked_sub(1)?)?;
        Some(Handle::Method(*m, name.clone()))
    } else {
        None
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
        let idx = self.const_index(c);
        out.push(Inst::LoadConst { dst, idx });
    }

    fn const_index(&mut self, c: Constant) -> u32 {
        match self.consts.iter().position(|k| *k == c) {
            Some(i) => i as u32,
            None => {
                self.consts.push(c);
                self.consts.len() as u32 - 1
            }
        }
    }

    /// Where declared field `index` of `class` is: its slot, and the
    /// data type held in place there, if any (`FnBuilder::ivar_layout`).
    fn ivar_layout(&self, class: ClassId, index: u32) -> (u32, Option<ClassId>) {
        match self
            .layouts
            .get(class as usize)
            .and_then(|l| l.ivars.get(index as usize))
        {
            Some(iv) => (iv.slot, iv.flat),
            None => (index, None),
        }
    }

    /// Read declared field `index` of the object in `obj` into `dst`, as
    /// `@name` in the class's own methods does (`FnBuilder::field_get`).
    fn field_get(&mut self, out: &mut Vec<Inst>, dst: Reg, obj: Reg, class: ClassId, index: u32) {
        let (slot, flat) = self.ivar_layout(class, index);
        let Some(d) = flat else {
            out.push(Inst::FieldGet {
                dst,
                obj,
                index: slot,
                class,
            });
            return;
        };
        let n = self.layouts[d as usize].slots.len() as u32;
        let args: Vec<Reg> = (0..n)
            .map(|k| {
                let r = self.reg();
                out.push(Inst::FieldGet {
                    dst: r,
                    obj,
                    index: slot + k,
                    class,
                });
                r
            })
            .collect();
        out.push(Inst::Call {
            dst,
            kind: CallKind::Construct {
                class: d,
                init: self.layouts[d as usize].init,
            },
            recv: None,
            args,
            splat: false,
            kw: Vec::new(),
            kw_splat: None,
            block: None,
            moved: 0,
        });
    }

    /// Write `src` to declared field `index` of the object in `obj`
    /// (`FnBuilder::field_set`).
    fn field_set(&mut self, out: &mut Vec<Inst>, obj: Reg, class: ClassId, index: u32, src: Reg) {
        let (slot, flat) = self.ivar_layout(class, index);
        let Some(d) = flat else {
            out.push(Inst::FieldSet {
                obj,
                index: slot,
                src,
                class,
            });
            return;
        };
        for k in 0..self.layouts[d as usize].slots.len() as u32 {
            let t = self.reg();
            out.push(Inst::FieldGet {
                dst: t,
                obj: src,
                index: k,
                class: d,
            });
            out.push(Inst::FieldSet {
                obj,
                index: slot + k,
                src: t,
                class,
            });
        }
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
