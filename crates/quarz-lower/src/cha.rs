//! What class hierarchy analysis rewrites once the whole program is
//! linked. Lowering does not look past a file's unit (each is lowered as
//! if compiled on its own, docs/05 §2): a call to a generated field
//! reader stays a call, and `new` on the receiver of a class method a
//! `ConstructRecv`, since a later unit may add a subclass that overrides
//! the reader or inherits the class method. Here, with every class
//! known, a reader nothing overrides becomes a read of the field (with
//! a data value held in place built from its physical fields), and a
//! `new` on a class with no subclass a plain construction.

use quarz_ir::*;

pub fn rewrite(functions: &mut [Function], world: &RtWorld) {
    let mut has_subclass = vec![false; world.classes.len()];
    for (d, k) in world.classes.iter().enumerate() {
        for a in &k.ancestors {
            if *a as usize != d {
                has_subclass[*a as usize] = true;
            }
        }
    }
    for f in functions.iter_mut() {
        rewrite_in(f, world, &has_subclass);
    }
}

fn rewrite_in(f: &mut Function, world: &RtWorld, has_subclass: &[bool]) {
    for b in 0..f.blocks.len() {
        let any = f.blocks[b].insts.iter().any(|i| match i {
            Inst::Call {
                kind: CallKind::Method(m),
                ..
            } => matches!(world.methods[*m as usize].synth, RtSynth::FieldGet(_)),
            Inst::Call {
                kind: CallKind::ConstructRecv { .. },
                ..
            } => true,
            _ => false,
        });
        if !any {
            continue;
        }
        let mut insts = Vec::with_capacity(f.blocks[b].insts.len());
        let mut lines = Vec::with_capacity(insts.capacity());
        let old_insts = std::mem::take(&mut f.blocks[b].insts);
        let old_lines = std::mem::take(&mut f.blocks[b].lines);
        for (inst, line) in old_insts.into_iter().zip(old_lines) {
            match inst {
                Inst::Call {
                    dst,
                    kind: CallKind::Method(m),
                    recv: Some(obj),
                    ref args,
                    splat: false,
                    ref kw,
                    kw_splat: None,
                    block: None,
                    ..
                } if args.is_empty() && kw.is_empty() => {
                    let method = &world.methods[m as usize];
                    let RtSynth::FieldGet(index) = method.synth else {
                        insts.push(inst);
                        lines.push(line);
                        continue;
                    };
                    if method.overridden {
                        insts.push(inst);
                        lines.push(line);
                        continue;
                    }
                    let class = method.owner;
                    let Some(ivar) = world.classes[class as usize].ivars.get(index as usize) else {
                        insts.push(inst);
                        lines.push(line);
                        continue;
                    };
                    match ivar.flat {
                        None => {
                            insts.push(Inst::FieldGet {
                                dst,
                                obj,
                                index: ivar.slot,
                                class,
                            });
                            lines.push(line);
                        }
                        Some(d) => {
                            // Its physical fields, then the data value.
                            let n = world.classes[d as usize].fields.len() as u32;
                            let mut parts = Vec::with_capacity(n as usize);
                            for k in 0..n {
                                let r = f.nregs;
                                f.nregs += 1;
                                insts.push(Inst::FieldGet {
                                    dst: r,
                                    obj,
                                    index: ivar.slot + k,
                                    class,
                                });
                                lines.push(line);
                                parts.push(r);
                            }
                            let init = world.classes[d as usize]
                                .methods
                                .get("initialize")
                                .and_then(|ms| {
                                    ms.iter().copied().find(|m| {
                                        world.methods[*m as usize].synth == RtSynth::DataInit
                                    })
                                });
                            insts.push(Inst::Call {
                                dst,
                                kind: CallKind::Construct { class: d, init },
                                recv: None,
                                args: parts,
                                splat: false,
                                kw: Vec::new(),
                                kw_splat: None,
                                block: None,
                                moved: 0,
                            });
                            lines.push(line);
                        }
                    }
                }
                Inst::Call {
                    dst,
                    kind: CallKind::ConstructRecv { class, init },
                    recv,
                    args,
                    splat,
                    kw,
                    kw_splat,
                    block,
                    moved,
                } if !has_subclass[class as usize] => {
                    insts.push(Inst::Call {
                        dst,
                        kind: CallKind::Construct { class, init },
                        recv,
                        args,
                        splat,
                        kw,
                        kw_splat,
                        block,
                        moved,
                    });
                    lines.push(line);
                }
                inst => {
                    insts.push(inst);
                    lines.push(line);
                }
            }
        }
        f.blocks[b].insts = insts;
        f.blocks[b].lines = lines;
    }
}
