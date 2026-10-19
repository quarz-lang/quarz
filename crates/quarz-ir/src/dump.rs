//! A textual rendering of QIR (`quarz ir FILE`).

use std::fmt::Write as _;

use crate::*;

pub fn dump_module(m: &Module) -> String {
    let mut out = String::new();
    for (i, meth) in m.world.methods.iter().enumerate() {
        let owner = m
            .world
            .classes
            .get(meth.owner as usize)
            .map(|c| c.name.as_str())
            .unwrap_or("?");
        let sep = if meth.singleton { "." } else { "#" };
        let _ = write!(out, "method {i} {owner}{sep}{}", meth.name);
        if let Some(f) = meth.func {
            let _ = write!(out, " fn={f}");
        }
        if let Some(k) = &meth.native_key {
            let _ = write!(out, " native={k}");
        }
        if meth.overridden {
            out.push_str(" overridden");
        }
        out.push('\n');
    }
    out.push('\n');
    for (i, f) in m.functions.iter().enumerate() {
        dump_function(&mut out, i as FuncId, f);
        out.push('\n');
    }
    out
}

pub fn dump_function(out: &mut String, id: FuncId, f: &Function) {
    let _ = writeln!(
        out,
        "fn {id} {:?} kind={:?} regs={} frame={} params={}",
        f.name,
        f.kind,
        f.nregs,
        f.frame_size,
        f.param_kinds.len()
    );
    for (i, c) in f.consts.iter().enumerate() {
        let _ = writeln!(out, "  const {i} = {c:?}");
    }
    for (i, b) in f.blocks.iter().enumerate() {
        match b.handler {
            Some(h) => {
                let _ = writeln!(out, " b{i} (handler b{} {:?}):", h.block, h.kind);
            }
            None => {
                let _ = writeln!(out, " b{i}:");
            }
        }
        for inst in &b.insts {
            let _ = writeln!(out, "    {inst:?}");
        }
        let _ = writeln!(out, "    {:?}", b.term);
    }
}
