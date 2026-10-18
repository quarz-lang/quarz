//! A textual rendering of QIR (`quarz ir FILE`).

use std::fmt::Write as _;

use crate::*;

pub fn dump_module(m: &Module) -> String {
    let mut out = String::new();
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
