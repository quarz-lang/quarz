//! The LLVM backend: the module as textual LLVM IR, compiled to an
//! object file by `clang`. Typed entries push no activation (see
//! `gen::Target::lazy_act`): every function carries unwind information
//! and line numbers (the QIR line, as the DWARF line), and the runtime
//! walks the native stack for backtraces (`quarz_vm::native_bt`).

use std::collections::HashMap;
use std::fmt::Write as _;
use std::path::Path;
use std::process::Command;

use quarz_ir::*;
use quarz_vm::layout as L;

use crate::builder::{Builder, FloatCC, IntCC, Ty};
use crate::gen::{self, Helpers};
use crate::unbox::{self, Num};

/// A declared function: its name and signature.
struct FnDecl {
    name: String,
    params: Vec<Ty>,
    rets: Vec<Ty>,
}

/// A signature for indirect calls.
struct SigDecl {
    params: Vec<Ty>,
    rets: Vec<Ty>,
}

/// Where a value comes from: an instruction result (`%vN`) or a
/// constant (written inline).
#[derive(Clone)]
struct Val {
    text: String,
    ty: Ty,
}

/// Where a conditional branch's weights go (see `Ll::branch_weights`).
const PROF_MARK: &str = "\u{1}prof:";

struct BlockData {
    /// The parameters: the values phis define.
    params: Vec<(u32, Ty)>,
    /// `(predecessor, arguments)` of each edge into the block.
    incoming: Vec<(u32, Vec<u32>)>,
    body: String,
    terminated: bool,
    /// Rarely run: a branch to it from a hot block gets branch weights.
    cold: bool,
}

/// The builder of one function, emitting text.
struct Ll<'a> {
    decls: &'a [FnDecl],
    sigs: &'a [SigDecl],
    /// Pointers are `ptr` (LLVM 15 and later) or `i8*` with casts at
    /// each access.
    opaque: bool,
    nparams: u32,
    rets: Vec<Ty>,
    vals: Vec<Val>,
    blocks: Vec<BlockData>,
    cur: u32,
    /// Allocas, at the top of the entry block.
    prologue: String,
    nvars: u32,
    nslots: u32,
    ntmp: u32,
    /// The metadata node of this function's subprogram, and of each
    /// line's location (ids are module-wide: `meta_base` and up).
    meta_base: u32,
    lines: Vec<u32>,
    line: Option<u32>,
    /// Intrinsics used (declared by the module).
    intrinsics: Vec<&'static str>,
}

fn ty_str(ty: Ty, opaque: bool) -> &'static str {
    match ty {
        Ty::I8 => "i8",
        Ty::I32 => "i32",
        Ty::I64 => "i64",
        Ty::F64 => "double",
        Ty::Ptr => {
            if opaque {
                "ptr"
            } else {
                "i8*"
            }
        }
    }
}

fn align_of(ty: Ty) -> u32 {
    match ty {
        Ty::I8 => 1,
        Ty::I32 => 4,
        Ty::I64 | Ty::F64 | Ty::Ptr => 8,
    }
}

/// The LLVM type of a function with these parameters and results.
fn fn_type(params: &[Ty], rets: &[Ty], opaque: bool) -> String {
    let ps: Vec<&str> = params.iter().map(|t| ty_str(*t, opaque)).collect();
    format!("{} ({})", ret_type(rets, opaque), ps.join(", "))
}

fn ret_type(rets: &[Ty], opaque: bool) -> String {
    match rets {
        [] => "void".to_string(),
        [r] => ty_str(*r, opaque).to_string(),
        rs => {
            let ts: Vec<&str> = rs.iter().map(|t| ty_str(*t, opaque)).collect();
            format!("{{ {} }}", ts.join(", "))
        }
    }
}

impl<'a> Ll<'a> {
    fn new(
        decls: &'a [FnDecl],
        sigs: &'a [SigDecl],
        opaque: bool,
        params: &[Ty],
        rets: &[Ty],
        meta_base: u32,
    ) -> Ll<'a> {
        let mut ll = Ll {
            decls,
            sigs,
            opaque,
            nparams: params.len() as u32,
            rets: rets.to_vec(),
            vals: Vec::new(),
            blocks: Vec::new(),
            cur: 0,
            prologue: String::new(),
            nvars: 0,
            nslots: 0,
            ntmp: 0,
            meta_base,
            lines: Vec::new(),
            line: None,
            intrinsics: Vec::new(),
        };
        for (i, p) in params.iter().enumerate() {
            ll.vals.push(Val {
                text: format!("%a{i}"),
                ty: *p,
            });
        }
        ll
    }

    fn t(&self, ty: Ty) -> &'static str {
        ty_str(ty, self.opaque)
    }

    /// A pointer to `ty`.
    fn pt(&self, ty: Ty) -> String {
        if self.opaque {
            "ptr".to_string()
        } else {
            format!("{}*", self.t(ty))
        }
    }

    fn val(&self, v: u32) -> &Val {
        &self.vals[v as usize]
    }

    fn new_val(&mut self, text: String, ty: Ty) -> u32 {
        self.vals.push(Val { text, ty });
        (self.vals.len() - 1) as u32
    }

    /// Emit an instruction defining a new value.
    fn def(&mut self, ty: Ty, inst: String) -> u32 {
        let id = self.vals.len() as u32;
        let text = format!("%v{id}");
        self.vals.push(Val {
            text: text.clone(),
            ty,
        });
        let body = &mut self.blocks[self.cur as usize].body;
        let _ = writeln!(body, "  {text} = {inst}");
        id
    }

    /// Emit an instruction with no result.
    fn emit(&mut self, inst: &str) {
        let body = &mut self.blocks[self.cur as usize].body;
        let _ = writeln!(body, "  {inst}");
    }

    /// A temporary name for an intermediate (an `i1` or a cast).
    fn tmp(&mut self) -> String {
        self.ntmp += 1;
        format!("%t{}", self.ntmp)
    }

    fn emit_tmp(&mut self, inst: String) -> String {
        let name = self.tmp();
        let body = &mut self.blocks[self.cur as usize].body;
        let _ = writeln!(body, "  {name} = {inst}");
        name
    }

    /// `ty %text` of a value.
    fn tv(&self, v: u32) -> String {
        let val = self.val(v);
        format!("{} {}", self.t(val.ty), val.text)
    }

    /// The value as `ty`, cast if needed.
    fn coerce(&mut self, v: u32, ty: Ty) -> u32 {
        let from = self.val(v).ty;
        if from == ty {
            return v;
        }
        let tv = self.tv(v);
        let to = self.t(ty);
        let inst = match (from, ty) {
            (Ty::Ptr, Ty::I64) => format!("ptrtoint {tv} to {to}"),
            (Ty::I64, Ty::Ptr) => format!("inttoptr {tv} to {to}"),
            (Ty::Ptr, Ty::I32 | Ty::I8) => {
                let w = self.emit_tmp(format!("ptrtoint {tv} to i64"));
                format!("trunc i64 {w} to {to}")
            }
            (Ty::I32 | Ty::I8, Ty::Ptr) => {
                let w = self.emit_tmp(format!("zext {tv} to i64"));
                format!("inttoptr i64 {w} to {to}")
            }
            (Ty::I8, Ty::I32 | Ty::I64) | (Ty::I32, Ty::I64) => format!("zext {tv} to {to}"),
            (Ty::I64, Ty::I32 | Ty::I8) | (Ty::I32, Ty::I8) => format!("trunc {tv} to {to}"),
            (Ty::F64, Ty::I64) | (Ty::I64, Ty::F64) => format!("bitcast {tv} to {to}"),
            (Ty::F64, _) | (_, Ty::F64) => {
                let w = self.emit_tmp(format!("bitcast {tv} to i64"));
                let w = self.new_val(w, Ty::I64);
                return self.coerce(w, ty);
            }
            _ => unreachable!("coerce {from:?} to {ty:?}"),
        };
        self.def(ty, inst)
    }

    /// The address `p + off`, as a pointer to `ty`.
    fn addr(&mut self, p: u32, off: i32, ty: Ty) -> String {
        let p = self.coerce(p, Ty::Ptr);
        let mut text = self.val(p).text.clone();
        if off != 0 {
            let pt = self.t(Ty::Ptr);
            text = self.emit_tmp(format!("getelementptr i8, {pt} {text}, i64 {off}"));
        }
        if !self.opaque && ty != Ty::Ptr {
            let to = self.pt(ty);
            text = self.emit_tmp(format!("bitcast i8* {text} to {to}"));
        } else if !self.opaque {
            text = self.emit_tmp(format!("bitcast i8* {text} to i8**"));
        }
        text
    }

    /// An `i1` from an `I8` (0 or 1).
    fn i1(&mut self, c: u32) -> String {
        let c = self.coerce(c, Ty::I8);
        let text = self.val(c).text.clone();
        self.emit_tmp(format!("icmp ne i8 {text}, 0"))
    }

    /// An `I8` value from an `i1` temporary.
    fn widen_i1(&mut self, t: &str) -> u32 {
        self.def(Ty::I8, format!("zext i1 {t} to i8"))
    }

    fn binop(&mut self, op: &str, a: u32, b: u32) -> u32 {
        let ty = self.val(a).ty;
        let b = self.coerce(b, ty);
        let (at, bt) = (self.val(a).text.clone(), self.val(b).text.clone());
        self.def(ty, format!("{op} {} {at}, {bt}", self.t(ty)))
    }

    fn fbinop(&mut self, op: &str, a: u32, b: u32) -> u32 {
        let a = self.coerce(a, Ty::F64);
        let b = self.coerce(b, Ty::F64);
        let (at, bt) = (self.val(a).text.clone(), self.val(b).text.clone());
        self.def(Ty::F64, format!("{op} double {at}, {bt}"))
    }

    fn dbg(&mut self) -> String {
        match self.line {
            Some(line) => {
                let k = match self.lines.iter().position(|l| *l == line) {
                    Some(k) => k,
                    None => {
                        self.lines.push(line);
                        self.lines.len() - 1
                    }
                };
                format!(", !dbg !{}", self.meta_base + 1 + k as u32)
            }
            None => String::new(),
        }
    }

    fn intrinsic(&mut self, decl: &'static str) {
        if !self.intrinsics.contains(&decl) {
            self.intrinsics.push(decl);
        }
    }

    fn overflow(&mut self, name: &str, a: u32, b: u32) -> (u32, u32) {
        let a = self.coerce(a, Ty::I64);
        let b = self.coerce(b, Ty::I64);
        let (at, bt) = (self.val(a).text.clone(), self.val(b).text.clone());
        let pair = self.emit_tmp(format!(
            "call {{ i64, i1 }} @llvm.{name}.with.overflow.i64(i64 {at}, i64 {bt})"
        ));
        let r = self.def(Ty::I64, format!("extractvalue {{ i64, i1 }} {pair}, 0"));
        let o = self.emit_tmp(format!("extractvalue {{ i64, i1 }} {pair}, 1"));
        let o = self.widen_i1(&o);
        (r, o)
    }

    /// `body` with each conditional branch's mark replaced by its weights:
    /// `!prof` when exactly one side is cold (the module's nodes !6 and !7).
    fn branch_weights(&self, body: &str) -> String {
        let mut out = String::with_capacity(body.len());
        let mut rest = body;
        while let Some(at) = rest.find(PROF_MARK) {
            out.push_str(&rest[..at]);
            let tail = &rest[at + PROF_MARK.len()..];
            let end = tail.find(';').unwrap_or(tail.len());
            let (t, e) = tail[..end].split_once(',').unwrap_or(("0", "0"));
            let cold = |b: &str| {
                b.parse::<usize>()
                    .ok()
                    .and_then(|b| self.blocks.get(b))
                    .is_some_and(|b| b.cold)
            };
            match (cold(t), cold(e)) {
                (true, false) => out.push_str(", !prof !6"),
                (false, true) => out.push_str(", !prof !7"),
                _ => {}
            }
            rest = &tail[(end + 1).min(tail.len())..];
        }
        out.push_str(rest);
        out
    }

    /// The text of the function: `define`, the allocas, the blocks with
    /// their phis, and the function's metadata nodes.
    fn finish(mut self, name: &str, attrs: &str, params: &[Ty]) -> (String, Vec<String>) {
        let mut out = String::new();
        let ps: Vec<String> = params
            .iter()
            .enumerate()
            .map(|(i, p)| format!("{} %a{i}", self.t(*p)))
            .collect();
        let _ = writeln!(
            out,
            "define internal {} @{name}({}) {attrs} !dbg !{} {{",
            ret_type(&self.rets, self.opaque),
            ps.join(", "),
            self.meta_base
        );
        let nblocks = self.blocks.len();
        for i in 0..nblocks {
            let _ = writeln!(out, "b{i}:");
            if i == 0 {
                out.push_str(&self.prologue);
            }
            // The phis.
            let params = self.blocks[i].params.clone();
            let incoming = self.blocks[i].incoming.clone();
            for (k, (v, ty)) in params.iter().enumerate() {
                let text = self.val(*v).text.clone();
                let t = self.t(*ty);
                if incoming.is_empty() {
                    let _ = writeln!(out, "  {text} = select i1 true, {t} undef, {t} undef");
                    continue;
                }
                let entries: Vec<String> = incoming
                    .iter()
                    .map(|(pred, args)| {
                        let arg = self.val(args[k]);
                        format!("[ {}, %b{pred} ]", arg.text)
                    })
                    .collect();
                let _ = writeln!(out, "  {text} = phi {t} {}", entries.join(", "));
            }
            let body = self.blocks[i].body.clone();
            out.push_str(&self.branch_weights(&body));
            if !self.blocks[i].terminated {
                out.push_str("  unreachable\n");
            }
        }
        out.push_str("}\n");
        let mut meta = vec![format!(
            "!{} = distinct !DISubprogram(name: \"{name}\", scope: !3, file: !3, line: 1, type: !4, spFlags: DISPFlagDefinition, unit: !0)",
            self.meta_base
        )];
        for (k, line) in self.lines.iter().enumerate() {
            meta.push(format!(
                "!{} = !DILocation(line: {line}, scope: !{})",
                self.meta_base + 1 + k as u32,
                self.meta_base
            ));
        }
        let _ = std::mem::take(&mut self.intrinsics);
        (out, meta)
    }
}

impl Builder for Ll<'_> {
    type Value = u32;
    type Block = u32;
    type Var = u32;
    type Func = u32;
    type Sig = u32;

    fn entry_block(&mut self) -> (u32, Vec<u32>) {
        let b = self.create_block();
        // The parameters are the first values (variables may follow).
        let params: Vec<u32> = (0..self.nparams).collect();
        (b, params)
    }

    fn create_block(&mut self) -> u32 {
        self.blocks.push(BlockData {
            params: Vec::new(),
            incoming: Vec::new(),
            body: String::new(),
            terminated: false,
            cold: false,
        });
        (self.blocks.len() - 1) as u32
    }

    fn switch_to_block(&mut self, block: u32) {
        self.cur = block;
    }

    fn append_block_param(&mut self, block: u32, ty: Ty) -> u32 {
        let id = self.vals.len() as u32;
        self.vals.push(Val {
            text: format!("%v{id}"),
            ty,
        });
        self.blocks[block as usize].params.push((id, ty));
        id
    }

    fn block_params(&self, block: u32) -> Vec<u32> {
        self.blocks[block as usize]
            .params
            .iter()
            .map(|(v, _)| *v)
            .collect()
    }

    fn declare_var(&mut self, ty: Ty) -> u32 {
        let id = self.nvars;
        self.nvars += 1;
        let t = self.t(ty);
        let _ = writeln!(
            self.prologue,
            "  %var{id} = alloca {t}, align {}",
            align_of(ty)
        );
        // The type is kept in a value slot (the variable's address).
        self.vals.push(Val {
            text: format!("%var{id}"),
            ty,
        });
        (self.vals.len() - 1) as u32
    }

    fn def_var(&mut self, var: u32, v: u32) {
        let ty = self.val(var).ty;
        let v = self.coerce(v, ty);
        let (vt, name) = (self.tv(v), self.val(var).text.clone());
        let pt = self.pt(ty);
        self.emit(&format!("store {vt}, {pt} {name}, align {}", align_of(ty)));
    }

    fn use_var(&mut self, var: u32) -> u32 {
        let ty = self.val(var).ty;
        let name = self.val(var).text.clone();
        let (t, pt) = (self.t(ty), self.pt(ty));
        self.def(ty, format!("load {t}, {pt} {name}, align {}", align_of(ty)))
    }

    fn stack_slot(&mut self, size: u32, align_log2: u8) -> u32 {
        let id = self.nslots;
        self.nslots += 1;
        let align = 1u32 << align_log2;
        let _ = writeln!(
            self.prologue,
            "  %slot{id} = alloca [{size} x i8], align {}",
            align.max(8)
        );
        if self.opaque {
            self.new_val(format!("%slot{id}"), Ty::Ptr)
        } else {
            let _ = writeln!(
                self.prologue,
                "  %slotp{id} = bitcast [{size} x i8]* %slot{id} to i8*"
            );
            self.new_val(format!("%slotp{id}"), Ty::Ptr)
        }
    }

    fn get_stack_pointer(&mut self) -> u32 {
        let pt = self.t(Ty::Ptr);
        self.intrinsic("stacksave");
        self.def(Ty::Ptr, format!("call {pt} @llvm.stacksave()"))
    }

    fn iconst(&mut self, ty: Ty, v: i64) -> u32 {
        match ty {
            Ty::Ptr => {
                if v == 0 {
                    self.new_val("null".to_string(), Ty::Ptr)
                } else {
                    let pt = self.t(Ty::Ptr);
                    self.def(Ty::Ptr, format!("inttoptr i64 {v} to {pt}"))
                }
            }
            Ty::I8 => self.new_val((v as i8).to_string(), ty),
            Ty::I32 => self.new_val((v as i32).to_string(), ty),
            _ => self.new_val(v.to_string(), ty),
        }
    }

    fn f64const(&mut self, v: f64) -> u32 {
        self.new_val(format!("0x{:016X}", v.to_bits()), Ty::F64)
    }

    fn iadd(&mut self, a: u32, b: u32) -> u32 {
        let (ta, tb) = (self.val(a).ty, self.val(b).ty);
        if ta == Ty::Ptr || tb == Ty::Ptr {
            let (p, i) = if ta == Ty::Ptr { (a, b) } else { (b, a) };
            let i = self.coerce(i, Ty::I64);
            let (pt, it) = (self.val(p).text.clone(), self.val(i).text.clone());
            let ptr = self.t(Ty::Ptr);
            return self.def(Ty::Ptr, format!("getelementptr i8, {ptr} {pt}, i64 {it}"));
        }
        self.binop("add", a, b)
    }

    fn isub(&mut self, a: u32, b: u32) -> u32 {
        if self.val(a).ty == Ty::Ptr {
            let b = self.coerce(b, Ty::I64);
            let bt = self.val(b).text.clone();
            let neg = self.def(Ty::I64, format!("sub i64 0, {bt}"));
            return self.iadd(a, neg);
        }
        self.binop("sub", a, b)
    }

    fn imul(&mut self, a: u32, b: u32) -> u32 {
        self.binop("mul", a, b)
    }

    fn smulhi(&mut self, a: u32, b: u32) -> u32 {
        let a = self.coerce(a, Ty::I64);
        let b = self.coerce(b, Ty::I64);
        let (at, bt) = (self.val(a).text.clone(), self.val(b).text.clone());
        let wa = self.emit_tmp(format!("sext i64 {at} to i128"));
        let wb = self.emit_tmp(format!("sext i64 {bt} to i128"));
        let m = self.emit_tmp(format!("mul i128 {wa}, {wb}"));
        let hi = self.emit_tmp(format!("lshr i128 {m}, 64"));
        self.def(Ty::I64, format!("trunc i128 {hi} to i64"))
    }

    fn sdiv(&mut self, a: u32, b: u32) -> u32 {
        self.binop("sdiv", a, b)
    }

    fn srem(&mut self, a: u32, b: u32) -> u32 {
        self.binop("srem", a, b)
    }

    fn band(&mut self, a: u32, b: u32) -> u32 {
        self.binop("and", a, b)
    }

    fn bor(&mut self, a: u32, b: u32) -> u32 {
        self.binop("or", a, b)
    }

    fn bxor(&mut self, a: u32, b: u32) -> u32 {
        self.binop("xor", a, b)
    }

    fn bnot(&mut self, a: u32) -> u32 {
        let ty = self.val(a).ty;
        let at = self.val(a).text.clone();
        self.def(ty, format!("xor {} {at}, -1", self.t(ty)))
    }

    fn iadd_imm(&mut self, a: u32, imm: i64) -> u32 {
        let ty = self.val(a).ty;
        let i = self.iconst(if ty == Ty::Ptr { Ty::I64 } else { ty }, imm);
        self.iadd(a, i)
    }

    fn imul_imm(&mut self, a: u32, imm: i64) -> u32 {
        let ty = self.val(a).ty;
        let i = self.iconst(ty, imm);
        self.binop("mul", a, i)
    }

    fn ishl_imm(&mut self, a: u32, imm: i64) -> u32 {
        let ty = self.val(a).ty;
        let at = self.val(a).text.clone();
        self.def(ty, format!("shl {} {at}, {imm}", self.t(ty)))
    }

    fn sshr_imm(&mut self, a: u32, imm: i64) -> u32 {
        let ty = self.val(a).ty;
        let at = self.val(a).text.clone();
        self.def(ty, format!("ashr {} {at}, {imm}", self.t(ty)))
    }

    fn sadd_overflow(&mut self, a: u32, b: u32) -> (u32, u32) {
        self.intrinsic("sadd");
        self.overflow("sadd", a, b)
    }

    fn ssub_overflow(&mut self, a: u32, b: u32) -> (u32, u32) {
        self.intrinsic("ssub");
        self.overflow("ssub", a, b)
    }

    fn smul_overflow(&mut self, a: u32, b: u32) -> (u32, u32) {
        self.intrinsic("smul");
        self.overflow("smul", a, b)
    }

    fn icmp(&mut self, cc: IntCC, a: u32, b: u32) -> u32 {
        let (ta, tb) = (self.val(a).ty, self.val(b).ty);
        let (a, b) = if ta == tb {
            (a, b)
        } else if ta == Ty::Ptr {
            (self.coerce(a, Ty::I64), self.coerce(b, Ty::I64))
        } else {
            (a, self.coerce(b, ta))
        };
        let pred = match cc {
            IntCC::Equal => "eq",
            IntCC::NotEqual => "ne",
            IntCC::SignedLessThan => "slt",
            IntCC::SignedLessThanOrEqual => "sle",
            IntCC::SignedGreaterThan => "sgt",
            IntCC::SignedGreaterThanOrEqual => "sge",
            IntCC::UnsignedLessThan => "ult",
            IntCC::UnsignedGreaterThan => "ugt",
            IntCC::UnsignedGreaterThanOrEqual => "uge",
        };
        let (at, bt) = (self.tv(a), self.val(b).text.clone());
        let t = self.emit_tmp(format!("icmp {pred} {at}, {bt}"));
        self.widen_i1(&t)
    }

    fn icmp_imm(&mut self, cc: IntCC, a: u32, imm: i64) -> u32 {
        let ty = self.val(a).ty;
        if ty == Ty::Ptr && imm == 0 {
            let pred = match cc {
                IntCC::Equal => "eq",
                IntCC::NotEqual => "ne",
                _ => unreachable!("pointer compared with null"),
            };
            let at = self.tv(a);
            let t = self.emit_tmp(format!("icmp {pred} {at}, null"));
            return self.widen_i1(&t);
        }
        let i = self.iconst(if ty == Ty::Ptr { Ty::I64 } else { ty }, imm);
        self.icmp(cc, a, i)
    }

    fn fcmp(&mut self, cc: FloatCC, a: u32, b: u32) -> u32 {
        let a = self.coerce(a, Ty::F64);
        let b = self.coerce(b, Ty::F64);
        let pred = match cc {
            FloatCC::Equal => "oeq",
            FloatCC::NotEqual => "une",
            FloatCC::LessThan => "olt",
            FloatCC::LessThanOrEqual => "ole",
            FloatCC::GreaterThan => "ogt",
            FloatCC::GreaterThanOrEqual => "oge",
        };
        let (at, bt) = (self.val(a).text.clone(), self.val(b).text.clone());
        let t = self.emit_tmp(format!("fcmp {pred} double {at}, {bt}"));
        self.widen_i1(&t)
    }

    fn fadd(&mut self, a: u32, b: u32) -> u32 {
        self.fbinop("fadd", a, b)
    }

    fn fsub(&mut self, a: u32, b: u32) -> u32 {
        self.fbinop("fsub", a, b)
    }

    fn fmul(&mut self, a: u32, b: u32) -> u32 {
        self.fbinop("fmul", a, b)
    }

    fn fdiv(&mut self, a: u32, b: u32) -> u32 {
        self.fbinop("fdiv", a, b)
    }

    fn fcvt_from_sint(&mut self, a: u32) -> u32 {
        let a = self.coerce(a, Ty::I64);
        let at = self.tv(a);
        self.def(Ty::F64, format!("sitofp {at} to double"))
    }

    fn bitcast(&mut self, ty: Ty, a: u32) -> u32 {
        self.coerce(a, ty)
    }

    fn uextend(&mut self, ty: Ty, a: u32) -> u32 {
        self.coerce(a, ty)
    }

    fn ireduce(&mut self, ty: Ty, a: u32) -> u32 {
        self.coerce(a, ty)
    }

    fn select(&mut self, c: u32, a: u32, b: u32) -> u32 {
        let ty = self.val(a).ty;
        let b = self.coerce(b, ty);
        let c1 = self.i1(c);
        let (at, bt) = (self.tv(a), self.tv(b));
        self.def(ty, format!("select i1 {c1}, {at}, {bt}"))
    }

    fn load(&mut self, ty: Ty, p: u32, off: i32) -> u32 {
        let addr = self.addr(p, off, ty);
        let (t, pt) = (self.t(ty), self.pt(ty));
        self.def(ty, format!("load {t}, {pt} {addr}, align {}", align_of(ty)))
    }

    fn uload8(&mut self, p: u32, off: i32) -> u32 {
        let v = self.load(Ty::I8, p, off);
        self.coerce(v, Ty::I64)
    }

    fn uload32(&mut self, p: u32, off: i32) -> u32 {
        let v = self.load(Ty::I32, p, off);
        self.coerce(v, Ty::I64)
    }

    fn store(&mut self, v: u32, p: u32, off: i32) {
        let ty = self.val(v).ty;
        let addr = self.addr(p, off, ty);
        let (vt, pt) = (self.tv(v), self.pt(ty));
        self.emit(&format!("store {vt}, {pt} {addr}, align {}", align_of(ty)));
    }

    fn jump(&mut self, block: u32, args: &[u32]) {
        let cur = self.cur;
        let args: Vec<u32> = args
            .iter()
            .zip(self.blocks[block as usize].params.clone())
            .map(|(a, (_, ty))| self.coerce(*a, ty))
            .collect();
        self.blocks[block as usize].incoming.push((cur, args));
        self.emit(&format!("br label %b{block}"));
        self.blocks[cur as usize].terminated = true;
    }

    fn brif(&mut self, c: u32, then: u32, then_args: &[u32], els: u32, els_args: &[u32]) {
        if then == els {
            // A phi takes one entry per predecessor: go through two.
            let (t, e) = (self.create_block(), self.create_block());
            self.brif(c, t, &[], e, &[]);
            self.switch_to_block(t);
            self.jump(then, then_args);
            self.switch_to_block(e);
            self.jump(els, els_args);
            return;
        }
        let cur = self.cur;
        let c1 = self.i1(c);
        for (block, args) in [(then, then_args), (els, els_args)] {
            let args: Vec<u32> = args
                .iter()
                .zip(self.blocks[block as usize].params.clone())
                .map(|(a, (_, ty))| self.coerce(*a, ty))
                .collect();
            self.blocks[block as usize].incoming.push((cur, args));
        }
        // The weights, if one side is cold, are decided when the function
        // is written out (a block is marked as it is filled).
        self.emit(&format!(
            "br i1 {c1}, label %b{then}, label %b{els}{PROF_MARK}{then},{els};"
        ));
        self.blocks[cur as usize].terminated = true;
    }

    fn set_cold(&mut self, block: u32) {
        self.blocks[block as usize].cold = true;
    }

    fn current_block(&self) -> u32 {
        self.cur
    }

    fn return_(&mut self, vals: &[u32]) {
        let rets = self.rets.clone();
        let vals: Vec<u32> = vals
            .iter()
            .zip(&rets)
            .map(|(v, ty)| self.coerce(*v, *ty))
            .collect();
        match vals.as_slice() {
            [] => self.emit("ret void"),
            [v] => {
                let vt = self.tv(*v);
                self.emit(&format!("ret {vt}"));
            }
            vs => {
                let st = ret_type(&rets, self.opaque);
                let mut agg = "undef".to_string();
                for (k, v) in vs.iter().enumerate() {
                    let vt = self.tv(*v);
                    agg = self.emit_tmp(format!("insertvalue {st} {agg}, {vt}, {k}"));
                }
                self.emit(&format!("ret {st} {agg}"));
            }
        }
        self.blocks[self.cur as usize].terminated = true;
    }

    fn call(&mut self, f: u32, args: &[u32]) -> Vec<u32> {
        let decl = &self.decls[f as usize];
        let (name, params, rets) = (decl.name.clone(), decl.params.clone(), decl.rets.clone());
        let callee = format!("@{name}");
        self.call_text(&callee, &params, &rets, args)
    }

    fn call_indirect(&mut self, sig: u32, callee: u32, args: &[u32]) -> Vec<u32> {
        let (params, rets) = (
            self.sigs[sig as usize].params.clone(),
            self.sigs[sig as usize].rets.clone(),
        );
        let callee = self.coerce(callee, Ty::Ptr);
        let mut text = self.val(callee).text.clone();
        if !self.opaque {
            let ft = fn_type(&params, &rets, false);
            text = self.emit_tmp(format!("bitcast i8* {text} to {ft}*"));
        }
        self.call_text(&text, &params, &rets, args)
    }

    fn set_line(&mut self, line: u32) {
        self.line = Some(line);
    }
}

impl Ll<'_> {
    fn call_text(&mut self, callee: &str, params: &[Ty], rets: &[Ty], args: &[u32]) -> Vec<u32> {
        assert_eq!(args.len(), params.len(), "arguments of {callee}");
        let args: Vec<String> = args
            .iter()
            .zip(params)
            .map(|(a, ty)| {
                let a = self.coerce(*a, *ty);
                self.tv(a)
            })
            .collect();
        let dbg = self.dbg();
        let rt = ret_type(rets, self.opaque);
        let call = format!("call {rt} {callee}({}){dbg}", args.join(", "));
        match rets {
            [] => {
                self.emit(&call);
                Vec::new()
            }
            [r] => vec![self.def(*r, call)],
            rs => {
                let agg = self.emit_tmp(call);
                rs.iter()
                    .enumerate()
                    .map(|(k, r)| self.def(*r, format!("extractvalue {rt} {agg}, {k}")))
                    .collect()
            }
        }
    }
}

// ----- the module -----------------------------------------------------------------------

/// The `clang` to compile with: `$QUARZ_CLANG`, or the first of `clang`
/// and the versioned names on `PATH`; with its major version.
fn find_clang() -> Result<(String, u32), String> {
    let candidates: Vec<String> = match std::env::var("QUARZ_CLANG") {
        Ok(c) => vec![c],
        Err(_) => std::iter::once("clang".to_string())
            .chain((14..=22).rev().map(|v| format!("clang-{v}")))
            .collect(),
    };
    for c in &candidates {
        let Ok(out) = Command::new(c).arg("--version").output() else {
            continue;
        };
        if !out.status.success() {
            continue;
        }
        let text = String::from_utf8_lossy(&out.stdout);
        // "... clang version 14.0.6 ..."
        let major = text
            .split("clang version ")
            .nth(1)
            .and_then(|rest| rest.split(['.', ' ']).next())
            .and_then(|v| v.parse::<u32>().ok())
            .unwrap_or(0);
        if major < 14 {
            return Err(format!("{c} is too old (clang 14 or later is needed)"));
        }
        return Ok((c.clone(), major));
    }
    Err("cannot find clang (install clang 14 or later, or set QUARZ_CLANG)".to_string())
}

/// The signature of a typed entry: the interpreter, the caller's
/// activation, the address of `self`, the parameters as machine values,
/// then the address of a `Value` for a result that does not fit; returns
/// the status and the result's bits.
fn typed_signature(sig: &unbox::TypedSig) -> (Vec<Ty>, Vec<Ty>) {
    let mut params = vec![Ty::Ptr, Ty::Ptr, Ty::Ptr];
    for p in &sig.params {
        params.push(match p {
            Num::Int => Ty::I64,
            Num::Float => Ty::F64,
        });
    }
    params.push(Ty::Ptr);
    (params, vec![Ty::I64])
}

/// Compile a module to the object file `object`.
pub fn compile(module: &Module, object: &Path) -> Result<(), String> {
    let (clang, major) = find_clang()?;
    let opaque = major >= 15;
    let ir = emit(module, opaque)?;
    let ll_path = object.with_extension("ll");
    std::fs::write(&ll_path, &ir).map_err(|e| format!("{}: {e}", ll_path.display()))?;
    let output = Command::new(&clang)
        .args(["-O2", "-c", "-x", "ir", "-Wno-override-module", "-o"])
        .arg(object)
        .arg(&ll_path)
        .output()
        .map_err(|e| format!("cannot run {clang}: {e}"))?;
    if std::env::var_os("QUARZ_KEEP_IR").is_none() {
        let _ = std::fs::remove_file(&ll_path);
    }
    if !output.status.success() {
        return Err(format!(
            "{clang} failed ({}):\n{}",
            output.status,
            String::from_utf8_lossy(&output.stderr)
        ));
    }
    Ok(())
}

/// Index of each runtime function in the declaration table.
struct RtIdx {
    h: Helpers<u32>,
    main: u32,
}

/// The module as LLVM IR text.
fn emit(module: &Module, opaque: bool) -> Result<String, String> {
    let (p, i32_, i64_) = (Ty::Ptr, Ty::I32, Ty::I64);
    let mut decls: Vec<FnDecl> = Vec::new();
    fn push(decls: &mut Vec<FnDecl>, name: &str, params: &[Ty], rets: &[Ty]) -> u32 {
        decls.push(FnDecl {
            name: name.to_string(),
            params: params.to_vec(),
            rets: rets.to_vec(),
        });
        (decls.len() - 1) as u32
    }
    let mut declare = |name: &str, params: &[Ty], rets: &[Ty]| push(&mut decls, name, params, rets);
    let rt = RtIdx {
        h: Helpers {
            exec: declare("qz_exec", &[p, p, i32_, i32_, i32_, p], &[i32_]),
            term: declare("qz_term", &[p, p, i32_, i32_, p], &[i32_]),
            block_param: declare("qz_block_param", &[p, p, i32_], &[]),
            frame_get: declare("qz_frame_get", &[p, i32_, i32_, p, i32_], &[]),
            frame_set: declare("qz_frame_set", &[p, i32_, i32_, p, i32_], &[]),
            load_const: declare("qz_load_const", &[p, i32_, i32_, p, i32_], &[]),
            interpolate: declare("qz_interpolate", &[p, p, i32_, i32_, i32_, p], &[i32_]),
            field_get: declare("qz_field_get", &[p, p, i32_, i32_, i32_], &[i32_]),
            field_set: declare("qz_field_set", &[p, p, i32_, i32_, i32_], &[i32_]),
            resume: declare("qz_resume", &[p, p, i32_, i32_, i32_, p, p, p], &[i32_]),
            enter_virtual: declare(
                "qz_enter_virtual",
                &[p, p, p, i32_, p, i32_, p, i32_, i32_, i64_, p, i32_],
                &[i32_],
            ),
            enter: declare(
                "qz_enter",
                &[
                    p, p, p, i32_, i32_, p, i32_, p, i32_, i32_, i32_, i32_, i64_,
                ],
                &[i32_],
            ),
            leave: declare("qz_leave", &[p, p, i32_, p, p, i32_, i32_], &[i32_]),
            push_call: declare("qz_push_call", &[p, p], &[]),
            pop_call: declare("qz_pop_call", &[p, p], &[]),
            stack_overflow: declare("qz_stack_overflow", &[p], &[i32_]),
            drop_value: declare("qz_drop_value", &[p], &[]),
            finalize: Some(declare("qz_finalize", &[p], &[])),
            clone_ptr: declare("qz_clone_ptr", &[p, p], &[]),
            call_static: declare(
                "qz_call_static",
                &[p, p, i32_, p, i32_, p, i32_, i32_, i32_],
                &[i32_],
            ),
            yield_: declare("qz_yield", &[p, p, p, p, i32_, i32_], &[i32_]),
            owned_call: declare(
                "qz_owned_call",
                &[p, p, i32_, p, i32_, i32_, i32_, p, i32_, i32_],
                &[i32_],
            ),
            hash_put_int: declare("qz_hash_put_int", &[p, i64_, i64_], &[i32_]),
            alloc_data: declare("qz_alloc_data", &[p, i32_, p, i32_, i32_], &[]),
            construct: declare("qz_construct", &[p, p, i32_, i32_, p, i32_, i32_], &[i32_]),
        },
        main: declare(
            "qz_main",
            &[p, i64_, p, i64_, i32_, p, i64_, i64_, i64_],
            &[i32_],
        ),
    };
    let body_params = [p, p, p];
    let funcs: Vec<u32> = (0..module.functions.len())
        .map(|i| declare(&format!("qz_fn_{i}"), &body_params, &[i32_]))
        .collect();
    let typed = unbox::typed_sigs(&module.functions, &module.world.methods);
    let typed_funcs: Vec<Option<u32>> = typed
        .iter()
        .enumerate()
        .map(|(i, t)| {
            t.as_ref().map(|sig| {
                let (params, rets) = typed_signature(sig);
                declare(&format!("qz_fn_{i}_t"), &params, &rets)
            })
        })
        .collect();
    // A typed function that may return before it needs a frame gets a
    // separate entry, which callers call (see `gen::Target::entry_of`).
    let entry_funcs: Vec<Option<u32>> = typed
        .iter()
        .enumerate()
        .map(|(i, t)| {
            let sig = t.as_ref()?;
            gen::typed_entry_region(
                &module.functions[i],
                &module.world.methods,
                &module.world.classes,
                &module.world.builtin,
                &typed,
                sig,
            )?;
            let (params, rets) = typed_signature(sig);
            Some(declare(&format!("qz_fn_{i}_e"), &params, &rets))
        })
        .collect();
    let nrt = rt.main as usize + 1;
    let sigs = vec![SigDecl {
        params: body_params.to_vec(),
        rets: vec![i32_],
    }];

    let mut out = String::new();
    out.push_str("; generated by quarz\n");
    for d in &decls[..nrt] {
        let ps: Vec<&str> = d.params.iter().map(|t| ty_str(*t, opaque)).collect();
        let _ = writeln!(
            out,
            "declare {} @{}({})",
            ret_type(&d.rets, opaque),
            d.name,
            ps.join(", ")
        );
    }
    let ptr = ty_str(Ty::Ptr, opaque);
    let _ = writeln!(out, "declare {ptr} @llvm.stacksave()");
    for name in ["sadd", "ssub", "smul"] {
        let _ = writeln!(
            out,
            "declare {{ i64, i1 }} @llvm.{name}.with.overflow.i64(i64, i64)"
        );
    }
    out.push('\n');

    // Metadata: !0 the unit, !1 and !2 the flags, !3 the file, !4 and !5
    // the (empty) subroutine type; functions take ids from !6 on.
    let mut meta: Vec<String> = Vec::new();
    // !0-!5 describe the unit, !6 and !7 are the branch weights.
    let mut meta_next: u32 = 8;
    let methods = &module.world.methods;
    // A `Release` runs deinitializers only in a program that has some.
    let has_deinit = methods
        .iter()
        .any(|m| m.name == "deinitialize" && m.func.is_some());
    let mut text = String::new();
    for (i, f) in module.functions.iter().enumerate() {
        let mut entries = vec![(None, funcs[i], None)];
        if let (Some(sig), Some(tf)) = (&typed[i], typed_funcs[i]) {
            entries.push((Some(sig.clone()), tf, None));
            if let Some(ef) = entry_funcs[i] {
                entries.push((Some(sig.clone()), ef, Some(tf)));
            }
        }
        for (sig, target, entry_of) in entries {
            let (params, rets) = match &sig {
                Some(s) => typed_signature(s),
                None => (body_params.to_vec(), vec![i32_]),
            };
            let mut b = Ll::new(&decls, &sigs, opaque, &params, &rets, meta_next);
            let mut callees: HashMap<FuncId, u32> = HashMap::new();
            let mut callees_typed: HashMap<FuncId, u32> = HashMap::new();
            for c in gen::direct_callees(f, methods) {
                callees.insert(c, funcs[c as usize]);
                if let Some(tf) = entry_funcs[c as usize].or(typed_funcs[c as usize]) {
                    callees_typed.insert(c, tf);
                }
            }
            let h = Helpers {
                resume: rt.h.resume,
                enter: rt.h.enter,
                enter_virtual: rt.h.enter_virtual,
                leave: rt.h.leave,
                push_call: rt.h.push_call,
                pop_call: rt.h.pop_call,
                stack_overflow: rt.h.stack_overflow,
                drop_value: rt.h.drop_value,
                finalize: rt.h.finalize.filter(|_| has_deinit),
                clone_ptr: rt.h.clone_ptr,
                exec: rt.h.exec,
                term: rt.h.term,
                block_param: rt.h.block_param,
                frame_get: rt.h.frame_get,
                frame_set: rt.h.frame_set,
                field_get: rt.h.field_get,
                load_const: rt.h.load_const,
                interpolate: rt.h.interpolate,
                field_set: rt.h.field_set,
                call_static: rt.h.call_static,
                yield_: rt.h.yield_,
                construct: rt.h.construct,
                alloc_data: rt.h.alloc_data,
                owned_call: rt.h.owned_call,
                hash_put_int: rt.h.hash_put_int,
            };
            gen::gen_function(
                gen::Target {
                    b: &mut b,
                    h,
                    callees,
                    callees_typed,
                    body_sig: 0,
                    lazy_act: true,
                    entry_of,
                },
                i as FuncId,
                f,
                methods,
                &module.functions,
                &module.world.classes,
                &module.world.builtin,
                sig.clone(),
                &typed,
            );
            // A typed entry's frame is found on the native stack: it must
            // stay one (no inlining, no tail calls).
            // An entry never shows in a backtrace (it calls the body to
            // do anything that could raise): it may be inlined into its
            // callers, and call the body as a tail call.
            let attrs = if entry_of.is_some() {
                "uwtable"
            } else if sig.is_some() {
                "noinline uwtable \"disable-tail-calls\"=\"true\""
            } else {
                "uwtable \"disable-tail-calls\"=\"true\""
            };
            let name = decls[target as usize].name.clone();
            let (fn_text, fn_meta) = b.finish(&name, attrs, &params);
            meta_next += fn_meta.len() as u32;
            meta.extend(fn_meta);
            text.push_str(&fn_text);
            text.push('\n');
        }
    }
    out.push_str(&text);

    // The serialized module and the table of compiled bodies.
    let bytes = quarz_ir::encode(module);
    let mut blob = String::with_capacity(bytes.len() * 4);
    for byte in &bytes {
        let _ = write!(blob, "\\{byte:02X}");
    }
    let _ = writeln!(
        out,
        "@qz_module_blob = internal constant [{} x i8] c\"{blob}\", align 8",
        bytes.len()
    );
    let n = module.functions.len();
    let entries: Vec<String> = (0..n)
        .map(|i| {
            if opaque {
                format!("ptr @qz_fn_{i}")
            } else {
                let ft = fn_type(&body_params, &[i32_], false);
                format!("i8* bitcast ({ft}* @qz_fn_{i} to i8*)")
            }
        })
        .collect();
    let _ = writeln!(
        out,
        "@qz_fn_table = internal constant [{n} x {ptr}] [{}], align 8",
        entries.join(", ")
    );
    // main(argc, argv) -> qz_main(blob, len, table, n, argc, argv, layout, vec_layout, flags)
    let blob_ptr = if opaque {
        "ptr @qz_module_blob".to_string()
    } else {
        format!(
            "i8* getelementptr ([{} x i8], [{} x i8]* @qz_module_blob, i64 0, i64 0)",
            bytes.len(),
            bytes.len()
        )
    };
    let table_ptr = if opaque {
        "ptr @qz_fn_table".to_string()
    } else {
        format!("i8* bitcast ([{n} x i8*]* @qz_fn_table to i8*)")
    };
    let _ = writeln!(
        out,
        "define i32 @main(i32 %argc, {ptr} %argv) {{\n  %code = call i32 @qz_main({blob_ptr}, i64 {}, {table_ptr}, i64 {n}, i32 %argc, {ptr} %argv, i64 {}, i64 {}, i64 1)\n  ret i32 %code\n}}",
        bytes.len(),
        L::SIGNATURE as i64,
        L::vec_layout_packed() as i64
    );
    let _ = writeln!(
        out,
        "\n!llvm.dbg.cu = !{{!0}}\n!llvm.module.flags = !{{!1, !2}}\n!0 = distinct !DICompileUnit(language: DW_LANG_C, file: !3, producer: \"quarz\", isOptimized: true, runtimeVersion: 0, emissionKind: LineTablesOnly)\n!1 = !{{i32 2, !\"Debug Info Version\", i32 3}}\n!2 = !{{i32 2, !\"Dwarf Version\", i32 4}}\n!3 = !DIFile(filename: \"quarz\", directory: \"/\")\n!4 = !DISubroutineType(types: !5)\n!5 = !{{}}\n!6 = !{{!\"branch_weights\", i32 1, i32 2000}}\n!7 = !{{!\"branch_weights\", i32 2000, i32 1}}"
    );
    for m in &meta {
        out.push_str(m);
        out.push('\n');
    }
    Ok(out)
}
