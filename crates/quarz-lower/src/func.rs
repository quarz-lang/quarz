//! Building one QIR function from an AST body.

use std::collections::{HashMap, HashSet};

use quarz_ir::*;
use quarz_syntax::ast::{self, Arg, Block as AstBlock, Expr, ExprKind, LValue, ParamKind, StrPart};
use quarz_syntax::token::OpAssign;
use quarz_syntax::Span;
use quarz_types::{CallTarget, ConstTarget, Output, VarRef, World};

use crate::capture::captured_slots;
use crate::rtworld::rt_type;
use crate::{Lowerer, UnitInput};

/// Key for constant-pool deduplication (floats by bit pattern).
#[derive(Clone, PartialEq, Eq, Hash)]
enum ConstKey {
    Nil,
    Bool(bool),
    Int(i64),
    BigInt(String, u8),
    Float(u64),
    Str(String),
    Symbol(String),
    Regexp(String, String),
    Bytes(Vec<u8>),
}

struct LoopCtx {
    next: BlockId,
    exit: BlockId,
    result: Reg,
    /// Number of handler regions open outside the loop.
    depth: usize,
}

/// A protected region: its handler, and its `ensure` body when a jump out
/// of the region must run it first.
struct Region<'a> {
    handler: Option<Handler>,
    ensure: Option<&'a [Expr]>,
}

/// Evaluated call arguments.
struct Args {
    pos: Vec<Reg>,
    splat: bool,
    kw: Vec<(u32, Reg)>,
    kw_splat: Option<Reg>,
    block: Option<Reg>,
}

pub struct FnBuilder<'a> {
    lw: &'a mut Lowerer,
    world: &'a World,
    out: &'a Output,
    func: Function,
    cur: BlockId,
    dead: bool,
    const_index: HashMap<ConstKey, u32>,
    /// Whether each enclosing function level (outermost first, this one
    /// last) allocates a heap frame.
    levels: Vec<bool>,
    captured: HashSet<u32>,
    all_captured: bool,
    slot_regs: HashMap<u32, Reg>,
    loops: Vec<LoopCtx>,
    handlers: Vec<Region<'a>>,
    retry_targets: Vec<BlockId>,
    method: Option<MethodId>,
    class_id: Option<ClassId>,
    is_block: bool,
    is_lambda: bool,
    file: u32,
}

impl<'a> FnBuilder<'a> {
    #[allow(clippy::too_many_arguments)]
    fn new(
        lw: &'a mut Lowerer,
        world: &'a World,
        out: &'a Output,
        name: String,
        kind: FuncKind,
        file: u32,
        outer_levels: &[bool],
        captured: HashSet<u32>,
        all_captured: bool,
        method: Option<MethodId>,
        class_id: Option<ClassId>,
    ) -> FnBuilder<'a> {
        let has_frame = all_captured || !captured.is_empty();
        let mut levels = outer_levels.to_vec();
        levels.push(has_frame);
        let mut func = Function::new(name, kind, file);
        func.blocks.push(quarz_ir::Block::default());
        if has_frame && !all_captured {
            func.frame_size = captured.iter().copied().max().unwrap_or(0) + 1;
        }
        FnBuilder {
            lw,
            world,
            out,
            func,
            cur: 0,
            dead: false,
            const_index: HashMap::new(),
            levels,
            captured,
            all_captured,
            slot_regs: HashMap::new(),
            loops: Vec::new(),
            handlers: vec![Region {
                handler: None,
                ensure: None,
            }],
            retry_targets: Vec::new(),
            method,
            class_id,
            is_block: false,
            is_lambda: false,
            file,
        }
    }

    fn finish(self) -> Function {
        self.func
    }

    // ----- entry points ------------------------------------------------------------------

    pub fn method(
        lw: &'a mut Lowerer,
        world: &'a World,
        out: &'a Output,
        mid: MethodId,
        body: &'a [Expr],
    ) -> Function {
        let m = world.method(mid);
        let defaults: Vec<&Expr> = m
            .params
            .iter()
            .filter_map(|p| p.default.as_deref())
            .collect();
        let nparams = m.params.len() as u32 + u32::from(m.block.is_some());
        let captured = captured_slots(body, &defaults, out, nparams);
        let name = format!("{}#{}", world.class(m.owner).name, m.name);
        let mut b = FnBuilder::new(
            lw,
            world,
            out,
            name,
            FuncKind::Method(mid),
            m.file,
            &[],
            captured,
            false,
            Some(mid),
            Some(m.owner),
        );
        // Parameters: bound by the runtime into argument slots in order;
        // the `&block` parameter comes last.
        for (i, p) in m.params.iter().enumerate() {
            let slot = i as u32;
            let r = VarRef { depth: 0, slot };
            match &p.default {
                Some(default) => {
                    let has = b.reg();
                    b.emit(Inst::HasArg {
                        dst: has,
                        index: slot,
                    });
                    let given = b.new_block();
                    let missing = b.new_block();
                    let join = b.new_block();
                    b.term(Term::Branch {
                        cond: has,
                        then: given,
                        els: missing,
                    });
                    b.switch(given);
                    let v = b.reg();
                    b.emit(Inst::Arg {
                        dst: v,
                        index: slot,
                    });
                    b.store_var(r, v);
                    b.term(Term::Jump(join));
                    b.switch(missing);
                    let v = b.expr(default);
                    b.store_var(r, v);
                    b.term(Term::Jump(join));
                    b.switch(join);
                }
                None => {
                    let v = b.reg();
                    b.emit(Inst::Arg {
                        dst: v,
                        index: slot,
                    });
                    b.store_var(r, v);
                }
            }
        }
        if m.block.is_some() {
            let slot = m.params.len() as u32;
            let v = b.reg();
            b.emit(Inst::BlockParam { dst: v });
            b.store_var(VarRef { depth: 0, slot }, v);
        }
        // `def initialize(@x: Int)`.
        for (i, p) in m.params.iter().enumerate() {
            if p.assigns_ivar {
                if let Some(idx) = world.field_index(m.owner, &p.name) {
                    let v = b.load_var(VarRef {
                        depth: 0,
                        slot: i as u32,
                    });
                    let obj = b.self_reg();
                    b.emit(Inst::FieldSet {
                        obj,
                        index: idx as u32,
                        src: v,
                    });
                }
            }
        }
        let v = b.body(body);
        b.term(Term::Return(v));
        b.finish()
    }

    /// A constant initializer or field default: one expression evaluated
    /// with `self` set by the runtime.
    pub fn init(
        lw: &'a mut Lowerer,
        world: &'a World,
        out: &'a Output,
        name: String,
        file: u32,
        class_id: Option<ClassId>,
        value: &'a Expr,
    ) -> Function {
        let captured = captured_slots(std::slice::from_ref(value), &[], out, 0);
        let mut b = FnBuilder::new(
            lw,
            world,
            out,
            name,
            FuncKind::Init,
            file,
            &[],
            captured,
            false,
            None,
            class_id,
        );
        let v = b.expr(value);
        b.term(Term::Return(v));
        b.finish()
    }

    pub fn top_level(
        lw: &'a mut Lowerer,
        world: &'a World,
        out: &'a Output,
        unit: &'a UnitInput<'a>,
    ) -> Function {
        let captured = captured_slots(unit.body, &[], out, 0);
        let kind = if unit.repl {
            FuncKind::Repl
        } else {
            FuncKind::TopLevel
        };
        let mut b = FnBuilder::new(
            lw,
            world,
            out,
            format!("top level of {}", unit.name),
            kind,
            unit.file,
            &[],
            captured,
            unit.repl,
            None,
            Some(unit.main_class),
        );
        let v = b.body(unit.body);
        b.term(Term::Return(v));
        b.finish()
    }

    /// Lower a block literal or lambda to its own function.
    fn block_function(&mut self, block: &'a AstBlock, call_id: u32, is_lambda: bool) -> FuncId {
        let params: Vec<&ast::Param> = block
            .params
            .list
            .iter()
            .filter(|p| p.kind != ParamKind::Block)
            .collect();
        let defaults: Vec<&Expr> = params.iter().filter_map(|p| p.default.as_ref()).collect();
        let captured = captured_slots(&block.body, &defaults, self.out, params.len() as u32);
        let id = self.lw.alloc_func();
        let name = format!(
            "{} in {}",
            if is_lambda { "lambda" } else { "block" },
            self.func.name
        );
        let mut b = FnBuilder::new(
            &mut *self.lw,
            self.world,
            self.out,
            name,
            FuncKind::Block,
            self.file,
            &self.levels,
            captured,
            false,
            self.method,
            self.class_id,
        );
        b.is_block = true;
        b.is_lambda = is_lambda;
        b.func.param_kinds = params
            .iter()
            .map(|p| match p.kind {
                ParamKind::Positional => RtParamKind::Positional,
                ParamKind::Rest => RtParamKind::Rest,
                ParamKind::KeywordOnly => RtParamKind::KeywordOnly,
                ParamKind::KeywordRest => RtParamKind::KeywordRest,
                ParamKind::Block => RtParamKind::Block,
            })
            .collect();
        let required = params
            .iter()
            .filter(|p| p.kind == ParamKind::Positional && p.default.is_none())
            .count() as i32;
        let optional = params
            .iter()
            .any(|p| p.kind == ParamKind::Rest || p.default.is_some());
        b.func.arity = if optional { -(required + 1) } else { required };
        for (i, p) in params.iter().enumerate() {
            let slot = i as u32;
            let r = VarRef { depth: 0, slot };
            match &p.default {
                Some(default) => {
                    let has = b.reg();
                    b.emit(Inst::HasArg {
                        dst: has,
                        index: slot,
                    });
                    let given = b.new_block();
                    let missing = b.new_block();
                    let join = b.new_block();
                    b.term(Term::Branch {
                        cond: has,
                        then: given,
                        els: missing,
                    });
                    b.switch(given);
                    let v = b.reg();
                    b.emit(Inst::Arg {
                        dst: v,
                        index: slot,
                    });
                    b.store_var(r, v);
                    b.term(Term::Jump(join));
                    b.switch(missing);
                    let v = b.expr(default);
                    b.store_var(r, v);
                    b.term(Term::Jump(join));
                    b.switch(join);
                }
                None => {
                    let v = b.reg();
                    b.emit(Inst::Arg {
                        dst: v,
                        index: slot,
                    });
                    b.store_var(r, v);
                }
            }
        }
        let v = b.body(&block.body);
        b.term(Term::Return(v));
        let f = b.finish();
        let _ = call_id;
        self.lw.set_func(id, f);
        id
    }

    // ----- building blocks ------------------------------------------------------------------

    fn reg(&mut self) -> Reg {
        let r = self.func.nregs;
        self.func.nregs += 1;
        r
    }

    fn emit(&mut self, inst: Inst) {
        if self.dead {
            return;
        }
        self.func.blocks[self.cur as usize].insts.push(inst);
    }

    fn new_block(&mut self) -> BlockId {
        let id = self.func.blocks.len() as BlockId;
        self.func.blocks.push(quarz_ir::Block {
            insts: Vec::new(),
            term: Term::Unreachable,
            handler: self.handlers.last().unwrap().handler,
        });
        id
    }

    fn switch(&mut self, b: BlockId) {
        self.cur = b;
        self.dead = false;
    }

    fn term(&mut self, t: Term) {
        if self.dead {
            return;
        }
        self.func.blocks[self.cur as usize].term = t;
        self.dead = true;
    }

    fn const_idx(&mut self, c: Constant) -> u32 {
        let key = match &c {
            Constant::Nil => ConstKey::Nil,
            Constant::Bool(b) => ConstKey::Bool(*b),
            Constant::Int(i) => ConstKey::Int(*i),
            Constant::BigInt { digits, base } => ConstKey::BigInt(digits.clone(), *base),
            Constant::Float(f) => ConstKey::Float(f.to_bits()),
            Constant::Str(s) => ConstKey::Str(s.clone()),
            Constant::Symbol(s) => ConstKey::Symbol(s.clone()),
            Constant::Regexp { source, flags } => ConstKey::Regexp(source.clone(), flags.clone()),
            Constant::Bytes(b) => ConstKey::Bytes(b.clone()),
        };
        if let Some(i) = self.const_index.get(&key) {
            return *i;
        }
        let i = self.func.consts.len() as u32;
        self.func.consts.push(c);
        self.const_index.insert(key, i);
        i
    }

    fn load_const(&mut self, c: Constant) -> Reg {
        let idx = self.const_idx(c);
        let dst = self.reg();
        self.emit(Inst::LoadConst { dst, idx });
        dst
    }

    fn nil(&mut self) -> Reg {
        self.load_const(Constant::Nil)
    }

    fn self_reg(&mut self) -> Reg {
        let dst = self.reg();
        self.emit(Inst::SelfRef { dst });
        dst
    }

    fn sym_const(&mut self, name: &str) -> u32 {
        self.const_idx(Constant::Symbol(name.to_string()))
    }

    fn str_const(&mut self, s: &str) -> u32 {
        self.const_idx(Constant::Str(s.to_string()))
    }

    // ----- leaving protected regions ---------------------------------------------------------

    /// Emit the `ensure` bodies of the regions opened since `depth`
    /// (innermost first), as a jump out of them must run them. The
    /// regions are popped so that the bodies run under the outer
    /// handlers; the caller restores them after its terminator.
    fn leave_regions(&mut self, depth: usize) -> Vec<Region<'a>> {
        let mut popped = Vec::new();
        while self.handlers.len() > depth {
            let region = self.handlers.pop().unwrap();
            if let Some(body) = region.ensure {
                // Continue in a block covered by the outer handler.
                let b = self.new_block();
                self.term(Term::Jump(b));
                self.switch(b);
                self.body(body);
            }
            popped.push(region);
        }
        popped.reverse();
        popped
    }

    /// `return` from the function, running the `ensure` bodies it leaves.
    fn return_through_ensures(&mut self, v: Reg) {
        let restore = self.leave_regions(1);
        self.term(Term::Return(v));
        self.handlers.extend(restore);
    }

    // ----- variables -----------------------------------------------------------------------

    fn var_ref(&self, span: Span) -> Option<VarRef> {
        self.out.var_refs.get(&span).copied()
    }

    /// Translate a checker depth into a heap-frame depth: levels without a
    /// frame of their own do not appear in the frame chain.
    fn frame_depth(&self, depth: u32) -> u32 {
        let n = self.levels.len() - 1;
        let target = n - depth as usize;
        self.levels[target + 1..=n].iter().filter(|h| **h).count() as u32
    }

    fn is_captured(&self, slot: u32) -> bool {
        self.all_captured || self.captured.contains(&slot)
    }

    fn slot_reg(&mut self, slot: u32) -> Reg {
        if let Some(r) = self.slot_regs.get(&slot) {
            return *r;
        }
        let r = self.reg();
        // Registers start as nil; a variable read before assignment is nil.
        self.slot_regs.insert(slot, r);
        r
    }

    fn load_var(&mut self, r: VarRef) -> Reg {
        if r.depth == 0 && !self.is_captured(r.slot) {
            let src = self.slot_reg(r.slot);
            let dst = self.reg();
            self.emit(Inst::Move { dst, src });
            return dst;
        }
        let depth = self.frame_depth(r.depth);
        let dst = self.reg();
        self.emit(Inst::FrameGet {
            dst,
            depth,
            slot: r.slot,
        });
        dst
    }

    fn store_var(&mut self, r: VarRef, src: Reg) {
        if r.depth == 0 && !self.is_captured(r.slot) {
            let dst = self.slot_reg(r.slot);
            self.emit(Inst::Move { dst, src });
            return;
        }
        let depth = self.frame_depth(r.depth);
        self.emit(Inst::FrameSet {
            depth,
            slot: r.slot,
            src,
        });
    }

    fn var_loc(&mut self, r: VarRef) -> VarLoc {
        if r.depth == 0 && !self.is_captured(r.slot) {
            VarLoc::Reg(self.slot_reg(r.slot))
        } else {
            VarLoc::Frame {
                depth: self.frame_depth(r.depth),
                slot: r.slot,
            }
        }
    }

    fn store_site(&mut self, span: Span, src: Reg) {
        if let Some(r) = self.var_ref(span) {
            self.store_var(r, src);
        }
    }

    // ----- expressions ---------------------------------------------------------------------

    fn body(&mut self, exprs: &'a [Expr]) -> Reg {
        let mut last = None;
        for e in exprs {
            last = Some(self.expr(e));
        }
        match last {
            Some(r) => r,
            None => self.nil(),
        }
    }

    fn expr(&mut self, e: &'a Expr) -> Reg {
        use ExprKind::*;
        match &e.kind {
            Nil => self.nil(),
            True => self.load_const(Constant::Bool(true)),
            False => self.load_const(Constant::Bool(false)),
            SelfRef => self.self_reg(),
            Int(lit) => {
                let as_float = self.out.float_literals.contains(&e.id);
                match lit.value {
                    Some(i) if as_float => self.load_const(Constant::Float(i as f64)),
                    Some(i) => self.load_const(Constant::Int(i)),
                    None if as_float => {
                        let f = if lit.base == 10 {
                            lit.digits.parse::<f64>().unwrap_or(f64::INFINITY)
                        } else {
                            f64::INFINITY
                        };
                        self.load_const(Constant::Float(f))
                    }
                    None => self.load_const(Constant::BigInt {
                        digits: lit.digits.clone(),
                        base: lit.base,
                    }),
                }
            }
            Float(f) => self.load_const(Constant::Float(*f)),
            Bytes(bytes) => self.load_const(Constant::Bytes(bytes.clone())),
            Str(parts) => self.str_parts(parts),
            Symbol(name) => self.load_const(Constant::Symbol(name.clone())),
            DSymbol(parts) => {
                let s = self.str_parts(parts);
                let dst = self.reg();
                self.emit(Inst::ToSym { dst, src: s });
                dst
            }
            Regexp { parts, flags } => {
                if parts.iter().all(|p| matches!(p, StrPart::Lit(_))) {
                    let source: String = parts
                        .iter()
                        .map(|p| match p {
                            StrPart::Lit(s) => s.as_str(),
                            _ => "",
                        })
                        .collect();
                    self.load_const(Constant::Regexp {
                        source,
                        flags: flags.clone(),
                    })
                } else {
                    let source = self.str_parts(parts);
                    let dst = self.reg();
                    self.emit(Inst::MakeRegexp {
                        dst,
                        source,
                        flags: flags.clone(),
                    });
                    dst
                }
            }
            Magic(m) => match m {
                ast::Magic::File => {
                    let name = self
                        .lw
                        .file_names
                        .get(self.file as usize)
                        .cloned()
                        .unwrap_or_default();
                    self.load_const(Constant::Str(name))
                }
                ast::Magic::Line => self.load_const(Constant::Int(0)),
                ast::Magic::Method => match self.method {
                    Some(mid) => {
                        let name = self.world.method(mid).name.clone();
                        self.load_const(Constant::Str(name))
                    }
                    None => self.nil(),
                },
            },
            Array(items) => {
                let mut regs = Vec::new();
                for a in items {
                    match a {
                        Arg::Positional(x) => regs.push(ArrayItem {
                            reg: self.expr(x),
                            splat: false,
                        }),
                        Arg::Splat(x) => regs.push(ArrayItem {
                            reg: self.expr(x),
                            splat: true,
                        }),
                        _ => {}
                    }
                }
                let dst = self.reg();
                self.emit(Inst::MakeArray { dst, items: regs });
                dst
            }
            Hash(entries) => {
                let mut items = Vec::new();
                for en in entries {
                    match en {
                        ast::HashEntry::Pair { key, value } => {
                            let k = self.expr(key);
                            let v = self.expr(value);
                            items.push(HashItem::Pair(k, v));
                        }
                        ast::HashEntry::DoubleSplat(x) => {
                            let h = self.expr(x);
                            items.push(HashItem::Splat(h));
                        }
                    }
                }
                let dst = self.reg();
                self.emit(Inst::MakeHash { dst, items });
                dst
            }
            Range { lo, hi, exclusive } => {
                let lo = lo.as_ref().map(|x| self.expr(x));
                let hi = hi.as_ref().map(|x| self.expr(x));
                let dst = self.reg();
                self.emit(Inst::MakeRange {
                    dst,
                    lo,
                    hi,
                    exclusive: *exclusive,
                });
                dst
            }
            Lambda(block) => {
                let func = self.block_function(block, e.id, true);
                let dst = self.reg();
                self.emit(Inst::MakeBlock {
                    dst,
                    func,
                    destructure: None,
                    is_lambda: true,
                });
                dst
            }
            Local(_) => match self.var_ref(e.span) {
                Some(r) => self.load_var(r),
                None => self.nil(),
            },
            IVar(name) => {
                let index = self.ivar_index(e.id, name);
                let obj = self.self_reg();
                let dst = self.reg();
                self.emit(Inst::FieldGet { dst, obj, index });
                dst
            }
            Const(_) | TypeApp(_) => match self.out.const_targets.get(&e.id) {
                Some(ConstTarget::Class(cid)) => {
                    let dst = self.reg();
                    self.emit(Inst::ClassRef { dst, class: *cid });
                    dst
                }
                Some(ConstTarget::VariantSingleton(cid)) => {
                    let dst = self.reg();
                    self.emit(Inst::VariantSingleton { dst, class: *cid });
                    dst
                }
                Some(ConstTarget::Const(cid)) => {
                    let dst = self.reg();
                    self.emit(Inst::ConstGet { dst, id: *cid });
                    dst
                }
                None => self.nil(),
            },
            Call(call) => self.call(e, call),
            MethodRef { recv, name } => {
                let r = self.expr(recv);
                let name = self.str_const(name);
                let dst = self.reg();
                self.emit(Inst::MethodRef { dst, recv: r, name });
                dst
            }
            Yield(args) => {
                let a = self.args(args);
                let dst = self.reg();
                self.emit(Inst::Call {
                    dst,
                    kind: CallKind::Yield,
                    recv: None,
                    args: a.pos,
                    splat: a.splat,
                    kw: a.kw,
                    kw_splat: a.kw_splat,
                    block: a.block,
                });
                dst
            }
            Super { args, block } => self.super_call(e, args.as_deref(), block.as_deref()),
            Assign { target, value } => self.assign(e, target, value),
            OpAssign { target, op, value } => self.op_assign(e, target, *op, value),
            MultiAssign { targets, value } => {
                let v = self.expr(value);
                self.assign_multi(targets, v);
                v
            }
            TypedDecl { value, .. } => {
                let v = self.expr(value);
                self.store_site(e.span, v);
                v
            }
            And(a, b) => {
                let res = self.reg();
                let l = self.expr(a);
                self.emit(Inst::Move { dst: res, src: l });
                let rhs = self.new_block();
                let join = self.new_block();
                self.term(Term::Branch {
                    cond: l,
                    then: rhs,
                    els: join,
                });
                self.switch(rhs);
                let r = self.expr(b);
                self.emit(Inst::Move { dst: res, src: r });
                self.term(Term::Jump(join));
                self.switch(join);
                res
            }
            Or(a, b) => {
                let res = self.reg();
                let l = self.expr(a);
                self.emit(Inst::Move { dst: res, src: l });
                let rhs = self.new_block();
                let join = self.new_block();
                self.term(Term::Branch {
                    cond: l,
                    then: join,
                    els: rhs,
                });
                self.switch(rhs);
                let r = self.expr(b);
                self.emit(Inst::Move { dst: res, src: r });
                self.term(Term::Jump(join));
                self.switch(join);
                res
            }
            Not(a) => {
                let v = self.expr(a);
                let dst = self.reg();
                self.emit(Inst::Not { dst, src: v });
                dst
            }
            If { cond, then, els } => {
                let res = self.reg();
                let c = self.expr(cond);
                let then_b = self.new_block();
                let else_b = self.new_block();
                let join = self.new_block();
                self.term(Term::Branch {
                    cond: c,
                    then: then_b,
                    els: else_b,
                });
                self.switch(then_b);
                let v = self.body(then);
                self.emit(Inst::Move { dst: res, src: v });
                self.term(Term::Jump(join));
                self.switch(else_b);
                let v = match els {
                    Some(els) => self.body(els),
                    None => self.nil(),
                };
                self.emit(Inst::Move { dst: res, src: v });
                self.term(Term::Jump(join));
                self.switch(join);
                res
            }
            While {
                cond,
                body,
                negate,
                do_while,
            } => {
                let res = self.nil();
                let cond_b = self.new_block();
                let body_b = self.new_block();
                let exit_b = self.new_block();
                self.term(Term::Jump(if *do_while { body_b } else { cond_b }));
                self.switch(cond_b);
                let c = self.expr(cond);
                if *negate {
                    self.term(Term::Branch {
                        cond: c,
                        then: exit_b,
                        els: body_b,
                    });
                } else {
                    self.term(Term::Branch {
                        cond: c,
                        then: body_b,
                        els: exit_b,
                    });
                }
                self.switch(body_b);
                self.loops.push(LoopCtx {
                    next: cond_b,
                    exit: exit_b,
                    result: res,
                    depth: self.handlers.len(),
                });
                self.body(body);
                self.loops.pop();
                self.term(Term::Jump(cond_b));
                self.switch(exit_b);
                res
            }
            Case {
                subject,
                whens,
                els,
            } => {
                let res = self.reg();
                let subject = subject.as_ref().map(|s| self.expr(s));
                let join = self.new_block();
                for w in whens {
                    let body_b = self.new_block();
                    for c in &w.conds {
                        let Arg::Positional(ce) = c else { continue };
                        let cv = self.expr(ce);
                        let matched = match subject {
                            Some(s) => {
                                let t = self.reg();
                                self.emit(Inst::CaseEq {
                                    dst: t,
                                    pattern: cv,
                                    value: s,
                                });
                                t
                            }
                            None => cv,
                        };
                        let next = self.new_block();
                        self.term(Term::Branch {
                            cond: matched,
                            then: body_b,
                            els: next,
                        });
                        self.switch(next);
                    }
                    let after = self.cur;
                    let after_dead = self.dead;
                    self.switch(body_b);
                    let v = self.body(&w.body);
                    self.emit(Inst::Move { dst: res, src: v });
                    self.term(Term::Jump(join));
                    self.cur = after;
                    self.dead = after_dead;
                }
                let v = match els {
                    Some(els) => self.body(els),
                    None => self.nil(),
                };
                self.emit(Inst::Move { dst: res, src: v });
                self.term(Term::Jump(join));
                self.switch(join);
                res
            }
            CaseIn { subject, arms, els } => {
                let res = self.reg();
                let v = self.expr(subject);
                let join = self.new_block();
                for arm in arms {
                    let fail = self.new_block();
                    self.pattern(&arm.pattern, v, fail);
                    if let Some(g) = &arm.guard {
                        let c = self.expr(&g.cond);
                        let ok = self.new_block();
                        if g.negate {
                            self.term(Term::Branch {
                                cond: c,
                                then: fail,
                                els: ok,
                            });
                        } else {
                            self.term(Term::Branch {
                                cond: c,
                                then: ok,
                                els: fail,
                            });
                        }
                        self.switch(ok);
                    }
                    let r = self.body(&arm.body);
                    self.emit(Inst::Move { dst: res, src: r });
                    self.term(Term::Jump(join));
                    self.switch(fail);
                }
                match els {
                    Some(els) => {
                        let r = self.body(els);
                        self.emit(Inst::Move { dst: res, src: r });
                        self.term(Term::Jump(join));
                    }
                    None => {
                        self.emit(Inst::NoMatch {
                            src: v,
                            is_assert: false,
                        });
                        self.term(Term::Unreachable);
                    }
                }
                self.switch(join);
                res
            }
            MatchPattern {
                value,
                pattern,
                raises,
            } => {
                let v = self.expr(value);
                let fail = self.new_block();
                let ok = self.new_block();
                self.pattern(pattern, v, fail);
                self.term(Term::Jump(ok));
                if *raises {
                    self.switch(fail);
                    self.emit(Inst::NoMatch {
                        src: v,
                        is_assert: true,
                    });
                    self.term(Term::Unreachable);
                    self.switch(ok);
                    self.nil()
                } else {
                    let res = self.reg();
                    let join = self.new_block();
                    self.switch(fail);
                    let f = self.load_const(Constant::Bool(false));
                    self.emit(Inst::Move { dst: res, src: f });
                    self.term(Term::Jump(join));
                    self.switch(ok);
                    let t = self.load_const(Constant::Bool(true));
                    self.emit(Inst::Move { dst: res, src: t });
                    self.term(Term::Jump(join));
                    self.switch(join);
                    res
                }
            }
            Begin(block) => self.begin(block),
            Return(value) => {
                let v = match value {
                    Some(x) => self.expr(x),
                    None => self.nil(),
                };
                if self.is_block && !self.is_lambda {
                    self.term(Term::ReturnOut(v));
                } else {
                    self.return_through_ensures(v);
                }
                self.nil()
            }
            Break(value) => {
                let v = match value {
                    Some(x) => self.expr(x),
                    None => self.nil(),
                };
                if let Some(l) = self.loops.last() {
                    let (result, exit, depth) = (l.result, l.exit, l.depth);
                    self.emit(Inst::Move {
                        dst: result,
                        src: v,
                    });
                    let restore = self.leave_regions(depth);
                    self.term(Term::Jump(exit));
                    self.handlers.extend(restore);
                } else if self.is_lambda {
                    self.return_through_ensures(v);
                } else {
                    self.term(Term::BreakOut(v));
                }
                self.nil()
            }
            Next(value) => {
                let v = match value {
                    Some(x) => self.expr(x),
                    None => self.nil(),
                };
                if let Some(l) = self.loops.last() {
                    let (next, depth) = (l.next, l.depth);
                    let restore = self.leave_regions(depth);
                    self.term(Term::Jump(next));
                    self.handlers.extend(restore);
                } else {
                    self.return_through_ensures(v);
                }
                self.nil()
            }
            Retry => {
                match self.retry_targets.last() {
                    Some(b) => {
                        let b = *b;
                        self.term(Term::Jump(b));
                    }
                    None => self.term(Term::Unreachable),
                }
                self.nil()
            }
            Seq(exprs) => self.body(exprs),
            Using(_) | Require { .. } => self.nil(),
            ClassDef(_)
            | ModuleDef(_)
            | DataDef(_)
            | EnumDef(_)
            | ExtensionDef(_)
            | MethodDef(_)
            | FieldDecl(_)
            | AttrDecl { .. }
            | Mixin { .. }
            | Visibility { .. }
            | Alias { .. }
            | TypeAlias { .. }
            | ConstAssign { .. }
            | Extern { .. } => self.nil(),
        }
    }

    fn str_parts(&mut self, parts: &'a [StrPart]) -> Reg {
        if parts.iter().all(|p| matches!(p, StrPart::Lit(_))) {
            let s: String = parts
                .iter()
                .map(|p| match p {
                    StrPart::Lit(s) => s.as_str(),
                    _ => "",
                })
                .collect();
            return self.load_const(Constant::Str(s));
        }
        let mut pieces = Vec::new();
        for p in parts {
            match p {
                StrPart::Lit(s) => {
                    let idx = self.str_const(s);
                    pieces.push(StrPiece::Lit(idx));
                }
                StrPart::Interp(e) => {
                    let r = self.expr(e);
                    pieces.push(StrPiece::Val(r));
                }
            }
        }
        let dst = self.reg();
        self.emit(Inst::Interpolate { dst, parts: pieces });
        dst
    }

    fn ivar_index(&self, node: u32, name: &str) -> u32 {
        if let Some(i) = self.out.ivar_fields.get(&node) {
            return *i as u32;
        }
        self.class_id
            .and_then(|c| self.world.field_index(c, name))
            .unwrap_or(0) as u32
    }

    // ----- calls -------------------------------------------------------------------------

    fn args(&mut self, args: &'a [Arg]) -> Args {
        let has_splat = args.iter().any(|a| matches!(a, Arg::Splat(_)));
        let mut items = Vec::new();
        let mut kw = Vec::new();
        let mut kw_splats = Vec::new();
        let mut block = None;
        for a in args {
            match a {
                Arg::Positional(e) => {
                    let r = self.expr(e);
                    items.push(ArrayItem {
                        reg: r,
                        splat: false,
                    });
                }
                Arg::Splat(e) => {
                    let r = self.expr(e);
                    items.push(ArrayItem {
                        reg: r,
                        splat: true,
                    });
                }
                Arg::Keyword { name, value, .. } => {
                    let v = self.expr(value);
                    let s = self.sym_const(name);
                    kw.push((s, v));
                }
                Arg::DoubleSplat(e) => {
                    let h = self.expr(e);
                    kw_splats.push(HashItem::Splat(h));
                }
                Arg::BlockPass(e) => {
                    block = Some(match &e.kind {
                        ExprKind::Symbol(name) => {
                            let name = self.str_const(name);
                            let dst = self.reg();
                            self.emit(Inst::SymbolProc { dst, name });
                            dst
                        }
                        _ => self.expr(e),
                    });
                }
            }
        }
        let (pos, splat) = if has_splat {
            let dst = self.reg();
            self.emit(Inst::MakeArray { dst, items });
            (vec![dst], true)
        } else {
            (items.into_iter().map(|i| i.reg).collect(), false)
        };
        let kw_splat = if kw_splats.is_empty() {
            None
        } else {
            let dst = self.reg();
            self.emit(Inst::MakeHash {
                dst,
                items: kw_splats,
            });
            Some(dst)
        };
        Args {
            pos,
            splat,
            kw,
            kw_splat,
            block,
        }
    }

    fn call(&mut self, e: &'a Expr, call: &'a ast::Call) -> Reg {
        let target = self.out.calls.get(&e.id);
        let recv = call.recv.as_ref().map(|r| self.expr(r));
        // `recv&.name`: nil when the receiver is nil.
        let (res, nil_join) = if call.safe_nav {
            let recv = recv.unwrap();
            let res = self.reg();
            let is_nil = self.reg();
            self.emit(Inst::IsNil {
                dst: is_nil,
                src: recv,
            });
            let nil_b = self.new_block();
            let go = self.new_block();
            let join = self.new_block();
            self.term(Term::Branch {
                cond: is_nil,
                then: nil_b,
                els: go,
            });
            self.switch(nil_b);
            let n = self.nil();
            self.emit(Inst::Move { dst: res, src: n });
            self.term(Term::Jump(join));
            self.switch(go);
            (Some(res), Some(join))
        } else {
            (None, None)
        };
        let value = self.call_value(e, call, target, recv);
        match (res, nil_join) {
            (Some(res), Some(join)) => {
                self.emit(Inst::Move {
                    dst: res,
                    src: value,
                });
                self.term(Term::Jump(join));
                self.switch(join);
                res
            }
            _ => value,
        }
    }

    fn call_value(
        &mut self,
        e: &'a Expr,
        call: &'a ast::Call,
        target: Option<&CallTarget>,
        recv: Option<Reg>,
    ) -> Reg {
        match target {
            Some(CallTarget::IsA(ty)) => {
                let src = recv.unwrap_or_else(|| self.self_reg());
                let dst = self.reg();
                self.emit(Inst::IsA {
                    dst,
                    src,
                    ty: rt_type(ty),
                });
                return dst;
            }
            Some(CallTarget::As { ty, optional }) => {
                let src = recv.unwrap_or_else(|| self.self_reg());
                let dst = self.reg();
                self.emit(Inst::As {
                    dst,
                    src,
                    ty: rt_type(ty),
                    optional: *optional,
                    name: self.world.type_name(ty),
                });
                return dst;
            }
            Some(CallTarget::Constant(b)) => return self.load_const(Constant::Bool(*b)),
            _ => {}
        }
        let mut a = self.args(&call.args);
        if let Some(b) = &call.block {
            let func = self.block_function(b, e.id, false);
            let destructure = self.out.block_destructure.get(&e.id).map(|n| *n as u32);
            let dst = self.reg();
            self.emit(Inst::MakeBlock {
                dst,
                func,
                destructure,
                is_lambda: false,
            });
            a.block = Some(dst);
        }
        let kind = match target {
            Some(CallTarget::Method { method }) => {
                let m = self.world.method(*method);
                let fast = m.is_native
                    && (m.owner == self.world.builtin.int || m.owner == self.world.builtin.float)
                    && FastOp::from_name(&m.name).is_some();
                if fast
                    && a.pos.len() == 1
                    && !a.splat
                    && a.kw.is_empty()
                    && a.kw_splat.is_none()
                    && a.block.is_none()
                {
                    let lhs = recv.unwrap_or_else(|| self.self_reg());
                    let dst = self.reg();
                    self.emit(Inst::BinOp {
                        dst,
                        op: FastOp::from_name(&m.name).unwrap(),
                        lhs,
                        rhs: a.pos[0],
                        method: Some(*method),
                    });
                    return dst;
                }
                CallKind::Method(*method)
            }
            Some(CallTarget::Constructor { class, init }) => CallKind::Construct {
                class: *class,
                init: *init,
            },
            Some(CallTarget::ProcCall) => CallKind::ProcCall,
            Some(CallTarget::Raise) => CallKind::Raise,
            Some(CallTarget::Super { method }) => CallKind::Super(*method),
            Some(CallTarget::IsA(_))
            | Some(CallTarget::As { .. })
            | Some(CallTarget::Constant(_)) => {
                unreachable!()
            }
            None => CallKind::Send(call.name.clone()),
        };
        let dst = self.reg();
        self.emit(Inst::Call {
            dst,
            kind,
            recv,
            args: a.pos,
            splat: a.splat,
            kw: a.kw,
            kw_splat: a.kw_splat,
            block: a.block,
        });
        dst
    }

    fn super_call(
        &mut self,
        e: &'a Expr,
        args: Option<&'a [Arg]>,
        block: Option<&'a AstBlock>,
    ) -> Reg {
        let Some(CallTarget::Super { method }) = self.out.calls.get(&e.id) else {
            return self.nil();
        };
        let method = *method;
        let mut a = match args {
            Some(args) => self.args(args),
            None => {
                // zsuper: forward the current method's parameters.
                let mut items = Vec::new();
                let mut kw = Vec::new();
                let mut has_rest = false;
                if let Some(mid) = self.method {
                    let m = self.world.method(mid);
                    for (i, p) in m.params.iter().enumerate() {
                        let v = self.load_var(VarRef {
                            depth: self.levels.len() as u32 - 1,
                            slot: i as u32,
                        });
                        match p.kind {
                            ParamKind::KeywordOnly => {
                                let s = self.sym_const(&p.name);
                                kw.push((s, v));
                            }
                            ParamKind::Rest => {
                                has_rest = true;
                                items.push(ArrayItem {
                                    reg: v,
                                    splat: true,
                                });
                            }
                            ParamKind::KeywordRest | ParamKind::Block => {}
                            ParamKind::Positional => items.push(ArrayItem {
                                reg: v,
                                splat: false,
                            }),
                        }
                    }
                }
                let (pos, splat) = if has_rest {
                    let dst = self.reg();
                    self.emit(Inst::MakeArray { dst, items });
                    (vec![dst], true)
                } else {
                    (items.into_iter().map(|i| i.reg).collect(), false)
                };
                Args {
                    pos,
                    splat,
                    kw,
                    kw_splat: None,
                    block: None,
                }
            }
        };
        a.block = match block {
            Some(b) => {
                let func = self.block_function(b, e.id, false);
                let destructure = self.out.block_destructure.get(&e.id).map(|n| *n as u32);
                let dst = self.reg();
                self.emit(Inst::MakeBlock {
                    dst,
                    func,
                    destructure,
                    is_lambda: false,
                });
                Some(dst)
            }
            None => {
                let dst = self.reg();
                self.emit(Inst::BlockParam { dst });
                Some(dst)
            }
        };
        let dst = self.reg();
        self.emit(Inst::Call {
            dst,
            kind: CallKind::Super(method),
            recv: None,
            args: a.pos,
            splat: a.splat,
            kw: a.kw,
            kw_splat: a.kw_splat,
            block: a.block,
        });
        dst
    }

    // ----- assignment ------------------------------------------------------------------------

    fn assign(&mut self, e: &'a Expr, target: &'a LValue, value: &'a Expr) -> Reg {
        match target {
            LValue::Local { span, .. } => {
                let r = self.var_ref(*span);
                // `x = x.meth(args)`: move the value out of `x` so that a
                // uniquely referenced collection is updated in place.
                if let (Some(r), ExprKind::Call(call)) = (r, &value.kind) {
                    if let Some(Expr {
                        kind: ExprKind::Local(_),
                        span: rspan,
                        ..
                    }) = &call.recv
                    {
                        let same = self.var_ref(*rspan) == Some(r);
                        if same && call.block.is_none() && !call.safe_nav {
                            if let Some(CallTarget::Method { method }) =
                                self.out.calls.get(&value.id)
                            {
                                let method = *method;
                                let a = self.args(&call.args);
                                if a.block.is_none() && !a.splat && a.kw_splat.is_none() {
                                    let loc = self.var_loc(r);
                                    let dst = self.reg();
                                    self.emit(Inst::OwnedCall {
                                        dst,
                                        method,
                                        recv: loc,
                                        args: a.pos,
                                        kw: a.kw,
                                    });
                                    return dst;
                                }
                                // Fall back to a plain call with the
                                // already evaluated arguments.
                                let recv = self.load_var(r);
                                let dst = self.reg();
                                self.emit(Inst::Call {
                                    dst,
                                    kind: CallKind::Method(method),
                                    recv: Some(recv),
                                    args: a.pos,
                                    splat: a.splat,
                                    kw: a.kw,
                                    kw_splat: a.kw_splat,
                                    block: a.block,
                                });
                                self.store_var(r, dst);
                                return dst;
                            }
                        }
                    }
                }
                let v = self.expr(value);
                if let Some(r) = r {
                    self.store_var(r, v);
                }
                v
            }
            LValue::IVar(name) => {
                let v = self.expr(value);
                let index = self.ivar_index(e.id, name);
                let obj = self.self_reg();
                self.emit(Inst::FieldSet { obj, index, src: v });
                v
            }
            LValue::Const(_) => self.nil(),
            LValue::Attr {
                recv,
                name,
                safe_nav,
            } => {
                let r = self.expr(recv);
                if *safe_nav {
                    let res = self.reg();
                    let is_nil = self.reg();
                    self.emit(Inst::IsNil {
                        dst: is_nil,
                        src: r,
                    });
                    let nil_b = self.new_block();
                    let go = self.new_block();
                    let join = self.new_block();
                    self.term(Term::Branch {
                        cond: is_nil,
                        then: nil_b,
                        els: go,
                    });
                    self.switch(nil_b);
                    let n = self.nil();
                    self.emit(Inst::Move { dst: res, src: n });
                    self.term(Term::Jump(join));
                    self.switch(go);
                    let v = self.expr(value);
                    self.send(r, &format!("{name}="), vec![v]);
                    self.emit(Inst::Move { dst: res, src: v });
                    self.term(Term::Jump(join));
                    self.switch(join);
                    return res;
                }
                let v = self.expr(value);
                self.send(r, &format!("{name}="), vec![v]);
                v
            }
            LValue::Index { recv, args } => {
                let r = self.expr(recv);
                let a = self.args(args);
                let v = self.expr(value);
                self.index_set(r, a, v);
                v
            }
        }
    }

    /// A call by name with positional arguments only.
    fn send(&mut self, recv: Reg, name: &str, args: Vec<Reg>) -> Reg {
        let dst = self.reg();
        self.emit(Inst::Call {
            dst,
            kind: CallKind::Send(name.to_string()),
            recv: Some(recv),
            args,
            splat: false,
            kw: Vec::new(),
            kw_splat: None,
            block: None,
        });
        dst
    }

    fn index_set(&mut self, recv: Reg, a: Args, value: Reg) {
        let (args, splat) = if a.splat {
            let dst = self.reg();
            self.emit(Inst::MakeArray {
                dst,
                items: vec![
                    ArrayItem {
                        reg: a.pos[0],
                        splat: true,
                    },
                    ArrayItem {
                        reg: value,
                        splat: false,
                    },
                ],
            });
            (vec![dst], true)
        } else {
            let mut args = a.pos;
            args.push(value);
            (args, false)
        };
        let dst = self.reg();
        self.emit(Inst::Call {
            dst,
            kind: CallKind::Send("[]=".to_string()),
            recv: Some(recv),
            args,
            splat,
            kw: Vec::new(),
            kw_splat: None,
            block: None,
        });
    }

    fn op_assign(&mut self, e: &'a Expr, target: &'a LValue, op: OpAssign, value: &'a Expr) -> Reg {
        // Read.
        enum Place {
            Local(Option<VarRef>),
            IVar(u32),
            Attr(Reg, String),
            Index(Reg, Vec<Reg>, bool),
        }
        let (current, place) = match target {
            LValue::Local { span, .. } => {
                let r = self.var_ref(*span);
                let cur = match r {
                    Some(r) => self.load_var(r),
                    None => self.nil(),
                };
                (cur, Place::Local(r))
            }
            LValue::IVar(name) => {
                let index = self.ivar_index(e.id, name);
                let obj = self.self_reg();
                let dst = self.reg();
                self.emit(Inst::FieldGet { dst, obj, index });
                (dst, Place::IVar(index))
            }
            LValue::Attr { recv, name, .. } => {
                let r = self.expr(recv);
                let cur = self.send(r, name, Vec::new());
                (cur, Place::Attr(r, name.clone()))
            }
            LValue::Index { recv, args } => {
                let r = self.expr(recv);
                let a = self.args(args);
                let dst = self.reg();
                self.emit(Inst::Call {
                    dst,
                    kind: CallKind::Send("[]".to_string()),
                    recv: Some(r),
                    args: a.pos.clone(),
                    splat: a.splat,
                    kw: Vec::new(),
                    kw_splat: None,
                    block: None,
                });
                (dst, Place::Index(r, a.pos, a.splat))
            }
            LValue::Const(_) => return self.nil(),
        };
        // Combine.
        let res = self.reg();
        let join = self.new_block();
        match op {
            OpAssign::OrOr | OpAssign::AndAnd => {
                self.emit(Inst::Move {
                    dst: res,
                    src: current,
                });
                let compute = self.new_block();
                if op == OpAssign::OrOr {
                    self.term(Term::Branch {
                        cond: current,
                        then: join,
                        els: compute,
                    });
                } else {
                    self.term(Term::Branch {
                        cond: current,
                        then: compute,
                        els: join,
                    });
                }
                self.switch(compute);
                let v = self.expr(value);
                self.emit(Inst::Move { dst: res, src: v });
            }
            _ => {
                let rhs = self.expr(value);
                let name = op.as_str().trim_end_matches('=').to_string();
                let v = match FastOp::from_name(&name) {
                    Some(fop) => {
                        let dst = self.reg();
                        self.emit(Inst::BinOp {
                            dst,
                            op: fop,
                            lhs: current,
                            rhs,
                            method: None,
                        });
                        dst
                    }
                    None => self.send(current, &name, vec![rhs]),
                };
                self.emit(Inst::Move { dst: res, src: v });
            }
        }
        // Write.
        match place {
            Place::Local(r) => {
                if let Some(r) = r {
                    self.store_var(r, res);
                }
            }
            Place::IVar(index) => {
                let obj = self.self_reg();
                self.emit(Inst::FieldSet {
                    obj,
                    index,
                    src: res,
                });
            }
            Place::Attr(recv, name) => {
                self.send(recv, &format!("{name}="), vec![res]);
            }
            Place::Index(recv, pos, splat) => {
                self.index_set(
                    recv,
                    Args {
                        pos,
                        splat,
                        kw: Vec::new(),
                        kw_splat: None,
                        block: None,
                    },
                    res,
                );
            }
        }
        self.term(Term::Jump(join));
        self.switch(join);
        res
    }

    fn assign_multi(&mut self, targets: &'a [ast::MultiTarget], v: Reg) {
        let items = self.reg();
        self.emit(Inst::ToArray { dst: items, src: v });
        let splat = targets
            .iter()
            .position(|t| matches!(t, ast::MultiTarget::Splat(_)));
        let n = targets.len();
        for (i, t) in targets.iter().enumerate() {
            let value = match splat {
                Some(si) if i == si => {
                    let after = (n - si - 1) as u32;
                    let dst = self.reg();
                    self.emit(Inst::ArraySlice {
                        dst,
                        arr: items,
                        from: si as u32,
                        drop_last: after,
                    });
                    dst
                }
                Some(si) if i > si => {
                    let from_end = (n - i) as i32;
                    let dst = self.reg();
                    self.emit(Inst::ArrayGet {
                        dst,
                        arr: items,
                        index: -from_end,
                    });
                    dst
                }
                _ => {
                    let dst = self.reg();
                    self.emit(Inst::ArrayGet {
                        dst,
                        arr: items,
                        index: i as i32,
                    });
                    dst
                }
            };
            match t {
                ast::MultiTarget::Single(lv) | ast::MultiTarget::Splat(Some(lv)) => {
                    self.assign_lvalue(lv, value)
                }
                ast::MultiTarget::Splat(None) => {}
                ast::MultiTarget::Nested(ts) => self.assign_multi(ts, value),
            }
        }
    }

    fn assign_lvalue(&mut self, lv: &'a LValue, v: Reg) {
        match lv {
            LValue::Local { span, .. } => self.store_site(*span, v),
            LValue::IVar(name) => {
                let index = self
                    .class_id
                    .and_then(|c| self.world.field_index(c, name))
                    .unwrap_or(0) as u32;
                let obj = self.self_reg();
                self.emit(Inst::FieldSet { obj, index, src: v });
            }
            LValue::Attr { recv, name, .. } => {
                let r = self.expr(recv);
                self.send(r, &format!("{name}="), vec![v]);
            }
            LValue::Index { recv, args } => {
                let r = self.expr(recv);
                let a = self.args(args);
                self.index_set(r, a, v);
            }
            LValue::Const(_) => {}
        }
    }

    // ----- begin / rescue / ensure ----------------------------------------------------------

    fn begin(&mut self, block: &'a ast::BeginBlock) -> Reg {
        let res = self.reg();
        let join = self.new_block();
        if let Some(ensure) = &block.ensure {
            // The handler block belongs to the outer region.
            let ens_handler = self.new_block();
            self.handlers.push(Region {
                handler: Some(Handler {
                    block: ens_handler,
                    kind: HandlerKind::Ensure,
                }),
                ensure: Some(ensure),
            });
            let entry = self.new_block();
            self.term(Term::Jump(entry));
            self.switch(entry);
            let v = self.rescue_region(block);
            self.emit(Inst::Move { dst: res, src: v });
            self.handlers.pop();
            // Normal completion: run `ensure` in the outer region.
            let after = self.new_block();
            self.term(Term::Jump(after));
            self.switch(after);
            self.body(ensure);
            self.term(Term::Jump(join));
            // Abrupt completion: run `ensure`, then continue the flow.
            self.switch(ens_handler);
            let flow = self.reg();
            self.emit(Inst::CatchAny { dst: flow });
            self.body(ensure);
            self.term(Term::Resume(flow));
        } else {
            let v = self.rescue_region(block);
            self.emit(Inst::Move { dst: res, src: v });
            self.term(Term::Jump(join));
        }
        self.switch(join);
        res
    }

    /// `begin ... rescue ... else ... end` without `ensure`.
    fn rescue_region(&mut self, block: &'a ast::BeginBlock) -> Reg {
        if block.rescues.is_empty() {
            let v = self.body(&block.body);
            return match &block.else_body {
                Some(e) => self.body(e),
                None => v,
            };
        }
        let res = self.reg();
        let join = self.new_block();
        let handler = self.new_block();
        self.handlers.push(Region {
            handler: Some(Handler {
                block: handler,
                kind: HandlerKind::Rescue,
            }),
            ensure: None,
        });
        let entry = self.new_block();
        self.term(Term::Jump(entry));
        self.switch(entry);
        let v = self.body(&block.body);
        self.handlers.pop();
        // `else` runs outside the protected region.
        let after = self.new_block();
        self.term(Term::Jump(after));
        self.switch(after);
        let v = match &block.else_body {
            Some(e) => self.body(e),
            None => v,
        };
        self.emit(Inst::Move { dst: res, src: v });
        self.term(Term::Jump(join));
        // Handler: find the matching clause.
        self.switch(handler);
        let exc = self.reg();
        self.emit(Inst::CatchException { dst: exc });
        for rescue in &block.rescues {
            let classes: Vec<ClassId> = match self.out.rescue_classes.get(&rescue.span) {
                Some(ids) => ids.clone(),
                None => vec![self.world.builtin.standard_error],
            };
            let body_b = self.new_block();
            for cid in classes {
                let t = self.reg();
                self.emit(Inst::ClassIsA {
                    dst: t,
                    src: exc,
                    class: cid,
                });
                let next = self.new_block();
                self.term(Term::Branch {
                    cond: t,
                    then: body_b,
                    els: next,
                });
                self.switch(next);
            }
            let after = self.cur;
            self.switch(body_b);
            if rescue.var.is_some() {
                self.store_site(rescue.span, exc);
            }
            self.retry_targets.push(entry);
            let v = self.body(&rescue.body);
            self.retry_targets.pop();
            self.emit(Inst::Move { dst: res, src: v });
            self.term(Term::Jump(join));
            self.switch(after);
        }
        self.term(Term::Raise(exc));
        self.switch(join);
        res
    }

    // ----- patterns ---------------------------------------------------------------------------

    /// Emit the checks of `pat` against the value in `v`; control falls
    /// through on a match and jumps to `fail` otherwise.
    fn pattern(&mut self, pat: &'a ast::Pattern, v: Reg, fail: BlockId) {
        use ast::PatternKind;
        match &pat.kind {
            PatternKind::Bind(_) => self.store_site(pat.span, v),
            PatternKind::Capture(inner, _) => {
                self.pattern(inner, v, fail);
                self.store_site(pat.span, v);
            }
            PatternKind::Alt(alts) => {
                let ok = self.new_block();
                let n = alts.len();
                for (i, a) in alts.iter().enumerate() {
                    let next = if i + 1 == n { fail } else { self.new_block() };
                    self.pattern(a, v, next);
                    self.term(Term::Jump(ok));
                    if i + 1 != n {
                        self.switch(next);
                    }
                }
                self.switch(ok);
            }
            PatternKind::Pin(e) => {
                let p = self.expr(e);
                let t = self.reg();
                self.emit(Inst::Equal { dst: t, a: p, b: v });
                self.check(t, fail);
            }
            PatternKind::Value(e) => {
                let p = self.expr(e);
                let t = self.reg();
                self.emit(Inst::CaseEq {
                    dst: t,
                    pattern: p,
                    value: v,
                });
                self.check(t, fail);
            }
            PatternKind::Range { lo, hi, exclusive } => {
                let lo = lo.as_ref().map(|x| self.expr(x));
                let hi = hi.as_ref().map(|x| self.expr(x));
                let range = self.reg();
                self.emit(Inst::MakeRange {
                    dst: range,
                    lo,
                    hi,
                    exclusive: *exclusive,
                });
                let t = self.reg();
                self.emit(Inst::CaseEq {
                    dst: t,
                    pattern: range,
                    value: v,
                });
                self.check(t, fail);
            }
            PatternKind::Const(_) => {
                let Some(cid) = self.out.pattern_classes.get(&pat.span).copied() else {
                    self.term(Term::Jump(fail));
                    return;
                };
                let t = self.reg();
                self.emit(Inst::ClassIsA {
                    dst: t,
                    src: v,
                    class: cid,
                });
                self.check(t, fail);
            }
            PatternKind::ConstArray(_, ap) => {
                let Some(cid) = self.out.pattern_classes.get(&pat.span).copied() else {
                    self.term(Term::Jump(fail));
                    return;
                };
                let t = self.reg();
                self.emit(Inst::ClassIsA {
                    dst: t,
                    src: v,
                    class: cid,
                });
                self.check(t, fail);
                let t = self.reg();
                self.emit(Inst::IsObject { dst: t, src: v });
                self.check(t, fail);
                let fields = self.reg();
                self.emit(Inst::ObjectFields {
                    dst: fields,
                    src: v,
                });
                self.array_pattern(ap, fields, pat.span, fail);
            }
            PatternKind::ConstHash(_, hp) => {
                let Some(cid) = self.out.pattern_classes.get(&pat.span).copied() else {
                    self.term(Term::Jump(fail));
                    return;
                };
                let t = self.reg();
                self.emit(Inst::ClassIsA {
                    dst: t,
                    src: v,
                    class: cid,
                });
                self.check(t, fail);
                let t = self.reg();
                self.emit(Inst::IsObject { dst: t, src: v });
                self.check(t, fail);
                self.object_hash_pattern(hp, v, fail);
            }
            PatternKind::Array(ap) => {
                let t = self.reg();
                self.emit(Inst::IsArray { dst: t, src: v });
                self.check(t, fail);
                self.array_pattern(ap, v, pat.span, fail);
            }
            PatternKind::Find {
                pre_rest,
                middle,
                post_rest,
            } => {
                let t = self.reg();
                self.emit(Inst::IsArray { dst: t, src: v });
                self.check(t, fail);
                let len = self.reg();
                self.emit(Inst::Len { dst: len, src: v });
                let m = self.load_const(Constant::Int(middle.len() as i64));
                let limit = self.reg();
                self.emit(Inst::BinOp {
                    dst: limit,
                    op: FastOp::Sub,
                    lhs: len,
                    rhs: m,
                    method: None,
                });
                // for i in 0..=limit
                let i = self.load_const(Constant::Int(0));
                let head = self.new_block();
                let try_b = self.new_block();
                let next_i = self.new_block();
                let ok = self.new_block();
                self.term(Term::Jump(head));
                self.switch(head);
                let c = self.reg();
                self.emit(Inst::BinOp {
                    dst: c,
                    op: FastOp::Le,
                    lhs: i,
                    rhs: limit,
                    method: None,
                });
                self.term(Term::Branch {
                    cond: c,
                    then: try_b,
                    els: fail,
                });
                self.switch(try_b);
                for (j, p) in middle.iter().enumerate() {
                    let jr = self.load_const(Constant::Int(j as i64));
                    let idx = self.reg();
                    self.emit(Inst::BinOp {
                        dst: idx,
                        op: FastOp::Add,
                        lhs: i,
                        rhs: jr,
                        method: None,
                    });
                    let elem = self.reg();
                    self.emit(Inst::ArrayGetReg {
                        dst: elem,
                        arr: v,
                        index: idx,
                    });
                    self.pattern(p, elem, next_i);
                }
                if pre_rest.is_some() {
                    let zero = self.load_const(Constant::Int(0));
                    let dst = self.reg();
                    self.emit(Inst::ArraySliceReg {
                        dst,
                        arr: v,
                        from: zero,
                        to: i,
                    });
                    self.store_site(pat.span, dst);
                }
                if post_rest.is_some() {
                    let from = self.reg();
                    self.emit(Inst::BinOp {
                        dst: from,
                        op: FastOp::Add,
                        lhs: i,
                        rhs: m,
                        method: None,
                    });
                    let dst = self.reg();
                    self.emit(Inst::ArraySliceReg {
                        dst,
                        arr: v,
                        from,
                        to: len,
                    });
                    self.store_site(Span::empty(pat.span.end as usize), dst);
                }
                self.term(Term::Jump(ok));
                self.switch(next_i);
                let one = self.load_const(Constant::Int(1));
                let inc = self.reg();
                self.emit(Inst::BinOp {
                    dst: inc,
                    op: FastOp::Add,
                    lhs: i,
                    rhs: one,
                    method: None,
                });
                self.emit(Inst::Move { dst: i, src: inc });
                self.term(Term::Jump(head));
                self.switch(ok);
            }
            PatternKind::Hash(hp) => {
                let is_hash = self.reg();
                self.emit(Inst::IsHash {
                    dst: is_hash,
                    src: v,
                });
                let hash_b = self.new_block();
                let not_hash = self.new_block();
                let ok = self.new_block();
                self.term(Term::Branch {
                    cond: is_hash,
                    then: hash_b,
                    els: not_hash,
                });
                self.switch(hash_b);
                for pair in &hp.pairs {
                    let key = self.sym_const(&pair.key);
                    let fv = self.reg();
                    let found = self.reg();
                    self.emit(Inst::HashGetSym {
                        dst: fv,
                        found,
                        hash: v,
                        key,
                    });
                    self.check(found, fail);
                    match &pair.pattern {
                        Some(p) => self.pattern(p, fv, fail),
                        None => self.store_site(pair.span, fv),
                    }
                }
                match &hp.rest {
                    Some(ast::HashPatternRest::Bind(_)) => {
                        let keys: Vec<u32> =
                            hp.pairs.iter().map(|p| self.sym_const(&p.key)).collect();
                        let dst = self.reg();
                        self.emit(Inst::HashRest { dst, hash: v, keys });
                        self.store_site(pat.span, dst);
                    }
                    Some(ast::HashPatternRest::Nil) => {
                        let len = self.reg();
                        self.emit(Inst::Len { dst: len, src: v });
                        let n = self.load_const(Constant::Int(hp.pairs.len() as i64));
                        let t = self.reg();
                        self.emit(Inst::BinOp {
                            dst: t,
                            op: FastOp::Eq,
                            lhs: len,
                            rhs: n,
                            method: None,
                        });
                        self.check(t, fail);
                    }
                    None => {}
                }
                self.term(Term::Jump(ok));
                self.switch(not_hash);
                let is_obj = self.reg();
                self.emit(Inst::IsObject {
                    dst: is_obj,
                    src: v,
                });
                self.check(is_obj, fail);
                self.object_hash_pattern(hp, v, fail);
                self.term(Term::Jump(ok));
                self.switch(ok);
            }
        }
    }

    /// Branch to `fail` unless `cond` is truthy.
    fn check(&mut self, cond: Reg, fail: BlockId) {
        let ok = self.new_block();
        self.term(Term::Branch {
            cond,
            then: ok,
            els: fail,
        });
        self.switch(ok);
    }

    fn array_pattern(&mut self, ap: &'a ast::ArrayPattern, items: Reg, span: Span, fail: BlockId) {
        let fixed = (ap.pre.len() + ap.post.len()) as i64;
        let len = self.reg();
        self.emit(Inst::Len {
            dst: len,
            src: items,
        });
        let n = self.load_const(Constant::Int(fixed));
        let t = self.reg();
        self.emit(Inst::BinOp {
            dst: t,
            op: if ap.rest.is_none() {
                FastOp::Eq
            } else {
                FastOp::Ge
            },
            lhs: len,
            rhs: n,
            method: None,
        });
        self.check(t, fail);
        for (i, p) in ap.pre.iter().enumerate() {
            let x = self.reg();
            self.emit(Inst::ArrayGet {
                dst: x,
                arr: items,
                index: i as i32,
            });
            self.pattern(p, x, fail);
        }
        let post_len = ap.post.len();
        for (k, p) in ap.post.iter().enumerate() {
            let x = self.reg();
            self.emit(Inst::ArrayGet {
                dst: x,
                arr: items,
                index: -((post_len - k) as i32),
            });
            self.pattern(p, x, fail);
        }
        if let Some(Some(_)) = &ap.rest {
            let dst = self.reg();
            self.emit(Inst::ArraySlice {
                dst,
                arr: items,
                from: ap.pre.len() as u32,
                drop_last: post_len as u32,
            });
            self.store_site(span, dst);
        }
    }

    fn object_hash_pattern(&mut self, hp: &'a ast::HashPattern, obj: Reg, fail: BlockId) {
        for pair in &hp.pairs {
            let name = self.str_const(&pair.key);
            let fv = self.reg();
            let found = self.reg();
            self.emit(Inst::FieldGetByName {
                dst: fv,
                found,
                obj,
                name,
            });
            self.check(found, fail);
            match &pair.pattern {
                Some(p) => self.pattern(p, fv, fail),
                None => self.store_site(pair.span, fv),
            }
        }
    }
}
