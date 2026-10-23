//! Building one QIR function from an AST body.

use rustc_hash::{FxHashMap as HashMap, FxHashSet as HashSet};

use quarz_ir::*;
use quarz_syntax::ast::{self, Arg, Block as AstBlock, Expr, ExprKind, LValue, ParamKind, StrPart};
use quarz_syntax::token::OpAssign;
use quarz_syntax::Span;
use quarz_types::{CallTarget, ConstTarget, Output, SelfOwner, Type, VarRef, World};

use crate::capture::captured_slots;
use crate::iter::{self, Kind, Shape, Source};
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
    /// For a block body lowered in place: where `next v` leaves its value.
    next_value: Option<Reg>,
}

/// A block lowered in place (see `iter`): its variables are registers of
/// the enclosing function.
struct InlineLevel {
    slot_regs: HashMap<u32, Reg>,
    /// The block's frame, for `Output::lexical_slots`.
    owner: SelfOwner,
    /// Its variables that live to the end of each pass of the body.
    lexical: Vec<Reg>,
}

impl InlineLevel {
    fn new(owner: SelfOwner) -> InlineLevel {
        InlineLevel {
            slot_regs: HashMap::default(),
            owner,
            lexical: Vec::new(),
        }
    }
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
    /// For each pair of consecutive levels, how many blocks lowered in
    /// place sit between them (the checker counts those as levels too).
    gaps: Vec<u32>,
    captured: HashSet<u32>,
    all_captured: bool,
    slot_regs: HashMap<u32, Reg>,
    /// The blocks currently being lowered in place, outermost first.
    inline: Vec<InlineLevel>,
    /// This function's frame, for `Output::lexical_slots` (none for an
    /// initializer).
    owner: Option<SelfOwner>,
    /// Its variables that live to the end of the function (`Inst::Release`
    /// before it returns) rather than their last use.
    lexical: Vec<Reg>,
    /// Inside an `instance_exec` block lowered in place: the register
    /// holding the receiver, which `self` means here.
    self_override: Option<Reg>,
    loops: Vec<LoopCtx>,
    handlers: Vec<Region<'a>>,
    retry_targets: Vec<BlockId>,
    method: Option<MethodId>,
    class_id: Option<ClassId>,
    is_block: bool,
    is_lambda: bool,
    file: u32,
    /// Source line of the expression being lowered.
    line: u32,
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
        gaps: Vec<u32>,
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
            const_index: HashMap::default(),
            levels,
            gaps,
            captured,
            all_captured,
            slot_regs: HashMap::default(),
            inline: Vec::new(),
            owner: None,
            lexical: Vec::new(),
            self_override: None,
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
            line: 0,
        }
    }

    /// Keep this function's `self` in its hidden frame slot when a block
    /// with a receiver inside it calls methods on it.
    fn store_self_slot(&mut self, owner: SelfOwner) {
        if let Some(slot) = self.out.self_slots.get(&owner) {
            let s = self.self_reg();
            self.store_var(
                VarRef {
                    depth: 0,
                    slot: *slot,
                },
                s,
            );
        }
    }

    fn line_of(&self, span: Span) -> u32 {
        match self.lw.files.get(self.file as usize) {
            Some(f) if !f.text.is_empty() => f.line_col(span.start).line as u32,
            _ => 0,
        }
    }

    /// The function, its lexical variables released at each exit (but the
    /// one it returns).
    fn finish(mut self) -> Function {
        if !self.lexical.is_empty() {
            for blk in self.func.blocks.iter_mut() {
                let (Term::Return(v) | Term::BreakOut(v) | Term::ReturnOut(v)) = blk.term else {
                    continue;
                };
                for &src in &self.lexical {
                    if src != v {
                        blk.insts.push(Inst::Release { src });
                        blk.lines.push(blk.term_line);
                    }
                }
            }
        }
        self.func
    }

    /// Release the lexical variables of a block lowered in place at the end
    /// of a pass of its body (where control is now).
    fn release_inline(&mut self, level: InlineLevel) {
        for src in level.lexical {
            self.emit(Inst::Release { src });
        }
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
        let captured = captured_slots(body, &defaults, out, world, nparams);
        let name = format!("{}#{}", world.class(m.owner).name, m.name);
        let mut b = FnBuilder::new(
            lw,
            world,
            out,
            name,
            FuncKind::Method(mid),
            m.file,
            &[],
            Vec::new(),
            captured,
            false,
            Some(mid),
            Some(m.owner),
        );
        b.owner = Some(SelfOwner::Method(mid));
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
                    let class = b.class_id.unwrap_or(u32::MAX);
                    b.field_set(obj, class, idx as u32, v);
                }
            }
        }
        b.store_self_slot(SelfOwner::Method(mid));
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
        let captured = captured_slots(std::slice::from_ref(value), &[], out, world, 0);
        let mut b = FnBuilder::new(
            lw,
            world,
            out,
            name,
            FuncKind::Init,
            file,
            &[],
            Vec::new(),
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
        let captured = captured_slots(unit.body, &[], out, world, 0);
        let kind = if unit.repl {
            FuncKind::Repl
        } else {
            FuncKind::TopLevel
        };
        let mut b = FnBuilder::new(
            lw,
            world,
            out,
            "<main>".to_string(),
            kind,
            unit.file,
            &[],
            Vec::new(),
            captured,
            unit.repl,
            None,
            Some(unit.main_class),
        );
        b.owner = Some(SelfOwner::Unit(unit.file));
        b.store_self_slot(SelfOwner::Unit(unit.file));
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
        let captured = captured_slots(
            &block.body,
            &defaults,
            self.out,
            self.world,
            params.len() as u32,
        );
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
            {
                let mut gaps = self.gaps.clone();
                gaps.push(self.inline.len() as u32);
                gaps
            },
            captured,
            false,
            self.method,
            self.class_id,
        );
        b.is_block = true;
        b.is_lambda = is_lambda;
        b.owner = Some(SelfOwner::Block(call_id));
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
        b.store_self_slot(SelfOwner::Block(call_id));
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
        let b = &mut self.func.blocks[self.cur as usize];
        b.insts.push(inst);
        b.lines.push(self.line);
    }

    fn new_block(&mut self) -> BlockId {
        let id = self.func.blocks.len() as BlockId;
        self.func.blocks.push(quarz_ir::Block {
            insts: Vec::new(),
            lines: Vec::new(),
            term: Term::Unreachable,
            term_line: self.line,
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
        let b = &mut self.func.blocks[self.cur as usize];
        b.term = t;
        b.term_line = self.line;
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

    /// The value of constant `cid` when its initializer is a literal
    /// (an integer, float, plain string, boolean or symbol).
    fn literal_const(&self, cid: quarz_types::ConstId) -> Option<Constant> {
        let info = self.world.consts.get(cid as usize)?;
        let value = info.value.as_ref()?;
        let is_float =
            matches!(&info.ty, Some(Type::Class(id, _)) if *id == self.world.builtin.float);
        Some(match &value.kind {
            ExprKind::Int(lit) => match lit.value {
                Some(i) if is_float => Constant::Float(i as f64),
                Some(i) if matches!(&info.ty, Some(Type::Class(id, _)) if *id == self.world.builtin.int) => {
                    Constant::Int(i)
                }
                _ => return None,
            },
            ExprKind::Float(f) if is_float => Constant::Float(*f),
            ExprKind::True => Constant::Bool(true),
            ExprKind::False => Constant::Bool(false),
            ExprKind::Symbol(name) => Constant::Symbol(name.clone()),
            ExprKind::Str(parts) => {
                let mut text = String::new();
                for p in parts {
                    match p {
                        StrPart::Lit(s) => text.push_str(s),
                        StrPart::Interp(_) => return None,
                    }
                }
                Constant::Str(text)
            }
            _ => return None,
        })
    }

    /// The operands of a chain of `String#+` (`a + b + c`, at least two
    /// `+`), which is built in one buffer like an interpolation.
    fn concat_chain(&self, e: &'a Expr, call: &'a ast::Call) -> Option<Vec<&'a Expr>> {
        let mut leaves: Vec<&'a Expr> = Vec::new();
        let mut depth = 0;
        let (mut cur_e, mut cur) = (e, call);
        loop {
            let Some(CallTarget::Method { method }) = self.out.calls.get(&cur_e.id) else {
                return None;
            };
            let m = self.world.method(*method);
            if !(m.is_native && m.owner == self.world.builtin.string && m.name == "+")
                || cur.block.is_some()
                || cur.safe_nav
                || cur.args.len() != 1
            {
                return None;
            }
            let Some(Arg::Positional(arg)) = cur.args.first() else {
                return None;
            };
            let recv = cur.recv.as_ref()?;
            leaves.push(arg);
            depth += 1;
            match &recv.kind {
                ExprKind::Call(inner) if self.is_string_plus(recv, inner) => {
                    cur_e = recv;
                    cur = inner;
                }
                _ => {
                    leaves.push(recv);
                    break;
                }
            }
        }
        if depth < 2 {
            return None;
        }
        leaves.reverse();
        Some(leaves)
    }

    fn is_string_plus(&self, e: &Expr, call: &ast::Call) -> bool {
        let Some(CallTarget::Method { method }) = self.out.calls.get(&e.id) else {
            return false;
        };
        let m = self.world.method(*method);
        m.is_native
            && m.owner == self.world.builtin.string
            && m.name == "+"
            && call.block.is_none()
            && !call.safe_nav
            && call.args.len() == 1
            && matches!(call.args.first(), Some(Arg::Positional(_)))
            && call.recv.is_some()
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
        match self.self_override {
            Some(src) => self.emit(Inst::Move { dst, src }),
            None => self.emit(Inst::SelfRef { dst }),
        }
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
    /// The checker's depth of the method's own level from here (for
    /// `super` without arguments, which forwards the method's parameters).
    fn method_level_depth(&self) -> u32 {
        self.inline.len() as u32 + (self.levels.len() as u32 - 1) + self.gaps.iter().sum::<u32>()
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
        if let Some(owner) = self.owner {
            if self.out.lexical_slots.contains(&(owner, slot)) {
                self.lexical.push(r);
            }
        }
        r
    }

    /// Where a variable lives: a register of this function (its own
    /// uncaptured variables, and every variable of a block lowered in
    /// place) or a slot of a heap frame.
    fn resolve(&mut self, r: VarRef) -> VarLoc {
        let k = self.inline.len();
        if (r.depth as usize) < k {
            let level = k - 1 - r.depth as usize;
            if let Some(reg) = self.inline[level].slot_regs.get(&r.slot) {
                return VarLoc::Reg(*reg);
            }
            let reg = self.reg();
            let lv = &mut self.inline[level];
            lv.slot_regs.insert(r.slot, reg);
            if self.out.lexical_slots.contains(&(lv.owner, r.slot)) {
                lv.lexical.push(reg);
            }
            return VarLoc::Reg(reg);
        }
        let d = r.depth - k as u32;
        if d == 0 && !self.is_captured(r.slot) {
            return VarLoc::Reg(self.slot_reg(r.slot));
        }
        // An outer level: step over the blocks lowered in place between
        // the real levels (nothing nested refers to their variables).
        let n = self.levels.len() - 1;
        let mut j = n;
        let mut rem = d;
        while rem > 0 {
            rem -= 1;
            let gap = self.gaps[j - 1];
            debug_assert!(
                rem >= gap,
                "variable of an inlined block referenced from a nested function"
            );
            rem -= gap;
            j -= 1;
        }
        let depth = self.levels[j + 1..=n].iter().filter(|h| **h).count() as u32;
        VarLoc::Frame {
            depth,
            slot: r.slot,
        }
    }

    fn load_var(&mut self, r: VarRef) -> Reg {
        let dst = self.reg();
        match self.resolve(r) {
            VarLoc::Reg(src) => self.emit(Inst::Move { dst, src }),
            VarLoc::Frame { depth, slot } => self.emit(Inst::FrameGet { dst, depth, slot }),
            VarLoc::Field { .. } => unreachable!("a variable is never a field"),
        }
        dst
    }

    fn store_var(&mut self, r: VarRef, src: Reg) {
        match self.resolve(r) {
            VarLoc::Reg(dst) => self.emit(Inst::Move { dst, src }),
            VarLoc::Frame { depth, slot } => self.emit(Inst::FrameSet { depth, slot, src }),
            VarLoc::Field { .. } => unreachable!("a variable is never a field"),
        }
    }

    fn var_loc(&mut self, r: VarRef) -> VarLoc {
        self.resolve(r)
    }

    fn store_site(&mut self, span: Span, src: Reg) {
        if let Some(r) = self.var_ref(span) {
            self.store_var(r, src);
        }
    }

    // ----- expressions ---------------------------------------------------------------------

    fn body(&mut self, exprs: &'a [Expr]) -> Reg {
        let mut last = None;
        for (i, e) in exprs.iter().enumerate() {
            let r = self.expr(e);
            // A value released observably that nothing uses goes at the
            // end of its statement.
            if i + 1 < exprs.len() && self.out.released_stmts.contains(&e.id) {
                self.emit(Inst::Release { src: r });
            }
            last = Some(r);
        }
        match last {
            Some(r) => r,
            None => self.nil(),
        }
    }

    fn expr(&mut self, e: &'a Expr) -> Reg {
        let saved = self.line;
        self.line = self.line_of(e.span);
        let mut r = self.expr_inner(e);
        // The result of something declared to return `Nil`.
        if self.out.discarded.contains(&e.id) {
            r = self.nil();
        }
        self.line = saved;
        r
    }

    fn expr_inner(&mut self, e: &'a Expr) -> Reg {
        use ExprKind::*;
        match &e.kind {
            // The expansion the checker chose (see `Output::for_loops`):
            // nested `each` calls when its value is not used.
            For(f) => {
                if self.out.for_loops.contains(&e.id) {
                    self.expr(&f.each);
                    self.nil()
                } else {
                    self.expr(&f.comprehension)
                }
            }
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
                        .files
                        .get(self.file as usize)
                        .map(|f| f.name.clone())
                        .unwrap_or_default();
                    self.load_const(Constant::Str(name))
                }
                ast::Magic::Line => {
                    let line = self.line;
                    self.load_const(Constant::Int(i64::from(line)))
                }
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
                self.share_proc(e.id, dst)
            }
            Local(_) => match self.var_ref(e.span) {
                Some(r) => self.load_var(r),
                None => self.nil(),
            },
            IVar(name) => {
                let index = self.ivar_index(e.id, name);
                let obj = self.self_reg();
                let class = self.class_id.unwrap_or(u32::MAX);
                self.field_get(obj, class, index)
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
                    // A constant initialized by a literal is the literal.
                    if let Some(c) = self.literal_const(*cid) {
                        return self.load_const(c);
                    }
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
                    moved: 0,
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
                let l = self.expr(a);
                if let Some(c) = self.out.logical_calls.get(&e.id) {
                    return self.logical_call(e, l, c);
                }
                let res = self.reg();
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
                let l = self.expr(a);
                if let Some(c) = self.out.logical_calls.get(&e.id) {
                    return self.logical_call(e, l, c);
                }
                let res = self.reg();
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
                // On a union with `!` in some members: a type test per
                // such member, the built-in negation for the others.
                if let Some(targets) = self.out.not_dispatch.get(&e.id) {
                    let res = self.reg();
                    let join = self.new_block();
                    for (ty, method) in targets {
                        let is = self.reg();
                        self.emit(Inst::IsA {
                            dst: is,
                            src: v,
                            ty: rt_type(ty),
                        });
                        let (yes, no) = (self.new_block(), self.new_block());
                        self.term(Term::Branch {
                            cond: is,
                            then: yes,
                            els: no,
                        });
                        self.switch(yes);
                        let d = self.reg();
                        self.emit(Inst::Call {
                            dst: d,
                            kind: CallKind::Method(*method),
                            recv: Some(v),
                            args: vec![],
                            splat: false,
                            kw: vec![],
                            kw_splat: None,
                            block: None,
                            moved: 0,
                        });
                        self.emit(Inst::Move { dst: res, src: d });
                        self.term(Term::Jump(join));
                        self.switch(no);
                    }
                    let d = self.reg();
                    self.emit(Inst::Not { dst: d, src: v });
                    self.emit(Inst::Move { dst: res, src: d });
                    self.term(Term::Jump(join));
                    self.switch(join);
                    return res;
                }
                let dst = self.reg();
                // A type with its own `!` is called (by name when the
                // members of a union have different ones).
                if let Some(CallTarget::Method { method }) = self.out.calls.get(&e.id) {
                    let kind = if self.out.dynamic_calls.contains(&e.id) {
                        CallKind::Send("!".to_string())
                    } else {
                        CallKind::Method(*method)
                    };
                    self.emit(Inst::Call {
                        dst,
                        kind,
                        recv: Some(v),
                        args: vec![],
                        splat: false,
                        kw: vec![],
                        kw_splat: None,
                        block: None,
                        moved: 0,
                    });
                    return dst;
                }
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
                    next_value: None,
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
                    let (next, depth, next_value) = (l.next, l.depth, l.next_value);
                    if let Some(dst) = next_value {
                        self.emit(Inst::Move { dst, src: v });
                    }
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

    /// `b << "text #{x}"` on a `String::Builder`: the interpolation is
    /// appended to the builder as it is built (no string is made, no
    /// call is dispatched); the result is the builder, as `<<`'s.
    fn builder_append(&mut self, e: &'a Expr, call: &'a ast::Call) -> Option<Reg> {
        let recv = call.recv.as_ref()?;
        if call.safe_nav || call.block.is_some() || call.args.len() != 1 {
            return None;
        }
        let ast::Arg::Positional(arg) = &call.args[0] else {
            return None;
        };
        let ExprKind::Str(parts) = &arg.kind else {
            return None;
        };
        if parts.iter().all(|p| matches!(p, StrPart::Lit(_))) {
            return None;
        }
        let Some(CallTarget::Method { method }) = self.out.calls.get(&e.id) else {
            return None;
        };
        let m = self.world.method(*method);
        let key = m.is_native.then(|| m.native_key(self.world))?;
        if !matches!(
            key.as_str(),
            "String::Builder#<<" | "String::Builder#push" | "String::Builder#append"
        ) {
            return None;
        }
        let builder = self.expr(recv);
        let mut pieces = Vec::new();
        for p in parts {
            match p {
                StrPart::Lit(s) => {
                    let idx = self.str_const(s);
                    pieces.push(StrPiece::Lit(idx));
                }
                StrPart::Interp(x) => {
                    let r = self.expr(x);
                    pieces.push(StrPiece::Val(r));
                }
            }
        }
        let dst = self.reg();
        self.emit(Inst::Interpolate {
            dst,
            parts: pieces,
            into: Some(builder),
        });
        Some(dst)
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
        self.emit(Inst::Interpolate {
            dst,
            parts: pieces,
            into: None,
        });
        dst
    }

    /// Where declared field `index` of `class` lives: its first physical
    /// field, and the data class stored by value there, if any.
    fn ivar_layout(&self, class: ClassId, index: u32) -> (u32, Option<ClassId>) {
        match self
            .lw
            .layouts
            .get(class as usize)
            .and_then(|l| l.ivars.get(index as usize))
        {
            Some(iv) => (iv.slot, iv.flat),
            None => (index, None),
        }
    }

    fn flat_size(&self, d: ClassId) -> u32 {
        self.lw.layouts[d as usize].slots.len() as u32
    }

    /// Read declared field `index` of the object in `obj`: the physical
    /// field, or, for a data value held in place, that value rebuilt
    /// from its physical fields (an allocation that scalar replacement
    /// removes when only its fields are read).
    fn field_get(&mut self, obj: Reg, class: ClassId, index: u32) -> Reg {
        let (slot, flat) = self.ivar_layout(class, index);
        let Some(d) = flat else {
            let dst = self.reg();
            self.emit(Inst::FieldGet {
                dst,
                obj,
                index: slot,
                class,
            });
            return dst;
        };
        let n = self.flat_size(d);
        let args: Vec<Reg> = (0..n)
            .map(|k| {
                let r = self.reg();
                self.emit(Inst::FieldGet {
                    dst: r,
                    obj,
                    index: slot + k,
                    class,
                });
                r
            })
            .collect();
        let dst = self.reg();
        self.emit(Inst::Call {
            dst,
            kind: CallKind::Construct {
                class: d,
                init: self.lw.layouts[d as usize].init,
            },
            recv: None,
            args,
            splat: false,
            kw: Vec::new(),
            kw_splat: None,
            block: None,
            moved: 0,
        });
        dst
    }

    /// Write `src` to declared field `index` of the object in `obj`: the
    /// physical field, or, for a data value held in place, its physical
    /// fields copied one by one.
    fn field_set(&mut self, obj: Reg, class: ClassId, index: u32, src: Reg) {
        let (slot, flat) = self.ivar_layout(class, index);
        let Some(d) = flat else {
            self.emit(Inst::FieldSet {
                obj,
                index: slot,
                src,
                class,
            });
            return;
        };
        for k in 0..self.flat_size(d) {
            let t = self.reg();
            self.emit(Inst::FieldGet {
                dst: t,
                obj: src,
                index: k,
                class: d,
            });
            self.emit(Inst::FieldSet {
                obj,
                index: slot + k,
                src: t,
                class,
            });
        }
    }

    /// The physical fields a data constructor of `class` takes, from
    /// the declared fields' values.
    fn flatten_args(&mut self, class: ClassId, args: Vec<Reg>) -> Vec<Reg> {
        let flats: Vec<Option<ClassId>> = match self.lw.layouts.get(class as usize) {
            Some(l)
                if l.ivars.len() == args.len() && l.ivars.iter().any(|iv| iv.flat.is_some()) =>
            {
                l.ivars.iter().map(|iv| iv.flat).collect()
            }
            _ => return args,
        };
        let mut out = Vec::new();
        for (r, flat) in args.into_iter().zip(flats) {
            match flat {
                None => out.push(r),
                Some(d) => {
                    for k in 0..self.flat_size(d) {
                        let t = self.reg();
                        self.emit(Inst::FieldGet {
                            dst: t,
                            obj: r,
                            index: k,
                            class: d,
                        });
                        out.push(t);
                    }
                }
            }
        }
        out
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
                            let method = match self.out.block_pass.get(&e.id) {
                                Some(quarz_types::BlockPass::Symbol(_, m)) => Some(*m),
                                _ => None,
                            };
                            let name = self.str_const(name);
                            let dst = self.reg();
                            self.emit(Inst::SymbolProc { dst, name, method });
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
        if let Some(shape) = iter::shape(e, call, self.out, self.world) {
            return self.inline_iter(e, call, shape);
        }
        if iter::exec_shape(e, call, self.out, self.world).is_some() {
            return self.inline_exec(e, call);
        }
        if self.out.bang_assign.contains(&e.id) {
            return self.bang_assign(e, call);
        }
        if let Some(leaves) = self.concat_chain(e, call) {
            let parts: Vec<StrPiece> = leaves
                .into_iter()
                .map(|l| StrPiece::Val(self.expr(l)))
                .collect();
            let dst = self.reg();
            self.emit(Inst::Interpolate {
                dst,
                parts,
                into: None,
            });
            return dst;
        }
        if let Some(dst) = self.builder_append(e, call) {
            return dst;
        }
        let target = self.out.calls.get(&e.id);
        let recv = match call.recv.as_ref() {
            Some(r) => Some(self.expr(r)),
            // An implicit-self call inside a block with a receiver that
            // goes to an enclosing `self`: read it from its hidden slot.
            None if self.out.outer_self_calls.contains(&e.id) => {
                let r = self.out.var_refs[&e.span];
                Some(self.load_var(r))
            }
            // In an `instance_exec` block lowered in place, `self` is the
            // receiver's register, not the activation's `self`.
            None if self.self_override.is_some()
                && matches!(
                    self.out.calls.get(&e.id),
                    Some(CallTarget::Method { .. }) | None
                ) =>
            {
                Some(self.self_reg())
            }
            None => None,
        };
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

    /// Whether the call `id` resolves to a native method, which may
    /// update its receiver in place when nothing else refers to it.
    /// Whether the call is to a native with an in-place variant: only
    /// the collections have them (an owned call to anything else, a
    /// number's `+` say, is a slower ordinary call).
    fn is_owned_native(&self, id: &u32) -> bool {
        let Some(CallTarget::Method { method }) = self.out.calls.get(id) else {
            return false;
        };
        let m = self.world.method(*method);
        let b = &self.world.builtin;
        m.is_native && [b.array, b.hash, b.set].contains(&m.owner)
    }

    /// `x.foo!(args)` as `x = x.foo(args)` (the checker resolved `foo`):
    /// an in-place update for a native, a call and a store otherwise.
    fn bang_assign(&mut self, e: &'a Expr, call: &'a ast::Call) -> Reg {
        let recv = call.recv.as_ref().unwrap();
        let Some(CallTarget::Method { method }) = self.out.calls.get(&e.id) else {
            return self.nil();
        };
        let method = *method;
        // A chain `x.foo!.bar!`: the inner call has stored into the place
        // already; this one uses its value and stores again.
        let mut root = recv;
        while let ExprKind::Call(inner) = &root.kind {
            if !self.out.bang_assign.contains(&root.id) {
                break;
            }
            match inner.recv.as_ref() {
                Some(r) => root = r,
                None => break,
            }
        }
        let chained = !std::ptr::eq(root, recv);
        let a = self.args(&call.args);
        let simple = a.block.is_none() && !a.splat && a.kw_splat.is_none();
        let owned = simple && self.world.method(method).is_native && !chained;
        match &root.kind {
            ExprKind::Local(_) => {
                let r = self.var_ref(root.span);
                if let (Some(r), true) = (r, owned) {
                    let loc = self.var_loc(r);
                    let dst = self.reg();
                    self.emit(Inst::OwnedCall {
                        dst,
                        method,
                        recv: loc,
                        args: a.pos,
                        kw: a.kw,
                        unused: false,
                    });
                    return dst;
                }
                let recv_reg = if chained {
                    self.expr(recv)
                } else {
                    match r {
                        Some(r) => self.load_var(r),
                        None => self.nil(),
                    }
                };
                let dst = self.reg();
                self.emit(Inst::Call {
                    dst,
                    kind: CallKind::Method(method),
                    recv: Some(recv_reg),
                    args: a.pos,
                    splat: a.splat,
                    kw: a.kw,
                    kw_splat: a.kw_splat,
                    block: a.block,
                    moved: 0,
                });
                if let Some(r) = r {
                    self.store_var(r, dst);
                }
                dst
            }
            ExprKind::IVar(name) => {
                let index = self.ivar_index(root.id, name);
                let class = self.class_id.unwrap_or(u32::MAX);
                let (slot, flat) = self.ivar_layout(class, index);
                if owned && flat.is_none() {
                    let obj = self.self_reg();
                    let dst = self.reg();
                    self.emit(Inst::OwnedCall {
                        dst,
                        method,
                        recv: VarLoc::Field { obj, index: slot },
                        args: a.pos,
                        kw: a.kw,
                        unused: false,
                    });
                    return dst;
                }
                let recv_reg = if chained {
                    self.expr(recv)
                } else {
                    let obj = self.self_reg();
                    self.field_get(obj, class, index)
                };
                let dst = self.reg();
                self.emit(Inst::Call {
                    dst,
                    kind: CallKind::Method(method),
                    recv: Some(recv_reg),
                    args: a.pos,
                    splat: a.splat,
                    kw: a.kw,
                    kw_splat: a.kw_splat,
                    block: a.block,
                    moved: 0,
                });
                let obj = self.self_reg();
                self.field_set(obj, class, index, dst);
                dst
            }
            _ => self.nil(),
        }
    }

    /// `recv.instance_exec(args) { ... }` with a literal block: the body
    /// in this function, `self` being the receiver's register (its class
    /// known from the receiver's static type), `break`/`next` jumping to
    /// the join with the call's value.
    fn inline_exec(&mut self, e: &'a Expr, call: &'a ast::Call) -> Reg {
        let block = call.block.as_ref().unwrap();
        let recv = match &call.recv {
            Some(r) => self.expr(r),
            None => self.self_reg(),
        };
        let recv_class = match &call.recv {
            Some(r) => match self.out.node_types.get(&r.id) {
                Some(Type::Class(id, _)) => Some(*id),
                _ => None,
            },
            None => self.class_id,
        };
        let args: Vec<Reg> = call
            .args
            .iter()
            .map(|a| match a {
                Arg::Positional(x) => self.expr(x),
                _ => unreachable!(),
            })
            .collect();
        let result = self.nil();
        let join = self.new_block();
        // The body's registers start as nil (it may run again in a loop).
        let clear_from = self.func.nregs;
        let clear_at = (self.cur, self.func.blocks[self.cur as usize].insts.len());
        self.emit(Inst::ClearRegs {
            from: clear_from,
            to: clear_from,
        });
        let saved_override = self.self_override.replace(recv);
        let saved_class = self.class_id;
        self.class_id = recv_class;
        self.inline.push(InlineLevel::new(SelfOwner::Block(e.id)));
        for pi in 0..block.params.list.len() {
            let src = match args.get(pi) {
                Some(r) => *r,
                None => self.nil(),
            };
            self.store_var(
                VarRef {
                    depth: 0,
                    slot: pi as u32,
                },
                src,
            );
        }
        self.store_self_slot(SelfOwner::Block(e.id));
        self.loops.push(LoopCtx {
            next: join,
            exit: join,
            result,
            depth: self.handlers.len(),
            next_value: Some(result),
        });
        let v = self.body(&block.body);
        self.loops.pop();
        self.emit(Inst::Move {
            dst: result,
            src: v,
        });
        self.term(Term::Jump(join));
        let level = self.inline.pop().expect("the inline level");
        self.self_override = saved_override;
        self.class_id = saved_class;
        let clear_to = self.func.nregs;
        if let Inst::ClearRegs { to, .. } =
            &mut self.func.blocks[clear_at.0 as usize].insts[clear_at.1]
        {
            *to = clear_to;
        }
        self.switch(join);
        self.release_inline(level);
        result
    }

    /// The `Int` operator method `op` (for a typed `BinOp`).
    fn int_op(&self, op: FastOp) -> Option<MethodId> {
        let name = match op {
            FastOp::Lt => "<",
            FastOp::Le => "<=",
            FastOp::Add => "+",
            _ => return None,
        };
        let int = self.world.builtin.int;
        self.world
            .methods
            .iter()
            .find(|m| {
                m.owner == int
                    && m.name == name
                    && m.params.len() == 1
                    && matches!(&m.params[0].ty, Type::Class(c, a) if *c == int && a.is_empty())
            })
            .map(|m| m.id)
    }

    /// `n.times { }`, `xs.each { }`, `(lo..hi).map { }` and the other
    /// shapes of `iter`: a counted loop in this function, with the block
    /// body lowered in place (`break` and `next` become jumps).
    fn inline_iter(&mut self, e: &'a Expr, call: &'a ast::Call, shape: Shape) -> Reg {
        let block = call.block.as_ref();
        let kind = shape.kind;
        // The receiver (or the range's bounds), then the arguments.
        let mut lo = None;
        let mut hi = None;
        let mut arr = None;
        let mut exclusive = false;
        match shape.source {
            Some(Source::Range) => {
                let ExprKind::Range {
                    lo: l,
                    hi: h,
                    exclusive: ex,
                } = &call.recv.as_ref().unwrap().kind
                else {
                    unreachable!()
                };
                lo = Some(self.expr(l.as_ref().unwrap()));
                hi = Some(self.expr(h.as_ref().unwrap()));
                exclusive = *ex;
            }
            Some(Source::Array) => arr = Some(self.expr(call.recv.as_ref().unwrap())),
            None => {
                let r = match &call.recv {
                    Some(x) => self.expr(x),
                    None => self.self_reg(),
                };
                if kind == Kind::Times {
                    hi = Some(r);
                    exclusive = true;
                } else {
                    lo = Some(r);
                }
            }
        }
        let args: Vec<Reg> = call
            .args
            .iter()
            .filter_map(|a| match a {
                Arg::Positional(x) => Some(self.expr(x)),
                // `&:name` (see `Shape::symbol`).
                Arg::BlockPass(_) => None,
                _ => unreachable!(),
            })
            .collect();
        if kind == Kind::Upto {
            hi = Some(args[0]);
        }
        if let Some(a) = arr {
            let len = self.reg();
            self.emit(Inst::Len { dst: len, src: a });
            hi = Some(len);
            exclusive = true;
        }
        let lo = match lo {
            Some(r) => r,
            None => self.load_const(Constant::Int(0)),
        };
        let hi = hi.unwrap();
        // The counter, the call's result, the block's value per
        // iteration, and the accumulator or the array being built.
        let i = self.reg();
        self.emit(Inst::Move { dst: i, src: lo });
        let result = self.nil();
        let acc = match kind {
            Kind::Reduce => {
                let r = self.reg();
                self.emit(Inst::Move {
                    dst: r,
                    src: args[0],
                });
                Some(r)
            }
            Kind::Count => {
                let r = self.reg();
                let zero = self.load_const(Constant::Int(0));
                self.emit(Inst::Move { dst: r, src: zero });
                Some(r)
            }
            _ => None,
        };
        let out = matches!(kind, Kind::Map | Kind::Select | Kind::Reject).then(|| {
            let r = self.reg();
            self.emit(Inst::MakeArray {
                dst: r,
                items: Vec::new(),
            });
            r
        });
        let cond_b = self.new_block();
        let body_b = self.new_block();
        let next_b = self.new_block();
        let done_b = self.new_block();
        let exit_b = self.new_block();
        self.term(Term::Jump(cond_b));
        self.switch(cond_b);
        let c = self.reg();
        let op = if exclusive { FastOp::Lt } else { FastOp::Le };
        let method = self.int_op(op);
        self.emit(Inst::BinOp {
            dst: c,
            op,
            lhs: i,
            rhs: hi,
            method,
        });
        self.term(Term::Branch {
            cond: c,
            then: body_b,
            els: done_b,
        });
        self.switch(body_b);
        let elem = match arr {
            Some(a) => {
                let x = self.reg();
                self.emit(Inst::ArrayGetReg {
                    dst: x,
                    arr: a,
                    index: i,
                });
                x
            }
            None => i,
        };
        // Every register the body uses (its variables, its temporaries
        // and its value) starts each iteration as nil, which also
        // releases what the previous iteration left: `acc = acc.push(x)`
        // then finds `acc` unshared and pushes in place. The range is
        // known once the body is lowered.
        let clear_from = self.func.nregs;
        let clear_at = (self.cur, self.func.blocks[self.cur as usize].insts.len());
        self.emit(Inst::ClearRegs {
            from: clear_from,
            to: clear_from,
        });
        let val = self.reg();
        let yielded: Vec<Reg> = match kind {
            Kind::EachWithIndex => vec![elem, i],
            Kind::Reduce => vec![acc.unwrap(), elem],
            _ => vec![elem],
        };
        self.inline.push(InlineLevel::new(SelfOwner::Block(e.id)));
        let nparams = block.map_or(0, |b| b.params.list.len());
        for pi in 0..nparams {
            let src = match yielded.get(pi) {
                Some(r) => *r,
                None => self.nil(),
            };
            self.store_var(
                VarRef {
                    depth: 0,
                    slot: pi as u32,
                },
                src,
            );
        }
        self.loops.push(LoopCtx {
            next: next_b,
            exit: exit_b,
            result,
            depth: self.handlers.len(),
            next_value: Some(val),
        });
        let v = match (block, shape.symbol) {
            (Some(block), _) => self.body(&block.body),
            // `&:name`: the method called on the element.
            (None, Some(m)) => {
                let d = self.reg();
                self.emit(Inst::Call {
                    dst: d,
                    kind: CallKind::Method(m),
                    recv: Some(elem),
                    args: Vec::new(),
                    splat: false,
                    kw: Vec::new(),
                    kw_splat: None,
                    block: None,
                    moved: 0,
                });
                d
            }
            (None, None) => unreachable!("an inlined iteration without a block"),
        };
        self.loops.pop();
        self.emit(Inst::Move { dst: val, src: v });
        self.term(Term::Jump(next_b));
        let level = self.inline.pop().expect("the inline level");
        let clear_to = self.func.nregs;
        if let Inst::ClearRegs { to, .. } =
            &mut self.func.blocks[clear_at.0 as usize].insts[clear_at.1]
        {
            *to = clear_to;
        }
        self.switch(next_b);
        self.release_inline(level);
        match kind {
            Kind::Map => self.emit(Inst::ArrayPush {
                arr: out.unwrap(),
                src: val,
            }),
            Kind::Select | Kind::Reject => {
                let push_b = self.new_block();
                let skip_b = self.new_block();
                let (then, els) = if kind == Kind::Select {
                    (push_b, skip_b)
                } else {
                    (skip_b, push_b)
                };
                self.term(Term::Branch {
                    cond: val,
                    then,
                    els,
                });
                self.switch(push_b);
                self.emit(Inst::ArrayPush {
                    arr: out.unwrap(),
                    src: elem,
                });
                self.term(Term::Jump(skip_b));
                self.switch(skip_b);
            }
            Kind::Reduce => self.emit(Inst::Move {
                dst: acc.unwrap(),
                src: val,
            }),
            Kind::Count => {
                let inc_b = self.new_block();
                let skip_b = self.new_block();
                self.term(Term::Branch {
                    cond: val,
                    then: inc_b,
                    els: skip_b,
                });
                self.switch(inc_b);
                let one = self.load_const(Constant::Int(1));
                let n = self.reg();
                let add = self.int_op(FastOp::Add);
                self.emit(Inst::BinOp {
                    dst: n,
                    op: FastOp::Add,
                    lhs: acc.unwrap(),
                    rhs: one,
                    method: add,
                });
                self.emit(Inst::Move {
                    dst: acc.unwrap(),
                    src: n,
                });
                self.term(Term::Jump(skip_b));
                self.switch(skip_b);
            }
            Kind::Any | Kind::All => {
                // The first accepted (`any?`) or rejected (`all?`) element
                // decides: the result is set and the loop left.
                let stop_b = self.new_block();
                let go_b = self.new_block();
                let (then, els) = if kind == Kind::Any {
                    (stop_b, go_b)
                } else {
                    (go_b, stop_b)
                };
                self.term(Term::Branch {
                    cond: val,
                    then,
                    els,
                });
                self.switch(stop_b);
                let decided = self.load_const(Constant::Bool(kind == Kind::Any));
                self.emit(Inst::Move {
                    dst: result,
                    src: decided,
                });
                self.emit(Inst::ClearRegs {
                    from: clear_from,
                    to: clear_from,
                });
                self.term(Term::Jump(exit_b));
                self.switch(go_b);
            }
            _ => {}
        }
        let one = self.load_const(Constant::Int(1));
        let next_i = self.reg();
        let add = self.int_op(FastOp::Add);
        self.emit(Inst::BinOp {
            dst: next_i,
            op: FastOp::Add,
            lhs: i,
            rhs: one,
            method: add,
        });
        self.emit(Inst::Move {
            dst: i,
            src: next_i,
        });
        self.term(Term::Jump(cond_b));
        self.switch(done_b);
        self.emit(Inst::ClearRegs {
            from: clear_from,
            to: clear_to,
        });
        match kind {
            Kind::Map | Kind::Select | Kind::Reject => self.emit(Inst::Move {
                dst: result,
                src: out.unwrap(),
            }),
            Kind::Reduce | Kind::Count => self.emit(Inst::Move {
                dst: result,
                src: acc.unwrap(),
            }),
            Kind::Any | Kind::All => {
                let v = self.load_const(Constant::Bool(kind == Kind::All));
                self.emit(Inst::Move {
                    dst: result,
                    src: v,
                });
            }
            _ => {}
        }
        self.term(Term::Jump(exit_b));
        self.switch(exit_b);
        result
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
            a.block = Some(self.share_proc(e.id, dst));
        }
        let kind = match target {
            Some(CallTarget::Method { .. }) if self.out.dynamic_calls.contains(&e.id) => {
                CallKind::Send(call.name.clone())
            }
            Some(CallTarget::Method { method }) => {
                let m = self.world.method(*method);
                // A generated field reader that nothing overrides is a
                // field access.
                if let quarz_types::Synth::FieldGet(name) = &m.synth {
                    if a.pos.is_empty()
                        && !a.splat
                        && a.kw.is_empty()
                        && a.kw_splat.is_none()
                        && a.block.is_none()
                        && !self.lw.overridden.contains(&(m.owner, m.name.clone()))
                    {
                        if let Some(index) = self.world.field_index(m.owner, name) {
                            let obj = recv.unwrap_or_else(|| self.self_reg());
                            return self.field_get(obj, m.owner, index as u32);
                        }
                    }
                }
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
            Some(CallTarget::Constructor { class, init }) => {
                // A data constructor takes the physical fields.
                let data_init = init
                    .is_some_and(|m| self.world.method(m).synth == quarz_types::Synth::DataInit);
                if data_init && !a.splat && a.kw.is_empty() && a.kw_splat.is_none() {
                    a.pos = self.flatten_args(*class, std::mem::take(&mut a.pos));
                }
                // `new` on the receiver of a class method that subclasses
                // may inherit: the class it is called on decides.
                if self.out.self_new.contains(&e.id)
                    && self
                        .world
                        .classes
                        .iter()
                        .any(|c| c.id != *class && self.world.class_is_a(c.id, *class))
                {
                    let (class, init) = (*class, *init);
                    let recv = Some(recv.unwrap_or_else(|| self.self_reg()));
                    let dst = self.reg();
                    self.emit(Inst::Call {
                        dst,
                        kind: CallKind::ConstructRecv { class, init },
                        recv,
                        args: a.pos,
                        splat: a.splat,
                        kw: a.kw,
                        kw_splat: a.kw_splat,
                        block: a.block,
                        moved: 0,
                    });
                    return dst;
                }
                CallKind::Construct {
                    class: *class,
                    init: *init,
                }
            }
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
            moved: 0,
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
                            depth: self.method_level_depth(),
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
                Some(self.share_proc(e.id, dst))
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
            moved: 0,
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
                            // Only natives update in place; a user method is
                            // better off called directly (or inlined).
                            if let Some(CallTarget::Method { method }) = self
                                .out
                                .calls
                                .get(&value.id)
                                .filter(|_| self.is_owned_native(&value.id))
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
                                        unused: false,
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
                                    moved: 0,
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
                let index = self.ivar_index(e.id, name);
                // `@x = @x.meth(args)`: update the field's value in place
                // when nothing else refers to it.
                if let ExprKind::Call(call) = &value.kind {
                    if let Some(Expr {
                        kind: ExprKind::IVar(rname),
                        ..
                    }) = &call.recv
                    {
                        if rname == name && call.block.is_none() && !call.safe_nav {
                            if let Some(CallTarget::Method { method }) = self
                                .out
                                .calls
                                .get(&value.id)
                                .filter(|_| self.is_owned_native(&value.id))
                            {
                                let method = *method;
                                let a = self.args(&call.args);
                                let class = self.class_id.unwrap_or(u32::MAX);
                                let (slot, flat) = self.ivar_layout(class, index);
                                if a.block.is_none()
                                    && !a.splat
                                    && a.kw_splat.is_none()
                                    && flat.is_none()
                                {
                                    let obj = self.self_reg();
                                    let dst = self.reg();
                                    self.emit(Inst::OwnedCall {
                                        dst,
                                        method,
                                        recv: VarLoc::Field { obj, index: slot },
                                        args: a.pos,
                                        kw: a.kw,
                                        unused: false,
                                    });
                                    return dst;
                                }
                                let obj = self.self_reg();
                                let recv = self.field_get(obj, class, index);
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
                                    moved: 0,
                                });
                                let obj = self.self_reg();
                                self.field_set(obj, class, index, dst);
                                return dst;
                            }
                        }
                    }
                }
                let v = self.expr(value);
                let obj = self.self_reg();
                let class = self.class_id.unwrap_or(u32::MAX);
                self.field_set(obj, class, index, v);
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
            moved: 0,
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
            moved: 0,
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
                let class = self.class_id.unwrap_or(u32::MAX);
                let dst = self.field_get(obj, class, index);
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
                    moved: 0,
                });
                (dst, Place::Index(r, a.pos, a.splat))
            }
            LValue::Const(_) => return self.nil(),
        };
        // Combine.
        let res = self.reg();
        let join = self.new_block();
        let logical = self.out.logical_calls.get(&e.id);
        match op {
            OpAssign::OrOr | OpAssign::AndAnd if logical.is_some() => {
                let v = self.logical_call(e, current, logical.unwrap());
                self.emit(Inst::Move { dst: res, src: v });
            }
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
                // The checker resolved the operator (`x += 1` is `x + 1`);
                // the method tells the compiler the operand types.
                let method = match self.out.calls.get(&e.id) {
                    Some(CallTarget::Method { method }) => Some(*method),
                    _ => None,
                };
                let v = match FastOp::from_name(&name) {
                    Some(fop) => {
                        let dst = self.reg();
                        self.emit(Inst::BinOp {
                            dst,
                            op: fop,
                            lhs: current,
                            rhs,
                            method,
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
                let class = self.class_id.unwrap_or(u32::MAX);
                self.field_set(obj, class, index, res);
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

    /// A block or lambda made where a shareable procedure is expected
    /// (`Output::shareable_procs`, by the id the checker recorded): a copy
    /// with what it captures copied, as `spawn` makes, which reads no
    /// frame of the creator's and so may run on any task.
    fn share_proc(&mut self, id: ast::NodeId, block: Reg) -> Reg {
        if !self.out.shareable_procs.contains(&id) {
            return block;
        }
        self.send(block, "__copy_captures", Vec::new())
    }

    /// `a && b` (or `x ||= b`) as the call of the type's own operator the
    /// checker made of it, `a.&&() { b }`, on `recv`, `a`'s value.
    fn logical_call(&mut self, e: &'a Expr, recv: Reg, c: &'a Expr) -> Reg {
        let ExprKind::Call(call) = &c.kind else {
            unreachable!("a logical call is a call")
        };
        let target = self.out.calls.get(&e.id);
        self.call_value(e, call, target, Some(recv))
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
                let class = self.class_id.unwrap_or(u32::MAX);
                self.field_set(obj, class, index, v);
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
