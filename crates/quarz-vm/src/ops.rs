//! What each instruction does, given its operands rather than the
//! instruction: the interpreter's `exec_inst` dispatches to these, and
//! compiled code calls them through `ffi`'s `qz_op_*` entries (an
//! executable carries no instructions), so both run the same code.

use crate::rc::Rc;
use std::cell::{Cell, RefCell};

use quarz_ir::*;
use smallvec::{smallvec, SmallVec};

use crate::interp::{fast_binop, ArgVec, Flow, Interp};
use crate::value::*;
use crate::vm::Activation;

/// What a call calls (`CallKind`, its name borrowed).
#[derive(Clone, Copy, Debug)]
pub enum CallOp<'a> {
    Method(MethodId),
    Send(&'a str),
    Construct {
        class: ClassId,
        init: Option<MethodId>,
    },
    ConstructRecv {
        class: ClassId,
        init: Option<MethodId>,
    },
    ProcCall,
    Yield,
    Super(MethodId),
    /// `CallKind::Function`: this method, not looked up on the receiver.
    Function(MethodId),
    Raise,
}

impl<'a> CallOp<'a> {
    pub fn of(kind: &'a CallKind) -> CallOp<'a> {
        match kind {
            CallKind::Method(m) => CallOp::Method(*m),
            CallKind::Send(name) => CallOp::Send(name),
            CallKind::Construct { class, init } => CallOp::Construct {
                class: *class,
                init: *init,
            },
            CallKind::ConstructRecv { class, init } => CallOp::ConstructRecv {
                class: *class,
                init: *init,
            },
            CallKind::ProcCall => CallOp::ProcCall,
            CallKind::Yield => CallOp::Yield,
            CallKind::Super(m) => CallOp::Super(*m),
            CallKind::Function(m) => CallOp::Function(*m),
            CallKind::Raise => CallOp::Raise,
        }
    }
}

/// A call's operands (`Inst::Call`).
#[derive(Clone, Copy, Debug)]
pub struct CallOps<'a> {
    pub dst: Reg,
    pub kind: CallOp<'a>,
    pub recv: Option<Reg>,
    pub args: &'a [Reg],
    pub splat: bool,
    pub kw: &'a [(u32, Reg)],
    pub kw_splat: Option<Reg>,
    pub block: Option<Reg>,
    pub moved: u16,
}

/// An in-place call's operands (`Inst::OwnedCall`).
#[derive(Clone, Copy, Debug)]
pub struct OwnedOps<'a> {
    pub dst: Reg,
    pub method: MethodId,
    pub recv: VarLoc,
    pub args: &'a [Reg],
    pub kw: &'a [(u32, Reg)],
    pub unused: bool,
}

impl Interp {
    pub fn op_load_const(
        &self,
        f: &FuncInfo,
        pool: &RefCell<Vec<Value>>,
        regs: &mut [Value],
        dst: Reg,
        idx: u32,
    ) -> Result<(), Flow> {
        regs[dst as usize] = self.constant(f, pool, idx)?;
        Ok(())
    }

    pub fn op_has_arg(&self, act: &Activation, regs: &mut [Value], dst: Reg, index: u32) {
        regs[dst as usize] = Value::Bool(act.has_arg(index));
    }

    pub fn op_field_get_by_name(
        &self,
        f: &FuncInfo,
        regs: &mut [Value],
        dst: Reg,
        found: Reg,
        obj: Reg,
        name: u32,
    ) {
        let name = self.str_const(f, name);
        let (v, ok) = match &regs[obj as usize] {
            Value::Object(o) => match self.field_index(o.class, name) {
                Some(i) => (self.logical_get(o, i), true),
                None => (Value::Nil, false),
            },
            _ => (Value::Nil, false),
        };
        regs[dst as usize] = v;
        regs[found as usize] = Value::Bool(ok);
    }

    pub fn op_unit_self(&self, regs: &mut [Value], dst: Reg, file: u32, class: ClassId) {
        regs[dst as usize] = self.unit_self_of(file, class);
    }

    pub fn op_const_get(&self, regs: &mut [Value], dst: Reg, id: u32) -> Result<(), Flow> {
        regs[dst as usize] = self.const_value(id)?;
        Ok(())
    }

    pub fn op_variant_singleton(&self, regs: &mut [Value], dst: Reg, class: ClassId) {
        regs[dst as usize] = self.variant_singleton(class);
    }

    pub fn op_call(
        &self,
        f: &FuncInfo,
        pool: &RefCell<Vec<Value>>,
        act: &Activation,
        regs: &mut [Value],
        c: CallOps<'_>,
    ) -> Result<(), Flow> {
        // A native with a by-reference version takes the receiver and
        // arguments from the registers directly. The method it resolves
        // to is kept for the call below.
        let mut resolved: Option<MethodId> = None;
        let target = match c.kind {
            CallOp::Method(mid) => Some((mid, true)),
            CallOp::Function(mid) => Some((mid, false)),
            _ => None,
        };
        if let Some((mid, dispatch)) = target {
            if !c.splat && c.kw.is_empty() && c.kw_splat.is_none() && c.block.is_none() {
                let recv_ref = match c.recv {
                    Some(r) => &regs[r as usize],
                    None => &act.self_val,
                };
                let mid = if dispatch {
                    self.resolve_dynamic(recv_ref, mid)
                } else {
                    mid
                };
                resolved = Some(mid);
                if c.args.len() <= 3 {
                    if let Some(fast) = self.program.fast_natives[mid as usize] {
                        let result = {
                            let refs: SmallVec<[&Value; 3]> =
                                c.args.iter().map(|r| &regs[*r as usize]).collect();
                            fast(self, recv_ref, &refs)
                        };
                        if let Some(r) = result {
                            let v = r?;
                            regs[c.dst as usize] = v;
                            if c.moved != 0 && crate::deinit::enabled() {
                                self.release_moved(regs, &c);
                            }
                            return Ok(());
                        }
                    }
                }
                // A method body with positional parameters: straight to
                // it (what `invoke` and `bind_params` would do, without
                // their checks), the arguments moved in as below.
                if let Some(fid) = self.program.direct_funcs[mid as usize] {
                    let recv = match c.recv {
                        Some(r) if c.moved & (1 << 15) != 0 => {
                            std::mem::replace(&mut regs[r as usize], Value::Nil)
                        }
                        Some(r) => regs[r as usize].clone(),
                        None => act.self_val.clone(),
                    };
                    let nparams = self.program.method(mid).params.len();
                    let mut pos = ArgVec::with_capacity(c.args.len());
                    let mut bits = c.moved & 0x7fff;
                    for r in c.args.iter().take(nparams) {
                        let slot = &mut regs[*r as usize];
                        pos.push(if bits & 1 != 0 {
                            std::mem::replace(slot, Value::Nil)
                        } else {
                            slot.clone()
                        });
                        bits >>= 1;
                    }
                    let n = pos.len();
                    let provided = if n >= 64 { u64::MAX } else { (1u64 << n) - 1 };
                    let v = self.run_method(mid, fid, recv, pos, provided, None)?;
                    regs[c.dst as usize] = v;
                    return Ok(());
                }
            }
        }
        // What the call reads for the last time moves into it (`moved`,
        // from lowering), so that a value passed on keeps a single
        // reference.
        let recv = match c.recv {
            Some(r) if c.moved & (1 << 15) != 0 => {
                std::mem::replace(&mut regs[r as usize], Value::Nil)
            }
            Some(r) => regs[r as usize].clone(),
            None => act.self_val.clone(),
        };
        let pos = if c.moved & 0x7fff != 0 {
            let mut pos = ArgVec::with_capacity(c.args.len());
            let mut bits = c.moved & 0x7fff;
            for r in c.args {
                let slot = &mut regs[*r as usize];
                pos.push(if bits & 1 != 0 {
                    std::mem::replace(slot, Value::Nil)
                } else {
                    slot.clone()
                });
                bits >>= 1;
            }
            pos
        } else {
            self.call_args(regs, c.args, c.splat)
        };
        let kw = self.call_kwargs(f, pool, regs, c.kw, c.kw_splat);
        let block = c.block.map(|b| regs[b as usize].clone());
        let r = match c.kind {
            CallOp::Method(mid) => {
                let mid = resolved.unwrap_or_else(|| self.resolve_dynamic(&recv, mid));
                let r = self.invoke(mid, recv, pos, kw, block.clone());
                self.catch_break(&block, r)
            }
            CallOp::Send(name) => {
                let r = self.send_kw(&recv, name, pos, kw, block.clone());
                self.catch_break(&block, r)
            }
            CallOp::Construct { class, init } => {
                let r = self.construct(class, init, pos, kw, block.clone());
                self.catch_break(&block, r)
            }
            CallOp::ConstructRecv { class, init } => {
                let (cid, init) = self.receiver_class_init(&recv, class, init);
                let r = self.construct(cid, init, pos, kw, block.clone());
                self.catch_break(&block, r)
            }
            CallOp::ProcCall => {
                let r = self.call_block(&recv, pos);
                self.catch_break(&block, r)
            }
            CallOp::Yield => {
                if act.block.is_nil() {
                    Err(self.raise(self.program.exc.runtime_error, "no block given (yield)"))
                } else {
                    self.call_block(&act.block, pos)
                }
            }
            CallOp::Super(mid) | CallOp::Function(mid) => {
                let r = self.invoke(mid, recv, pos, kw, block.clone());
                self.catch_break(&block, r)
            }
            CallOp::Raise => self.eval_raise(pos),
        };
        regs[c.dst as usize] = r?;
        // What the call released (what moved into it, a block's frame
        // left by `break`) is finalized at its end, as compiled code does.
        if crate::deinit::enabled() {
            self.finalize_pending();
        }
        Ok(())
    }

    /// After a call that read its operands in place: in a program with a
    /// `deinitialize`, those it read for the last time (`moved`) are
    /// released now, as when they move into a call, and finalized.
    #[cold]
    fn release_moved(&self, regs: &mut [Value], c: &CallOps<'_>) {
        let mut bits = c.moved & 0x7fff;
        for r in c.args.iter().take(15) {
            if bits & 1 != 0 && *r != c.dst {
                regs[*r as usize] = Value::Nil;
            }
            bits >>= 1;
        }
        if let Some(r) = c.recv {
            if c.moved & (1 << 15) != 0 && r != c.dst {
                regs[r as usize] = Value::Nil;
            }
        }
        if crate::deinit::pending() {
            self.run_deinitializers();
        }
    }

    pub fn op_owned_call(
        &self,
        f: &FuncInfo,
        pool: &RefCell<Vec<Value>>,
        act: &Activation,
        regs: &mut [Value],
        c: OwnedOps<'_>,
    ) -> Result<(), Flow> {
        if c.kw.is_empty() && c.args.len() <= 2 {
            // The arguments by reference: the fast paths clone only what
            // they keep.
            let argv: SmallVec<[Value; 2]> =
                c.args.iter().map(|r| regs[*r as usize].clone()).collect();
            let refs: SmallVec<[&Value; 2]> = argv.iter().collect();
            match c.recv {
                VarLoc::Reg(r) => {
                    if self.owned_fast(c.method, &mut regs[r as usize], &refs) {
                        if !c.unused {
                            regs[c.dst as usize] = regs[r as usize].clone();
                        }
                        return Ok(());
                    }
                }
                VarLoc::Field { obj, index } => {
                    if let Value::Object(o) = &regs[obj as usize] {
                        // SAFETY: `owned_fast` runs no Quarz code, and the
                        // field of `@x = @x.meth` belongs to a mutable
                        // object, which only its own task touches.
                        if let Some(slot) = unsafe { o.field_value_mut(index as usize) } {
                            if self.owned_fast(c.method, slot, &refs) {
                                if !c.unused {
                                    let v = slot.clone();
                                    regs[c.dst as usize] = v;
                                }
                                return Ok(());
                            }
                        }
                    }
                }
                VarLoc::Frame { .. } => {}
            }
        }
        let pos = self.call_args(regs, c.args, false);
        let kw = self.call_kwargs(f, pool, regs, c.kw, None);
        let take_field = |obj: Reg, index: u32| -> Value {
            match &regs[obj as usize] {
                Value::Object(o) => o.take_field(index as usize),
                _ => Value::Nil,
            }
        };
        let put_field = |regs: &[Value], obj: Reg, index: u32, v: Value| {
            if let Value::Object(o) = &regs[obj as usize] {
                if (index as usize) < o.field_count() {
                    o.set_field(index as usize, v);
                }
            }
        };
        let old = match c.recv {
            VarLoc::Reg(r) => std::mem::replace(&mut regs[r as usize], Value::Nil),
            VarLoc::Frame { depth, slot } => {
                let fr = self.frame(act);
                let old = fr.get(depth, slot);
                fr.set(depth, slot, Value::Nil);
                old
            }
            VarLoc::Field { obj, index } => take_field(obj, index),
        };
        match self.invoke_owned(c.method, old, pos, kw) {
            Ok(v) => {
                let v = if c.unused {
                    v
                } else {
                    regs[c.dst as usize] = v.clone();
                    v
                };
                match c.recv {
                    VarLoc::Reg(r) => regs[r as usize] = v,
                    VarLoc::Frame { depth, slot } => self.frame(act).set(depth, slot, v),
                    VarLoc::Field { obj, index } => put_field(regs, obj, index, v),
                }
                Ok(())
            }
            Err((e, old)) => {
                match c.recv {
                    VarLoc::Reg(r) => regs[r as usize] = old,
                    VarLoc::Frame { depth, slot } => self.frame(act).set(depth, slot, old),
                    VarLoc::Field { obj, index } => put_field(regs, obj, index, old),
                }
                Err(e)
            }
        }
    }

    pub fn op_binop(
        &self,
        regs: &mut [Value],
        dst: Reg,
        op: FastOp,
        lhs: Reg,
        rhs: Reg,
        method: Option<MethodId>,
    ) -> Result<(), Flow> {
        let v = match fast_binop(op, &regs[lhs as usize], &regs[rhs as usize]) {
            Some(v) => v,
            None => {
                let l = regs[lhs as usize].clone();
                let r = regs[rhs as usize].clone();
                match method {
                    Some(mid) => {
                        let mid = self.resolve_dynamic(&l, mid);
                        self.invoke(mid, l, smallvec![r], Vec::new(), None)?
                    }
                    None => self.send(&l, op.name(), smallvec![r], None)?,
                }
            }
        };
        regs[dst as usize] = v;
        Ok(())
    }

    pub fn op_case_eq(
        &self,
        regs: &mut [Value],
        dst: Reg,
        pattern: Reg,
        value: Reg,
    ) -> Result<(), Flow> {
        let r = self.case_eq(&regs[pattern as usize], &regs[value as usize])?;
        regs[dst as usize] = Value::Bool(r);
        Ok(())
    }

    pub fn op_equal(&self, regs: &mut [Value], dst: Reg, a: Reg, b: Reg) -> Result<(), Flow> {
        let r = self.values_equal(&regs[a as usize], &regs[b as usize])?;
        regs[dst as usize] = Value::Bool(r);
        Ok(())
    }

    pub fn op_class_is_a(&self, regs: &mut [Value], dst: Reg, src: Reg, class: ClassId) {
        let r = self
            .program
            .world
            .class_is_a(self.class_of(&regs[src as usize]), class);
        regs[dst as usize] = Value::Bool(r);
    }

    pub fn op_is_a(&self, regs: &mut [Value], dst: Reg, src: Reg, ty: &RtType) {
        let r = self.is_a(&regs[src as usize], ty);
        regs[dst as usize] = Value::Bool(r);
    }

    #[allow(clippy::too_many_arguments)]
    pub fn op_as(
        &self,
        regs: &mut [Value],
        dst: Reg,
        src: Reg,
        ty: &RtType,
        optional: bool,
        name: &str,
    ) -> Result<(), Flow> {
        let v = regs[src as usize].clone();
        regs[dst as usize] = if self.is_a(&v, ty) {
            v
        } else if optional {
            Value::Nil
        } else {
            return Err(self.err_type(&format!("cannot cast {} to {name}", self.class_name(&v))));
        };
        Ok(())
    }

    pub fn op_make_block(
        &self,
        act: &Activation,
        regs: &mut [Value],
        dst: Reg,
        func: FuncId,
        destructure: Option<u32>,
        is_lambda: bool,
    ) {
        let tag = self.new_tag();
        regs[dst as usize] = Value::Proc(Rc::new(Closure {
            body: ClosureBody::Func(func),
            frame: act.frame.clone(),
            self_val: act.self_val.clone(),
            destructure: destructure.map(|n| n as usize),
            is_lambda,
            tag,
            method_block: (!act.block.is_nil()).then(|| act.block.clone()),
            method_tag: if is_lambda { tag } else { act.method_tag },
            file: act.file,
        }));
    }

    #[allow(clippy::too_many_arguments)]
    pub fn op_method_ref(
        &self,
        f: &FuncInfo,
        act: &Activation,
        regs: &mut [Value],
        dst: Reg,
        recv: Reg,
        name: u32,
        method: Option<MethodId>,
    ) {
        let tag = self.new_tag();
        regs[dst as usize] = Value::Proc(Rc::new(Closure {
            body: ClosureBody::BoundMethod {
                recv: regs[recv as usize].clone(),
                name: Rc::from(self.str_const(f, name)),
                method,
            },
            frame: None,
            self_val: Value::Nil,
            destructure: None,
            is_lambda: true,
            tag,
            method_block: None,
            method_tag: tag,
            file: act.file,
        }));
    }

    #[allow(clippy::too_many_arguments)]
    pub fn op_symbol_proc(
        &self,
        f: &FuncInfo,
        act: &Activation,
        regs: &mut [Value],
        dst: Reg,
        name: u32,
        method: Option<MethodId>,
        discard: bool,
        among: Option<Rc<Vec<(RtType, MethodId)>>>,
    ) {
        let tag = self.new_tag();
        regs[dst as usize] = Value::Proc(Rc::new(Closure {
            body: ClosureBody::MethodName(
                Rc::from(self.str_const(f, name)),
                Cell::new(None),
                method,
                discard,
                among,
            ),
            frame: None,
            self_val: Value::Nil,
            destructure: None,
            is_lambda: true,
            tag,
            method_block: None,
            method_tag: tag,
            file: act.file,
        }));
    }

    /// `[items]`: each a register and whether it is splatted.
    pub fn op_make_array(
        &self,
        regs: &mut [Value],
        dst: Reg,
        items: impl ExactSizeIterator<Item = (Reg, bool)>,
    ) {
        let mut out = Vec::with_capacity(items.len());
        for (reg, splat) in items {
            let v = &regs[reg as usize];
            if splat {
                match v {
                    Value::Array(a) => out.extend(a.iter()),
                    other => out.push(other.clone()),
                }
            } else {
                out.push(v.clone());
            }
        }
        regs[dst as usize] = Value::array(out);
    }

    pub fn op_make_hash(
        &self,
        regs: &mut [Value],
        dst: Reg,
        items: impl ExactSizeIterator<Item = HashItem>,
    ) -> Result<(), Flow> {
        let mut map = ValueMap::with_capacity_and_hasher(items.len(), Default::default());
        for item in items {
            match item {
                HashItem::Pair(k, v) => {
                    map.insert(regs[k as usize].clone(), regs[v as usize].clone());
                }
                HashItem::Splat(h) => {
                    if let Value::Hash(h) = &regs[h as usize] {
                        for (k, v) in h.as_map().iter() {
                            map.insert(k.clone(), v.clone());
                        }
                    }
                }
            }
        }
        // What a key's own `==` or `hash` raised (`crate::keys`).
        crate::keys::check()?;
        regs[dst as usize] = Value::Hash(Rc::new(crate::value::HashData::from(map)));
        Ok(())
    }

    pub fn op_make_range(
        &self,
        regs: &mut [Value],
        dst: Reg,
        lo: Option<Reg>,
        hi: Option<Reg>,
        exclusive: bool,
    ) {
        let lo = lo.map(|r| regs[r as usize].clone()).unwrap_or(Value::Nil);
        let hi = hi.map(|r| regs[r as usize].clone()).unwrap_or(Value::Nil);
        regs[dst as usize] = Value::Range(Rc::new(RangeVal { lo, hi, exclusive }));
    }

    pub fn op_make_regexp(
        &self,
        regs: &mut [Value],
        dst: Reg,
        source: Reg,
        flags: &str,
    ) -> Result<(), Flow> {
        let source = self.to_s(&regs[source as usize])?;
        regs[dst as usize] = self.make_regexp(&source, flags)?;
        Ok(())
    }

    pub fn op_to_sym(&self, regs: &mut [Value], dst: Reg, src: Reg) -> Result<(), Flow> {
        let s = self.to_s(&regs[src as usize])?;
        regs[dst as usize] = Value::Symbol(self.intern(&s));
        Ok(())
    }

    pub fn op_is_array(&self, regs: &mut [Value], dst: Reg, src: Reg) {
        regs[dst as usize] = Value::Bool(matches!(regs[src as usize], Value::Array(_)));
    }

    pub fn op_is_hash(&self, regs: &mut [Value], dst: Reg, src: Reg) {
        regs[dst as usize] = Value::Bool(matches!(regs[src as usize], Value::Hash(_)));
    }

    pub fn op_is_object(&self, regs: &mut [Value], dst: Reg, src: Reg) {
        regs[dst as usize] = Value::Bool(matches!(regs[src as usize], Value::Object(_)));
    }

    pub fn op_to_array(&self, regs: &mut [Value], dst: Reg, src: Reg) {
        let v = match &regs[src as usize] {
            Value::Array(a) => Value::Array(a.clone()),
            other => Value::array(vec![other.clone()]),
        };
        regs[dst as usize] = v;
    }

    pub fn op_len(&self, regs: &mut [Value], dst: Reg, src: Reg) {
        let n = match &regs[src as usize] {
            Value::Array(a) => a.len(),
            Value::Hash(h) => h.len(),
            Value::Str(s) => s.chars().count(),
            Value::Short(s) => s.chars().count(),
            _ => 0,
        };
        regs[dst as usize] = Value::Int(n as i64);
    }

    pub fn op_array_get(&self, regs: &mut [Value], dst: Reg, arr: Reg, index: i32) {
        let v = match &regs[arr as usize] {
            Value::Array(a) => {
                let i = if index < 0 {
                    a.len().checked_sub((-index) as usize)
                } else {
                    Some(index as usize)
                };
                i.and_then(|i| a.get(i)).unwrap_or(Value::Nil)
            }
            _ => Value::Nil,
        };
        regs[dst as usize] = v;
    }

    pub fn op_array_get_reg(&self, regs: &mut [Value], dst: Reg, arr: Reg, index: Reg) {
        let v = match (&regs[arr as usize], &regs[index as usize]) {
            (Value::Array(a), Value::Int(i)) => {
                let i = if *i < 0 {
                    a.len().checked_sub((-*i) as usize)
                } else {
                    Some(*i as usize)
                };
                i.and_then(|i| a.get(i)).unwrap_or(Value::Nil)
            }
            _ => Value::Nil,
        };
        regs[dst as usize] = v;
    }

    /// `ArrayNewWords`.
    pub fn op_array_new_words(&self, regs: &mut [Value], dst: Reg, capacity: Reg, float: bool) {
        let n = match regs[capacity as usize] {
            Value::Int(n) => n.max(0) as usize,
            _ => 0,
        };
        regs[dst as usize] = if float {
            Value::floats(Vec::with_capacity(n))
        } else {
            Value::ints(Vec::with_capacity(n))
        };
    }

    /// `ArrayIndex`: `Array#[]` with an Int.
    pub fn op_array_index(
        &self,
        regs: &mut [Value],
        dst: Reg,
        arr: Reg,
        index: Reg,
    ) -> Result<(), Flow> {
        let v = match (&regs[arr as usize], &regs[index as usize]) {
            (Value::Array(a), Value::Int(i)) => {
                let n = a.len() as i64;
                let at = if *i < 0 { n + i } else { *i };
                if at < 0 || at >= n {
                    return Err(self.err_index(&format!("index {i} out of bounds (size {n})")));
                }
                a.get(at as usize).unwrap_or(Value::Nil)
            }
            _ => return Err(self.err_type("internal error: ArrayIndex on a non-Array")),
        };
        regs[dst as usize] = v;
        Ok(())
    }

    /// `ArrayWords`: the array with its elements stored as machine words
    /// (`Int`s, or `Float`s with `float`), copied only when they are not.
    pub fn op_array_words(
        &self,
        regs: &mut [Value],
        dst: Reg,
        arr: Reg,
        float: bool,
    ) -> Result<(), Flow> {
        let v = match &regs[arr as usize] {
            Value::Array(a) => match (&**a, float) {
                (ArrayData::Ints(_), false) | (ArrayData::Floats(_), true) => {
                    Value::Array(a.clone())
                }
                (data, false) => {
                    let mut words = Vec::with_capacity(data.len());
                    for v in data.iter() {
                        match v {
                            Value::Int(i) => words.push(i),
                            _ => {
                                return Err(self.err_type("internal error: a non-Int in Array[Int]"))
                            }
                        }
                    }
                    Value::ints(words)
                }
                (data, true) => {
                    let mut words = Vec::with_capacity(data.len());
                    for v in data.iter() {
                        match v {
                            Value::Float(f) => words.push(f),
                            _ => {
                                return Err(
                                    self.err_type("internal error: a non-Float in Array[Float]")
                                )
                            }
                        }
                    }
                    Value::floats(words)
                }
            },
            _ => return Err(self.err_type("internal error: ArrayWords on a non-Array")),
        };
        regs[dst as usize] = v;
        Ok(())
    }

    pub fn op_array_slice(
        &self,
        regs: &mut [Value],
        dst: Reg,
        arr: Reg,
        from: u32,
        drop_last: u32,
    ) {
        let v = match &regs[arr as usize] {
            Value::Array(a) => {
                let from = from as usize;
                let end = a.len().saturating_sub(drop_last as usize).max(from);
                if from >= a.len() {
                    Value::array(Vec::new())
                } else {
                    a.slice(from, end.min(a.len()))
                }
            }
            _ => Value::array(Vec::new()),
        };
        regs[dst as usize] = v;
    }

    pub fn op_array_slice_reg(&self, regs: &mut [Value], dst: Reg, arr: Reg, from: Reg, to: Reg) {
        let v = match (
            &regs[arr as usize],
            &regs[from as usize],
            &regs[to as usize],
        ) {
            (Value::Array(a), Value::Int(from), Value::Int(to)) => {
                let from = (*from).clamp(0, a.len() as i64) as usize;
                let to = (*to).clamp(from as i64, a.len() as i64) as usize;
                a.slice(from, to)
            }
            _ => Value::array(Vec::new()),
        };
        regs[dst as usize] = v;
    }

    pub fn op_object_fields(&self, regs: &mut [Value], dst: Reg, src: Reg) {
        let v = match &regs[src as usize] {
            Value::Object(o) => Value::array(self.logical_values(o)),
            _ => Value::array(Vec::new()),
        };
        regs[dst as usize] = v;
    }

    #[allow(clippy::too_many_arguments)]
    pub fn op_hash_get_sym(
        &self,
        f: &FuncInfo,
        pool: &RefCell<Vec<Value>>,
        regs: &mut [Value],
        dst: Reg,
        found: Reg,
        hash: Reg,
        key: u32,
    ) {
        let key = Value::Symbol(self.symbol_const(f, pool, key));
        let (v, ok) = match &regs[hash as usize] {
            Value::Hash(h) => match h.get(&key) {
                Some(v) => (v.clone(), true),
                None => (Value::Nil, false),
            },
            _ => (Value::Nil, false),
        };
        regs[dst as usize] = v;
        regs[found as usize] = Value::Bool(ok);
    }

    pub fn op_array_push(&self, regs: &mut [Value], arr: Reg, src: Reg) -> Result<(), Flow> {
        let v = regs[src as usize].clone();
        match &mut regs[arr as usize] {
            Value::Array(a) => crate::value::unique_mut(a).push(v),
            other => {
                return Err(self.err_type(&format!(
                    "expected an array, got {}",
                    self.class_name(other)
                )))
            }
        }
        Ok(())
    }

    pub fn op_hash_rest(
        &self,
        f: &FuncInfo,
        pool: &RefCell<Vec<Value>>,
        regs: &mut [Value],
        dst: Reg,
        hash: Reg,
        keys: impl Iterator<Item = u32>,
    ) {
        let keys: Vec<Symbol> = keys.map(|k| self.symbol_const(f, pool, k)).collect();
        let v = match &regs[hash as usize] {
            Value::Hash(h) => {
                // A copy, the matched keys taken out: the entries keep
                // their hashes, so no key's own `hash` or `==` runs.
                let mut rest: ValueMap = h.as_map().into_owned();
                rest.retain(|k, _| !matches!(k, Value::Symbol(s) if keys.contains(s)));
                Value::Hash(Rc::new(crate::value::HashData::from(rest)))
            }
            _ => Value::Hash(Rc::new(crate::value::HashData::from(ValueMap::default()))),
        };
        regs[dst as usize] = v;
    }

    pub fn op_catch_exception(
        &self,
        regs: &mut [Value],
        pending: &mut Option<Flow>,
        dst: Reg,
    ) -> Result<(), Flow> {
        regs[dst as usize] = match pending.take() {
            Some(Flow::Raise(e)) => e,
            Some(other) => return Err(other),
            None => Value::Nil,
        };
        Ok(())
    }

    pub fn op_catch_any(&self, regs: &mut [Value], pending: &mut Option<Flow>, dst: Reg) {
        regs[dst as usize] = Value::Flow(Rc::new(RefCell::new(pending.take())));
    }

    pub fn op_rescuing(&self, regs: &[Value], src: Reg, enter: bool) {
        let handle = |exc: &Value| {
            if enter {
                self.start_rescuing(exc.clone());
            } else {
                self.end_rescuing(exc);
            }
        };
        match &regs[src as usize] {
            Value::Flow(fb) => {
                if let Some(Flow::Raise(e)) = &*fb.borrow() {
                    handle(e);
                }
            }
            e @ Value::Object(_) => handle(e),
            _ => {}
        }
    }

    /// `Inst::MarkUsable`: an `initialize` failing from here on leaves an
    /// object whose `deinitialize` runs (see `Interp::construct`).
    pub fn op_mark_usable(&self, regs: &[Value], obj: Reg) {
        if let Value::Object(o) = &regs[obj as usize] {
            o.set_usable();
        }
    }

    pub fn op_no_match(&self, regs: &[Value], src: Reg, is_assert: bool) -> Flow {
        let v = &regs[src as usize];
        let shown = match self.inspect(v) {
            Ok(s) => s,
            Err(e) => return e,
        };
        let msg = if is_assert {
            format!("{shown} does not match the pattern")
        } else {
            format!("no pattern matched {shown}")
        };
        self.raise(self.program.exc.no_matching_pattern, &msg)
    }

    /// The flow a terminator that leaves the function starts (`Raise`,
    /// `BreakOut`, `ReturnOut`, `Resume`, `Unreachable`), or `None` when
    /// it resumes nothing.
    pub fn op_term(&self, act: &Activation, regs: &[Value], term: &Term) -> Option<Flow> {
        Some(match term {
            Term::Raise(r) => Flow::Raise(regs[*r as usize].clone()),
            Term::BreakOut(r) => Flow::Break(regs[*r as usize].clone(), act.closure_tag),
            Term::ReturnOut(r) => Flow::Return(regs[*r as usize].clone(), act.method_tag),
            Term::Resume(r) => match &regs[*r as usize] {
                Value::Flow(fb) => fb.borrow_mut().take()?,
                _ => return None,
            },
            _ => Flow::Raise(self.make_exception(
                self.program.exc.runtime_error,
                "internal error: unreachable code executed",
            )),
        })
    }
}
