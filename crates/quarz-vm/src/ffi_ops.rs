//! The runtime entries compiled code calls for the instructions it does
//! not do inline, one per kind of instruction (`qz_op_*`): an executable
//! carries no instructions, only their operands, as arguments and, for
//! lists, as arrays of words in its data. Each runs `crate::ops`, as the
//! interpreter does.
//!
//! Every entry takes the interpreter, the activation, the function, the
//! line (recorded in the activation, as for backtraces) and the
//! registers, then the operands; a register that may be absent is
//! `NONE`. It returns the status the compiled code goes on with.

use std::cell::RefCell;
use std::sync::atomic::{AtomicPtr, Ordering};

use quarz_ir::{FastOp, HashItem, Reg, RtType, StrPiece, Term, VarLoc};
use smallvec::SmallVec;

use crate::ffi::STATUS_OK;
use crate::interp::{Flow, Interp};
use crate::ops::{CallOp, CallOps, OwnedOps};
use crate::value::Value;
use crate::vm::Activation;

/// An absent register or method.
pub const NONE: u32 = u32::MAX;

fn opt(w: u32) -> Option<u32> {
    (w != NONE).then_some(w)
}

/// The `n` words at `p`.
///
/// # Safety
/// `p` points at `n` words of the executable's data (or `n` is 0).
unsafe fn words<'a>(p: *const u32, n: u32) -> &'a [u32] {
    if n == 0 {
        &[]
    } else {
        unsafe { std::slice::from_raw_parts(p, n as usize) }
    }
}

/// The text of `n` bytes at `p`.
///
/// # Safety
/// As for `words`, UTF-8.
unsafe fn text<'a>(p: *const u8, n: u32) -> &'a str {
    if n == 0 {
        ""
    } else {
        unsafe { std::str::from_utf8_unchecked(std::slice::from_raw_parts(p, n as usize)) }
    }
}

/// The type encoded in `w` (see `encode_type`), from position `*at`.
fn decode_type(w: &[u32], at: &mut usize) -> RtType {
    let tag = w[*at];
    *at += 1;
    match tag {
        0 => RtType::Nothing,
        1 => {
            *at += 1;
            RtType::Class(w[*at - 1])
        }
        2 => RtType::ClassObject,
        3 => {
            let n = w[*at] as usize;
            *at += 1;
            RtType::Union((0..n).map(|_| decode_type(w, at)).collect())
        }
        4 => {
            *at += 1;
            RtType::Tuple(w[*at - 1])
        }
        5 => RtType::Proc,
        _ => RtType::Any,
    }
}

/// `ty` as words (what compiled code passes to `qz_op_is_a`/`qz_op_as`).
pub fn encode_type(ty: &RtType, out: &mut Vec<u32>) {
    match ty {
        RtType::Nothing => out.push(0),
        RtType::Class(c) => out.extend([1, *c]),
        RtType::ClassObject => out.push(2),
        RtType::Union(ms) => {
            out.extend([3, ms.len() as u32]);
            for m in ms {
                encode_type(m, out);
            }
        }
        RtType::Tuple(n) => out.extend([4, *n]),
        RtType::Proc => out.push(5),
        RtType::Any => out.push(6),
    }
}

/// The type at a site: decoded the first time, kept in the site's cell.
///
/// # Safety
/// `cell` is the site's pointer-sized cell (null at first), `w` its
/// words.
unsafe fn site_type<'a>(cell: *mut *const RtType, w: &[u32]) -> &'a RtType {
    let cell = unsafe { &*(cell as *const AtomicPtr<RtType>) };
    let p = cell.load(Ordering::Acquire);
    if !p.is_null() {
        return unsafe { &*p };
    }
    let fresh = Box::into_raw(Box::new(decode_type(w, &mut 0)));
    match cell.compare_exchange(
        std::ptr::null_mut(),
        fresh,
        Ordering::AcqRel,
        Ordering::Acquire,
    ) {
        Ok(_) => unsafe { &*fresh },
        // Another thread decoded it first: its copy is the one kept.
        Err(theirs) => {
            drop(unsafe { Box::from_raw(fresh) });
            unsafe { &*theirs }
        }
    }
}

/// The common part of an entry: `$body` runs with the interpreter, the
/// activation, the function, its pool and the registers.
macro_rules! op_entry {
    ($(#[$doc:meta])* $name:ident ($($arg:ident: $ty:ty),*)
     |$rt:ident, $act:ident, $f:ident, $pool:ident, $regs:ident| $body:block) => {
        $(#[$doc])*
        ///
        /// # Safety
        /// The pointers are compiled code's: the running interpreter, the
        /// activation, the function's registers and its data.
        #[no_mangle]
        #[allow(unused_variables, clippy::too_many_arguments, clippy::redundant_closure_call)]
        pub unsafe extern "C" fn $name(
            rt: *const Interp,
            act: *const Activation,
            fid: u32,
            line: u32,
            regs: *mut Value,
            $($arg: $ty),*
        ) -> u32 {
            let $rt = unsafe { &*rt };
            let $act = unsafe { &*act };
            $act.line.set(line);
            let funcs = $rt.funcs.borrow();
            let $f = &*funcs[fid as usize];
            let pools = $rt.pools.borrow();
            let $pool: &RefCell<Vec<Value>> = &pools[fid as usize];
            let $regs = unsafe { std::slice::from_raw_parts_mut(regs, $f.nregs as usize) };
            let r: Result<(), Flow> = (|| $body)();
            match r {
                Ok(()) => STATUS_OK,
                Err(flow) => $rt.park_flow(flow),
            }
        }
    };
}

op_entry!(
    /// `LoadConst` of a constant compiled code does not write itself.
    qz_op_load_const(dst: u32, idx: u32) |rt, act, f, pool, regs| {
        rt.op_load_const(f, pool, regs, dst, idx)
    }
);

op_entry!(qz_op_has_arg(dst: u32, index: u32) |rt, act, f, pool, regs| {
    rt.op_has_arg(act, regs, dst, index);
    Ok(())
});

op_entry!(
    qz_op_field_get_by_name(dst: u32, found: u32, obj: u32, name: u32) |rt, act, f, pool, regs| {
        rt.op_field_get_by_name(f, regs, dst, found, obj, name);
        Ok(())
    }
);

op_entry!(qz_op_const_get(dst: u32, id: u32) |rt, act, f, pool, regs| {
    rt.op_const_get(regs, dst, id)
});

op_entry!(qz_op_variant_singleton(dst: u32, class: u32) |rt, act, f, pool, regs| {
    rt.op_variant_singleton(regs, dst, class);
    Ok(())
});

op_entry!(
    /// A call compiled code does not make itself. `desc`: destination,
    /// kind and its two operands, receiver, splat, keyword splat, block,
    /// moved bits, argument count, keyword count, then the arguments and
    /// the keywords (name constant, register); `name` is a `Send`'s.
    qz_op_call(desc: *const u32, name: *const u8, name_len: u32) |rt, act, f, pool, regs| {
        let head = unsafe { words(desc, 11) };
        let (nargs, nkw) = (head[9], head[10]);
        let rest = unsafe { words(desc.add(11), nargs + 2 * nkw) };
        let kw: SmallVec<[(u32, Reg); 4]> = rest[nargs as usize..]
            .chunks(2)
            .map(|p| (p[0], p[1]))
            .collect();
        let (a, b) = (head[2], head[3]);
        let kind = match head[1] {
            0 => CallOp::Method(a),
            1 => CallOp::Send(unsafe { text(name, name_len) }),
            2 => CallOp::Construct { class: a, init: opt(b) },
            3 => CallOp::ConstructRecv { class: a, init: opt(b) },
            4 => CallOp::ProcCall,
            5 => CallOp::Yield,
            6 => CallOp::Super(a),
            _ => CallOp::Raise,
        };
        rt.op_call(
            f,
            pool,
            act,
            regs,
            CallOps {
                dst: head[0],
                kind,
                recv: opt(head[4]),
                args: &rest[..nargs as usize],
                splat: head[5] != 0,
                kw: &kw,
                kw_splat: opt(head[6]),
                block: opt(head[7]),
                moved: head[8] as u16,
            },
        )
    }
);

op_entry!(
    /// An in-place call compiled code does not make itself. `desc`:
    /// destination, method, location kind (register, frame, field) and
    /// its two operands, whether the result is unused, argument count,
    /// keyword count, the arguments, the keywords.
    qz_op_owned_call(desc: *const u32) |rt, act, f, pool, regs| {
        let head = unsafe { words(desc, 8) };
        let (nargs, nkw) = (head[6], head[7]);
        let rest = unsafe { words(desc.add(8), nargs + 2 * nkw) };
        let kw: SmallVec<[(u32, Reg); 4]> = rest[nargs as usize..]
            .chunks(2)
            .map(|p| (p[0], p[1]))
            .collect();
        let recv = match head[2] {
            0 => VarLoc::Reg(head[3]),
            1 => VarLoc::Frame { depth: head[3], slot: head[4] },
            _ => VarLoc::Field { obj: head[3], index: head[4] },
        };
        rt.op_owned_call(
            f,
            pool,
            act,
            regs,
            OwnedOps {
                dst: head[0],
                method: head[1],
                recv,
                args: &rest[..nargs as usize],
                kw: &kw,
                unused: head[5] != 0,
            },
        )
    }
);

op_entry!(
    qz_op_binop(dst: u32, op: u32, lhs: u32, rhs: u32, method: u32) |rt, act, f, pool, regs| {
        rt.op_binop(regs, dst, FastOp::from_index(op), lhs, rhs, opt(method))
    }
);

op_entry!(qz_op_case_eq(dst: u32, pattern: u32, value: u32) |rt, act, f, pool, regs| {
    rt.op_case_eq(regs, dst, pattern, value)
});

op_entry!(qz_op_equal(dst: u32, a: u32, b: u32) |rt, act, f, pool, regs| {
    rt.op_equal(regs, dst, a, b)
});

op_entry!(qz_op_class_is_a(dst: u32, src: u32, class: u32) |rt, act, f, pool, regs| {
    rt.op_class_is_a(regs, dst, src, class);
    Ok(())
});

op_entry!(
    qz_op_is_a(dst: u32, src: u32, ty: *const u32, n: u32, cell: *mut *const RtType)
    |rt, act, f, pool, regs| {
        let ty = unsafe { site_type(cell, words(ty, n)) };
        rt.op_is_a(regs, dst, src, ty);
        Ok(())
    }
);

op_entry!(
    qz_op_as(
        dst: u32,
        src: u32,
        ty: *const u32,
        n: u32,
        cell: *mut *const RtType,
        optional: u32,
        name: *const u8,
        name_len: u32
    ) |rt, act, f, pool, regs| {
        let ty = unsafe { site_type(cell, words(ty, n)) };
        rt.op_as(regs, dst, src, ty, optional != 0, unsafe { text(name, name_len) })
    }
);

op_entry!(
    qz_op_make_block(dst: u32, func: u32, destructure: u32, is_lambda: u32)
    |rt, act, f, pool, regs| {
        rt.op_make_block(act, regs, dst, func, opt(destructure), is_lambda != 0);
        Ok(())
    }
);

op_entry!(qz_op_method_ref(dst: u32, recv: u32, name: u32) |rt, act, f, pool, regs| {
    rt.op_method_ref(f, act, regs, dst, recv, name);
    Ok(())
});

op_entry!(qz_op_symbol_proc(dst: u32, name: u32, method: u32) |rt, act, f, pool, regs| {
    rt.op_symbol_proc(f, act, regs, dst, name, opt(method));
    Ok(())
});

op_entry!(
    /// `items`: `n` pairs of register and splat flag.
    qz_op_make_array(dst: u32, items: *const u32, n: u32) |rt, act, f, pool, regs| {
        let w = unsafe { words(items, 2 * n) };
        rt.op_make_array(regs, dst, w.chunks(2).map(|p| (p[0], p[1] != 0)));
        Ok(())
    }
);

op_entry!(
    /// `items`: `n` triples: 0 and a key and a value register, or 1 and
    /// a splatted register.
    qz_op_make_hash(dst: u32, items: *const u32, n: u32) |rt, act, f, pool, regs| {
        let w = unsafe { words(items, 3 * n) };
        rt.op_make_hash(
            regs,
            dst,
            w.chunks(3).map(|t| {
                if t[0] == 0 {
                    HashItem::Pair(t[1], t[2])
                } else {
                    HashItem::Splat(t[1])
                }
            }),
        );
        Ok(())
    }
);

op_entry!(
    qz_op_make_range(dst: u32, lo: u32, hi: u32, exclusive: u32) |rt, act, f, pool, regs| {
        rt.op_make_range(regs, dst, opt(lo), opt(hi), exclusive != 0);
        Ok(())
    }
);

op_entry!(
    qz_op_make_regexp(dst: u32, source: u32, flags: *const u8, flags_len: u32)
    |rt, act, f, pool, regs| {
        rt.op_make_regexp(regs, dst, source, unsafe { text(flags, flags_len) })
    }
);

op_entry!(
    /// `parts`: `n` pairs: 0 and a string constant, or 1 and a register
    /// converted with `to_s`. `dead`: the result of an append to a
    /// builder is not read.
    qz_op_interpolate(dst: u32, parts: *const u32, n: u32, into: u32, dead: u32)
    |rt, act, f, pool, regs| {
        let w = unsafe { words(parts, 2 * n) };
        let parts = w.as_chunks::<2>().0.iter().map(|p| {
            if p[0] == 0 {
                StrPiece::Lit(p[1])
            } else {
                StrPiece::Val(p[1])
            }
        });
        let into = opt(into);
        if dead != 0 {
            if let Some(r) = into {
                if let Value::StringBuilder(_) = &regs[r as usize] {
                    return rt.append_interpolation(f, regs, parts, r);
                }
            }
        }
        regs[dst as usize] = rt.interpolate_inst(f, regs, parts, into)?;
        Ok(())
    }
);

/// The entries of the instructions with a destination and a source.
macro_rules! unary_entry {
    ($name:ident, $op:ident) => {
        op_entry!($name(dst: u32, src: u32) |rt, act, f, pool, regs| {
            rt.$op(regs, dst, src);
            Ok(())
        });
    };
}

op_entry!(qz_op_to_sym(dst: u32, src: u32) |rt, act, f, pool, regs| {
    rt.op_to_sym(regs, dst, src)
});
unary_entry!(qz_op_is_array, op_is_array);
unary_entry!(qz_op_is_hash, op_is_hash);
unary_entry!(qz_op_is_object, op_is_object);
unary_entry!(qz_op_to_array, op_to_array);
unary_entry!(qz_op_len, op_len);
unary_entry!(qz_op_object_fields, op_object_fields);

op_entry!(qz_op_array_get(dst: u32, arr: u32, index: i32) |rt, act, f, pool, regs| {
    rt.op_array_get(regs, dst, arr, index);
    Ok(())
});

op_entry!(qz_op_array_get_reg(dst: u32, arr: u32, index: u32) |rt, act, f, pool, regs| {
    rt.op_array_get_reg(regs, dst, arr, index);
    Ok(())
});

op_entry!(qz_op_array_new_words(dst: u32, capacity: u32, float: u32) |rt, act, f, pool, regs| {
    rt.op_array_new_words(regs, dst, capacity, float != 0);
    Ok(())
});

op_entry!(qz_op_array_index(dst: u32, arr: u32, index: u32) |rt, act, f, pool, regs| {
    rt.op_array_index(regs, dst, arr, index)
});

op_entry!(qz_op_array_words(dst: u32, arr: u32, float: u32) |rt, act, f, pool, regs| {
    rt.op_array_words(regs, dst, arr, float != 0)
});

op_entry!(
    qz_op_array_slice(dst: u32, arr: u32, from: u32, drop_last: u32) |rt, act, f, pool, regs| {
        rt.op_array_slice(regs, dst, arr, from, drop_last);
        Ok(())
    }
);

op_entry!(
    qz_op_array_slice_reg(dst: u32, arr: u32, from: u32, to: u32) |rt, act, f, pool, regs| {
        rt.op_array_slice_reg(regs, dst, arr, from, to);
        Ok(())
    }
);

op_entry!(
    qz_op_hash_get_sym(dst: u32, found: u32, hash: u32, key: u32) |rt, act, f, pool, regs| {
        rt.op_hash_get_sym(f, pool, regs, dst, found, hash, key);
        Ok(())
    }
);

op_entry!(qz_op_array_push(arr: u32, src: u32) |rt, act, f, pool, regs| {
    rt.op_array_push(regs, arr, src)
});

op_entry!(
    /// `keys`: `n` symbol constants.
    qz_op_hash_rest(dst: u32, hash: u32, keys: *const u32, n: u32) |rt, act, f, pool, regs| {
        let keys = unsafe { words(keys, n) };
        rt.op_hash_rest(f, pool, regs, dst, hash, keys.iter().copied());
        Ok(())
    }
);

op_entry!(qz_op_catch_exception(dst: u32) |rt, act, f, pool, regs| {
    let mut pending = rt.pending_flow.borrow_mut().take();
    let r = rt.op_catch_exception(regs, &mut pending, dst);
    *rt.pending_flow.borrow_mut() = pending;
    r
});

op_entry!(qz_op_catch_any(dst: u32) |rt, act, f, pool, regs| {
    let mut pending = rt.pending_flow.borrow_mut().take();
    rt.op_catch_any(regs, &mut pending, dst);
    *rt.pending_flow.borrow_mut() = pending;
    Ok(())
});

op_entry!(qz_op_no_match(src: u32, is_assert: u32) |rt, act, f, pool, regs| {
    Err(rt.op_no_match(regs, src, is_assert != 0))
});

op_entry!(
    /// A terminator that leaves the function: `kind` 0 `raise`, 1 a
    /// block's `break`, 2 a block's `return`, 3 the end of an `ensure`
    /// resuming its flow, 4 unreachable; `reg` its operand.
    qz_op_term(kind: u32, reg: u32) |rt, act, f, pool, regs| {
        let term = match kind {
            0 => Term::Raise(reg),
            1 => Term::BreakOut(reg),
            2 => Term::ReturnOut(reg),
            3 => Term::Resume(reg),
            _ => Term::Unreachable,
        };
        match rt.op_term(act, regs, &term) {
            Some(flow) => Err(flow),
            None => Ok(()),
        }
    }
);
