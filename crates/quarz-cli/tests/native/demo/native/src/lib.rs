//! The demo cog's native methods (`src/demo.qz`): one use of each of the
//! ABI's functions, and the ways a method can fail.

use quarz_ext::{Call, Kind, Result, Value};

fn add<'c>(cx: &Call<'c>, _: Value<'c>, a: &[Value<'c>]) -> Result<Value<'c>> {
    Ok(cx.int(cx.get_int(a[0])? + cx.get_int(a[1])?))
}

fn describe<'c>(cx: &Call<'c>, _: Value<'c>, a: &[Value<'c>]) -> Result<Value<'c>> {
    let name = match cx.kind(a[0]) {
        Kind::Nil => "nil",
        Kind::Bool => "bool",
        Kind::Int => "int",
        Kind::Float => "float",
        Kind::String => "string",
        Kind::Bytes => "bytes",
        Kind::Symbol => "symbol",
        Kind::Array => "array",
        Kind::Hash => "hash",
        Kind::Other => "other",
    };
    cx.string(name)
}

fn reverse<'c>(cx: &Call<'c>, _: Value<'c>, a: &[Value<'c>]) -> Result<Value<'c>> {
    let s: String = cx.get_str(a[0])?.chars().rev().collect();
    cx.string(&s)
}

fn bytes_sum<'c>(cx: &Call<'c>, _: Value<'c>, a: &[Value<'c>]) -> Result<Value<'c>> {
    Ok(cx.int(cx.get_bytes(a[0])?.iter().map(|b| i64::from(*b)).sum()))
}

fn zeros<'c>(cx: &Call<'c>, _: Value<'c>, a: &[Value<'c>]) -> Result<Value<'c>> {
    let n = cx.get_int(a[0])? as usize;
    Ok(cx.bytes_with(n, |buf| {
        if let Some(last) = buf.last_mut() {
            *last = 7;
        }
    }))
}

fn squares<'c>(cx: &Call<'c>, _: Value<'c>, a: &[Value<'c>]) -> Result<Value<'c>> {
    let n = cx.get_int(a[0])?;
    let xs = cx.array(n as usize);
    for i in 0..n {
        cx.push(xs, cx.int(i * i))?;
    }
    Ok(xs)
}

fn sum<'c>(cx: &Call<'c>, _: Value<'c>, a: &[Value<'c>]) -> Result<Value<'c>> {
    let mut total = 0;
    for i in 0..cx.array_len(a[0])? {
        let x = cx.array_get(a[0], i)?;
        total += cx.get_int(x)?;
        cx.release(x);
    }
    Ok(cx.int(total))
}

fn invert<'c>(cx: &Call<'c>, _: Value<'c>, a: &[Value<'c>]) -> Result<Value<'c>> {
    let out = cx.hash();
    for i in 0..cx.hash_len(a[0])? {
        let (k, v) = cx.hash_entry(a[0], i)?;
        cx.put(out, v, k)?;
    }
    Ok(out)
}

fn sym<'c>(cx: &Call<'c>, _: Value<'c>, a: &[Value<'c>]) -> Result<Value<'c>> {
    let s = cx.get_str(a[0])?;
    cx.symbol(s)
}

fn scale<'c>(cx: &Call<'c>, _: Value<'c>, a: &[Value<'c>]) -> Result<Value<'c>> {
    Ok(cx.float(cx.get_float(a[0])? * cx.get_float(a[1])?))
}

fn fail<'c>(cx: &Call<'c>, _: Value<'c>, a: &[Value<'c>]) -> Result<Value<'c>> {
    let message = cx.get_str(a[0])?;
    Err(cx.raise("ArgumentError", message))
}

fn fail_with<'c>(cx: &Call<'c>, _: Value<'c>, a: &[Value<'c>]) -> Result<Value<'c>> {
    let class = cx.get_str(a[0])?;
    Err(cx.raise(class, "from native code"))
}

fn panic<'c>(_: &Call<'c>, _: Value<'c>, _: &[Value<'c>]) -> Result<Value<'c>> {
    panic!("the demo panics")
}

fn push_lent<'c>(cx: &Call<'c>, _: Value<'c>, a: &[Value<'c>]) -> Result<Value<'c>> {
    cx.push(a[0], cx.int(2))?;
    Ok(a[0])
}

fn wrong<'c>(cx: &Call<'c>, _: Value<'c>, _: &[Value<'c>]) -> Result<Value<'c>> {
    cx.string("not an Int")
}

fn nothing<'c>(_: &Call<'c>, _: Value<'c>, _: &[Value<'c>]) -> Result<Value<'c>> {
    Ok(Value::NONE)
}

fn shout<'c>(cx: &Call<'c>, recv: Value<'c>, _: &[Value<'c>]) -> Result<Value<'c>> {
    let s = cx.get_str(recv)?.to_uppercase();
    cx.string(&s)
}

/// A handle of one call, kept past it: for `use_kept`, which must be
/// refused it.
static KEPT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

fn keep<'c>(_: &Call<'c>, _: Value<'c>, a: &[Value<'c>]) -> Result<Value<'c>> {
    KEPT.store(a[0].handle(), std::sync::atomic::Ordering::Relaxed);
    Ok(a[0])
}

fn use_kept<'c>(cx: &Call<'c>, _: Value<'c>, _: &[Value<'c>]) -> Result<Value<'c>> {
    // SAFETY: deliberately another call's handle: quarz refuses it.
    let old = unsafe { Value::from_raw(KEPT.load(std::sync::atomic::Ordering::Relaxed)) };
    Ok(cx.int(cx.get_int(old)?))
}

quarz_ext::module! {
    cog: "demo",
    "Demo.add" => add,
    "Demo.describe" => describe,
    "Demo.reverse" => reverse,
    "Demo.bytes_sum" => bytes_sum,
    "Demo.zeros" => zeros,
    "Demo.squares" => squares,
    "Demo.sum" => sum,
    "Demo.invert" => invert,
    "Demo.sym" => sym,
    "Demo.scale" => scale,
    "Demo.fail" => fail,
    "Demo.fail_with" => fail_with,
    "Demo.panic" => panic,
    "Demo.push_lent" => push_lent,
    "Demo.wrong" => wrong,
    "Demo.nothing" => nothing,
    "Demo.keep" => keep,
    "Demo.use_kept" => use_kept,
    "String#shout" => shout,
}
