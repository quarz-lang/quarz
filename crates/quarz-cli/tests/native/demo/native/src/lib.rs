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
        _ => "invalid",
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

/// Reads each element, releases it, then reads the text again: the bytes
/// lent stay valid to the end of the call (docs/15, handle rules 2 and 5),
/// for a short string (inside its handle's value) as for a long one.
fn released<'c>(cx: &Call<'c>, _: Value<'c>, a: &[Value<'c>]) -> Result<Value<'c>> {
    let mut texts = Vec::new();
    for i in 0..cx.array_len(a[0])? {
        let v = cx.array_get(a[0], i)?;
        let s = cx.get_str(v)?;
        cx.release(v);
        // (Kept: its bytes were lent.)
        if cx.kind(v) == Kind::Invalid {
            return Err(cx.raise("RuntimeError", "released while its text was lent"));
        }
        texts.push(s);
    }
    cx.string(&texts.join("|"))
}

fn released_bytes<'c>(cx: &Call<'c>, _: Value<'c>, a: &[Value<'c>]) -> Result<Value<'c>> {
    let mut all = Vec::new();
    for i in 0..cx.array_len(a[0])? {
        let v = cx.array_get(a[0], i)?;
        let b = cx.get_bytes(v)?;
        cx.release(v);
        all.push(b);
    }
    Ok(cx.int(all.iter().map(|b| b.iter().map(|x| i64::from(*x)).sum::<i64>()).sum()))
}

/// A string the call made, the only holder of its text, released after
/// its text was lent; and made bytes released, then returned.
fn released_made<'c>(cx: &Call<'c>, _: Value<'c>, a: &[Value<'c>]) -> Result<Value<'c>> {
    let n = cx.get_int(a[0])? as usize;
    let v = cx.string(&"x".repeat(n))?;
    let s = cx.get_str(v)?;
    cx.release(v);
    let b = cx.bytes_with(2, |buf| buf.copy_from_slice(b"ok"));
    cx.release(b);
    let tail = cx.get_bytes(b)?;
    cx.string(&format!("{} {}", s.len(), std::str::from_utf8(tail).unwrap_or("?")))
}

/// `n` short strings made, their text read and each released, then more
/// values made (more chunks boxed): every text read stays valid, inline
/// or in a chunk (docs/15, rule 5).
fn released_many<'c>(cx: &Call<'c>, _: Value<'c>, a: &[Value<'c>]) -> Result<Value<'c>> {
    let n = cx.get_int(a[0])? as usize;
    let mut texts = Vec::new();
    for i in 0..n {
        let v = cx.string(&format!("v{i}"))?;
        let s = cx.get_str(v)?;
        cx.release(v);
        if cx.kind(v) == Kind::Invalid {
            return Err(cx.raise("RuntimeError", "released while its text was lent"));
        }
        texts.push(s);
    }
    for i in 0..100 {
        cx.int(i);
    }
    for (i, s) in texts.iter().enumerate() {
        if *s != format!("v{i}") {
            return Err(cx.raise("RuntimeError", "a lent text changed"));
        }
    }
    cx.string(&format!("{} texts, the last {}", texts.len(), texts.last().copied().unwrap_or("")))
}

fn int_map<'c>(cx: &Call<'c>, _: Value<'c>, a: &[Value<'c>]) -> Result<Value<'c>> {
    let h = cx.hash();
    for i in 0..cx.get_int(a[0])? {
        cx.put(h, cx.int(i), cx.int(i * 10))?;
    }
    Ok(h)
}

fn floats<'c>(cx: &Call<'c>, _: Value<'c>, a: &[Value<'c>]) -> Result<Value<'c>> {
    let xs = cx.array(0);
    for i in 0..cx.get_int(a[0])? {
        cx.push(xs, cx.float(i as f64 / 2.0))?;
    }
    Ok(xs)
}

fn byte_list<'c>(cx: &Call<'c>, _: Value<'c>, a: &[Value<'c>]) -> Result<Value<'c>> {
    let xs = cx.array(0);
    for i in 0..cx.get_int(a[0])? {
        cx.push(xs, cx.bytes(&[i as u8, 1]))?;
    }
    Ok(xs)
}

fn make<'c>(cx: &Call<'c>, _: Value<'c>, _: &[Value<'c>]) -> Result<Value<'c>> {
    cx.string("not a crate")
}

fn twice<'c>(cx: &Call<'c>, _: Value<'c>, a: &[Value<'c>]) -> Result<Value<'c>> {
    let once = cx.call_block(&[a[0]])?;
    cx.call_block(&[once])
}

thread_local! {
    static DEPTH: std::cell::RefCell<i64> = const { std::cell::RefCell::new(0) };
}

/// Entered again by its own block: no borrow held across `call_block`
/// (docs/15).
fn depth<'c>(cx: &Call<'c>, _: Value<'c>, a: &[Value<'c>]) -> Result<Value<'c>> {
    let d = DEPTH.with(|d| {
        let mut d = d.borrow_mut();
        *d += 1;
        *d
    });
    let r = cx.call_block(&[a[0]]);
    DEPTH.with(|d| *d.borrow_mut() -= 1);
    Ok(cx.int(cx.get_int(r?)? * 10 + d))
}

/// A `Counter`'s data: unshareable (a `Cell`).
struct Counter(std::cell::Cell<i64>);

/// A `Pool`'s data: shareable (`Send + Sync`).
struct Pool(std::sync::atomic::AtomicI64);

/// A `Bomb`'s data, whose drop panics.
struct Bomb;
impl Drop for Bomb {
    fn drop(&mut self) {
        panic!("the bomb went off");
    }
}

fn counter_open<'c>(cx: &Call<'c>, _: Value<'c>, a: &[Value<'c>]) -> Result<Value<'c>> {
    cx.object(Counter(std::cell::Cell::new(cx.get_int(a[0])?)))
}

fn counter_value<'c>(cx: &Call<'c>, recv: Value<'c>, _: &[Value<'c>]) -> Result<Value<'c>> {
    Ok(cx.int(cx.data::<Counter>(recv)?.0.get()))
}

fn counter_bump<'c>(cx: &Call<'c>, recv: Value<'c>, _: &[Value<'c>]) -> Result<Value<'c>> {
    let c = cx.data::<Counter>(recv)?;
    c.0.set(c.0.get() + 1);
    Ok(cx.int(c.0.get()))
}

fn pool_open<'c>(cx: &Call<'c>, _: Value<'c>, _: &[Value<'c>]) -> Result<Value<'c>> {
    cx.object(Pool(std::sync::atomic::AtomicI64::new(7)))
}

fn pool_size<'c>(cx: &Call<'c>, recv: Value<'c>, _: &[Value<'c>]) -> Result<Value<'c>> {
    let p = cx.data::<Pool>(recv)?;
    Ok(cx.int(p.0.load(std::sync::atomic::Ordering::Relaxed)))
}

fn bomb_open<'c>(cx: &Call<'c>, _: Value<'c>, _: &[Value<'c>]) -> Result<Value<'c>> {
    cx.object(Bomb)
}

fn smuggle<'c>(cx: &Call<'c>, _: Value<'c>, _: &[Value<'c>]) -> Result<Value<'c>> {
    cx.object(Counter(std::cell::Cell::new(0)))?;
    Ok(cx.int(0))
}

fn peek<'c>(cx: &Call<'c>, _: Value<'c>, a: &[Value<'c>]) -> Result<Value<'c>> {
    Ok(cx.int(cx.data::<Counter>(a[0])?.0.get()))
}

/// A `Probe`'s data: its drop is counted.
struct Probe;
static DROPS: std::sync::atomic::AtomicI64 = std::sync::atomic::AtomicI64::new(0);
impl Drop for Probe {
    fn drop(&mut self) {
        DROPS.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    }
}

fn probe_open<'c>(cx: &Call<'c>, _: Value<'c>, _: &[Value<'c>]) -> Result<Value<'c>> {
    cx.object(Probe)
}

fn drops<'c>(cx: &Call<'c>, _: Value<'c>, _: &[Value<'c>]) -> Result<Value<'c>> {
    Ok(cx.int(DROPS.load(std::sync::atomic::Ordering::SeqCst)))
}

quarz_ext::module! {
    cog: "demo",
    classes: {
        "Counter" => Counter,
        "Pool" => Pool: shareable,
        "Bomb" => Bomb,
        "Probe" => Probe: shareable,
    },
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
    "Crate.make" => make,
    "Demo.nothing" => nothing,
    "Demo.keep" => keep,
    "Demo.use_kept" => use_kept,
    "Demo.released" => released,
    "Demo.released_bytes" => released_bytes,
    "Demo.released_made" => released_made,
    "Demo.released_many" => released_many,
    "Demo.int_map" => int_map,
    "Demo.floats" => floats,
    "Demo.byte_list" => byte_list,
    "Demo.twice" => twice,
    "Demo.depth" => depth,
    "Demo.smuggle" => smuggle,
    "Demo.peek" => peek,
    "Demo.drops" => drops,
    "Probe.open" => probe_open,
    "Counter.open" => counter_open,
    "Counter#value" => counter_value,
    "Counter#bump" => counter_bump,
    "Pool.open" => pool_open,
    "Pool#size" => pool_size,
    "Bomb.open" => bomb_open,
    "String#shout" => shout,
}
