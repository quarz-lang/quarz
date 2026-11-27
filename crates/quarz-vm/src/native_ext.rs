//! A cog's native code (#677, docs/15): its library's module, loaded
//! once per process (`load`), its entries bound to the cog's `native def`s
//! (`check`, `bind`, by `RtMethod::ext` and the key), and a call of one
//! (`call`) through the native ABI (`quarz_ext::sys`).
//!
//! A call's values are handles on a frame of the call's own: those it is
//! lent (the receiver, the arguments, the block) and those it makes. A
//! handle names its frame by a serial, so one from another call is
//! refused (`TypeError`), never followed. Nothing an API function does
//! runs Quarz code.

use std::collections::HashMap;
use std::ffi::{c_void, CString};
use std::path::Path;
use std::sync::Mutex;

use quarz_ext::sys::*;
use quarz_ir::{MethodId, RtParamKind, RtWorld};

use crate::interp::{ArgVec, EvalResult, Flow, Interp};
use crate::rc::Rc;
use crate::value::{ArrayData, HashData, Symbol, Value};

/// A cog's native entry.
pub type Entry = QzEntry;

/// A loaded module: its cog and its entries by key.
struct Module {
    cog: String,
    entries: HashMap<String, Entry>,
}

/// The modules loaded so far; a library is never unloaded.
static MODULES: Mutex<Vec<Module>> = Mutex::new(Vec::new());

extern "C" {
    fn dlopen(file: *const std::ffi::c_char, mode: i32) -> *mut c_void;
    fn dlsym(handle: *mut c_void, symbol: *const std::ffi::c_char) -> *mut c_void;
    fn dlerror() -> *const std::ffi::c_char;
}

const RTLD_NOW: i32 = 2;

fn dl_error() -> String {
    // SAFETY: `dlerror` gives a NUL-terminated message, or null.
    let e = unsafe { dlerror() };
    if e.is_null() {
        return "unknown error".to_string();
    }
    unsafe { std::ffi::CStr::from_ptr(e) }
        .to_string_lossy()
        .into_owned()
}

/// Load cog `cog`'s native library at `path` and keep its module (once
/// per process: a second load of the cog does nothing).
pub fn load(cog: &str, path: &Path) -> Result<(), String> {
    let mut modules = MODULES.lock().expect("the modules");
    if modules.iter().any(|m| m.cog == cog) {
        return Ok(());
    }
    let where_ = || format!("the native library of cog `{cog}` ({})", path.display());
    let file = CString::new(path.as_os_str().as_encoded_bytes())
        .map_err(|_| format!("{}: a path with a NUL", where_()))?;
    // SAFETY: a library's initializers run here, as any loaded library's.
    let handle = unsafe { dlopen(file.as_ptr(), RTLD_NOW) };
    if handle.is_null() {
        return Err(format!("cannot load {}: {}", where_(), dl_error()));
    }
    let symbol = init_symbol(cog);
    let name = CString::new(symbol.clone()).expect("a symbol");
    let init = unsafe { dlsym(handle, name.as_ptr()) };
    if init.is_null() {
        return Err(format!(
            "{} has no `{symbol}`, the init `quarz_ext::module!` makes for cog `{cog}`",
            where_()
        ));
    }
    // SAFETY: the symbol is the cog's `QzInit` (the ABI's contract).
    let init: QzInit = unsafe { std::mem::transmute::<*mut c_void, QzInit>(init) };
    let module = unsafe { init(&API) };
    if module.is_null() {
        return Err(format!(
            "{} refused this quarz's native ABI {QZ_ABI_MAJOR}.{QZ_ABI_MINOR}: it was built for another",
            where_()
        ));
    }
    // SAFETY: init gave a module that lives as long as the library.
    let module = unsafe { &*module };
    // (Read first, whatever the major: the prefix that never changes.)
    if module.abi_major != QZ_ABI_MAJOR || module.abi_minor > QZ_ABI_MINOR {
        return Err(format!(
            "{} was built for the native ABI {}.{}; this quarz has {QZ_ABI_MAJOR}.{QZ_ABI_MINOR}",
            where_(),
            module.abi_major,
            module.abi_minor
        ));
    }
    if module.method_size < std::mem::size_of::<QzMethod>() {
        return Err(format!("{}: its methods' size is too small", where_()));
    }
    if module.n_methods > 0 && module.methods.is_null() {
        return Err(format!("{}: its methods are a null pointer", where_()));
    }
    let mut entries = HashMap::new();
    for i in 0..module.n_methods {
        // SAFETY: `n_methods` methods `method_size` apart.
        let m = unsafe {
            &*((module.methods as *const u8).add(i * module.method_size) as *const QzMethod)
        };
        // SAFETY: `key_len` bytes at `key` (none read when null or empty).
        let key = unsafe { bytes_at(m.key, m.key_len) };
        let Ok(key) = std::str::from_utf8(key) else {
            return Err(format!("{}: a method's key is not UTF-8", where_()));
        };
        if entries.insert(key.to_string(), m.entry).is_some() {
            return Err(format!("{} defines `{key}` twice", where_()));
        }
    }
    modules.push(Module {
        cog: cog.to_string(),
        entries,
    });
    Ok(())
}

/// Whether every cog's native of `world` has its entry, and every entry
/// a `native def`: an error naming the cog and the key otherwise. The
/// command checks it after loading the libraries, before running.
pub fn check(world: &RtWorld) -> Result<(), String> {
    let modules = MODULES.lock().expect("the modules");
    for (i, cog) in world.native_cogs.iter().enumerate() {
        let Some(module) = modules.iter().find(|m| &m.cog == cog) else {
            return Err(format!(
                "cog `{cog}` brings native code (`[native]` in its Cog.toml), but its library is not loaded"
            ));
        };
        let declared: Vec<&str> = world
            .methods
            .iter()
            .filter(|m| m.ext == Some(i as u32))
            .filter_map(|m| m.native_key.as_deref())
            .collect();
        for key in &declared {
            if !module.entries.contains_key(*key) {
                return Err(format!(
                    "cog `{cog}` declares `native def` `{key}`, which its native library does not define"
                ));
            }
        }
        let mut extra: Vec<&String> = module
            .entries
            .keys()
            .filter(|k| !declared.contains(&k.as_str()))
            .collect();
        extra.sort();
        if let Some(key) = extra.first() {
            return Err(format!(
                "cog `{cog}`'s native library defines `{key}`, which the cog does not declare `native def`"
            ));
        }
    }
    Ok(())
}

/// Each method's entry (`RtMethod::ext` and its key), by method id:
/// `None` for every other method, and for one whose module is not loaded
/// (the call then says so, `call_unbound`).
pub fn bind(world: &RtWorld) -> Vec<Option<Entry>> {
    if world.native_cogs.is_empty() {
        return vec![None; world.methods.len()];
    }
    let modules = MODULES.lock().expect("the modules");
    world
        .methods
        .iter()
        .map(|m| {
            let cog = world.native_cogs.get(m.ext? as usize)?;
            let module = modules.iter().find(|x| &x.cog == cog)?;
            module.entries.get(m.native_key.as_deref()?).copied()
        })
        .collect()
}

// ----- a call ------------------------------------------------------------------------

/// One call's values: lent (`lent`: the receiver, the arguments, the
/// block) and made (`made`, boxed so that a lent pointer into one stays
/// put; `pinned` once bytes of it were lent, so that `release` keeps it
/// to the end of the call), the symbol names lent (`names`, one per
/// symbol), and the pending exception.
struct Frame<'a> {
    interp: &'a Interp,
    serial: u32,
    lent: Vec<Value>,
    made: Vec<Option<Box<Value>>>,
    pinned: Vec<bool>,
    names: Vec<(Symbol, Rc<str>)>,
    pending: Option<Value>,
}

thread_local! {
    static SERIAL: std::cell::Cell<u32> = const { std::cell::Cell::new(0) };
}

fn next_serial() -> u32 {
    SERIAL.with(|s| {
        let n = s.get().wrapping_add(1).max(1);
        s.set(n);
        n
    })
}

impl Frame<'_> {
    fn handle(&self, index: usize) -> QzValue {
        (u64::from(self.serial) << 32) | (index as u64 + 1)
    }

    /// The value of `h`, a handle of this call's.
    fn value(&self, h: QzValue) -> Option<&Value> {
        if (h >> 32) as u32 != self.serial || h & 0xFFFF_FFFF == 0 {
            return None;
        }
        let i = (h & 0xFFFF_FFFF) as usize - 1;
        if i < self.lent.len() {
            return self.lent.get(i);
        }
        self.made.get(i - self.lent.len())?.as_deref()
    }

    fn make(&mut self, v: Value) -> QzValue {
        self.made.push(Some(Box::new(v)));
        self.pinned.push(false);
        self.handle(self.lent.len() + self.made.len() - 1)
    }

    /// Keep `h`'s value to the end of the call, whatever `release` is
    /// asked: bytes of it were lent (`string_get`, `bytes_get`,
    /// `bytes_new_uninit`), and a short string's live in its box. (A lent
    /// value is kept to the end anyway.)
    fn pin(&mut self, h: QzValue) {
        if (h >> 32) as u32 != self.serial || h & 0xFFFF_FFFF == 0 {
            return;
        }
        let i = (h & 0xFFFF_FFFF) as usize - 1;
        if let Some(p) = i
            .checked_sub(self.lent.len())
            .and_then(|i| self.pinned.get_mut(i))
        {
            *p = true;
        }
    }

    /// A made value of this call's, to change in place.
    fn made_mut(&mut self, h: QzValue) -> Option<&mut Value> {
        if (h >> 32) as u32 != self.serial || h & 0xFFFF_FFFF == 0 {
            return None;
        }
        let i = ((h & 0xFFFF_FFFF) as usize - 1).checked_sub(self.lent.len())?;
        self.made.get_mut(i)?.as_deref_mut()
    }

    /// Raise `flow`'s exception: pending, `QZ_RAISED`.
    fn raise(&mut self, flow: Flow) -> QzStatus {
        if self.pending.is_none() {
            if let Flow::Raise(e) = flow {
                self.pending = Some(e);
            }
        }
        QZ_RAISED
    }

    fn type_error(&mut self, message: &str) -> QzStatus {
        let e = self.interp.err_type(message);
        self.raise(e)
    }

    fn stale(&mut self) -> QzStatus {
        self.type_error("a native method used a handle that is not one of its call's (docs/15)")
    }
}

/// Call the cog's native `mid` (its `entry`) on `recv` and the arguments,
/// bound to the declared parameters' positions (the defaults of those
/// left out filled in): its result, or what it raised. Its result is
/// checked against its declaration under `QUARZ_VERIFY`.
pub fn call(
    interp: &Interp,
    mid: MethodId,
    entry: Entry,
    recv: Value,
    args: ArgVec,
    kw: Vec<(Symbol, Value)>,
    block: Option<Value>,
) -> EvalResult {
    let m = interp.program.method(mid);
    let key = m.native_key.as_deref().unwrap_or(&m.name).to_string();
    let values = bind_params(interp, mid, args, kw)?;
    let nargs = values.len();
    let mut lent = Vec::with_capacity(nargs + 2);
    lent.push(recv);
    lent.extend(values);
    let has_block = block.is_some();
    if let Some(b) = block {
        lent.push(b);
    }
    let mut frame = Frame {
        interp,
        serial: next_serial(),
        lent,
        made: Vec::new(),
        pinned: Vec::new(),
        names: Vec::new(),
        pending: None,
    };
    let recv_h = frame.handle(0);
    let arg_hs: Vec<QzValue> = (1..=nargs).map(|i| frame.handle(i)).collect();
    let blk_h = if has_block {
        frame.handle(nargs + 1)
    } else {
        0
    };
    let mut out: QzValue = 0;
    // SAFETY: the entry is the cog's (`check`), given this call's frame,
    // which outlives the call.
    let status = unsafe {
        entry(
            &mut frame as *mut Frame as *mut QzCall,
            recv_h,
            arg_hs.as_ptr(),
            nargs,
            blk_h,
            &mut out,
        )
    };
    let result = match status {
        QZ_OK if frame.pending.is_some() => Err(Flow::Raise(frame.pending.take().unwrap())),
        QZ_OK if out == 0 => {
            if m.result == interp.program.world.builtin.nil {
                Ok(Value::Nil)
            } else {
                Err(interp.err_runtime(&format!(
                    "native `{key}` returned no result, but its declared result is {}",
                    m.ret.as_deref().unwrap_or("not Void")
                )))
            }
        }
        QZ_OK => match frame.value(out) {
            Some(v) => Ok(v.clone()),
            None => Err(interp.err_runtime(&format!(
                "native `{key}` returned a handle that is not one of its call's"
            ))),
        },
        QZ_RAISED => match frame.pending.take() {
            Some(e) => Err(Flow::Raise(e)),
            None => Err(interp.err_runtime(&format!(
                "native `{key}` returned QZ_RAISED with no exception pending"
            ))),
        },
        s => Err(interp.err_runtime(&format!(
            "native `{key}` returned the status {s}, neither QZ_OK nor QZ_RAISED"
        ))),
    };
    if let Ok(v) = &result {
        interp.check_native_result(mid, v, &frame.lent[0]);
    }
    result
}

/// The arguments at the declared parameters' positions (positional, then
/// keyword-only), each left out taking its literal default
/// (`RtParam::default`): what the entry is given, `nargs` the declared
/// count.
fn bind_params(
    interp: &Interp,
    mid: MethodId,
    args: ArgVec,
    mut kw: Vec<(Symbol, Value)>,
) -> Result<Vec<Value>, Flow> {
    let m = interp.program.method(mid);
    let mut args = args.into_iter();
    let mut out = Vec::with_capacity(m.params.len());
    for p in &m.params {
        let positional = match p.kind {
            RtParamKind::Positional => true,
            RtParamKind::KeywordOnly => false,
            _ => continue,
        };
        let given = if positional { args.next() } else { None };
        let given = given.or_else(|| {
            let at = kw
                .iter()
                .position(|(s, _)| *interp.symbol_name(*s) == *p.name)?;
            Some(kw.remove(at).1)
        });
        let value = match given {
            Some(v) => v,
            None => match p.default.as_ref().and_then(|c| interp.literal_default(c)) {
                Some(v) => v,
                None => {
                    return Err(interp.err_arg(&format!(
                        "`{}` was not given its parameter `{}`",
                        m.name, p.name
                    )))
                }
            },
        };
        out.push(value);
    }
    Ok(out)
}

// ----- the API -----------------------------------------------------------------------

/// The frame of `cx`, a call's.
///
/// # Safety
/// `cx` is the frame `call` passed to the entry, during the call.
unsafe fn frame<'a>(cx: *mut QzCall) -> &'a mut Frame<'a> {
    &mut *(cx as *mut Frame)
}

/// A status function's start: `QZ_RAISED` at once with an exception
/// pending.
macro_rules! pending_status {
    ($f:expr) => {
        if $f.pending.is_some() {
            return QZ_RAISED;
        }
    };
}

/// A maker's start: 0 at once with an exception pending.
macro_rules! pending_maker {
    ($f:expr) => {
        if $f.pending.is_some() {
            return 0;
        }
    };
}

unsafe extern "C" fn kind(cx: *mut QzCall, v: QzValue) -> QzKind {
    let f = frame(cx);
    match f.value(v) {
        None => QZ_INVALID,
        Some(Value::Nil) => QZ_NIL,
        Some(Value::Bool(_)) => QZ_BOOL,
        Some(Value::Int(_)) | Some(Value::BigInt(_)) => QZ_INT,
        Some(Value::Float(_)) => QZ_FLOAT,
        Some(Value::Str(_)) | Some(Value::Short(_)) => QZ_STRING,
        Some(Value::Bytes(_)) => QZ_BYTES,
        Some(Value::Symbol(_)) => QZ_SYMBOL,
        Some(Value::Array(_)) => QZ_ARRAY,
        Some(Value::Hash(_)) => QZ_HASH,
        Some(_) => QZ_OTHER,
    }
}

unsafe extern "C" fn nil(cx: *mut QzCall) -> QzValue {
    let f = frame(cx);
    pending_maker!(f);
    f.make(Value::Nil)
}

unsafe extern "C" fn bool_new(cx: *mut QzCall, b: QzBool) -> QzValue {
    let f = frame(cx);
    pending_maker!(f);
    f.make(Value::Bool(b != 0))
}

/// What was expected, and the class of what `v` is.
fn expected(f: &Frame, what: &str, v: &Value) -> String {
    format!(
        "a native method expected {what}, got {}",
        f.interp.class_name(v)
    )
}

unsafe extern "C" fn bool_get(cx: *mut QzCall, v: QzValue, out: *mut QzBool) -> QzStatus {
    let f = frame(cx);
    pending_status!(f);
    match f.value(v) {
        Some(Value::Bool(b)) => {
            *out = QzBool::from(*b);
            QZ_OK
        }
        Some(other) => {
            let m = expected(f, "a Bool", other);
            f.type_error(&m)
        }
        None => f.stale(),
    }
}

unsafe extern "C" fn int_new(cx: *mut QzCall, i: i64) -> QzValue {
    let f = frame(cx);
    pending_maker!(f);
    f.make(Value::Int(i))
}

unsafe extern "C" fn int_get(cx: *mut QzCall, v: QzValue, out: *mut i64) -> QzStatus {
    let f = frame(cx);
    pending_status!(f);
    match f.value(v) {
        Some(Value::Int(i)) => {
            *out = *i;
            QZ_OK
        }
        Some(Value::BigInt(_)) => {
            let e = f.interp.raise(
                f.interp.program.exc.range_error,
                "a native method was given an Integer beyond 64 bits",
            );
            f.raise(e)
        }
        Some(other) => {
            let m = expected(f, "an Int", other);
            f.type_error(&m)
        }
        None => f.stale(),
    }
}

unsafe extern "C" fn float_new(cx: *mut QzCall, x: f64) -> QzValue {
    let f = frame(cx);
    pending_maker!(f);
    f.make(Value::Float(x))
}

unsafe extern "C" fn float_get(cx: *mut QzCall, v: QzValue, out: *mut f64) -> QzStatus {
    let f = frame(cx);
    pending_status!(f);
    match f.value(v) {
        Some(Value::Float(x)) => {
            *out = *x;
            QZ_OK
        }
        Some(other) => {
            let m = expected(f, "a Float", other);
            f.type_error(&m)
        }
        None => f.stale(),
    }
}

/// `n` bytes at `p` (none when `n` is 0, whatever `p`).
unsafe fn bytes_at<'a>(p: *const u8, n: usize) -> &'a [u8] {
    if n == 0 || p.is_null() {
        &[]
    } else {
        std::slice::from_raw_parts(p, n)
    }
}

unsafe extern "C" fn string_new(
    cx: *mut QzCall,
    p: *const u8,
    n: usize,
    out: *mut QzValue,
) -> QzStatus {
    let f = frame(cx);
    pending_status!(f);
    match std::str::from_utf8(bytes_at(p, n)) {
        Ok(s) => {
            *out = f.make(Value::str(s));
            QZ_OK
        }
        Err(_) => {
            let e = f
                .interp
                .err_arg("a native method made a String of bytes that are not UTF-8");
            f.raise(e)
        }
    }
}

/// Lend `bytes` out through `p` and `n`.
unsafe fn lend(bytes: &[u8], p: *mut *const u8, n: *mut usize) -> QzStatus {
    *p = bytes.as_ptr();
    *n = bytes.len();
    QZ_OK
}

unsafe extern "C" fn string_get(
    cx: *mut QzCall,
    v: QzValue,
    p: *mut *const u8,
    n: *mut usize,
) -> QzStatus {
    let f = frame(cx);
    pending_status!(f);
    // (A short string is inside its `Value`, which the frame keeps in
    // place: lent or boxed.)
    match f.value(v) {
        Some(s @ (Value::Str(_) | Value::Short(_))) => {
            let status = lend(s.as_str().unwrap_or("").as_bytes(), p, n);
            f.pin(v);
            status
        }
        Some(other) => {
            let m = expected(f, "a String", other);
            f.type_error(&m)
        }
        None => f.stale(),
    }
}

unsafe extern "C" fn bytes_new(cx: *mut QzCall, p: *const u8, n: usize) -> QzValue {
    let f = frame(cx);
    pending_maker!(f);
    f.make(Value::bytes(bytes_at(p, n).to_vec()))
}

unsafe extern "C" fn bytes_new_uninit(cx: *mut QzCall, n: usize, p: *mut *mut u8) -> QzValue {
    let f = frame(cx);
    if f.pending.is_some() {
        *p = std::ptr::null_mut();
        return 0;
    }
    let h = f.make(Value::bytes(vec![0; n]));
    f.pin(h);
    // The bytes, the frame's alone until the call returns.
    *p = match f.made_mut(h) {
        Some(Value::Bytes(b)) => Rc::get_mut(b).map_or(std::ptr::null_mut(), |b| b.as_mut_ptr()),
        _ => std::ptr::null_mut(),
    };
    h
}

unsafe extern "C" fn bytes_get(
    cx: *mut QzCall,
    v: QzValue,
    p: *mut *const u8,
    n: *mut usize,
) -> QzStatus {
    let f = frame(cx);
    pending_status!(f);
    match f.value(v) {
        Some(Value::Bytes(b)) => {
            let b: &[u8] = b;
            let status = lend(b, p, n);
            f.pin(v);
            status
        }
        // (A secret's bytes are never lent: ABI 1.0.)
        Some(other) => {
            let m = expected(f, "Bytes", other);
            f.type_error(&m)
        }
        None => f.stale(),
    }
}

unsafe extern "C" fn symbol_new(
    cx: *mut QzCall,
    p: *const u8,
    n: usize,
    out: *mut QzValue,
) -> QzStatus {
    let f = frame(cx);
    pending_status!(f);
    match std::str::from_utf8(bytes_at(p, n)) {
        Ok(s) => {
            let sym = f.interp.intern(s);
            *out = f.make(Value::Symbol(sym));
            QZ_OK
        }
        Err(_) => {
            let e = f
                .interp
                .err_arg("a native method made a Symbol of bytes that are not UTF-8");
            f.raise(e)
        }
    }
}

unsafe extern "C" fn symbol_get(
    cx: *mut QzCall,
    v: QzValue,
    p: *mut *const u8,
    n: *mut usize,
) -> QzStatus {
    let f = frame(cx);
    pending_status!(f);
    match f.value(v) {
        Some(Value::Symbol(s)) => {
            // (One name per symbol: a loop asking the same ones keeps one
            // each.)
            let sym = *s;
            let at = match f.names.iter().position(|(x, _)| *x == sym) {
                Some(at) => at,
                None => {
                    let name = f.interp.symbol_name(sym);
                    f.names.push((sym, name));
                    f.names.len() - 1
                }
            };
            lend(f.names[at].1.as_bytes(), p, n)
        }
        Some(other) => {
            let m = expected(f, "a Symbol", other);
            f.type_error(&m)
        }
        None => f.stale(),
    }
}

unsafe extern "C" fn array_len(cx: *mut QzCall, a: QzValue, out: *mut usize) -> QzStatus {
    let f = frame(cx);
    pending_status!(f);
    match f.value(a) {
        Some(Value::Array(a)) => {
            *out = a.len();
            QZ_OK
        }
        Some(other) => {
            let m = expected(f, "an Array", other);
            f.type_error(&m)
        }
        None => f.stale(),
    }
}

unsafe extern "C" fn array_get(
    cx: *mut QzCall,
    a: QzValue,
    i: usize,
    out: *mut QzValue,
) -> QzStatus {
    let f = frame(cx);
    pending_status!(f);
    let got = match f.value(a) {
        Some(Value::Array(arr)) => arr.get(i).ok_or(arr.len()),
        Some(other) => {
            let m = expected(f, "an Array", other);
            return f.type_error(&m);
        }
        None => return f.stale(),
    };
    match got {
        Ok(v) => {
            *out = f.make(v);
            QZ_OK
        }
        Err(len) => {
            let e = f
                .interp
                .err_index(&format!("index {i} outside an array of {len}"));
            f.raise(e)
        }
    }
}

unsafe extern "C" fn array_new(cx: *mut QzCall, capacity: usize) -> QzValue {
    let f = frame(cx);
    pending_maker!(f);
    f.make(Value::Array(Rc::new(ArrayData::from_values(
        Vec::with_capacity(capacity.min(1 << 20)),
    ))))
}

/// The value of `v` to put into a collection (a clone: the handle stays
/// valid).
fn item(f: &Frame, v: QzValue) -> Option<Value> {
    f.value(v).cloned()
}

unsafe extern "C" fn array_push(cx: *mut QzCall, a: QzValue, v: QzValue) -> QzStatus {
    let f = frame(cx);
    pending_status!(f);
    let Some(v) = item(f, v) else {
        return f.stale();
    };
    // Only an array this call made and has not given away (put into a
    // collection: then shared) changes in place.
    let outcome = match f.made_mut(a) {
        Some(Value::Array(arr)) => match Rc::get_mut(arr) {
            Some(arr) => {
                arr.push(v);
                InPlace::Done
            }
            None => InPlace::Shared,
        },
        Some(_) => InPlace::OtherKind,
        None => InPlace::NotMade,
    };
    outcome.status(f, a, "pushed to", "an array")
}

/// What changing a collection in place (`array_push`, `hash_put`) came
/// to.
enum InPlace {
    Done,
    /// Made by the call, but given away since (put into a collection).
    Shared,
    /// Made by the call, of another kind.
    OtherKind,
    /// Not made by the call: lent, or not a handle of the call's.
    NotMade,
}

impl InPlace {
    fn status(self, f: &mut Frame, h: QzValue, verb: &str, what: &str) -> QzStatus {
        match self {
            InPlace::Done => QZ_OK,
            InPlace::Shared => f.type_error(&format!(
                "a native method {verb} {what} it gave away (docs/15)"
            )),
            InPlace::OtherKind => f.type_error(&format!(
                "a native method {verb} what is not {what} it made"
            )),
            InPlace::NotMade if f.value(h).is_some() => f.type_error(&format!(
                "a native method {verb} {what} it did not make: values are immutable (docs/15)"
            )),
            InPlace::NotMade => f.stale(),
        }
    }
}

unsafe extern "C" fn hash_len(cx: *mut QzCall, h: QzValue, out: *mut usize) -> QzStatus {
    let f = frame(cx);
    pending_status!(f);
    match f.value(h) {
        Some(Value::Hash(h)) => {
            *out = h.len();
            QZ_OK
        }
        Some(other) => {
            let m = expected(f, "a Hash", other);
            f.type_error(&m)
        }
        None => f.stale(),
    }
}

/// Whether `k` may be a key of `hash_get` and `hash_put` (ABI 1.0): one
/// whose `==` and `hash` are built in, so that no Quarz code runs.
fn plain_key(k: &Value) -> bool {
    matches!(
        k,
        Value::Nil
            | Value::Int(_)
            | Value::Str(_)
            | Value::Short(_)
            | Value::Bytes(_)
            | Value::Symbol(_)
    )
}

const KEY_KINDS: &str =
    "a native method's hash key is an Int, a String, Bytes, a Symbol or nil (docs/15)";

unsafe extern "C" fn hash_get(
    cx: *mut QzCall,
    h: QzValue,
    k: QzValue,
    out: *mut QzValue,
    found: *mut QzBool,
) -> QzStatus {
    let f = frame(cx);
    pending_status!(f);
    let Some(key) = f.value(k) else {
        return f.stale();
    };
    if !plain_key(key) {
        return f.type_error(KEY_KINDS);
    }
    let got = match f.value(h) {
        Some(Value::Hash(map)) => map.get(key),
        Some(other) => {
            let m = expected(f, "a Hash", other);
            return f.type_error(&m);
        }
        None => return f.stale(),
    };
    match got {
        Some(v) => {
            *out = f.make(v);
            *found = 1;
        }
        None => {
            *out = 0;
            *found = 0;
        }
    }
    QZ_OK
}

unsafe extern "C" fn hash_entry(
    cx: *mut QzCall,
    h: QzValue,
    i: usize,
    k: *mut QzValue,
    v: *mut QzValue,
) -> QzStatus {
    let f = frame(cx);
    pending_status!(f);
    // (Both kinds of storage by index: O(1).)
    let got = match f.value(h) {
        Some(Value::Hash(map)) => match &**map {
            HashData::Values(m) => m.get_index(i).map(|(a, b)| (a.clone(), b.clone())),
            HashData::Ints(m) => m
                .get_index(i)
                .map(|(a, b)| (Value::Int(*a), Value::Int(*b))),
        }
        .ok_or(map.len()),
        Some(other) => {
            let m = expected(f, "a Hash", other);
            return f.type_error(&m);
        }
        None => return f.stale(),
    };
    match got {
        Ok((a, b)) => {
            *k = f.make(a);
            *v = f.make(b);
            QZ_OK
        }
        Err(len) => {
            let e = f
                .interp
                .err_index(&format!("entry {i} outside a hash of {len}"));
            f.raise(e)
        }
    }
}

unsafe extern "C" fn hash_new(cx: *mut QzCall) -> QzValue {
    let f = frame(cx);
    pending_maker!(f);
    f.make(Value::Hash(Rc::new(HashData::default())))
}

unsafe extern "C" fn hash_put(cx: *mut QzCall, h: QzValue, k: QzValue, v: QzValue) -> QzStatus {
    let f = frame(cx);
    pending_status!(f);
    let (Some(key), Some(value)) = (item(f, k), item(f, v)) else {
        return f.stale();
    };
    if !plain_key(&key) {
        return f.type_error(KEY_KINDS);
    }
    let outcome = match f.made_mut(h) {
        Some(Value::Hash(map)) => match Rc::get_mut(map) {
            Some(map) => {
                map.insert(key, value);
                InPlace::Done
            }
            None => InPlace::Shared,
        },
        Some(_) => InPlace::OtherKind,
        None => InPlace::NotMade,
    };
    outcome.status(f, h, "put into", "a hash")
}

unsafe extern "C" fn exception_class(
    cx: *mut QzCall,
    p: *const u8,
    n: usize,
    out: *mut QzValue,
) -> QzStatus {
    let f = frame(cx);
    pending_status!(f);
    let name = String::from_utf8_lossy(bytes_at(p, n)).into_owned();
    let world = &f.interp.program.world;
    let Some(c) = world.class_by_name(&name) else {
        let e = f
            .interp
            .err_arg(&format!("a native method named no class: `{name}`"));
        return f.raise(e);
    };
    if !world.class(c).raisable_by_native {
        let e = f.interp.err_arg(&format!(
            "a native method cannot raise `{name}`: not an exception class made from a message alone (it is abstract or generic, or one of its classes up to the built-in ones declares an `initialize` or a field, docs/15)"
        ));
        return f.raise(e);
    }
    *out = f.make(Value::Class(c));
    QZ_OK
}

unsafe extern "C" fn raise(cx: *mut QzCall, cls: QzValue, p: *const u8, n: usize) -> QzStatus {
    let f = frame(cx);
    pending_status!(f);
    let c = match f.value(cls) {
        Some(Value::Class(c)) if f.interp.program.world.class(*c).raisable_by_native => *c,
        Some(_) => {
            return f.type_error("a native method raised what `exception_class` did not give")
        }
        None => return f.stale(),
    };
    let message = String::from_utf8_lossy(bytes_at(p, n)).into_owned();
    f.pending = Some(f.interp.make_exception(c, &message));
    QZ_RAISED
}

unsafe extern "C" fn release(cx: *mut QzCall, v: QzValue) {
    let f = frame(cx);
    if (v >> 32) as u32 != f.serial || v & 0xFFFF_FFFF == 0 {
        return;
    }
    let i = (v & 0xFFFF_FFFF) as usize - 1;
    let Some(i) = i.checked_sub(f.lent.len()) else {
        return;
    };
    // (Bytes of it lent: kept to the end of the call.)
    if f.pinned.get(i).copied().unwrap_or(true) {
        return;
    }
    if let Some(slot) = f.made.get_mut(i) {
        *slot = None;
    }
}

/// The API quarz gives every cog, ABI 1.0.
static API: QzApi = QzApi {
    abi_major: QZ_ABI_MAJOR,
    abi_minor: QZ_ABI_MINOR,
    size: std::mem::size_of::<QzApi>(),
    kind,
    nil,
    bool_new,
    bool_get,
    int_new,
    int_get,
    float_new,
    float_get,
    string_new,
    string_get,
    bytes_new,
    bytes_new_uninit,
    bytes_get,
    symbol_new,
    symbol_get,
    array_len,
    array_get,
    array_new,
    array_push,
    hash_len,
    hash_get,
    hash_entry,
    hash_new,
    hash_put,
    exception_class,
    raise,
    release,
};
