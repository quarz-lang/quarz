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

use std::collections::{HashMap, HashSet};
use std::ffi::{c_void, CString};
use std::path::Path;
use std::sync::Mutex;

use quarz_ext::sys::*;
use quarz_ir::{ClassId, MethodId, RtParamKind, RtWorld};

use crate::interp::{ArgVec, EvalResult, Flow, Interp, NativeResult};
use crate::rc::Rc;
use crate::value::{ArrayData, HashData, Symbol, Value};

/// A cog's native entry.
pub type Entry = QzEntry;

/// A loaded module: its cog and its entries by key.
struct Module {
    cog: String,
    entries: HashMap<String, Entry>,
    /// Its `native class`es (ABI 1.1), in the module's order (the index
    /// `object_new` and `object_data` take): each one's name, the drop of
    /// its data and its flags (`QZ_CLASS_SHAREABLE`).
    classes: Vec<(String, QzDrop, u32)>,
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

/// Load cog `cog`'s native library at `path` (`dlopen`, local: each
/// library binds its own symbols) and keep its module (`register`): what
/// the interpreter does. Once per process: a second load of the cog does
/// nothing.
pub fn load(cog: &str, path: &Path) -> Result<(), String> {
    if MODULES
        .lock()
        .expect("the modules")
        .iter()
        .any(|m| m.cog == cog)
    {
        return Ok(());
    }
    let where_ = format!("the native library of cog `{cog}` ({})", path.display());
    let file = CString::new(path.as_os_str().as_encoded_bytes())
        .map_err(|_| format!("{where_}: a path with a NUL"))?;
    // SAFETY: a library's initializers run here, as any loaded library's.
    let handle = unsafe { dlopen(file.as_ptr(), RTLD_NOW) };
    if handle.is_null() {
        return Err(format!("cannot load {where_}: {}", dl_error()));
    }
    let symbol = init_symbol(cog);
    let name = CString::new(symbol.clone()).expect("a symbol");
    let init = unsafe { dlsym(handle, name.as_ptr()) };
    if init.is_null() {
        return Err(format!(
            "{where_} has no `{symbol}`, the init `quarz_ext::module!` makes for cog `{cog}`"
        ));
    }
    // SAFETY: the symbol is the cog's `QzInit` (the ABI's contract).
    let init: QzInit = unsafe { std::mem::transmute::<*mut c_void, QzInit>(init) };
    register(cog, init, &where_)
}

/// Keep cog `cog`'s module, which its `init` gives (`where_` names it in
/// errors): the module's versions checked, its entries by key. What a
/// built program does with the inits it was linked with (`qz_main`'s
/// table), and the interpreter after `dlopen` (`load`): one way to bind
/// a cog's natives. Once per process per cog.
pub fn register(cog: &str, init: QzInit, where_: &str) -> Result<(), String> {
    let mut modules = MODULES.lock().expect("the modules");
    if modules.iter().any(|m| m.cog == cog) {
        return Ok(());
    }
    // SAFETY: the cog's init, given the API (the ABI's contract).
    let module = unsafe { init(&API) };
    if module.is_null() {
        return Err(format!(
            "{where_} refused this quarz's native ABI {QZ_ABI_MAJOR}.{QZ_ABI_MINOR} (its init returned no module): it was built for another"
        ));
    }
    // SAFETY: init gave a module that lives as long as the process.
    let module = unsafe { &*module };
    // (Read first, whatever the major: the prefix that never changes.)
    if module.abi_major != QZ_ABI_MAJOR || module.abi_minor > QZ_ABI_MINOR {
        return Err(format!(
            "{where_} was built for the native ABI {}.{}; this quarz has {QZ_ABI_MAJOR}.{QZ_ABI_MINOR}",
            module.abi_major, module.abi_minor
        ));
    }
    if module.method_size < std::mem::size_of::<QzMethod>() {
        return Err(format!("{where_}: its methods' size is too small"));
    }
    if module.n_methods > 0 && module.methods.is_null() {
        return Err(format!("{where_}: its methods are a null pointer"));
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
            return Err(format!("{where_}: a method's key is not UTF-8"));
        };
        if entries.insert(key.to_string(), m.entry).is_some() {
            return Err(format!("{where_} defines `{key}` twice"));
        }
    }
    // The classes (ABI 1.1): read only from a module of minor 1 or more,
    // which has the fields.
    let mut classes: Vec<(String, QzDrop, u32)> = Vec::new();
    if module.abi_minor >= 1 && module.n_classes > 0 {
        if module.classes.is_null() || module.class_size < std::mem::size_of::<QzClass>() {
            return Err(format!("{where_}: its classes are malformed"));
        }
        for i in 0..module.n_classes {
            // SAFETY: `n_classes` classes `class_size` apart.
            let c = unsafe {
                &*((module.classes as *const u8).add(i * module.class_size) as *const QzClass)
            };
            // SAFETY: `name_len` bytes at `name`.
            let name = unsafe { bytes_at(c.name, c.name_len) };
            let Ok(name) = std::str::from_utf8(name) else {
                return Err(format!("{where_}: a class's name is not UTF-8"));
            };
            if classes.iter().any(|(n, _, _)| n == name) {
                return Err(format!("{where_} lists the class `{name}` twice"));
            }
            if u32::try_from(i).is_err() {
                return Err(format!("{where_} lists too many classes"));
            }
            classes.push((name.to_string(), c.drop, c.flags));
        }
    }
    modules.push(Module {
        cog: cog.to_string(),
        entries,
        classes,
    });
    Ok(())
}

/// Whether every cog's native of `world` has its entry, and every entry
/// a `native def`: an error naming the cog and the key otherwise. Read
/// from `RtWorld::native_cogs` (every declaration, whatever `shake`
/// kept). Checked after the modules are registered, before running.
pub fn check(world: &RtWorld) -> Result<(), String> {
    // (A program without native cogs does nothing here.)
    if world.native_cogs.is_empty() {
        return Ok(());
    }
    let modules = MODULES.lock().expect("the modules");
    for cog in &world.native_cogs {
        let name = &cog.name;
        let Some(module) = modules.iter().find(|m| &m.cog == name) else {
            return Err(format!(
                "cog `{name}` brings native code (`[native]` in its Cog.toml), but its library is not loaded"
            ));
        };
        let declared: HashSet<&str> = cog.methods.iter().map(|(_, k)| k.as_str()).collect();
        let mut missing: Vec<&&str> = declared
            .iter()
            .filter(|k| !module.entries.contains_key(**k))
            .collect();
        missing.sort();
        if let Some(key) = missing.first() {
            return Err(format!(
                "cog `{name}` declares `native def` `{key}`, which its native library does not define"
            ));
        }
        let mut extra: Vec<&String> = module
            .entries
            .keys()
            .filter(|k| !declared.contains(k.as_str()))
            .collect();
        extra.sort();
        if let Some(key) = extra.first() {
            return Err(format!(
                "cog `{name}`'s native library defines `{key}`, which the cog does not declare `native def`"
            ));
        }
        // Its classes, both ways, and whether each is shareable.
        for (_, class, shareable) in &cog.classes {
            let Some((_, _, flags)) = module.classes.iter().find(|(n, _, _)| n == class) else {
                return Err(format!(
                    "cog `{name}` declares `native class {class}`, which its native library does not list"
                ));
            };
            let listed = flags & QZ_CLASS_SHAREABLE != 0;
            if listed != *shareable {
                return Err(if *shareable {
                    format!("cog `{name}` declares `{class}` Shareable, but its native library does not mark it shareable (its data must be `Send + Sync`)")
                } else {
                    format!("cog `{name}`'s native library marks `{class}` shareable, but the cog does not declare it `Shareable`")
                });
            }
        }
        let mut unlisted: Vec<&String> = module
            .classes
            .iter()
            .map(|(k, _, _)| k)
            .filter(|k| !cog.classes.iter().any(|(_, c, _)| c == *k))
            .collect();
        unlisted.sort();
        if let Some(class) = unlisted.first() {
            return Err(format!(
                "cog `{name}`'s native library lists the class `{class}`, which the cog does not declare `native class`"
            ));
        }
    }
    Ok(())
}

/// Each method's entry, by method id, for a program of `n` methods:
/// from `RtWorld::native_cogs`' declarations and the cogs' modules;
/// `None` for every other method, and for one whose module is not
/// registered (a call then says so).
pub fn bind(world: &RtWorld, n: usize) -> Vec<Option<Entry>> {
    let mut out = vec![None; n];
    if world.native_cogs.is_empty() {
        return out;
    }
    let modules = MODULES.lock().expect("the modules");
    for cog in &world.native_cogs {
        let Some(module) = modules.iter().find(|m| m.cog == cog.name) else {
            continue;
        };
        for (id, key) in &cog.methods {
            if let Some(slot) = out.get_mut(*id as usize) {
                *slot = module.entries.get(key).copied();
            }
        }
    }
    out
}

/// Each native cog's classes, by `RtWorld::native_cogs` index and then by
/// the index in its module's list (what `object_new` and `object_data`
/// take): the class and the drop of its data. Bound once, as the methods
/// are; `check` has matched both sides, so an entry is `None` only for a
/// cog whose module is not registered (whose calls never run).
pub type ClassTable = Vec<Vec<Option<(ClassId, QzDrop)>>>;

pub fn bind_classes(world: &RtWorld) -> ClassTable {
    if world.native_cogs.is_empty() {
        return Vec::new();
    }
    let modules = MODULES.lock().expect("the modules");
    world
        .native_cogs
        .iter()
        .map(|cog| {
            let Some(module) = modules.iter().find(|m| m.cog == cog.name) else {
                return Vec::new();
            };
            module
                .classes
                .iter()
                .map(|(name, drop, _)| {
                    cog.classes
                        .iter()
                        .find(|(_, c, _)| c == name)
                        .map(|(id, _, _)| (*id, *drop))
                })
                .collect()
        })
        .collect()
}

// ----- native objects ------------------------------------------------------------

/// The data of an object of a cog's `native class` (ABI 1.1): its class,
/// the cog's pointer, and the cog's drop for it, run when the last
/// reference goes, on whichever worker drops it (a shareable class's data
/// is `Send + Sync`, the wrapper's bound; an unshareable one's never
/// leaves its task, the checker's rule).
pub struct NativeObject {
    pub class: ClassId,
    data: *mut c_void,
    drop: QzDrop,
}

// SAFETY: see the type's doc: what crosses threads is a shareable
// class's data, `Send + Sync` by the wrapper's bound, or a C cog's word.
unsafe impl Send for NativeObject {}
unsafe impl Sync for NativeObject {}

impl std::fmt::Debug for NativeObject {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "NativeObject(class {})", self.class)
    }
}

impl NativeObject {
    pub fn data(&self) -> *mut c_void {
        self.data
    }
}

impl Drop for NativeObject {
    fn drop(&mut self) {
        // (A panic in the cog's drop is caught by its wrapper, reported
        // once and the data leaked: decided on #677.)
        // SAFETY: the cog's drop for this data, called once.
        unsafe { (self.drop)(self.data) }
    }
}

// ----- a call ------------------------------------------------------------------------

/// The values a call makes that live inline in its frame
/// (`Made::inline`), before the first chunk.
const INLINE: usize = 8;
/// The values of one chunk past them (`Made::chunks`).
const CHUNK: usize = 32;

/// One call's values: lent (`lent`: the receiver, the arguments, the
/// block), made (`made`), the symbol names lent (`names`, one per
/// symbol), and the pending exception.
///
/// **Addresses** (docs/15, handle rule 5): a pointer `string_get`,
/// `bytes_get` or `bytes_new_uninit` lends may point inside a `Value`
/// itself (a `Short` string's bytes), so every value a handle names
/// stays at one address until the entry returns:
/// - the frame is a local of `call`, never moved between the entry's
///   call and its return (the cog holds `&mut frame` as its `QzCall`);
/// - `lent` is complete before the entry is called (the receiver, the
///   call's argument list as bound, the block) and never changed after,
///   so its values stay put, inline or spilled;
/// - a made value's slot is inline in the frame (`Made::inline`), or in a
///   chunk, which never moves once boxed (`Made::chunks` may reallocate
///   its vector of boxes, never a box);
/// - `release` leaves a value whose bytes were lent (`Made::pin`).
struct Frame<'a> {
    interp: &'a Interp,
    /// The cog's native this call runs (what `object_new` may make).
    mid: MethodId,
    serial: u32,
    lent: Lent,
    made: Made,
    /// (Allocated by the first `symbol_get`, #1203.)
    names: Option<Box<Names>>,
    /// What the call raised, or a block's `break`/`return` it carries
    /// (`call_block`), pending until the entry returns.
    pending: Option<Flow>,
}

/// The symbols' names a call lent, one per symbol (`symbol_get`).
type Names = Vec<(Symbol, Rc<str>)>;

/// The values a call lends its entry, by index: the receiver (0), the
/// arguments bound to the declared parameters (1 to `args.len()`), and the
/// block after them. The argument list is the call's own, kept as it came
/// when it needed no binding (#1203).
struct Lent {
    recv: Value,
    args: ArgVec,
    block: Option<Value>,
}

impl Lent {
    fn len(&self) -> usize {
        1 + self.args.len() + usize::from(self.block.is_some())
    }

    fn get(&self, i: usize) -> Option<&Value> {
        match i {
            0 => Some(&self.recv),
            i if i <= self.args.len() => self.args.get(i - 1),
            i if i == self.args.len() + 1 => self.block.as_ref(),
            _ => None,
        }
    }
}

/// The values a call made, by index (`Frame::make`): the first `INLINE`
/// inline, the rest in boxed chunks of `CHUNK` (their addresses: see
/// `Frame`), with a bit per value set once bytes of it were lent.
struct Made {
    len: usize,
    /// (Dropped by `Made`'s `Drop`, the slots in use only.)
    inline: std::mem::ManuallyDrop<[Option<Value>; INLINE]>,
    /// Bit `i`: bytes of value `i` were lent (the first 64).
    pinned: u64,
    /// Past the first values: allocated only when a call makes that many,
    /// so that dropping a frame that did not is a null check (#1203).
    spill: Option<Box<Spill>>,
}

/// `Made`'s values past `INLINE`, and pins past 64.
#[derive(Default)]
struct Spill {
    // (Boxed: a chunk keeps its address when the vector grows.)
    #[allow(clippy::vec_box)]
    chunks: Vec<Box<[Option<Value>; CHUNK]>>,
    /// Word `w`: bits of values `64 * (w + 1)` on.
    pinned: Vec<u64>,
}

impl Drop for Made {
    fn drop(&mut self) {
        // (Slots past `len` were never filled: `None`, nothing to drop.)
        for slot in &mut self.inline[..self.len.min(INLINE)] {
            *slot = None;
        }
    }
}

impl Made {
    fn new() -> Made {
        Made {
            len: 0,
            inline: std::mem::ManuallyDrop::new([const { None }; INLINE]),
            pinned: 0,
            spill: None,
        }
    }

    /// Keep `v`: its index.
    fn push(&mut self, v: Value) -> usize {
        let i = self.len;
        if i < INLINE {
            self.inline[i] = Some(v);
        } else {
            let spill = self.spill.get_or_insert_with(Box::default);
            let j = i - INLINE;
            if j.is_multiple_of(CHUNK) {
                spill.chunks.push(Box::new([const { None }; CHUNK]));
            }
            spill.chunks[j / CHUNK][j % CHUNK] = Some(v);
            if i >= 64 && (i - 64) / 64 >= spill.pinned.len() {
                spill.pinned.push(0);
            }
        }
        self.len += 1;
        i
    }

    fn slot(&self, i: usize) -> Option<&Option<Value>> {
        if i >= self.len {
            None
        } else if i < INLINE {
            Some(&self.inline[i])
        } else {
            let j = i - INLINE;
            Some(&self.spill.as_ref()?.chunks[j / CHUNK][j % CHUNK])
        }
    }

    fn slot_mut(&mut self, i: usize) -> Option<&mut Option<Value>> {
        if i >= self.len {
            None
        } else if i < INLINE {
            Some(&mut self.inline[i])
        } else {
            let j = i - INLINE;
            Some(&mut self.spill.as_mut()?.chunks[j / CHUNK][j % CHUNK])
        }
    }

    fn get(&self, i: usize) -> Option<&Value> {
        self.slot(i)?.as_ref()
    }

    fn get_mut(&mut self, i: usize) -> Option<&mut Value> {
        self.slot_mut(i)?.as_mut()
    }

    /// Bytes of value `i` were lent: kept to the end of the call.
    fn pin(&mut self, i: usize) {
        if i >= self.len {
            return;
        }
        if i < 64 {
            self.pinned |= 1 << i;
        } else if let Some(w) = self
            .spill
            .as_mut()
            .and_then(|s| s.pinned.get_mut((i - 64) / 64))
        {
            *w |= 1 << (i % 64);
        }
    }

    fn is_pinned(&self, i: usize) -> bool {
        if i < 64 {
            self.pinned >> i & 1 == 1
        } else {
            self.spill
                .as_ref()
                .and_then(|s| s.pinned.get((i - 64) / 64))
                .is_some_and(|w| w >> (i % 64) & 1 == 1)
        }
    }

    /// Let go of value `i`, unless bytes of it were lent.
    fn release(&mut self, i: usize) {
        if i >= self.len || self.is_pinned(i) {
            return;
        }
        if let Some(slot) = self.slot_mut(i) {
            *slot = None;
        }
    }

    /// Value `i`, taken out (the result, once the entry has returned).
    fn take(&mut self, i: usize) -> Option<Value> {
        self.slot_mut(i)?.take()
    }
}

/// The calls' serials, process-wide (ABI 1.1): a handle carries its
/// call's, so that one from any other call (on this thread or another
/// worker's, where a cog may have smuggled it) is refused, never taken
/// for a value of this call's. (0 is never a serial: wrapping skips it.)
static SERIAL: std::sync::atomic::AtomicU32 = std::sync::atomic::AtomicU32::new(0);

fn next_serial() -> u32 {
    loop {
        let n = SERIAL
            .fetch_add(1, std::sync::atomic::Ordering::Relaxed)
            .wrapping_add(1);
        if n != 0 {
            return n;
        }
    }
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
        self.made.get(i - self.lent.len())
    }

    fn make(&mut self, v: Value) -> QzValue {
        let i = self.made.push(v);
        self.handle(self.lent.len() + i)
    }

    /// The result `h`, once the entry has returned: a made value taken
    /// out, a lent one copied.
    fn take(&mut self, h: QzValue) -> Option<Value> {
        if (h >> 32) as u32 != self.serial || h & 0xFFFF_FFFF == 0 {
            return None;
        }
        let i = (h & 0xFFFF_FFFF) as usize - 1;
        match i.checked_sub(self.lent.len()) {
            None => self.lent.get(i).cloned(),
            Some(i) => self.made.take(i),
        }
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
        if let Some(i) = i.checked_sub(self.lent.len()) {
            self.made.pin(i);
        }
    }

    /// A made value of this call's, to change in place.
    fn made_mut(&mut self, h: QzValue) -> Option<&mut Value> {
        if (h >> 32) as u32 != self.serial || h & 0xFFFF_FFFF == 0 {
            return None;
        }
        let i = ((h & 0xFFFF_FFFF) as usize - 1).checked_sub(self.lent.len())?;
        self.made.get_mut(i)
    }

    /// Keep `flow` (an exception, or a block's `break`/`return`) pending,
    /// the first only: `QZ_RAISED`.
    fn raise(&mut self, flow: Flow) -> QzStatus {
        if self.pending.is_none() {
            self.pending = Some(flow);
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
/// left out filled in): its result, or what it raised. Its result's
/// class is tested against its declaration on every call
/// (`Interp::native_result_test`), a mismatch raising `TypeError`.
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
    // (Named on the error paths only.)
    let key = || m.native_key.as_deref().unwrap_or(&m.name);
    // (`lent` is filled in place, and complete before the entry is
    // called: never pushed to after.)
    let mut frame = Frame {
        interp,
        mid,
        serial: next_serial(),
        lent: Lent {
            recv,
            args: bind_params(interp, mid, args, kw)?,
            block,
        },
        made: Made::new(),
        names: None,
        pending: None,
    };
    let nargs = frame.lent.args.len();
    let has_block = frame.lent.block.is_some();
    let recv_h = frame.handle(0);
    let mut arg_buf = [0; INLINE];
    let spilled: Vec<QzValue>;
    let arg_hs: &[QzValue] = if nargs <= INLINE {
        for (i, h) in arg_buf[..nargs].iter_mut().enumerate() {
            *h = frame.handle(i + 1);
        }
        &arg_buf[..nargs]
    } else {
        spilled = (1..=nargs).map(|i| frame.handle(i)).collect();
        &spilled
    };
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
        QZ_OK if frame.pending.is_some() => Err(frame.pending.take().unwrap()),
        QZ_OK if out == 0 => {
            if m.result == interp.program.world.builtin.nil {
                Ok(Value::Nil)
            } else {
                Err(interp.err_runtime(&format!(
                    "native `{}` returned no result, but its declared result is {}",
                    key(),
                    m.ret.as_deref().unwrap_or("not Void")
                )))
            }
        }
        QZ_OK => match frame.take(out) {
            Some(v) => Ok(v),
            None => Err(interp.err_runtime(&format!(
                "native `{}` returned a handle that is not one of its call's",
                key()
            ))),
        },
        QZ_RAISED => match frame.pending.take() {
            Some(flow) => Err(flow),
            None => Err(interp.err_runtime(&format!(
                "native `{}` returned QZ_RAISED with no exception pending",
                key()
            ))),
        },
        s => Err(interp.err_runtime(&format!(
            "native `{}` returned the status {s}, neither QZ_OK nor QZ_RAISED",
            key()
        ))),
    };
    // A cog's native is trusted for nothing: its result's class is tested
    // on every call (decided on #677), by the test `QUARZ_VERIFY` runs for
    // the standard natives, and a mismatch is the program's `TypeError`.
    if let Ok(v) = &result {
        let self_class = interp.self_class(mid, &frame.lent.recv);
        match interp.native_result_test(mid, v, self_class) {
            Ok(()) => {}
            Err(NativeResult::Mismatch(what)) => return Err(interp.err_type(&what)),
            Err(NativeResult::NoTest(what)) => {
                return Err(interp.err_runtime(&format!("internal error: {what}")))
            }
        }
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
) -> Result<ArgVec, Flow> {
    let m = interp.program.method(mid);
    // Positional parameters only (`RtMethod::positional_only`), each
    // given positionally: the call's own argument list, as it is.
    // (Every other call takes the loop below, which also has every
    // error: none can happen here.)
    if m.positional_only && kw.is_empty() && args.len() == m.params.len() {
        return Ok(args);
    }
    let mut out = ArgVec::with_capacity(m.params.len());
    let mut args = args.into_iter();
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
    // (The checker lets no such call through, a procedure's included:
    // refused here all the same, never dropped.)
    if args.next().is_some() {
        return Err(interp.err_arg(&format!(
            "`{}` was given more arguments than it takes",
            m.name
        )));
    }
    if let Some((k, _)) = kw.first() {
        return Err(interp.err_arg(&format!(
            "`{}` was given the keyword `{}`, which it does not take",
            m.name,
            interp.symbol_name(*k)
        )));
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
            let interp = f.interp;
            let names = f.names.get_or_insert_with(Box::default);
            let at = match names.iter().position(|(x, _)| *x == sym) {
                Some(at) => at,
                None => {
                    names.push((sym, interp.symbol_name(sym)));
                    names.len() - 1
                }
            };
            lend(names[at].1.as_bytes(), p, n)
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
    f.pending = Some(Flow::Raise(f.interp.make_exception(c, &message)));
    QZ_RAISED
}

/// Call the method's block with `nargs` handles of this call's (ABI
/// 1.1): its value a handle of this call's. The block runs on the calling
/// task, through the block call a standard native's `yield` makes
/// (`Interp::call_block`: `next` gives its value). It may suspend the
/// task (a `Channel` receive): the native's frames stay where they are on
/// the task's stack, and the task resumes on the same worker (docs/15).
/// The block may enter natives again, this one included (each a frame of
/// its own). What it raises, and a `break` or `return` out of it, is
/// pending: `QZ_RAISED`, and the entry's caller gets it when the entry
/// returns.
unsafe extern "C" fn call_block(
    cx: *mut QzCall,
    blk: QzValue,
    args: *const QzValue,
    nargs: usize,
    out: *mut QzValue,
) -> QzStatus {
    let f = frame(cx);
    pending_status!(f);
    let block = match f.value(blk) {
        Some(b @ Value::Proc(_)) => b.clone(),
        Some(other) => {
            let m = expected(f, "a block", other);
            return f.type_error(&m);
        }
        None => return f.stale(),
    };
    let mut argv = ArgVec::new();
    for i in 0..nargs {
        match f.value(*args.add(i)) {
            Some(v) => argv.push(v.clone()),
            None => return f.stale(),
        }
    }
    let interp = f.interp;
    // (While the block runs, the task may suspend inside this native: its
    // coroutine is then never unwound, `Scheduler`'s `Drop`.)
    let task = interp.current_task();
    task.set_in_native(true);
    let result = interp.call_block(&block, argv);
    task.set_in_native(false);
    match result {
        Ok(v) => {
            *out = f.make(v);
            QZ_OK
        }
        Err(flow) => f.raise(flow),
    }
}

/// The class `cls` of this call's cog (ABI 1.1: the index in its
/// module's list) with the drop of its data, from the table bound at
/// start (`bind_classes`): no lock, no search. Else what is wrong, for a
/// `TypeError`.
fn native_class(f: &Frame, cls: u32) -> Result<(ClassId, QzDrop), String> {
    let program = &f.interp.program;
    let ext = program.method(f.mid).ext;
    let entry = ext
        .and_then(|k| program.ext_classes.get(k as usize))
        .and_then(|t| t.get(cls as usize))
        .copied()
        .flatten();
    entry.ok_or_else(|| {
        format!("a native method named the class {cls}, which its cog's module does not list")
    })
}

/// An object of the cog's class `cls` (its index), holding `data` (ABI
/// 1.1): a handle of this call's. Only a class the calling method's declaration
/// returns (`RtMethod::makes`: what `shake` keeps live), else `TypeError`;
/// on an error the data is still the cog's.
unsafe extern "C" fn object_new(
    cx: *mut QzCall,
    cls: u32,
    data: *mut c_void,
    out: *mut QzValue,
) -> QzStatus {
    let f = frame(cx);
    pending_status!(f);
    let (class, drop) = match native_class(f, cls) {
        Ok(c) => c,
        Err(m) => return f.type_error(&m),
    };
    let m = f.interp.program.method(f.mid);
    if !m.makes.contains(&class) {
        let msg = format!(
            "a native method made an object of `{}`, which its declaration does not return (docs/15)",
            f.interp.program.world.classes[class as usize].name
        );
        return f.type_error(&msg);
    }
    *out = f.make(Value::Native(Rc::new(NativeObject { class, data, drop })));
    QZ_OK
}

/// The data of `v`, an object of exactly the cog's class `cls` (its
/// index, ABI 1.1): else `TypeError`. Valid while `v` is (the call's handle keeps
/// it).
unsafe extern "C" fn object_data(
    cx: *mut QzCall,
    v: QzValue,
    cls: u32,
    out: *mut *mut c_void,
) -> QzStatus {
    let f = frame(cx);
    pending_status!(f);
    let (class, _) = match native_class(f, cls) {
        Ok(c) => c,
        Err(m) => return f.type_error(&m),
    };
    match f.value(v) {
        Some(Value::Native(o)) if o.class == class => {
            *out = o.data();
            QZ_OK
        }
        Some(other) => {
            let name = f.interp.program.world.classes[class as usize].name.clone();
            let m = expected(f, &format!("an object of {name}"), other);
            f.type_error(&m)
        }
        None => f.stale(),
    }
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
    f.made.release(i);
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
    call_block,
    object_new,
    object_data,
};
