//! Where compiled code handed its activation to the interpreter
//! (`ffi::qz_resume`: a speculation failed). `QUARZ_COUNT_DEOPTS=1`
//! counts them by site, on every thread, and prints them at exit. Off,
//! a hand-over costs one load of the flag more, against the rest of the
//! function interpreted.

use std::sync::atomic::{AtomicU8, Ordering};
use std::sync::Mutex;

use quarz_ir::{Function, Inst};

/// 0: not read yet, 1: off, 2: on.
static COUNTING: AtomicU8 = AtomicU8::new(0);

/// A site: function name, block, instruction (`None` for the
/// terminator), and what is there; with its count (few sites: a list).
type Site = (String, u32, Option<u32>, String);
static SITES: Mutex<Vec<(Site, u64)>> = Mutex::new(Vec::new());

/// Whether hand-overs are counted (the environment is read once).
pub fn counting() -> bool {
    match COUNTING.load(Ordering::Relaxed) {
        0 => {
            let on = std::env::var_os("QUARZ_COUNT_DEOPTS").is_some();
            COUNTING.store(if on { 2 } else { 1 }, Ordering::Relaxed);
            on
        }
        c => c == 2,
    }
}

/// Count a hand-over at instruction `inst` of `block` of `f`.
#[cold]
#[inline(never)]
pub fn record(f: &Function, block: u32, inst: u32) {
    let blk = f.blocks.get(block as usize);
    let (index, what) = match blk.and_then(|b| b.insts.get(inst as usize)) {
        Some(i) => (Some(inst), label(i)),
        None => (None, "terminator".to_string()),
    };
    let site = (f.name.clone(), block, index, what);
    let mut sites = SITES.lock().unwrap_or_else(|e| e.into_inner());
    match sites.iter_mut().find(|(s, _)| *s == site) {
        Some((_, n)) => *n += 1,
        None => sites.push((site, 1)),
    }
}

/// The kind of an instruction (and the operator of a `BinOp`).
fn label(inst: &Inst) -> String {
    if let Inst::BinOp { op, .. } = inst {
        return format!("BinOp {op:?}");
    }
    let text = format!("{inst:?}");
    let end = text.find([' ', '{', '(']).unwrap_or(text.len());
    text[..end].to_string()
}

/// Print the counts (most frequent first) on standard error, when on.
#[cold]
#[inline(never)]
pub fn report() {
    if !counting() {
        return;
    }
    let mut rows = SITES.lock().unwrap_or_else(|e| e.into_inner()).clone();
    rows.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));
    let total: u64 = rows.iter().map(|(_, n)| *n).sum();
    eprintln!("quarz: {total} deoptimizations");
    for ((name, block, index, what), n) in rows {
        let at = match index {
            Some(i) => format!("b{block}.{i}"),
            None => format!("b{block}"),
        };
        eprintln!("  {n:>8}  {name} {at} {what}");
    }
}
