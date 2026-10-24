//! Compiled frames found on the native stack: the typed entries the LLVM
//! backend emits push no activation, so a backtrace walks the native
//! stack with the C unwinder (every compiled function carries unwind
//! information there) and maps each return address back to a function
//! and a line. The backend encodes the QIR line as the DWARF line; the
//! build then keeps only what is needed here, the typed entries' ranges
//! and the line rows, in a section of its own (`SECTION`, written by
//! `table`) and strips the symbols and the debug information. An
//! executable left unstripped is read through its symbol table and DWARF
//! line table instead.

use std::borrow::Cow;
use std::ffi::c_void;
use std::sync::OnceLock;

use gimli::{EndianSlice, RunTimeEndian};
use object::{Object, ObjectSection, ObjectSymbol};
use quarz_ir::FuncId;

extern "C" {
    fn _Unwind_Backtrace(
        trace: extern "C" fn(*mut c_void, *mut c_void) -> i32,
        arg: *mut c_void,
    ) -> i32;
    fn _Unwind_GetIP(ctx: *mut c_void) -> usize;
    fn _Unwind_GetCFA(ctx: *mut c_void) -> usize;
}

/// What the executable says about its compiled code: the typed entries
/// by address, and the line table.
struct Info {
    /// `(start, end, function)` of each typed entry at run time, sorted.
    typed: Vec<(usize, usize, FuncId)>,
    /// `(address, line)` rows of every line program, sorted.
    lines: Vec<(usize, u32)>,
}

static INFO: OnceLock<Option<Info>> = OnceLock::new();

/// The section a stripped executable keeps its table in.
pub const SECTION: &str = ".quarz_bt";

fn load() -> Option<Info> {
    let data: &'static [u8] = Box::leak(std::fs::read("/proc/self/exe").ok()?.into_boxed_slice());
    let file = object::File::parse(data).ok()?;
    match file.section_by_name(SECTION) {
        Some(s) => decode(s.data().ok()?),
        None => {
            // The load base: where `qz_main` is now, against where the
            // file says it is.
            let link_main = file
                .symbols()
                .find(|s| s.name() == Ok("qz_main"))
                .map(|s| s.address() as usize)?;
            let base = (crate::ffi::qz_main as *const () as usize).wrapping_sub(link_main);
            from_dwarf(&file, base)
        }
    }
}

/// The typed entries and the line rows of `file`, at `base`.
fn from_dwarf<'a>(file: &object::File<'a>, base: usize) -> Option<Info> {
    let mut typed: Vec<(usize, usize, FuncId)> = file
        .symbols()
        .filter_map(|s| {
            let name = s.name().ok()?;
            let fid: FuncId = name
                .strip_prefix("qz_fn_")?
                .strip_suffix("_t")?
                .parse()
                .ok()?;
            let start = base.wrapping_add(s.address() as usize);
            Some((start, start + s.size() as usize, fid))
        })
        .collect();
    typed.sort();
    let section = |id: gimli::SectionId| -> Result<EndianSlice<'a, RunTimeEndian>, gimli::Error> {
        let bytes: &'a [u8] = match file.section_by_name(id.name()) {
            Some(s) => match s.uncompressed_data() {
                Ok(Cow::Borrowed(b)) => b,
                Ok(Cow::Owned(v)) => Box::leak(v.into_boxed_slice()),
                Err(_) => &[],
            },
            None => &[],
        };
        Ok(EndianSlice::new(bytes, RunTimeEndian::Little))
    };
    let dwarf = gimli::Dwarf::load(section).ok()?;
    let mut lines: Vec<(usize, u32)> = Vec::new();
    let mut units = dwarf.units();
    while let Ok(Some(header)) = units.next() {
        let Ok(unit) = dwarf.unit(header) else {
            continue;
        };
        let Some(program) = unit.line_program.clone() else {
            continue;
        };
        let mut rows = program.rows();
        while let Ok(Some((_, row))) = rows.next_row() {
            if row.end_sequence() {
                continue;
            }
            let line = row.line().map(|l| l.get() as u32).unwrap_or(0);
            lines.push((base.wrapping_add(row.address() as usize), line));
        }
    }
    lines.sort();
    Some(Info { typed, lines })
}

/// The table `SECTION` holds for the linked executable `exe` (for the
/// build, before it strips it): little-endian words, the link address of
/// `qz_main`, the count of typed entries and each one's start, end and
/// function, then the count of line rows and each one's address and
/// line. Only the rows inside typed entries are kept.
pub fn table(exe: &[u8]) -> Result<Vec<u8>, String> {
    let file = object::File::parse(exe).map_err(|e| e.to_string())?;
    let link_main = file
        .symbols()
        .find(|s| s.name() == Ok("qz_main"))
        .map(|s| s.address())
        .ok_or("no qz_main in the executable")?;
    let info = from_dwarf(&file, 0).ok_or("no line table in the executable")?;
    let inside = |a: usize| {
        let k = info.typed.partition_point(|&(start, _, _)| start <= a);
        k.checked_sub(1)
            .and_then(|i| info.typed.get(i))
            .is_some_and(|&(_, end, _)| a < end)
    };
    let lines: Vec<(usize, u32)> = info
        .lines
        .iter()
        .copied()
        .filter(|&(a, _)| inside(a))
        .collect();
    let mut out: Vec<u8> = Vec::new();
    let mut word = |w: u64| out.extend_from_slice(&w.to_le_bytes());
    word(link_main);
    word(info.typed.len() as u64);
    for &(start, end, fid) in &info.typed {
        word(start as u64);
        word(end as u64);
        word(u64::from(fid));
    }
    word(lines.len() as u64);
    for &(addr, line) in &lines {
        word(addr as u64);
        word(u64::from(line));
    }
    Ok(out)
}

/// The table of `SECTION` (see `table`), at the running executable's
/// load base.
fn decode(bytes: &[u8]) -> Option<Info> {
    let mut words = bytes
        .as_chunks::<8>()
        .0
        .iter()
        .map(|c| u64::from_le_bytes(*c) as usize);
    let link_main = words.next()?;
    let base = (crate::ffi::qz_main as *const () as usize).wrapping_sub(link_main);
    let n = words.next()?;
    let mut typed = Vec::with_capacity(n);
    for _ in 0..n {
        let (start, end, fid) = (words.next()?, words.next()?, words.next()?);
        typed.push((
            base.wrapping_add(start),
            base.wrapping_add(end),
            fid as FuncId,
        ));
    }
    let n = words.next()?;
    let mut lines = Vec::with_capacity(n);
    for _ in 0..n {
        let (addr, line) = (words.next()?, words.next()?);
        lines.push((base.wrapping_add(addr), line as u32));
    }
    Some(Info { typed, lines })
}

/// The typed entries on the native stack, innermost first: each with
/// the frame's stack address, its function and the line of the call it
/// is in.
pub fn frames() -> Vec<(usize, FuncId, u32)> {
    let Some(info) = INFO.get_or_init(load) else {
        return Vec::new();
    };
    let mut raw: Vec<(usize, usize)> = Vec::new();
    extern "C" fn visit(ctx: *mut c_void, arg: *mut c_void) -> i32 {
        // SAFETY: `arg` is the vector below, alive for the walk.
        let raw = unsafe { &mut *(arg as *mut Vec<(usize, usize)>) };
        // SAFETY: the unwinder hands a valid context.
        let (ip, cfa) = unsafe { (_Unwind_GetIP(ctx), _Unwind_GetCFA(ctx)) };
        raw.push((ip, cfa));
        0
    }
    // SAFETY: the callback only records addresses.
    unsafe { _Unwind_Backtrace(visit, &mut raw as *mut _ as *mut c_void) };
    let (lo, hi) = crate::sched::stack_range();
    let mut out = Vec::new();
    for (ip, cfa) in raw {
        if cfa < lo || cfa > hi {
            continue;
        }
        // The return address is just past the call: look the call up.
        let at = ip.saturating_sub(1);
        let k = info.typed.partition_point(|&(start, _, _)| start <= at);
        let Some(&(start, end, fid)) = k.checked_sub(1).and_then(|i| info.typed.get(i)) else {
            continue;
        };
        if at < start || at >= end {
            continue;
        }
        let r = info.lines.partition_point(|&(addr, _)| addr <= at);
        let line = r
            .checked_sub(1)
            .and_then(|i| info.lines.get(i))
            .map(|&(_, l)| l)
            .unwrap_or(0);
        out.push((cfa, fid, line));
    }
    out
}
