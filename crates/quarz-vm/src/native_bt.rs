//! Compiled frames found on the native stack: the typed entries the LLVM
//! backend emits push no activation, so a backtrace walks the native
//! stack with the C unwinder (every compiled function carries unwind
//! information there) and maps each return address back to a function
//! and a line through the executable's own symbol table and DWARF line
//! table (the backend encodes the QIR line as the DWARF line).

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

fn load() -> Option<Info> {
    let data: &'static [u8] = Box::leak(std::fs::read("/proc/self/exe").ok()?.into_boxed_slice());
    let file = object::File::parse(data).ok()?;
    // The load base: where `qz_main` is now, against where the file
    // says it is.
    let link_main = file
        .symbols()
        .find(|s| s.name() == Ok("qz_main"))
        .map(|s| s.address() as usize)?;
    let base = (crate::ffi::qz_main as *const () as usize).wrapping_sub(link_main);
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
    let section =
        |id: gimli::SectionId| -> Result<EndianSlice<'static, RunTimeEndian>, gimli::Error> {
            let bytes: &'static [u8] = match file.section_by_name(id.name()) {
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
