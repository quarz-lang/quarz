//! A compiled program's methods, which it decodes one by one when first
//! needed rather than all at start-up (most of a program's methods are
//! never called; decoding them was a third of its start-up).
//!
//! `quarz build` encodes them apart (`encode`), with what the runtime
//! derives from every method when it loads a program, computed then:
//! where its natives are, whether its parameters are positional only,
//! the function a call can go straight to, whether it has a dispatch
//! column. The section is little-endian 32-bit words, read in place:
//!
//! ```text
//! count, owned ids (6 words),
//! count records of RECORD words: offset, length, native positions (3),
//!   flags, direct function, (unused),
//! the methods' encodings
//! ```
//!
//! A native position is the place of the method's native in the
//! program's own table of that kind (plain, by-reference, in place),
//! which lists the natives its methods use (`natives::PLAIN` and so on).

use std::sync::OnceLock;

use quarz_ir::{Droppable, FuncId, MethodId, RtMethod, RtParamKind, RtSynth};

const RECORD: usize = 8;
const HEADER: usize = 7;
const NONE: u32 = u32::MAX;

/// Its parameters are positional and it takes no block.
pub const POSITIONAL: u32 = 1;
/// A descendant of its owner overrides it: it has a dispatch column.
pub const VSLOT: u32 = 2;

/// The natives `Interp::with_state` finds by key for the owned calls.
pub const OWNED_KEYS: [&str; 6] = [
    "Array#push",
    "Array#set",
    "Hash#put",
    "Hash#delete",
    "Set#add",
    "Set#delete",
];

/// The section for `methods`, whose natives are at `positions` in the
/// program's tables (by key).
pub fn encode(methods: &[RtMethod], positions: &[quarz_ir::HashMap<&str, u32>; 3]) -> Vec<u8> {
    let n = methods.len();
    let mut words: Vec<u32> = Vec::with_capacity(HEADER + n * RECORD);
    words.push(n as u32);
    for key in OWNED_KEYS {
        let id = methods
            .iter()
            .position(|m| m.ext.is_none() && m.native_key.as_deref() == Some(key));
        words.push(id.map_or(NONE, |i| i as u32));
    }
    let mut data: Vec<u8> = Vec::new();
    for m in methods {
        let (offset, len) = if m.is_dropped() {
            (0, 0)
        } else {
            let bytes = quarz_ir::encode_method(m);
            let at = data.len();
            data.extend_from_slice(&bytes);
            (at as u32, bytes.len() as u32)
        };
        // (A cog's native is bound to its module's entry, never to a
        // standard native of its key: `native_ext::bind`.)
        let natives = match m.native_key.as_deref().filter(|_| m.ext.is_none()) {
            Some(key) => positions
                .each_ref()
                .map(|p| p.get(key).copied().unwrap_or(NONE)),
            None => [NONE; 3],
        };
        let positional = !m.has_block && m.params.iter().all(|p| p.kind == RtParamKind::Positional);
        let mut flags = 0;
        if positional {
            flags |= POSITIONAL;
        }
        if m.dispatch() == quarz_ir::Dispatch::Virtual {
            flags |= VSLOT;
        }
        let plain = positional
            && m.native_key.is_none()
            && matches!(m.synth, RtSynth::None)
            && !m.is_abstract;
        let direct = if plain { m.func.unwrap_or(NONE) } else { NONE };
        words.extend([
            offset, len, natives[0], natives[1], natives[2], flags, direct, 0,
        ]);
    }
    let mut out: Vec<u8> = words.iter().flat_map(|w| w.to_le_bytes()).collect();
    out.extend_from_slice(&data);
    out
}

/// The methods of a compiled program, decoded when first asked for.
pub struct Lazy {
    bytes: &'static [u8],
    count: usize,
    cells: Box<[OnceLock<RtMethod>]>,
    /// The program's tables of natives (addresses of functions of the
    /// kind of each table).
    natives: [&'static [usize]; 3],
}

impl Lazy {
    /// The section `bytes` and the tables of natives (static: the
    /// program's own).
    pub fn new(bytes: &'static [u8], natives: [&'static [usize]; 3]) -> Result<Lazy, String> {
        let mut lazy = Lazy {
            bytes,
            natives,
            count: 0,
            cells: Box::new([]),
        };
        if bytes.len() < HEADER * 4 {
            return Err("truncated method table".into());
        }
        let count = lazy.word(0) as usize;
        if bytes.len() < (HEADER + count * RECORD) * 4 {
            return Err("truncated method table".into());
        }
        lazy.count = count;
        lazy.cells = (0..count).map(|_| OnceLock::new()).collect();
        Ok(lazy)
    }

    fn word(&self, i: usize) -> u32 {
        let b = &self.bytes[i * 4..i * 4 + 4];
        u32::from_le_bytes([b[0], b[1], b[2], b[3]])
    }

    fn record(&self, id: MethodId, k: usize) -> u32 {
        self.word(HEADER + id as usize * RECORD + k)
    }

    pub fn count(&self) -> usize {
        self.count
    }

    /// The methods of the `OWNED_KEYS` natives.
    pub fn owned(&self) -> [Option<MethodId>; 6] {
        std::array::from_fn(|k| Some(self.word(1 + k)).filter(|w| *w != NONE))
    }

    /// The address of method `id`'s native in table `which`
    /// (`natives::PLAIN` and so on).
    pub fn native(&self, id: MethodId, which: usize) -> Option<usize> {
        let at = Some(self.record(id, 2 + which)).filter(|w| *w != NONE)?;
        self.natives[which].get(at as usize).copied()
    }

    pub fn flags(&self, id: MethodId) -> u32 {
        self.record(id, 5)
    }

    pub fn direct_func(&self, id: MethodId) -> Option<FuncId> {
        Some(self.record(id, 6)).filter(|w| *w != NONE)
    }

    /// Method `id`, decoded the first time.
    pub fn get(&self, id: MethodId) -> &RtMethod {
        self.cells[id as usize].get_or_init(|| {
            let (offset, len) = (self.record(id, 0) as usize, self.record(id, 1) as usize);
            if len == 0 {
                return RtMethod::dropped();
            }
            let start = (HEADER + self.count * RECORD) * 4 + offset;
            quarz_ir::decode_method(&self.bytes[start..start + len])
                .unwrap_or_else(|e| panic!("corrupt method {id}: {e}"))
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use quarz_ir::Droppable;

    fn native(key: &str, ext: Option<u32>) -> RtMethod {
        let mut m = RtMethod::dropped();
        m.name = "size".into();
        m.native_key = Some(key.into());
        m.ext = ext;
        m
    }

    /// A cog's native whose key a standard native also has (#677): the
    /// standard one gets its position in the natives' table, the cog's
    /// none (it is bound to its module's entry, `native_ext::bind`). (The
    /// checker refuses such a declaration; this is the tables' own guard.)
    #[test]
    fn a_cogs_native_never_takes_a_standard_natives_position() {
        let methods = vec![native("Range#size", None), native("Range#size", Some(0))];
        let mut positions: [quarz_ir::HashMap<&str, u32>; 3] = Default::default();
        positions[0].insert("Range#size", 0);
        let bytes: &'static [u8] = Box::leak(encode(&methods, &positions).into_boxed_slice());
        let table: &'static [usize] = Box::leak(vec![0x1234usize].into_boxed_slice());
        let lazy = Lazy::new(bytes, [table, &[], &[]]).unwrap();
        assert_eq!(lazy.native(0, crate::natives::PLAIN), Some(0x1234));
        assert_eq!(lazy.native(1, crate::natives::PLAIN), None);
    }
}
