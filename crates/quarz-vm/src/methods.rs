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
//! count, fingerprint (2 words), owned ids (6 words),
//! count records of RECORD words: offset, length, native positions (3),
//!   flags, direct function, (unused),
//! the methods' encodings
//! ```

use std::sync::OnceLock;

use quarz_ir::{Droppable, FuncId, MethodId, RtMethod, RtParamKind, RtSynth};

const RECORD: usize = 8;
const HEADER: usize = 9;
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
/// registries whose keys hash to `fingerprint`.
pub fn encode(
    methods: &[RtMethod],
    positions: &[quarz_ir::HashMap<&'static str, u32>; 3],
    fingerprint: u64,
) -> Vec<u8> {
    let n = methods.len();
    let mut words: Vec<u32> = Vec::with_capacity(HEADER + n * RECORD);
    words.push(n as u32);
    words.push(fingerprint as u32);
    words.push((fingerprint >> 32) as u32);
    for key in OWNED_KEYS {
        let id = methods
            .iter()
            .position(|m| m.native_key.as_deref() == Some(key));
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
        let natives = match m.native_key.as_deref() {
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
        if m.overridden && !m.singleton && !m.is_extension {
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
}

impl Lazy {
    /// The section `bytes` (static: the program's own).
    pub fn new(bytes: &'static [u8]) -> Result<Lazy, String> {
        let mut lazy = Lazy {
            bytes,
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

    pub fn fingerprint(&self) -> u64 {
        u64::from(self.word(1)) | (u64::from(self.word(2)) << 32)
    }

    /// The methods of the `OWNED_KEYS` natives.
    pub fn owned(&self) -> [Option<MethodId>; 6] {
        std::array::from_fn(|k| Some(self.word(3 + k)).filter(|w| *w != NONE))
    }

    /// Where method `id`'s native is in registry `which` (`natives::PLAIN`
    /// and so on).
    pub fn native_at(&self, id: MethodId, which: usize) -> Option<u32> {
        Some(self.record(id, 2 + which)).filter(|w| *w != NONE)
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
