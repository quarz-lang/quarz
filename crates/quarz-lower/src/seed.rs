//! What a standard-library set made at first use keeps of its
//! compile-time lowering (#1097): the functions its generated methods'
//! bodies are copied from (`lift`), for the lowerer a program that loads
//! the set starts with.
//!
//! The program's lowering lowers every other method again, as for a set
//! precompiled when `quarz` was built: of the set's rounds it needs only
//! the block functions a generated method was lifted from, and the blocks
//! they make. The other functions of those rounds (the methods the
//! statements' runs reached) are kept as empty bodies, so that every id
//! stays where the world's `Generated::func` names it.

use quarz_ir::{FuncKind, Function, Inst};
use quarz_types::World;

use crate::Lowerer;

#[derive(Clone, serde::Serialize, serde::Deserialize)]
pub struct LowererSeed {
    /// The set's rounds' functions by id, those no generated method needs
    /// emptied.
    pub functions: Vec<Function>,
    /// The quoted call sites' next number: the program's continue after
    /// the set's, so that no two sites of a process share one.
    pub next_quoted_site: i64,
}

impl Lowerer {
    /// The seed for a program that loads the set this lowerer made
    /// (`world` is the set's checked world).
    pub fn seed(&self, world: &World) -> LowererSeed {
        let mut keep = vec![false; self.done.len()];
        let mut work: Vec<u32> = world
            .methods
            .iter()
            .filter_map(|m| m.generated.as_ref().map(|g| g.func))
            .collect();
        while let Some(f) = work.pop() {
            let Some(k) = keep.get_mut(f as usize) else {
                continue;
            };
            if std::mem::replace(k, true) {
                continue;
            }
            for b in &self.done[f as usize].blocks {
                for inst in &b.insts {
                    if let Inst::MakeBlock { func, .. } = inst {
                        work.push(*func);
                    }
                }
            }
        }
        let functions = self
            .done
            .iter()
            .zip(&keep)
            .map(|(f, keep)| {
                if *keep {
                    f.clone()
                } else {
                    quarz_ir::shake::empty_function(String::new(), FuncKind::Init, f.file, 0)
                }
            })
            .collect();
        LowererSeed {
            functions,
            next_quoted_site: self.next_quoted_site,
        }
    }

    /// A lowerer continuing a set's seed: its functions are the first
    /// ones, by their ids.
    pub fn from_seed(seed: LowererSeed) -> Lowerer {
        let mut lw = Lowerer::new();
        lw.next_func = seed.functions.len() as u32;
        lw.round_base = lw.next_func;
        lw.done = seed.functions;
        lw.next_quoted_site = seed.next_quoted_site;
        lw
    }
}

impl LowererSeed {
    pub fn encode(&self) -> Vec<u8> {
        bincode::serde::encode_to_vec(self, bincode::config::standard()).expect("encode a seed")
    }

    /// `None`: not a seed's bytes.
    pub fn decode(bytes: &[u8]) -> Option<LowererSeed> {
        bincode::serde::decode_from_slice(bytes, bincode::config::standard())
            .ok()
            .map(|(s, _)| s)
    }
}
