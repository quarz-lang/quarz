//! The safety net over the witness rows the runtime reads (report-only,
//! `tmp/plan-safety-net.md`): every row (class `C`, requirement `req`,
//! what runs `by`) of `RtWorld::override_rows`, `witness_rows` and
//! `class_override_rows` is checked as an override for `C` itself, by the
//! declarer's one pair check (`Declarer::check_override_pair`), with `C`'s
//! own instantiation of `req`'s module and of `by`'s owner (or, for an
//! extension's method, of the extension's target, `World::extension_subst`).
//! No de-duplication across classes, no skipping by bound.
//!
//! The bound label of a refusal (`Bound`) says only what a conditional
//! extension's bound says for `C`'s own arguments for its target. It is
//! not reachability: a value of `C` may reach the row although the bound
//! fails for `C`'s arguments (by variance, `C < Sink[Object]` being a
//! `Sink[Dog]` under `class Sink[in T]`, or through a scoped extension
//! that makes the bound hold where it is active, #604's round 2), and
//! whether it holds for some instantiation of a generic `C` is #556's.

use crate::declare::Declarer;
use crate::types::{ClassId, MethodId, Type};
use crate::world::{View, World};

/// What a conditional extension's bound says for the class's own
/// arguments for its target (not reachability, see the module's comment).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Bound {
    /// `by` is not a conditional extension's method.
    None,
    Holds,
    Fails,
    /// The class's arguments for the target are its own parameters (#556).
    Unknown,
}

/// The net's answer for one row.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Verdict {
    /// `by` may stand in for `req` on `C` (or `by` is `req` itself).
    Passes,
    /// Nothing implements `req` for `C`: the row names the abstract
    /// requirement itself (#600, #555).
    NoImplementation,
    /// `check_override_pair` refuses the pair in `C`'s frame.
    Refused { reason: String, bound: Bound },
    /// `req`'s owner is not among `C`'s ancestors in the override view:
    /// no frame to compare in (an internal inconsistency, listed apart).
    NoFrame,
}

/// One checked row.
#[derive(Clone, Debug)]
pub struct Checked {
    /// The table: `override`, `witness` or `class`.
    pub table: &'static str,
    pub class: ClassId,
    pub req: MethodId,
    pub by: MethodId,
    pub verdict: Verdict,
}

/// Check every row: the instance side's (`override_rows`, `witness_rows`
/// where a witness is given) and the class side's (`class_override_rows`).
pub fn check(
    world: &World,
    override_rows: &[(ClassId, MethodId, MethodId)],
    witness_rows: &[(ClassId, MethodId, Option<MethodId>)],
    class_rows: &[(ClassId, MethodId, MethodId)],
) -> Vec<Checked> {
    let mut d = Declarer::with_world(world.clone());
    let rows = override_rows
        .iter()
        .map(|(c, r, b)| ("override", *c, *r, *b))
        .chain(
            witness_rows
                .iter()
                .filter_map(|(c, r, w)| w.map(|w| ("witness", *c, *r, w))),
        )
        .chain(class_rows.iter().map(|(c, r, b)| ("class", *c, *r, *b)));
    rows.map(|(table, class, req, by)| Checked {
        table,
        class,
        req,
        by,
        verdict: check_row(&mut d, class, req, by),
    })
    .collect()
}

fn check_row(d: &mut Declarer, c: ClassId, req: MethodId, by: MethodId) -> Verdict {
    if by == req {
        return if d.world.method(req).is_abstract {
            Verdict::NoImplementation
        } else {
            Verdict::Passes
        };
    }
    let own_args = d.world.own_args(c);
    let own = Type::Class(c, own_args.clone());
    let typed = d.world.resolution(c, &own_args, View::Override);
    let args_of = |k: ClassId| {
        if k == c {
            Some(own_args.clone())
        } else {
            typed.iter().find(|(x, _)| *x == k).map(|(_, a)| a.clone())
        }
    };
    let req_owner = d.world.method(req).owner;
    let Some(aargs) = args_of(req_owner) else {
        return Verdict::NoFrame;
    };
    let (mine, bound) = match d.world.method(by).extension {
        Some(e) => {
            let ext = d.world.extensions[e as usize].clone();
            let targs = args_of(ext.target).unwrap_or_default();
            let bound = if ext.type_params.iter().all(|tp| tp.bounds.is_empty()) {
                Bound::None
            } else if targs.iter().any(|t| t.has_params()) {
                Bound::Unknown
            } else if d.world.extension_bounds_hold(&ext, &targs) {
                Bound::Holds
            } else {
                Bound::Fails
            };
            (d.world.extension_subst(&ext, &targs), bound)
        }
        None => {
            let owner = d.world.method(by).owner;
            let mine = match args_of(owner) {
                Some(a) => d.world.class_subst(owner, &a),
                None => Default::default(),
            };
            (mine, Bound::None)
        }
    };
    let (subst, mine_subst) = d.implementation_substs(by, req, req_owner, &aargs, own, mine);
    let before = d.diagnostics.len();
    d.check_override_pair(by, req, &subst, &mine_subst, None);
    let reasons: Vec<String> = d.diagnostics[before..]
        .iter()
        .map(|(_, diag)| diag.message.clone())
        .collect();
    d.diagnostics.truncate(before);
    if reasons.is_empty() {
        Verdict::Passes
    } else {
        Verdict::Refused {
            reason: reasons.join("; "),
            bound,
        }
    }
}

/// The report's lines: one per refused row, one per row with no
/// implementation or no frame, then a summary.
pub fn report(world: &World, checked: &[Checked]) -> Vec<String> {
    let name = |m: MethodId| {
        let mi = world.method(m);
        let sep = if mi.singleton { "." } else { "#" };
        format!("{}{sep}{}", world.class(mi.owner).name, mi.name)
    };
    let mut out = Vec::new();
    let (mut refused, mut fails, mut unknown, mut holds, mut noimpl, mut noframe) =
        (0, 0, 0, 0, 0, 0);
    for r in checked {
        let cname = &world.class(r.class).name;
        match &r.verdict {
            Verdict::Passes => {}
            Verdict::NoImplementation => {
                noimpl += 1;
                out.push(format!(
                    "witness-net: no-impl  [{}]  {cname}  {}",
                    r.table,
                    name(r.req)
                ));
            }
            Verdict::NoFrame => {
                noframe += 1;
                out.push(format!(
                    "witness-net: no-frame  [{}]  {cname}  {}  by {}",
                    r.table,
                    name(r.req),
                    name(r.by)
                ));
            }
            Verdict::Refused { reason, bound } => {
                refused += 1;
                let b = match bound {
                    Bound::None => "",
                    Bound::Holds => {
                        holds += 1;
                        "  [bound for its own arguments: holds]"
                    }
                    Bound::Fails => {
                        fails += 1;
                        "  [bound for its own arguments: fails]"
                    }
                    Bound::Unknown => {
                        unknown += 1;
                        "  [bound for its own arguments: unknown]"
                    }
                };
                out.push(format!(
                    "witness-net: refused  [{}]  {cname}  {}  by {}{b}: {reason}",
                    r.table,
                    name(r.req),
                    name(r.by)
                ));
            }
        }
    }
    out.push(format!(
        "witness-net: summary  rows {}, refused {refused} (bound holds {holds}, fails {fails}, unknown {unknown}), no-impl {noimpl}, no-frame {noframe}",
        checked.len()
    ));
    out
}
