//! The order of `static` statements (`Checker::superclass_first`,
//! docs/14 §2) over generated hierarchies, against the function it
//! replaced (#719): a walk of the declared superclasses and includes,
//! which `World::superclass_chain` replaced once only a class body holds
//! statements (#718). The two must give the same order on every input.

use super::*;
use crate::declare::Declarer;
use crate::load::unit_base;

/// The ordering as it was before #719, kept as the reference: the same
/// loop over the ancestors its own walk found.
fn reference_order(world: &World, stmts: Vec<(usize, StaticStmt)>) -> Vec<(usize, StaticStmt)> {
    let mut ancestors: HashMap<ClassId, HashSet<ClassId>> = HashMap::default();
    for (_, stmt) in &stmts {
        ancestors
            .entry(stmt.class)
            .or_insert_with(|| reference_ancestors(world, stmt.class));
    }
    let mut todo: Vec<Option<(usize, StaticStmt)>> = stmts.into_iter().map(Some).collect();
    let mut out = Vec::with_capacity(todo.len());
    while out.len() < todo.len() {
        let waits = |c: ClassId, todo: &[Option<(usize, StaticStmt)>]| {
            let own = &ancestors[&c];
            todo.iter()
                .flatten()
                .any(|(_, s)| s.class != c && own.contains(&s.class))
        };
        let pick = (0..todo.len())
            .find(|&k| matches!(&todo[k], Some((_, s)) if !waits(s.class, &todo)))
            .or_else(|| (0..todo.len()).find(|&k| todo[k].is_some()))
            .expect("a statement left");
        out.push(todo[pick].take().expect("not taken"));
    }
    out
}

/// The walk `statement_ancestors` did before #719: the superclasses and
/// the declared includes, transitively, the class itself left out.
fn reference_ancestors(world: &World, class: ClassId) -> HashSet<ClassId> {
    let mut seen: HashSet<ClassId> = HashSet::default();
    let mut stack = vec![class];
    while let Some(c) = stack.pop() {
        let info = world.class(c);
        let edges = info.superclass.iter().chain(&info.includes);
        for t in edges {
            if let Type::Class(id, _) = t {
                if *id != class && seen.insert(*id) {
                    stack.push(*id);
                }
            }
        }
    }
    seen
}

/// A small deterministic generator (xorshift64*), so that a failing case
/// is reproduced by its seed.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_f491_4f6c_dd1d)
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
    fn chance(&mut self, percent: u64) -> bool {
        self.next() % 100 < percent
    }
    fn shuffle<T>(&mut self, v: &mut [T]) {
        for i in (1..v.len()).rev() {
            v.swap(i, self.below(i + 1));
        }
    }
}

/// A program of classes `C{i}` (some generic) under `Object` or an
/// earlier class, modules `M{j}` including earlier modules, classes
/// including modules, extensions of non-generic classes including a
/// module `X{i}`, and up to three statements per class, the declarations
/// in a random text order.
fn hierarchy(rng: &mut Rng) -> String {
    let classes = 2 + rng.below(14);
    let modules = rng.below(5);
    let generic: Vec<bool> = (0..classes).map(|_| rng.chance(25)).collect();
    let mut items: Vec<String> = Vec::new();
    for j in 0..modules {
        let mut body = String::new();
        for k in 0..j {
            if rng.chance(30) {
                body.push_str(&format!("  include M{k}\n"));
            }
        }
        items.push(format!("module M{j}\n{body}end\n"));
    }
    for i in 0..classes {
        let params = if generic[i] { "[T]" } else { "" };
        let mut head = format!("class C{i}{params}");
        if i > 0 && rng.chance(75) {
            let p = rng.below(i);
            let args = match (generic[p], generic[i] && rng.chance(50)) {
                (false, _) => "",
                (true, true) => "[T]",
                (true, false) => "[Int]",
            };
            head.push_str(&format!(" < C{p}{args}"));
        }
        let mut body = String::new();
        for j in 0..modules {
            if rng.chance(25) {
                body.push_str(&format!("  include M{j}\n"));
            }
        }
        for _ in 0..rng.below(4) {
            body.push_str("  mark(1)\n");
        }
        items.push(format!("{head}\n{body}end\n"));
        // A module of its own: an extension cannot include one the class
        // already has.
        if !generic[i] && rng.chance(20) {
            items.push(format!(
                "module X{i}\nend\nextension C{i}\n  include X{i}\nend\n"
            ));
        }
    }
    rng.shuffle(&mut items);
    items.concat()
}

/// The statements of `src` in both orders, by their `World::static_stmts`
/// indices, and its declaration errors.
fn both_orders(prelude: &World, src: &str) -> (Vec<usize>, Vec<usize>, Vec<String>) {
    let base = unit_base(0);
    let parsed = quarz_syntax::parse_with_bases(src, base, base);
    assert!(
        !parsed.diagnostics.iter().any(|d| d.is_error()),
        "parse errors for {src:?}: {:?}",
        parsed.diagnostics
    );
    let mut declarer = Declarer::with_world(prelude.clone());
    declarer.collect_unit(&parsed.program, 1);
    declarer.resolve_headers();
    let errors: Vec<String> = declarer
        .diagnostics
        .iter()
        .filter(|(_, d)| d.is_error())
        .map(|(_, d)| d.message.clone())
        .collect();
    let main = declarer.units[0].main;
    let checker = Checker::new(declarer.world, vec![None, Some(main)]);
    let stmts: Vec<(usize, StaticStmt)> = checker
        .world
        .static_stmts
        .iter()
        .cloned()
        .enumerate()
        .collect();
    let new = checker.superclass_first(stmts.clone());
    let old = reference_order(&checker.world, stmts);
    let ids = |v: Vec<(usize, StaticStmt)>| v.into_iter().map(|(i, _)| i).collect();
    (ids(new), ids(old), errors)
}

/// The prelude declared and checked once, as the cache gives it
/// (`Session::new`): each case declares its program over a copy.
fn prelude_world() -> World {
    let prelude = quarz_syntax::parse(crate::PRELUDE_SOURCE);
    let (state, diagnostics) = crate::prelude_state(&prelude.program);
    assert!(
        !diagnostics.iter().any(|(_, d)| d.is_error()),
        "{diagnostics:?}"
    );
    state.world
}

#[test]
fn superclass_first_keeps_the_order_over_generated_hierarchies() {
    let prelude = prelude_world();
    let mut reordered = 0;
    for seed in 1..=300u64 {
        let mut rng = Rng(seed.wrapping_mul(0x9e37_79b9_7f4a_7c15) | 1);
        let src = hierarchy(&mut rng);
        let (new, old, errors) = both_orders(&prelude, &src);
        assert!(errors.is_empty(), "seed {seed}: {errors:?}\n{src}");
        assert_eq!(new, old, "seed {seed}:\n{src}");
        if new.windows(2).any(|w| w[0] > w[1]) {
            reordered += 1;
        }
    }
    // The generated hierarchies do reorder statements: the property is
    // not met by giving the order unchanged.
    assert!(reordered > 100, "only {reordered} cases reordered");
}

/// Hand-written cases: a subclass written first, a class including a
/// module and one an extension makes include it, and a superclass cycle
/// (an error, whose statements the fallback still orders).
#[test]
fn superclass_first_keeps_the_order_in_written_cases() {
    let prelude = prelude_world();
    let cases = [
        ("class B < A\n  mark(1)\nend\nclass A\n  mark(1)\nend\n", vec![1, 0], true),
        (
            "class C\n  include M\n  mark(1)\nend\nmodule M\nend\nextension C\n  include N\nend\nmodule N\nend\nclass D < C\n  mark(1)\nend\n",
            vec![0, 1],
            true,
        ),
        (
            "class G[T]\n  mark(1)\nend\nclass H < G[Int]\n  mark(1)\nend\nclass K[U] < G[U]\n  mark(1)\nend\n",
            vec![0, 1, 2],
            true,
        ),
        ("class A < B\n  mark(1)\nend\nclass B < A\n  mark(1)\nend\n", vec![], false),
    ];
    for (src, want, clean) in cases {
        let (new, old, errors) = both_orders(&prelude, src);
        assert_eq!(errors.is_empty(), clean, "{src}: {errors:?}");
        assert_eq!(new, old, "{src}");
        if clean {
            assert_eq!(new, want, "{src}");
        }
    }
}
