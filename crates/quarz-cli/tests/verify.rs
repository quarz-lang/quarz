//! `QUARZ_VERIFY`: the interpreter checks the facts compiled code trusts.
//! A program the checker accepts never violates one, so each test lowers
//! one and changes its QIR to lie, runs it in a child process (a violation
//! stops the process) and expects the report.

mod common;

use std::process::Command;

use quarz_ir::{Inst, Module};

/// Run `module` in a child of this test binary, which re-enters the test
/// named `name` with `QUARZ_VERIFY_CHILD` set and runs it there: the
/// child's exit code and standard error.
fn in_child(name: &str, module: impl FnOnce() -> Module) -> (Option<i32>, String) {
    in_child_with(name, "1", module)
}

/// `in_child`, with `QUARZ_VERIFY` set to `verify`.
fn in_child_with(
    name: &str,
    verify: &str,
    module: impl FnOnce() -> Module,
) -> (Option<i32>, String) {
    if std::env::var("QUARZ_VERIFY_CHILD").as_deref() == Ok(name) {
        let code = quarz_cli::run_module(module(), Vec::new());
        std::process::exit(code);
    }
    let out = Command::new(std::env::current_exe().unwrap())
        .args([name, "--exact", "--nocapture", "--test-threads=1"])
        .env("QUARZ_VERIFY_CHILD", name)
        .env("QUARZ_VERIFY", verify)
        .output()
        .expect("run the test binary");
    (
        out.status.code(),
        String::from_utf8_lossy(&out.stderr).into_owned(),
    )
}

fn class_id(module: &Module, name: &str) -> u32 {
    module
        .world
        .classes
        .iter()
        .position(|c| c.name == name)
        .unwrap_or_else(|| panic!("no class {name}")) as u32
}

/// Every instruction of every function, to change.
fn insts(module: &mut Module) -> impl Iterator<Item = &mut Inst> {
    module
        .functions
        .iter_mut()
        .flat_map(|f| f.blocks.iter_mut())
        .flat_map(|b| b.insts.iter_mut())
}

#[test]
fn an_array_word_read_out_of_range_stops_the_program() {
    let (code, err) = in_child("an_array_word_read_out_of_range_stops_the_program", || {
        let mut module = common::lower("xs = [1, 2, 3]\ns = 0\nxs.each { |x| s += x }\np s\n");
        // The loop reads the element at the array's length instead.
        let main = module.units.last().unwrap().body as usize;
        let f = &mut module.functions[main];
        let len = f
            .blocks
            .iter()
            .flat_map(|b| &b.insts)
            .find_map(|i| match i {
                Inst::Len { dst, .. } => Some(*dst),
                _ => None,
            })
            .expect("the loop's length");
        let mut changed = false;
        for inst in f.blocks.iter_mut().flat_map(|b| b.insts.iter_mut()) {
            if let Inst::ArrayGetWord { index, .. } = inst {
                *index = len;
                changed = true;
            }
        }
        assert!(changed, "no ArrayGetWord");
        module
    });
    assert_eq!(code, Some(101), "{err}");
    assert!(
        err.contains("QIR fact violated: ArrayGetWord index 3 out of range (len 3)"),
        "{err}"
    );
}

#[test]
fn a_field_read_on_another_class_stops_the_program() {
    let (code, err) = in_child("a_field_read_on_another_class_stops_the_program", || {
        let mut module = common::lower(
            "class A\n  var @x: Int\n  def initialize(@x: Int) end\n  def x -> Int = @x\nend\n\
             class B\n  var @y: Int\n  def initialize(@y: Int) end\nend\n\
             p A.new(1).x\np B.new(2)\n",
        );
        // Reads of A's field claim it is B's.
        let (a, b) = (class_id(&module, "A"), class_id(&module, "B"));
        let mut changed = false;
        for inst in insts(&mut module) {
            if let Inst::FieldGet { class, .. } = inst {
                if *class == a {
                    *class = b;
                    changed = true;
                }
            }
        }
        assert!(changed, "no FieldGet of A");
        module
    });
    assert_eq!(code, Some(101), "{err}");
    assert!(
        err.contains("QIR fact violated: FieldGet of B on a A"),
        "{err}"
    );
}

#[test]
fn an_int_operator_on_a_float_stops_the_program() {
    let (code, err) = in_child("an_int_operator_on_a_float_stops_the_program", || {
        let mut module =
            common::lower("def f(a: Float, b: Float) -> Float = a + b\np f(1.5, 2.0)\n");
        // `Float#+` claimed to be `Int#+`.
        let int_plus = module
            .world
            .methods
            .iter()
            .position(|m| m.owner == module.world.builtin.int && m.name == "+")
            .expect("Int#+") as u32;
        let float = module.world.builtin.float;
        let methods = module.world.methods.clone();
        let mut changed = false;
        for inst in insts(&mut module) {
            if let Inst::BinOp {
                method: Some(m), ..
            } = inst
            {
                if methods[*m as usize].owner == float {
                    *m = int_plus;
                    changed = true;
                }
            }
        }
        assert!(changed, "no Float BinOp");
        module
    });
    assert_eq!(code, Some(101), "{err}");
    assert!(
        err.contains("QIR fact violated: BinOp Int#+ on a Float"),
        "{err}"
    );
}

// ----- The checker of the QIR the passes leave (quarz_lower::verify) -----

use quarz_lower::verify::{verify, Stage};

/// A program with a word loop, a handler, a call and constants: it
/// passes the checks, and each test breaks one thing in its `<main>`.
const SAMPLE: &str =
    "def f(n: Int) -> Int\n  begin\n    10 / n\n  rescue ZeroDivisionError\n    0\n  end\nend\n\
    def g(n: Int) -> Int\n  begin\n    n + 1\n  ensure\n    p n\n  end\nend\n\
    xs = [1, 2, 3]\ns = 0\nxs.each { |x| s += x }\nys = xs.map { |x| x * 2 }\n\
    p f(s), f(0), g(1), ys\n";

/// The violations of `<main>` after `stage` once `change` broke it.
fn broken(stage: Stage, change: impl FnOnce(&mut quarz_ir::Function)) -> Vec<String> {
    let mut module = common::lower(SAMPLE);
    let main = module.units.last().unwrap().body as usize;
    let n = module.functions.len();
    assert!(verify(&module.functions[main], &module.world, n, Stage::Moves).is_empty());
    change(&mut module.functions[main]);
    verify(&module.functions[main], &module.world, n, stage)
        .into_iter()
        .map(|v| v.what)
        .collect()
}

/// The functions of the lowered sample pass, after the last pass.
#[test]
fn lowered_functions_pass_the_checks() {
    let module = common::lower(SAMPLE);
    let n = module.functions.len();
    for f in &module.functions {
        let found = verify(f, &module.world, n, Stage::Moves);
        assert!(found.is_empty(), "{}: {found:?}", f.name);
    }
}

fn first_inst(f: &mut quarz_ir::Function, pick: impl Fn(&Inst) -> bool) -> &mut Inst {
    f.blocks
        .iter_mut()
        .flat_map(|b| b.insts.iter_mut())
        .find(|i| pick(i))
        .expect("the instruction")
}

#[test]
fn a_word_read_of_another_register_is_found() {
    let found = broken(Stage::Moves, |f| {
        let Inst::ArrayGetWord { arr, index, .. } =
            first_inst(f, |i| matches!(i, Inst::ArrayGetWord { .. }))
        else {
            unreachable!()
        };
        // The index register instead of the words.
        *arr = *index;
    });
    assert!(
        found.iter().any(|w| w.starts_with("ArrayGetWord reads")),
        "{found:?}"
    );
}

#[test]
fn a_register_past_the_function_is_found() {
    let found = broken(Stage::Moves, |f| {
        let n = f.nregs;
        let Inst::LoadConst { dst, .. } = first_inst(f, |i| matches!(i, Inst::LoadConst { .. }))
        else {
            unreachable!()
        };
        *dst = n;
    });
    assert!(found.iter().any(|w| w.contains("past the")), "{found:?}");
}

#[test]
fn a_clear_past_the_registers_is_found() {
    let found = broken(Stage::Moves, |f| {
        let n = f.nregs;
        f.blocks[0]
            .insts
            .push(Inst::ClearRegs { from: 0, to: n + 1 });
        f.blocks[0].lines.push(0);
    });
    assert!(
        found.iter().any(|w| w.starts_with("ClearRegs")),
        "{found:?}"
    );
}

#[test]
fn a_jump_out_of_the_function_is_found() {
    let found = broken(Stage::Moves, |f| {
        let n = f.blocks.len() as u32;
        let b = f
            .blocks
            .iter_mut()
            .find(|b| matches!(b.term, quarz_ir::Term::Jump(_)))
            .unwrap();
        b.term = quarz_ir::Term::Jump(n);
    });
    assert!(
        found.iter().any(|w| w.starts_with("jump to block")),
        "{found:?}"
    );
}

#[test]
fn lines_out_of_step_with_instructions_are_found() {
    let found = broken(Stage::Moves, |f| f.blocks[0].lines.push(0));
    assert!(found.iter().any(|w| w.contains("lines for")), "{found:?}");
}

#[test]
fn a_constant_out_of_range_is_found() {
    let found = broken(Stage::Moves, |f| {
        let n = f.consts.len() as u32;
        let Inst::LoadConst { idx, .. } = first_inst(f, |i| matches!(i, Inst::LoadConst { .. }))
        else {
            unreachable!()
        };
        *idx = n;
    });
    assert!(found.iter().any(|w| w.starts_with("constant")), "{found:?}");
}

/// Moves exist only once `mark_moves` ran: the final QIR checked as if
/// after an earlier pass has them too early.
#[test]
fn moves_before_mark_moves_are_found() {
    let found = broken(Stage::Copyprop, |_| {});
    assert!(
        found
            .iter()
            .any(|w| w == "Take before mark_moves" || w.starts_with("moved operands")),
        "{found:?}"
    );
}

#[test]
fn a_catch_outside_its_handler_is_found() {
    let mut module = common::lower(SAMPLE);
    let n = module.functions.len();
    let f = module
        .functions
        .iter_mut()
        .find(|f| f.name == "main#f")
        .expect("f");
    let (bi, ii) = f
        .blocks
        .iter()
        .enumerate()
        .find_map(|(bi, b)| {
            b.insts
                .iter()
                .position(|i| matches!(i, Inst::CatchException { .. }))
                .map(|ii| (bi, ii))
        })
        .expect("a CatchException");
    let inst = f.blocks[bi].insts.remove(ii);
    let line = f.blocks[bi].lines.remove(ii);
    f.blocks[0].insts.insert(0, inst);
    f.blocks[0].lines.insert(0, line);
    let found: Vec<String> = verify(f, &module.world, n, Stage::Moves)
        .into_iter()
        .map(|v| v.what)
        .collect();
    assert!(
        found
            .iter()
            .any(|w| w == "CatchException outside a rescue handler"),
        "{found:?}"
    );
}

/// The violations of the function named `name` once `change` broke it.
fn broken_fn(name: &str, change: impl FnOnce(&mut quarz_ir::Function)) -> Vec<String> {
    let mut module = common::lower(SAMPLE);
    let n = module.functions.len();
    let f = module
        .functions
        .iter_mut()
        .find(|f| f.name == name)
        .unwrap_or_else(|| panic!("no {name}"));
    change(f);
    verify(f, &module.world, n, Stage::Moves)
        .into_iter()
        .map(|v| v.what)
        .collect()
}

#[test]
fn a_word_append_to_another_array_is_found() {
    let found = broken(Stage::Moves, |f| {
        let words = f
            .blocks
            .iter()
            .flat_map(|b| &b.insts)
            .find_map(|i| match i {
                Inst::ArrayWords { dst, .. } => Some(*dst),
                _ => None,
            })
            .expect("the read words");
        let Inst::ArrayPushWord { arr, .. } =
            first_inst(f, |i| matches!(i, Inst::ArrayPushWord { .. }))
        else {
            unreachable!()
        };
        // The array read as words, not the one being built.
        *arr = words;
    });
    assert!(
        found.iter().any(|w| w.starts_with("ArrayPushWord on")),
        "{found:?}"
    );
}

#[test]
fn an_update_of_a_borrowed_element_is_found() {
    let found = broken(Stage::Moves, |f| {
        let b = &mut f.blocks[0];
        b.insts.push(Inst::ArrayGetReg {
            dst: 0,
            arr: 1,
            index: 2,
            borrow: true,
            objects: false,
        });
        b.insts.push(Inst::ArrayPush { arr: 0, src: 2 });
        b.lines.extend([0, 0]);
    });
    assert!(
        found.iter().any(|w| w.contains("a borrowed element")),
        "{found:?}"
    );
}

#[test]
fn a_resume_of_something_not_caught_is_found() {
    let found = broken_fn("main#g", |f| {
        let b = f
            .blocks
            .iter()
            .position(|b| matches!(b.term, quarz_ir::Term::Resume(_)))
            .expect("a Resume");
        // Continues the parameter instead of the caught flow.
        f.blocks[b].term = quarz_ir::Term::Resume(0);
    });
    assert!(
        found.iter().any(|w| w.starts_with("Resume of")),
        "{found:?}"
    );
}

#[test]
fn a_block_that_is_its_own_handler_is_found() {
    let found = broken_fn("main#f", |f| {
        let b = f.blocks.iter().position(|b| b.handler.is_some()).unwrap();
        f.blocks[b].handler.as_mut().unwrap().block = b as u32;
    });
    assert!(
        found.iter().any(|w| w == "the block is its own handler"),
        "{found:?}"
    );
}

#[test]
fn a_parameter_past_the_method_is_found() {
    let found = broken_fn("main#f", |f| {
        let Inst::Arg { index, .. } = first_inst(f, |i| matches!(i, Inst::Arg { .. })) else {
            unreachable!()
        };
        *index = 5;
    });
    assert!(found.iter().any(|w| w == "parameter 5 of 1"), "{found:?}");
}

// ----- Moves (C) -----

/// Where `pick` first matches in `f`: (block, instruction).
fn find(f: &quarz_ir::Function, pick: impl Fn(&Inst) -> bool) -> (usize, usize) {
    f.blocks
        .iter()
        .enumerate()
        .find_map(|(bi, b)| b.insts.iter().position(&pick).map(|ii| (bi, ii)))
        .expect("the instruction")
}

#[test]
fn a_read_after_a_take_is_found() {
    let found = broken(Stage::Moves, |f| {
        let (bi, ii) = find(f, |i| matches!(i, Inst::Take { .. }));
        let Inst::Take { src, .. } = f.blocks[bi].insts[ii] else {
            unreachable!()
        };
        // Its source read again just after.
        f.blocks[bi]
            .insts
            .insert(ii + 1, Inst::IsNil { dst: src, src });
        f.blocks[bi].lines.insert(ii + 1, 0);
    });
    assert!(
        found.iter().any(|w| w.contains("moved out or released")),
        "{found:?}"
    );
}

#[test]
fn a_read_after_a_release_is_found() {
    // (A call after the last read keeps the end of `c`'s scope.)
    let mut module =
        common::lower("class C\nend\ndef h -> Void\n  c = C.new\n  p c\n  p 1\nend\nh\n");
    let n = module.functions.len();
    let f = module
        .functions
        .iter_mut()
        .find(|f| f.name == "main#h")
        .unwrap();
    let (bi, ii) = find(f, |i| matches!(i, Inst::Release { .. }));
    let Inst::Release { src } = f.blocks[bi].insts[ii] else {
        unreachable!()
    };
    f.blocks[bi]
        .insts
        .insert(ii + 1, Inst::IsNil { dst: src, src });
    f.blocks[bi].lines.insert(ii + 1, 0);
    let found: Vec<String> = verify(f, &module.world, n, Stage::Moves)
        .into_iter()
        .map(|v| v.what)
        .collect();
    assert!(
        found.iter().any(|w| w.contains("moved out or released")),
        "{found:?}"
    );
}

#[test]
fn an_operand_moved_and_read_again_is_found() {
    let found = broken(Stage::Moves, |f| {
        let (bi, ii) = find(
            f,
            |i| matches!(i, Inst::Call { args, .. } if !args.is_empty()),
        );
        let Inst::Call { args, moved, .. } = &mut f.blocks[bi].insts[ii] else {
            unreachable!()
        };
        // The first argument moved, and read once more after the call.
        *moved |= 1;
        let a = args[0];
        f.blocks[bi]
            .insts
            .insert(ii + 1, Inst::IsNil { dst: a, src: a });
        f.blocks[bi].lines.insert(ii + 1, 0);
    });
    assert!(
        found.iter().any(|w| w.contains("moved out or released")),
        "{found:?}"
    );
}

#[test]
fn a_take_into_itself_is_found() {
    let found = broken(Stage::Moves, |f| {
        let Inst::Take { dst, src } = first_inst(f, |i| matches!(i, Inst::Take { .. })) else {
            unreachable!()
        };
        *dst = *src;
    });
    assert!(found.iter().any(|w| w.contains("into itself")), "{found:?}");
}

// ----- Borrows (D) and register sharing (E) -----

#[test]
fn a_write_of_a_borrowed_element_register_is_found() {
    let mut module = common::lower(
        "class P\n  @v: Int\n  def initialize(@v: Int) end\n  def v -> Int = @v\nend\n\
         def s(ps: Array[P]) -> Int\n  t = 0\n  ps.each { |q| t += q.v }\n  t\nend\n\
         p s([P.new(1), P.new(2)])\n",
    );
    let n = module.functions.len();
    let f = module
        .functions
        .iter_mut()
        .find(|f| f.name == "main#s")
        .unwrap();
    let (bi, ii) = find(f, |i| matches!(i, Inst::ArrayGetReg { borrow: true, .. }));
    let Inst::ArrayGetReg { dst, .. } = f.blocks[bi].insts[ii] else {
        unreachable!()
    };
    // (Checked up to register sharing, see `verify::Checker::borrows`:
    // the final QIR's moves are too early there, and not the point.)
    let world = &module.world;
    let borrow_found = |f: &quarz_ir::Function| -> Vec<String> {
        verify(f, world, n, Stage::Regshare)
            .into_iter()
            .map(|v| v.what)
            .filter(|w| w.contains("borrow"))
            .collect()
    };
    assert!(borrow_found(f).is_empty());
    f.blocks[bi]
        .insts
        .insert(ii + 1, Inst::LoadConst { dst, idx: 0 });
    f.blocks[bi].lines.insert(ii + 1, 0);
    let found = borrow_found(f);
    assert!(
        found
            .iter()
            .any(|w| w.contains("a borrowed element's register")),
        "{found:?}"
    );
}

/// The lowered sample, its `<main>`'s index and the identity map of its
/// registers.
fn regshare_sample() -> (quarz_ir::Module, usize, Vec<u32>) {
    let module = common::lower(SAMPLE);
    let main = module.units.last().unwrap().body as usize;
    let map: Vec<u32> = (0..module.functions[main].nregs).collect();
    (module, main, map)
}

fn regshare_found(
    old: &quarz_ir::Function,
    new: &quarz_ir::Function,
    map: &[u32],
    world: &quarz_ir::RtWorld,
) -> Vec<String> {
    quarz_lower::verify::regshare(old, new, map, world)
        .into_iter()
        .map(|v| v.what)
        .collect()
}

#[test]
fn sharing_a_counted_and_a_number_register_is_found() {
    let (module, main, mut map) = regshare_sample();
    let f = &module.functions[main];
    let heap = quarz_ir::live::heap_possible(f, &module.world.methods);
    let mentioned = |r: u32| {
        f.blocks
            .iter()
            .flat_map(|b| &b.insts)
            .any(|i| i.defs().contains(&r) || i.uses().contains(&r))
    };
    let counted = (0..f.nregs)
        .find(|r| heap[*r as usize] && mentioned(*r))
        .unwrap();
    let number = (0..f.nregs)
        .find(|r| !heap[*r as usize] && mentioned(*r))
        .unwrap();
    map[number as usize] = counted;
    let new = quarz_lower::verify::renumber(f, &map);
    let found = regshare_found(f, &new, &map, &module.world);
    assert!(
        found
            .iter()
            .any(|w| w.contains("a counted and a non-counted")),
        "{found:?}"
    );
}

#[test]
fn a_result_sharing_an_operand_is_found() {
    let (module, main, mut map) = regshare_sample();
    let f = &module.functions[main];
    let (dst, lhs) = f
        .blocks
        .iter()
        .flat_map(|b| &b.insts)
        .find_map(|i| match i {
            Inst::BinOp { dst, lhs, .. } if dst != lhs => Some((*dst, *lhs)),
            _ => None,
        })
        .unwrap();
    map[dst as usize] = lhs;
    let new = quarz_lower::verify::renumber(f, &map);
    let found = regshare_found(f, &new, &map, &module.world);
    assert!(
        found.iter().any(|w| w.contains("shares with its operand")),
        "{found:?}"
    );
}

#[test]
fn a_clear_left_out_is_found() {
    let (module, main, map) = regshare_sample();
    let f = &module.functions[main];
    let heap = quarz_ir::live::heap_possible(f, &module.world.methods);
    let mut new = f.clone();
    let (bi, ii) = find(
        &new,
        |i| matches!(i, Inst::ClearRegs { from, to } if (*from..*to).any(|r| heap[r as usize])),
    );
    new.blocks[bi].insts.remove(ii);
    new.blocks[bi].lines.remove(ii);
    let found = regshare_found(f, &new, &map, &module.world);
    assert!(
        found.iter().any(|w| w.contains("no longer clears")),
        "{found:?}"
    );
}

#[test]
fn two_live_registers_sharing_are_found() {
    let (module, main, mut map) = regshare_sample();
    let f = &module.functions[main];
    let heap = quarz_ir::live::heap_possible(f, &module.world.methods);
    let live = quarz_ir::live::liveness(f);
    // Two registers of one kind live at once.
    let (a, b) = live
        .iter()
        .flatten()
        .find_map(|at| {
            let regs: Vec<u32> = (0..f.nregs).filter(|r| at[*r as usize]).collect();
            regs.iter().find_map(|a| {
                regs.iter()
                    .find(|b| a < *b && heap[*a as usize] == heap[**b as usize])
                    .map(|b| (*a, *b))
            })
        })
        .unwrap();
    map[b as usize] = a;
    let new = quarz_lower::verify::renumber(f, &map);
    let found = regshare_found(f, &new, &map, &module.world);
    assert!(
        found
            .iter()
            .any(|w| w.contains(&format!("r{a} and r{b}, both live"))),
        "{found:?}"
    );
}

#[test]
fn a_release_redirected_to_another_variable_is_found() {
    let (module, main, _) = regshare_sample();
    let f = &module.functions[main];
    let (bi, ii) = find(f, |i| matches!(i, Inst::Release { .. }));
    let Inst::Release { src } = f.blocks[bi].insts[ii] else {
        unreachable!()
    };
    let other = (0..f.nregs).find(|r| *r != src).unwrap();
    let mut new = f.clone();
    new.blocks[bi].insts[ii] = Inst::Release { src: other };
    let found: Vec<String> = quarz_lower::verify::copyprop(f, &new)
        .into_iter()
        .map(|v| v.what)
        .collect();
    assert!(
        found
            .iter()
            .any(|w| w.contains(&format!("releases r{other} instead of r{src}"))),
        "{found:?}"
    );
}

#[test]
fn a_release_removed_without_its_copy_is_found() {
    let (module, main, _) = regshare_sample();
    let f = &module.functions[main];
    assert!(quarz_lower::verify::copyprop(f, f).is_empty());
    let (bi, ii) = find(f, |i| matches!(i, Inst::Release { .. }));
    let mut new = f.clone();
    new.blocks[bi].insts.remove(ii);
    new.blocks[bi].lines.remove(ii);
    let found: Vec<String> = quarz_lower::verify::copyprop(f, &new)
        .into_iter()
        .map(|v| v.what)
        .collect();
    assert!(
        found.iter().any(|w| w.contains("is removed, with no copy")),
        "{found:?}"
    );
}

// ----- The moved shadow (QUARZ_VERIFY=moves) -----

#[test]
fn a_run_reading_a_moved_register_stops() {
    let name = "a_run_reading_a_moved_register_stops";
    let (code, err) = in_child_with(name, "moves", || {
        let mut module = common::lower("def f(s: String) -> String = s + \"!\"\np f(\"a\" * 2)\n");
        let main = module.units.last().unwrap().body as usize;
        let f = &mut module.functions[main];
        let (bi, ii) = find(
            f,
            |i| matches!(i, Inst::Call { moved, .. } if *moved & 0x7fff != 0),
        );
        let Inst::Call { args, moved, .. } = &f.blocks[bi].insts[ii] else {
            unreachable!()
        };
        // The operand the call moved, read again after it.
        let r = args[moved.trailing_zeros() as usize];
        f.blocks[bi]
            .insts
            .insert(ii + 1, Inst::IsNil { dst: r, src: r });
        f.blocks[bi].lines.insert(ii + 1, 0);
        module
    });
    assert_eq!(code, Some(101), "{err}");
    assert!(err.contains("QIR fact violated: IsNil reads r"), "{err}");
}
