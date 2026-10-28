/-
Random testing before proving (design §5): programs made at random over
a fixed class table and methods, the top level random. Each one `check`
accepts must never get stuck when run (`lake exe fuzz`).
-/

import Plausible
import QuarzCore.Program
import QuarzCore.Semantics

namespace QuarzCore.Fuzz

open Plausible

/-- Object; A < Object with an immutable `@a : Int?` and a `var @v :
Str`; B < A; E < Object, whose `==` says yes to anything; D < A with an
immutable `@c : Int` to assign, its `initialize` generated (`super`). -/
def classes : ClassTable :=
  [⟨"Object", none, []⟩,
   ⟨"A", some 0, [⟨"a", [.int, .nil], false, none⟩, ⟨"v", [.str], true, none⟩]⟩,
   ⟨"B", some 1, []⟩,
   ⟨"E", some 0, []⟩,
   ⟨"D", some 1, [⟨"c", [.int], false, none⟩]⟩]

def atoms : List Atom := [.nil, .bool, .int, .str, .float, .cls 0, .cls 1, .cls 2, .cls 3, .cls 4]

def methods : List Method :=
  [ -- A#get -> Int?: reads and narrows its field.
    ⟨1, "get", [], [.int, .nil], none, [],
      .ite (.field "a" [.int, .nil]) (.field "a" [.int]) .nil⟩,
    -- B#get: an override.
    ⟨2, "get", [], [.int], none, [], .int 7⟩,
    -- A#each(n: Int) { |Int| }: yields twice.
    ⟨1, "each", [("n", [.int])], [.nil], some ⟨[[.int]], [.int, .nil, .bool, .str, .cls 0]⟩,
      [("n", [.int])], .seq (.yield [.var "n" [.int]]) (.seq (.yield [.int 2]) .nil)⟩,
    -- A#set(s: Str): assigns the var field.
    ⟨1, "set", [("s", [.str])], [.str], none, [("s", [.str])], .setField "v" (.var "s" [.str])⟩,
    ⟨3, "==", [("o", [.nil, .bool, .cls 0])], [.bool], none, [("o", [.nil, .bool, .cls 0])], .tru⟩,
    -- A#initialize(a: Int?, v: Str): sets both (B inherits it), then
    -- calls `get`, which D overrides to read the field it sets before
    -- `super`.
    ⟨1, "initialize", [("a", [.int, .nil]), ("v", [.str])], [.nil], none,
      [("a", [.int, .nil]), ("v", [.str])],
      .seq (.setField "a" (.var "a" [.int, .nil]))
        (.seq (.setField "v" (.var "v" [.str])) (.call .self "get" []))⟩ ]

/-- The top level's locals. -/
def locals : List (String × Ty) :=
  [("x", [.int, .nil]), ("y", [.cls 1, .nil]), ("z", [.bool, .nil, .int]), ("e", [.cls 3, .nil]),
   ("k", [.int]), ("o", [.cls 0]), ("f", [.float, .nil])]

def genTy : Gen Ty := do
  let n ← Gen.choose Nat 0 3 (by omega)
  let mut t : Ty := []
  for _ in [0:n.val] do
    t := (← Gen.elements atoms (by decide)) :: t
  return t

def genAtom : Gen Atom := Gen.elements atoms (by decide)

def genVar : Gen String := Gen.elements (locals.map (·.1)) (by decide)

mutual

/-- An expression, `d` levels deep at most. A read's annotation is
mostly its local's declared type, sometimes a random one (most of those
the checker rejects, which is the point). -/
partial def genExpr : Nat → Gen Expr
  | 0 => do
    let x ← genVar
    let t := (locals.find? (·.1 == x)).map (·.2) |>.getD []
    Gen.oneOfWithDefault (pure .nil)
      [pure .nil, pure .tru, pure (.int 1), pure (.str "s"), pure (.flt "0.5"), pure (.var x t),
       do return .var x (← genTy), pure (.new 1 [.int 1, .str "v"]), pure (.new 2 [.nil, .str "w"]),
       pure (.new 3 []), pure (.new 4 [.int 4])]
  | d + 1 => do
    let sub := genExpr d
    let x ← genVar
    let t := (locals.find? (·.1 == x)).map (·.2) |>.getD []
    -- A read narrowed as a test would narrow it: the tests' types.
    let narrowed ← Gen.elements [t, Ty.remove t .nil, Ty.keep t [.nil], Ty.keep t [.nil, .bool],
      t.filter (·.le classes (.cls 1)), [.int], [.cls 1]] (by simp)
    Gen.frequency (pure .nil)
      [(3, genExpr 0),
       (2, return .var x narrowed),
       (3, do return .assign x (← sub)),
       (3, do return .seq (← sub) (← sub)),
       (4, do return .ite (← genTest d) (← sub) (← sub)),
       (1, do return .while (← genTest d) (← sub)),
       (2, do return .call (← sub) "get" []),
       (1, do return .call (← sub) "set" [.str "t"]),
       (2, do return .callBlk (← sub) "each" [.int 3] ["k"] (← sub)),
       (1, pure .raise),
       (2, do return .prim "f" [] [] (← genTy)),
       (1, return .assign "o" (.prim "h" [] [] [.cls 0])),
       (1, do return .prim "g" [← sub] [[.nil, .bool, .int, .str, .cls 0]] [.int, .nil]),
       (2, do return .and (← sub) (← sub)),
       (2, do return .or (← sub) (← sub)),
       (1, do return .not (← sub))]
/-- A test of a local, mostly. -/
partial def genTest (d : Nat) : Gen Expr := do
  let x ← genVar
  let t := (locals.find? (·.1 == x)).map (·.2) |>.getD []
  let r := Expr.var x t
  Gen.frequency (pure r)
    [(2, pure r), (2, pure (.isNil r)), (2, do return .isA r (← genAtom)), (2, pure (.eqNil r)),
     (1, pure (.neNil r)), (1, pure (.eqTrue r)), (1, pure (.eqFalse r)),
     (2, do return .not (← genTest d)), (1, do return .and (← genTest d) (← genTest d)),
     (1, do return .or (← genTest d) (← genTest d)), (1, genExpr d)]

/-- A body for `D#initialize(c: Int)`: assigning `@c`, `super` (with
fitting arguments or not), uses of the object, in any order; most orders
the checker rejects. -/
partial def genInit : Nat → Gen Expr
  | 0 => Gen.elements [.nil, .setField "c" (.var "c" [.int]), .superInit 1 [.var "c" [.int], .str "s"],
      .superInit 1 [.nil, .str "t"], .superInit 1 [.str "u"], .call .self "get" [], .self,
      .field "c" [.int], .field "a" [.int, .nil]] (by simp)
  | d + 1 => do
    let sub := genInit d
    Gen.frequency (pure .nil)
      [(4, genInit 0),
       (4, do return .seq (← sub) (← sub)),
       (2, do return .ite (.prim "b" [] [] [.bool]) (← sub) (← sub)),
       (1, do return .while (.prim "b" [] [] [.bool]) (← sub)),
       (1, do return .callBlk .self "each" [.int 1] ["k"] (← sub)),
       (1, pure .raise),
       (1, do return .ret (← sub))]

end

/-- Built-in methods answering at random (seeded by the fuel left): a
value of one of the type's atoms, an existing object for a class (an
exception if there is none). -/
def oracle : Oracle := fun n s t =>
  match t[n % (t.length + 1)]? with
  | some .nil => some .nil
  | some .bool => some (.bool (n % 2 == 0))
  | some .int => some (.int n)
  | some .str => some (.str "o")
  | some .float => some (.flt "1.5")
  -- `Object` holds every value.
  | some (.cls 0) => some (match n % 6 with
    | 0 => .nil
    | 1 => .bool false
    | 2 => .int 3
    | 3 => .str "p"
    | 4 => .flt "2.5"
    | _ => .obj 0)
  | some (.cls k) =>
    (s.objs.zipIdx.find? fun (o, _) => classes.subclass o.cls k).map fun (_, l) => .obj l
  | none => none

def program (body : Expr) (init : Expr := .seq (.setField "c" (.var "c" [.int])) (.superInit 1 [.nil, .str "d"])) :
    Program :=
  ⟨classes, methods ++ [⟨4, "initialize", [("c", [.int])], [.nil], none, [("c", [.int]), ("k", [.int])], init⟩,
    ⟨4, "get", [], [.int], none, [], .field "c" [.int]⟩],
    ⟨0, "<main>", [], [.nil, .bool, .int, .str, .cls 0], none, locals, body⟩, []⟩

end QuarzCore.Fuzz
