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
immutable `@c : Int` to assign, its `initialize` generated (`super`).
Generic: Box[T] with an immutable `@v : T` and a `var @w : T?`;
IntBox < Box[Int]; Pair[S, T] with `@a : S` and `@b : T`; OBox[out T]
with `@v : T`, `get` and `each` (yields `@v`); Cell[T] with `var @v : T`
and `set`; Sink[in T] with `put(x: T)`; IntOBox < OBox[Int], overriding
`get`; AHold[T <: A] with `@v : T` and `ag`, calling `get` through the
bound; data DPt(n: Int); data DEq whose `==` says yes to anything;
enum Sh with variants Ci(r: Int) and Pt. -/
def classes : ClassTable :=
  [⟨"Object", none, [], [], [], [], .cls⟩,
   ⟨"A", some 0, [⟨"a", [.int, .nil], false, none⟩, ⟨"v", [.str], true, none⟩], [], [], [], .cls⟩,
   ⟨"B", some 1, [], [], [], [], .cls⟩,
   ⟨"E", some 0, [], [], [], [], .cls⟩,
   ⟨"D", some 1, [⟨"c", [.int], false, none⟩], [], [], [], .cls⟩,
   ⟨"Box", some 0, [⟨"v", [.param 0], false, none⟩, ⟨"w", [.param 0, .nil], true, none⟩], [.inv], [], [], .cls⟩,
   ⟨"IntBox", some 5, [], [], [[.int]], [], .cls⟩,
   ⟨"Pair", some 0, [⟨"a", [.param 0], false, none⟩, ⟨"b", [.param 1], false, none⟩], [.inv, .inv], [], [], .cls⟩,
   ⟨"OBox", some 0, [⟨"v", [.param 0], false, none⟩], [.co], [], [], .cls⟩,
   ⟨"Cell", some 0, [⟨"v", [.param 0], true, none⟩], [.inv], [], [], .cls⟩,
   ⟨"Sink", some 0, [], [.contra], [], [], .cls⟩,
   ⟨"IntOBox", some 8, [], [], [[.int]], [], .cls⟩,
   ⟨"AHold", some 0, [⟨"v", [.param 0], false, none⟩], [.inv], [], [[.cls 1 []]], .cls⟩,
   ⟨"DPt", some 0, [⟨"n", [.int], false, none⟩], [], [], [], .data⟩,
   ⟨"DEq", some 0, [], [], [], [], .data⟩,
   ⟨"Sh", some 0, [], [], [], [], .enumC⟩,
   ⟨"Ci", some 15, [⟨"r", [.int], false, none⟩], [], [], [], .variant⟩,
   ⟨"Pt", some 15, [], [], [], [], .variant⟩,
   ⟨"Proc0", some 0, [], [.co], [], [], .proc⟩,
   ⟨"Proc1", some 0, [], [.contra, .co], [], [], .proc⟩,
   ⟨"Arr", some 0, [], [.co], [], [], .builtin⟩]

/-- The atoms of random types and `is_a?` tests (`Box` without its
argument is ill formed: the checker rejects a test of it). -/
def atoms : List Atom :=
  [.nil, .bool, .int, .str, .float, .cls 0 [], .cls 1 [], .cls 2 [], .cls 3 [], .cls 4 [],
   .cls 5 [[.int]], .cls 5 [[.str]], .cls 5 [], .cls 6 [], .cls 7 [[.int], [.str]],
   .cls 8 [[.cls 0 []]], .cls 8 [[.int]], .cls 9 [[.cls 0 []]], .cls 9 [[.int]],
   .cls 10 [[.int]], .cls 11 []]

def methods : List Method :=
  [ -- A#get -> Int?: reads and narrows its field.
    ⟨1, "get", [], [.int, .nil], none, [],
      .ite (.field "a" [.int, .nil]) (.field "a" [.int]) .nil⟩,
    -- B#get: an override.
    ⟨2, "get", [], [.int], none, [], .int 7⟩,
    -- A#each(n: Int) { |Int| }: yields twice.
    ⟨1, "each", [("n", [.int])], [.nil], some ⟨[[.int]], [.int, .nil, .bool, .str, .cls 0 []]⟩,
      [("n", [.int])], .seq (.yield [.var "n" [.int]]) (.seq (.yield [.int 2]) .nil)⟩,
    -- A#safe_each(n: Int) { |Int| }: yields, rescuing what the block
    -- raises (the block may stop anywhere: after the call, what it
    -- assigns is un-narrowed).
    ⟨1, "safe_each", [("n", [.int])], [.nil], some ⟨[[.int]], [.int, .nil, .bool, .str, .cls 0 []]⟩,
      [("n", [.int]), ("ex", [.cls 0 []])], .rescue (.yield [.var "n" [.int]]) "ex" .nil .nil⟩,
    -- A#set(s: Str): assigns the var field.
    ⟨1, "set", [("s", [.str])], [.str], none, [("s", [.str])], .setField "v" (.var "s" [.str])⟩,
    ⟨3, "==", [("o", [.nil, .bool, .cls 0 []])], [.bool], none, [("o", [.nil, .bool, .cls 0 []])], .tru⟩,
    -- A#initialize(a: Int?, v: Str): sets both (B inherits it), then
    -- calls `get`, which D overrides to read the field it sets before
    -- `super`.
    ⟨1, "initialize", [("a", [.int, .nil]), ("v", [.str])], [.nil], none,
      [("a", [.int, .nil]), ("v", [.str])],
      .seq (.setField "a" (.var "a" [.int, .nil]))
        (.seq (.setField "v" (.var "v" [.str])) (.call .self "get" []))⟩,
    -- Box#get -> T; Box#put(x: T) -> T?: assigns the var field;
    -- Box#initialize(v: T).
    ⟨5, "get", [], [.param 0], none, [], .field "v" [.param 0]⟩,
    ⟨5, "put", [("x", [.param 0])], [.param 0, .nil], none, [("x", [.param 0])],
      .seq (.setField "w" (.var "x" [.param 0])) (.field "w" [.param 0, .nil])⟩,
    ⟨5, "initialize", [("v", [.param 0])], [.nil], none, [("v", [.param 0])],
      .setField "v" (.var "v" [.param 0])⟩,
    -- IntBox#get -> Int: an override reading the inherited field at `Int`.
    ⟨6, "get", [], [.int], none, [], .field "v" [.int]⟩,
    -- Pair#swap -> Pair[T, S], naming the class's parameters in `new`.
    ⟨7, "swap", [], [.cls 7 [[.param 1], [.param 0]]], none, [],
      .new 7 [[.param 1], [.param 0]] [.field "b" [.param 1], .field "a" [.param 0]]⟩,
    ⟨7, "initialize", [("a", [.param 0]), ("b", [.param 1])], [.nil], none,
      [("a", [.param 0]), ("b", [.param 1])],
      .seq (.setField "a" (.var "a" [.param 0])) (.setField "b" (.var "b" [.param 1]))⟩,
    -- OBox#get -> T; OBox#initialize(v: T).
    ⟨8, "get", [], [.param 0], none, [], .field "v" [.param 0]⟩,
    ⟨8, "initialize", [("v", [.param 0])], [.nil], none, [("v", [.param 0])],
      .setField "v" (.var "v" [.param 0])⟩,
    -- OBox#each { |T| }: yields `@v` (a block's parameter: a positive
    -- position).
    ⟨8, "each", [], [.nil], some ⟨[[.param 0]], [.int, .nil, .bool, .str, .cls 0 []]⟩, [],
      .seq (.yield [.field "v" [.param 0]]) .nil⟩,
    -- Sink#put(x: T); IntOBox#get -> Int, reading the inherited field.
    ⟨10, "put", [("x", [.param 0])], [.nil], none, [("x", [.param 0])], .nil⟩,
    ⟨11, "get", [], [.int], none, [], .field "v" [.int]⟩,
    -- AHold#ag -> Int?: `@v.get`, `@v` a `T <: A`; AHold#initialize(v: T).
    ⟨12, "ag", [], [.int, .nil], none, [], .call (.field "v" [.param 0]) "get" []⟩,
    ⟨12, "initialize", [("v", [.param 0])], [.nil], none, [("v", [.param 0])],
      .setField "v" (.var "v" [.param 0])⟩,
    -- DPt's generated `initialize`; DEq#==.
    ⟨13, "initialize", [("n", [.int])], [.nil], none, [("n", [.int])], .setField "n" (.var "n" [.int])⟩,
    ⟨13, "n", [], [.int], none, [], .field "n" [.int]⟩,
    ⟨16, "initialize", [("r", [.int])], [.nil], none, [("r", [.int])], .setField "r" (.var "r" [.int])⟩,
    ⟨16, "r", [], [.int], none, [], .field "r" [.int]⟩,
    ⟨14, "==", [("o", [.nil, .bool, .cls 0 []])], [.bool], none, [("o", [.nil, .bool, .cls 0 []])], .tru⟩,
    -- Cell#get -> T; Cell#set(x: T) -> T; Cell#initialize(v: T).
    ⟨9, "get", [], [.param 0], none, [], .field "v" [.param 0]⟩,
    ⟨9, "set", [("x", [.param 0])], [.param 0], none, [("x", [.param 0])],
      .seq (.setField "v" (.var "x" [.param 0])) (.var "x" [.param 0])⟩,
    ⟨9, "initialize", [("v", [.param 0])], [.nil], none, [("v", [.param 0])],
      .setField "v" (.var "v" [.param 0])⟩ ]

/-- The top level's locals. -/
def locals : List (String × Ty) :=
  [("x", [.int, .nil]), ("y", [.cls 1 [], .nil]), ("z", [.bool, .nil, .int]), ("e", [.cls 3 [], .nil]),
   ("k", [.int]), ("o", [.cls 0 []]), ("f", [.float, .nil]),
   ("bi", [.cls 5 [[.int]], .nil]), ("bs", [.cls 5 [[.str]]]), ("ib", [.cls 6 [], .nil]),
   ("p", [.cls 7 [[.int], [.str]], .nil]),
   ("oi", [.cls 8 [[.int]], .nil]), ("oo", [.cls 8 [[.cls 0 []]], .nil]),
   ("ci", [.cls 9 [[.int]], .nil]), ("co", [.cls 9 [[.cls 0 []]], .nil]),
   ("si", [.cls 10 [[.int]], .nil]),
   ("ah", [.cls 12 [[.cls 2 []]], .nil]), ("ae", [.cls 12 [[.cls 3 []]], .nil]),
   ("dp", [.cls 13 [], .nil]), ("de", [.cls 14 [], .nil]),
   ("sh", [.cls 15 []]), ("cc", [.cls 16 []]), ("ex", [.cls 0 []]),
   ("pf", [.cls 18 [[.nil]]]), ("pg", [.cls 19 [[.int], [.int, .nil]]]),
   ("xs", [.cls 20 [[.int]], .nil]), ("ys", [.cls 20 [[.int, .nil]], .nil])]

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
       do return .var x (← genTy), pure (.new 1 [] [.int 1, .str "v"]), pure (.new 2 [] [.nil, .str "w"]),
       pure (.new 3 [] []), pure (.new 4 [] [.int 4]),
       pure (.new 5 [[.int]] [.int 1]), pure (.new 5 [[.str]] [.str "s"]), pure (.new 6 [] [.int 2]),
       pure (.new 7 [[.int], [.str]] [.int 1, .str "a"]),
       -- Ill typed, the wrong number of type arguments: rejected.
       pure (.new 5 [[.int]] [.str "x"]), pure (.new 5 [] [.int 1])]
  | d + 1 => do
    let sub := genExpr d
    let x ← genVar
    let t := (locals.find? (·.1 == x)).map (·.2) |>.getD []
    -- A read narrowed as a test would narrow it: the tests' types.
    let narrowed ← Gen.elements [t, Ty.remove t .nil, Ty.keep t [.nil], Ty.keep t [.nil, .bool],
      t.filter (·.le classes [] (.cls 1 [])), [.int], [.cls 1 []],
      t.filter (·.le classes [] (.cls 5 [[.int]])), [.cls 6 []]] (by simp)
    Gen.frequency (pure .nil)
      [(3, genExpr 0),
       (2, return .var x narrowed),
       (3, do return .assign x (← sub)),
       (3, do return .seq (← sub) (← sub)),
       (4, do return .ite (← genTest d) (← sub) (← sub)),
       (1, do return .while (← genTest d) (← sub)),
       (2, do return .call (← sub) "get" []),
       (1, do return .call (← sub) "set" [.str "t"]),
       (1, do return .call (← sub) "put" [.int 1]),
       (1, do return .call (← sub) "put" [.str "q"]),
       (1, do return .call (← sub) "swap" []),
       -- Flows between the boxes: a `Box[Str]` into the `Box[Int]?` local,
       -- what a box gives into the `Int` local (the arguments' soundness).
       (2, do return .assign "bi" (← sub)),
       (2, do return .assign "ib" (← sub)),
       (2, do return .assign "k" (.call (← sub) "get" [])),
       (2, do return .callBlk (← sub) "each" [.int 3] ["k"] (← sub)),
       (1, pure (.raise (.str "boom"))),
       -- `rescue`, its exception in `ex` (this table has no `Exception`:
       -- any value is one), and `ensure`.
       (2, do return .rescue (← sub) "ex" (← sub) (← sub)),
       (1, do return .ensure (← sub) (← sub)),
       (1, pure (.raise (.var "ex" [.cls 0 []]))),
       -- The body changes `x`, then raises (or a built-in call does): the
       -- handler must not see `x` as before.
       (1, pure (.seq (.assign "x" (.int 1)) (.rescue (.seq (.assign "x" .nil) (.raise (.str "boom")))
         "ex" (.assign "x" (.var "x" [.int])) .nil))),
       (1, pure (.seq (.assign "x" (.int 1)) (.ensure (.seq (.assign "x" .nil) (.raise (.str "boom")))
         (.assign "x" (.var "x" [.int]))))),
       -- Procedures: a lambda that changes `x`, called later; one taking an
       -- `Int`; `x` read after a call (which may run one).
       (1, pure (.assign "pf" (.lambda [] [] [.nil] (.assign "x" .nil)))),
       (1, pure (.assign "pg" (.lambda [("lq", [.int])] [] [.int, .nil] (.var "lq" [.int])))),
       -- Lambdas C0 accepts: reading `x` as declared into an own local;
       -- giving `nil`; then called after `x` changed.
       (2, pure (.seq (.assign "x" (.int 1)) (.assign "pf" (.lambda [] [("lk", [.int, .nil])] [.nil]
         (.seq (.assign "lk" (.var "x" [.int, .nil])) .nil))))),
       (1, pure (.assign "pf" (.lambda [] [] [.nil] .nil))),
       (1, pure (.assign "pg" (.lambda [("lq", [.int])] [] [.int, .nil] (.var "x" [.int, .nil])))),
       (2, pure (.seq (.assign "x" (.int 1)) (.seq (.assign "pg" (.lambda [("lq", [.int])] [] [.int, .nil]
         (.var "x" [.int, .nil]))) (.seq (.assign "x" .nil)
         (.assign "x" (.callProc (.var "pg" [.cls 19 [[.int], [.int, .nil]]]) [.int 1])))))),
       (1, pure (.callProc (.var "pf" [.cls 18 [[.nil]]]) [])),
       (1, do return .assign "x" (.callProc (.var "pg" [.cls 19 [[.int], [.int, .nil]]]) [← sub])),
       (2, pure (.seq (.assign "pf" (.lambda [] [] [.nil] (.assign "x" .nil)))
         (.seq (.assign "x" (.int 1)) (.seq (.callProc (.var "pf" [.cls 18 [[.nil]]]) [])
         (.assign "k" (.var "x" [.int])))))),
       -- A lambda reading `x` as narrowed where it is made, run after `x`
       -- changed.
       (2, pure (.seq (.assign "x" (.int 1)) (.seq (.assign "pf" (.lambda [] [("lk", [.int])] [.nil]
         (.seq (.assign "lk" (.var "x" [.int])) .nil))) (.seq (.assign "x" .nil)
         (.callProc (.var "pf" [.cls 18 [[.nil]]]) []))))),
       (1, pure (.seq (.assign "x" (.int 1)) (.seq (.call (.var "y" [.cls 1 []]) "get" [])
         (.assign "k" (.var "x" [.int]))))),
       -- A block that changes `x` and raises, rescued by the method: `x`
       -- is not as the block's end has it.
       (1, do return .seq (.assign "x" (.int 1)) (.seq (.callBlk (.new 1 [] [.int 1, .str "v"]) "safe_each" [.int 3] ["k"]
         (.seq (.assign "x" .nil) (.seq (.raise (.str "boom")) (.assign "x" (.int 2)))))
         (.assign "x" (.var "x" [.int])))),
       (2, do return .prim "f" [] [] (← genTy)),
       -- Arrays (design §14): made by built-in calls, covariant, their
       -- elements read.
       (1, return .assign "xs" (.prim "arr" [.int 1] [[.int]] [.cls 20 [[.int]]])),
       (1, return .assign "ys" (.prim "arr" [.nil] [[.int, .nil]] [.cls 20 [[.int, .nil]]])),
       (1, pure (.seq (.assign "xs" (.prim "arr" [] [] [.cls 20 [[.int]]]))
         (.assign "ys" (.var "xs" [.cls 20 [[.int]]])))),
       (1, pure (.seq (.assign "xs" (.prim "arr" [] [] [.cls 20 [[.int]]]))
         (.assign "k" (.prim "at" [.var "xs" [.cls 20 [[.int]]]] [[.cls 20 [[.int]]]] [.int])))),
       (1, pure (.assign "ys" (.prim "push" [.var "ys" [.cls 20 [[.int, .nil]], .nil]]
         [[.cls 20 [[.int, .nil]], .nil]] [.cls 20 [[.int, .nil]]]))),
       (1, return .assign "o" (.prim "h" [] [] [.cls 0 []])),
       (1, do return .prim "g" [← sub] [[.nil, .bool, .int, .str, .cls 0 []]] [.int, .nil]),
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
       (1, pure (.raise (.str "boom"))),
       (1, do return .ret (← sub))]

/-- Uses of the boxes: boxes made and assigned to the box locals (of the
right argument or not), what they give assigned to the `Int` local, the
locals read, tests of them; most orders the checker rejects, and the
rest must not get stuck: a `Box[Str]` read as a `Box[Int]` would. -/
partial def genBox : Nat → Gen Expr
  | 0 => Gen.frequency (pure .nil)
      [(3, pure (.assign "bi" (.new 5 [[.int]] [.int 1]))), (3, pure (.assign "bi" (.new 5 [[.str]] [.str "s"]))),
       (1, pure (.assign "bs" (.new 5 [[.str]] [.str "s"]))), (1, pure (.assign "bi" (.var "bs" [.cls 5 [[.str]]]))),
       (2, pure (.assign "ib" (.new 6 [] [.int 2]))), (2, pure (.assign "bi" (.var "ib" [.cls 6 []]))),
       (3, pure (.assign "x" (.call (.var "bi" [.cls 5 [[.int]]]) "get" []))),
       (1, pure (.assign "x" (.call (.var "ib" [.cls 6 []]) "get" []))),
       (1, pure (.assign "x" (.call (.var "bi" [.cls 5 [[.int]]]) "put" [.int 3]))),
       (1, pure (.call (.var "bs" [.cls 5 [[.str]]]) "put" [.str "q"])),
       (1, pure (.call (.var "bs" [.cls 5 [[.str]]]) "put" [.int 1])),
       (1, pure (.var "x" [.int, .nil])), (1, pure (.var "bi" [.cls 5 [[.int]], .nil])),
       (1, pure (.assign "p" (.new 7 [[.int], [.str]] [.int 1, .str "a"]))),
       (1, pure (.assign "p" (.call (.call (.var "p" [.cls 7 [[.int], [.str]]]) "swap" []) "swap" []))),
       (1, pure (.assign "p" (.call (.var "p" [.cls 7 [[.int], [.str]]]) "swap" []))),
       (1, pure (.ite (.isA (.var "bi" [.cls 5 [[.int]], .nil]) (.cls 6 []))
         (.assign "x" (.call (.var "bi" [.cls 6 []]) "get" [])) .nil)),
       (1, pure (.ite (.isNil (.var "bi" [.cls 5 [[.int]], .nil])) .nil
         (.assign "x" (.call (.var "bi" [.cls 5 [[.int]]]) "get" [])))),
       -- Variance: an `OBox[Int]` read as an `OBox[Object]`; a `Cell[Int]`
       -- assigned where a `Cell[Object]` is (rejected unless the order is
       -- wrong), a `Str` set through it, the `Cell[Int]` read back.
       (2, pure (.assign "oi" (.new 8 [[.int]] [.int 1]))), (2, pure (.assign "oo" (.var "oi" [.cls 8 [[.int]], .nil]))),
       (1, pure (.assign "oo" (.new 8 [[.str]] [.str "o"]))),
       (2, pure (.ite (.isNil (.var "oi" [.cls 8 [[.int]], .nil])) .nil
         (.assign "x" (.call (.var "oi" [.cls 8 [[.int]]]) "get" [])))),
       (2, pure (.assign "ci" (.new 9 [[.int]] [.int 1]))),
       (2, pure (.ite (.isNil (.var "co" [.cls 9 [[.cls 0 []]], .nil])) .nil
         (.call (.var "co" [.cls 9 [[.cls 0 []]]]) "set" [.str "s"]))),
       (2, pure (.ite (.isNil (.var "ci" [.cls 9 [[.int]], .nil])) .nil
         (.assign "x" (.call (.var "ci" [.cls 9 [[.int]]]) "get" []))))]
  | d + 1 => do
    let sub := genBox d
    Gen.frequency (pure .nil)
      [(3, genBox 0),
       (6, do return .seq (← sub) (← sub)),
       (2, do return .ite (.prim "b" [] [] [.bool]) (← sub) (← sub)),
       (1, do return .while (.prim "b" [] [] [.bool]) (← sub)),
       (1, do return .ite (← genTest 1) (← sub) (← sub))]

end

/-- Steps of the variance scenario: boxes and cells made, seen through a
wider argument, written through it, read back at the narrow one. Only
a sound order of the arguments keeps a `Str` out of a `Cell[Int]`. -/
def varSteps : List Expr :=
  [.assign "ci" (.new 9 [[.int]] [.int 1]),
   .assign "co" (.var "ci" [.cls 9 [[.int]], .nil]),
   .ite (.isNil (.var "co" [.cls 9 [[.cls 0 []]], .nil])) .nil
     (.call (.var "co" [.cls 9 [[.cls 0 []]]]) "set" [.str "s"]),
   .ite (.isNil (.var "ci" [.cls 9 [[.int]], .nil])) .nil
     (.assign "x" (.call (.var "ci" [.cls 9 [[.int]]]) "get" [])),
   .assign "oi" (.new 8 [[.int]] [.int 1]),
   .assign "oo" (.var "oi" [.cls 8 [[.int]], .nil]),
   .assign "oi" (.var "oo" [.cls 8 [[.cls 0 []]], .nil]),
   .ite (.isNil (.var "oi" [.cls 8 [[.int]], .nil])) .nil
     (.assign "x" (.call (.var "oi" [.cls 8 [[.int]]]) "get" [])),
   -- Accepted writes and calls through wider views: a `Cell[Object]` set
   -- to a `Str`; an `OBox[Int]` or an `IntOBox` seen as an
   -- `OBox[Object]`, its `get` and `each` run there; a `Sink[Object]`
   -- seen as a `Sink[Int]`.
   .assign "co" (.new 9 [[.cls 0 []]] [.int 1]),
   .assign "oo" (.new 11 [] [.int 3]),
   .assign "oi" (.new 11 [] [.int 4]),
   .ite (.isNil (.var "oo" [.cls 8 [[.cls 0 []]], .nil])) .nil
     (.assign "o" (.call (.var "oo" [.cls 8 [[.cls 0 []]]]) "get" [])),
   .ite (.isNil (.var "oo" [.cls 8 [[.cls 0 []]], .nil])) .nil
     (.callBlk (.var "oo" [.cls 8 [[.cls 0 []]]]) "each" [] ["o"] .nil),
   .ite (.isNil (.var "oi" [.cls 8 [[.int]], .nil])) .nil
     (.callBlk (.var "oi" [.cls 8 [[.int]]]) "each" [] ["k"] (.assign "x" (.var "k" [.int]))),
   .assign "si" (.new 10 [[.cls 0 []]] []),
   .ite (.isNil (.var "si" [.cls 10 [[.int]], .nil])) .nil
     (.call (.var "si" [.cls 10 [[.int]]]) "put" [.int 1]),
   -- Bounds: an `AHold[B]` (B < A) and its `ag`; an `AHold[E]` (E is no
   -- `A`) made, which the bound check rejects, and its `ag`.
   .assign "ah" (.new 12 [[.cls 2 []]] [.new 2 [] [.nil, .str "w"]]),
   .ite (.isNil (.var "ah" [.cls 12 [[.cls 2 []]], .nil])) .nil
     (.assign "x" (.call (.var "ah" [.cls 12 [[.cls 2 []]]]) "ag" [])),
   .assign "ae" (.new 12 [[.cls 3 []]] [.new 3 [] []]),
   .ite (.isNil (.var "ae" [.cls 12 [[.cls 3 []]], .nil])) .nil
     (.assign "x" (.call (.var "ae" [.cls 12 [[.cls 3 []]]]) "ag" [])),
   -- `data`: `== nil` narrows a DPt (final), not a DEq (its own `==`).
   .assign "dp" (.new 13 [] [.int 2]),
   .ite (.eqNil (.var "dp" [.cls 13 [], .nil])) (.var "dp" [.nil])
     (.assign "x" (.call (.var "dp" [.cls 13 []]) "n" [])),
   .assign "de" (.new 14 [] []),
   .ite (.eqNil (.var "de" [.cls 14 [], .nil])) (.var "de" [.nil]) .nil,
   -- `case/in` on an enum, as the translator writes it: covering both
   -- variants (the rest `absurd`), or one only (rejected), or with a
   -- capture.
   .assign "sh" (.new 16 [] [.int 3]),
   .assign "sh" (.new 17 [] []),
   -- An `Sh` from a built-in call: of the enum's type, not narrowed; then
   -- a `case` covering one variant (rejected) or both.
   .assign "sh" (.prim "sh" [] [] [.cls 15 []]),
   .seq (.assign "sh" (.new 17 [] [])) (.seq (.assign "sh" (.prim "sh" [] [] [.cls 15 []]))
     (.ite (.isA (.var "sh" [.cls 15 []]) (.cls 16 [])) (.assign "x" .nil) .absurd)),
   .seq (.assign "sh" (.new 17 [] [])) (.seq (.assign "sh" (.prim "sh" [] [] [.cls 15 []]))
     (.ite (.isA (.var "sh" [.cls 15 []]) (.cls 16 [])) (.assign "x" .nil)
       (.ite (.isA (.var "sh" [.cls 15 []]) (.cls 17 [])) (.assign "x" (.int 1)) .absurd))),
   .ite (.isA (.var "sh" [.cls 15 []]) (.cls 16 [])) (.assign "x" .nil)
     (.ite (.isA (.var "sh" [.cls 15 []]) (.cls 17 [])) (.assign "x" (.int 0)) .absurd),
   .ite (.isA (.var "sh" [.cls 15 []]) (.cls 16 [])) (.assign "x" .nil) .absurd,
   .ite (.isA (.var "sh" [.cls 15 []]) (.cls 16 []))
     (.seq (.assign "cc" (.var "sh" [.cls 16 []])) (.assign "x" (.call (.var "cc" [.cls 16 []]) "r" [])))
     (.ite (.isA (.var "sh" [.cls 15 []]) (.cls 17 [])) .nil .absurd)]

/-- `n` steps of the variance scenario, in a random order. -/
def genVarSeq : Nat → Gen Expr
  | 0 => pure .nil
  | n + 1 => do return .seq (← Gen.elements varSteps (by simp [varSteps])) (← genVarSeq n)

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
  | some (.cls 0 []) => some (match n % 6 with
    | 0 => .nil
    | 1 => .bool false
    | 2 => .int 3
    | 3 => .str "p"
    | 4 => .flt "2.5"
    | _ => .obj 0)
  | some (.cls k as) =>
    (s.objs.zipIdx.find? fun (_, l) => s.hasType classes (.obj l) [.cls k as]).map fun (_, l) => .obj l
  -- A type parameter: no value here.
  | some (.param _) => none
  | none => none

def program (body : Expr) (init : Expr := .seq (.setField "c" (.var "c" [.int])) (.superInit 1 [.nil, .str "d"])) :
    Program :=
  ⟨classes, methods ++ [⟨4, "initialize", [("c", [.int])], [.nil], none, [("c", [.int]), ("k", [.int])], init⟩,
    ⟨4, "get", [], [.int], none, [], .field "c" [.int]⟩],
    ⟨0, "<main>", [], [.nil, .bool, .int, .str, .cls 0 []], none, locals, body⟩, []⟩

end QuarzCore.Fuzz
