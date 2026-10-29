/-
Small programs, checked and run (`lake build` runs the `#guard`s).
-/

import QuarzCore.Program
import QuarzCore.Semantics

namespace QuarzCore.Examples

def object : Class := ⟨"Object", none, [], [], [], []⟩

/-- No built-in method returns. -/
def noPrim : Oracle := fun _ _ _ => none

/-- `x: Int? = nil; if x then x else 0 end`, the read in the `then`
branch annotated `Int`. -/
def narrowed : Program :=
  ⟨[object], [], ⟨0, "<main>", [], [.int, .nil], none, [("x", [.int, .nil])],
    .seq (.assign "x" .nil) (.ite (.var "x" [.int, .nil]) (.var "x" [.int]) (.int 0))⟩, []⟩

#guard narrowed.check
#guard match run narrowed noPrim 100 with | .ok (.int 0) _ => true | _ => false

/-- The same read, but not narrowed: annotating it `Int` is rejected. -/
def unnarrowed : Program :=
  ⟨[object], [], ⟨0, "<main>", [], [.int, .nil], none, [("x", [.int, .nil])],
    .seq (.assign "x" .nil) (.var "x" [.int])⟩, []⟩

#guard !unnarrowed.check
-- (Run anyway, the read is stuck: the value is `nil`.)
#guard match run unnarrowed noPrim 100 with | .stuck => true | _ => false

/-- A class whose `==` says yes to `nil` (09b19e3): `c == nil` does not
narrow `c`, of a class type. -/
def eqClass : Class := ⟨"E", some 0, [], [], [], []⟩

def eqMethod : Method :=
  ⟨1, "==", [("o", [.cls 0 []])], [.bool], none, [("o", [.cls 0 []])], .tru⟩

def equalNil (ann : Ty) : Program :=
  ⟨[object, eqClass], [eqMethod], ⟨0, "<main>", [], [.cls 1 [], .nil], none, [("c", [.cls 1 [], .nil])],
    .seq (.assign "c" (.new 1 [] []))
      (.ite (.eqNil (.var "c" [.cls 1 [], .nil])) (.var "c" ann) .nil)⟩, []⟩

#guard (equalNil [.cls 1 [], .nil]).check
#guard !(equalNil [.nil]).check
#guard match run (equalNil [.nil]) noPrim 100 with | .stuck => true | _ => false

/-- A loop un-narrows what it assigns: `x` may be `nil` again at the
test (docs/02 §6). -/
def loop (ann : Ty) : Program :=
  ⟨[object], [], ⟨0, "<main>", [], [.nil], none, [("x", [.int, .nil])],
    .seq (.assign "x" (.int 1))
      (.while (.var "x" ann) (.assign "x" .nil))⟩, []⟩

#guard (loop [.int, .nil]).check
#guard !(loop [.int]).check

/-! `initialize` and definite assignment (docs/01 §3). Class 1 has `@x:
Int` (to be assigned) and `@lbl: String = "p"`; `initialize(v: Int)`
runs `body`. -/

def initClass (extra : List Field := []) : Class :=
  ⟨"P", some 0, [⟨"x", [.int], false, none⟩, ⟨"lbl", [.str], false, some 0⟩] ++ extra, [], [], []⟩

def initMethod (body : Expr) : Method :=
  ⟨1, "initialize", [("v", [.int])], [.nil], none, [("v", [.int])], body⟩

def getx : Method := ⟨1, "getx", [], [.int], none, [], .field "x" [.int]⟩

def setx : Method := ⟨1, "setx", [], [.int], none, [], .setField "x" (.int 1)⟩

def initProg (body : Expr) (main : Expr := .call (.new 1 [] [.int 3]) "getx" [])
    (extra : List Method := []) (fields : List Field := []) (defaults : List Expr := [.str "p"]) :
    Program :=
  ⟨[object, initClass fields], [initMethod body, getx] ++ extra,
    ⟨0, "<main>", [], [.nil, .bool, .int, .str, .cls 0 []], none, [], main⟩, defaults⟩

def assignX : Expr := .setField "x" (.var "v" [.int])

-- Assigned, then `self` used: fine, and `new` gives a made object.
#guard (initProg (.seq assignX (.call .self "getx" []))).check
#guard match run (initProg (.seq assignX (.call .self "getx" []))) noPrim 100 with
  | .ok (.int 3) _ => true | _ => false
-- A field with a default may be read before; one to assign may not.
#guard (initProg (.seq (.field "lbl" [.str]) assignX)).check
#guard !(initProg (.seq (.field "x" [.int]) assignX)).check
-- No `self` before every field is set, nor a `return`; none unassigned.
#guard !(initProg (.seq (.call .self "getx" []) assignX)).check
#guard !(initProg (.seq (.ret .nil) assignX)).check
#guard !(initProg .nil).check
-- Assigned on one branch only: not set after the `if`.
#guard !(initProg (.ite (.prim "c" [] [] [.bool]) assignX .nil)).check
#guard (initProg (.ite (.prim "c" [] [] [.bool]) assignX assignX)).check
-- A default reads only the fields before it that hold a value.
#guard !(initProg assignX (fields := [⟨"y", [.int], false, some 1⟩])
  (defaults := [.str "p", .field "x" [.int]])).check
#guard (initProg assignX (fields := [⟨"n", [.str], false, some 1⟩])
  (defaults := [.str "p", .field "lbl" [.str]])).check
-- An immutable field is assigned only in `initialize`, which no call reaches.
#guard !(initProg assignX (extra := [setx])).check
#guard !(initProg assignX (main := .call (.new 1 [] [.int 3]) "initialize" [.int 4])).check

/-- A class with only `var @a: Int = default`, and `geta`. -/
def defaultProg (default : Expr) : Program :=
  ⟨[object, ⟨"Q", some 0, [⟨"a", [.int], true, some 0⟩], [], [], []⟩],
    [⟨1, "geta", [], [.int], none, [], .field "a" [.int]⟩],
    ⟨0, "<main>", [], [.nil, .bool, .int, .str, .cls 0 []], none, [], .call (.new 1 [] []) "geta" []⟩,
    [default]⟩

-- A default never uses the object, even once it has set every field.
#guard (defaultProg (.seq (.setField "a" (.int 1)) (.int 2))).check
#guard !(defaultProg (.seq (.setField "a" (.int 1)) (.call .self "geta" []))).check

/-! ### `super` in `initialize`

P has `@x : Int`, assigned by its `initialize`, which then calls `who`;
C < P has `@y : Int` and overrides `who` to read it. -/

def superProg (body : Expr) : Program :=
  ⟨[object, ⟨"P", some 0, [⟨"x", [.int], false, none⟩], [], [], []⟩, ⟨"C", some 1, [⟨"y", [.int], false, none⟩], [], [], []⟩],
    [⟨1, "initialize", [("v", [.int])], [.nil], none, [("v", [.int])],
        .seq (.setField "x" (.var "v" [.int])) (.call .self "who" [])⟩,
     ⟨1, "who", [], [.int], none, [], .field "x" [.int]⟩,
     ⟨2, "initialize", [("w", [.int])], [.nil], none, [("w", [.int])], body⟩,
     ⟨2, "who", [], [.int], none, [], .field "y" [.int]⟩],
    ⟨0, "<main>", [], [.nil, .bool, .int, .str, .cls 0 []], none, [], .call (.new 2 [] [.int 5]) "who" []⟩, []⟩

def assignY : Expr := .setField "y" (.var "w" [.int])

-- Its own field first, then `super`: P's `initialize` calls C's `who`,
-- which reads `@y`, already set.
#guard (superProg (.seq assignY (.superInit 1 [.int 2]))).check
#guard match run (superProg (.seq assignY (.superInit 1 [.int 2]))) noPrim 100 with
  | .ok (.int 5) _ => true | _ => false
-- After `super`, the object may be used.
#guard (superProg (.seq assignY (.seq (.superInit 1 [.int 2]) (.call .self "who" [])))).check
-- `super` before its own field, `self` before `super`, no `super` (the
-- inherited field never set), `super` into another class, or in a block:
-- all rejected.
#guard !(superProg (.seq (.superInit 1 [.int 2]) assignY)).check
#guard !(superProg (.seq assignY (.seq .self (.superInit 1 [.int 2])))).check
#guard !(superProg assignY).check
#guard !(superProg (.seq assignY (.superInit 0 []))).check
#guard !(superProg (.seq assignY (.callBlk .self "who" [] [] (.superInit 1 [.int 2])))).check
-- `super` twice is fine; in a loop, or after a `return` path, the
-- inherited field is not set at the end.
#guard (superProg (.seq assignY (.seq (.superInit 1 [.int 2]) (.superInit 1 [.int 3])))).check
#guard !(superProg (.seq assignY (.while (.prim "c" [] [] [.bool]) (.superInit 1 [.int 2])))).check
#guard !(superProg (.seq assignY (.seq (.ite (.prim "c" [] [] [.bool]) (.ret .nil) .nil)
  (.superInit 1 [.int 2])))).check

/-! ### Generics (G1a)

Box[T] with an immutable `@v : T`; IntBox < Box[Int], overriding `get`;
Pair[S, T], whose `swap` makes a `Pair[T, S]`. -/

def boxProg (body : Expr) (locals : List (String × Ty) := []) : Program :=
  ⟨[object,
    ⟨"Box", some 0, [⟨"v", [.param 0], false, none⟩], [.inv], [], []⟩,
    ⟨"IntBox", some 1, [], [], [[.int]], []⟩,
    ⟨"Pair", some 0, [⟨"a", [.param 0], false, none⟩, ⟨"b", [.param 1], false, none⟩], [.inv, .inv], [], []⟩],
   [⟨1, "get", [], [.param 0], none, [], .field "v" [.param 0]⟩,
    ⟨1, "initialize", [("v", [.param 0])], [.nil], none, [("v", [.param 0])],
      .setField "v" (.var "v" [.param 0])⟩,
    ⟨2, "get", [], [.int], none, [], .field "v" [.int]⟩,
    ⟨3, "swap", [], [.cls 3 [[.param 1], [.param 0]]], none, [],
      .new 3 [[.param 1], [.param 0]] [.field "b" [.param 1], .field "a" [.param 0]]⟩,
    ⟨3, "initialize", [("a", [.param 0]), ("b", [.param 1])], [.nil], none,
      [("a", [.param 0]), ("b", [.param 1])],
      .seq (.setField "a" (.var "a" [.param 0])) (.setField "b" (.var "b" [.param 1]))⟩],
   ⟨0, "<main>", [], [.nil, .bool, .int, .str, .cls 0 []], none, locals, body⟩, []⟩

-- `Box[Int].new(3).get` is an `Int`; `IntBox.new(4).get` runs the
-- override, reading the inherited field at `Int`.
#guard (boxProg (.call (.new 1 [[.int]] [.int 3]) "get" [])).check
#guard match run (boxProg (.call (.new 1 [[.int]] [.int 3]) "get" [])) noPrim 100 with
  | .ok (.int 3) _ => true | _ => false
#guard (boxProg (.call (.new 2 [] [.int 4]) "get" [])).check
#guard match run (boxProg (.call (.new 2 [] [.int 4]) "get" [])) noPrim 100 with
  | .ok (.int 4) _ => true | _ => false
-- `Pair[Int, Str].new(1, "a").swap.swap`: a `Pair[Int, Str]` again.
#guard (boxProg (.assign "p" (.call (.call (.new 3 [[.int], [.str]] [.int 1, .str "a"]) "swap" []) "swap" []))
  [("p", [.cls 3 [[.int], [.str]], .nil])]).check
#guard !(boxProg (.assign "p" (.call (.new 3 [[.int], [.str]] [.int 1, .str "a"]) "swap" []))
  [("p", [.cls 3 [[.int], [.str]], .nil])]).check
#guard match run (boxProg (.call (.call (.new 3 [[.int], [.str]] [.int 1, .str "a"]) "swap" []) "swap" []))
    noPrim 100 with
  | .ok (.obj _) _ => true | _ => false
-- Ill-typed arguments, the wrong number of type arguments, a `Str` box
-- where an `Int` one is declared: rejected.
#guard !(boxProg (.new 1 [[.int]] [.str "x"])).check
#guard !(boxProg (.new 1 [] [.int 1])).check
#guard (boxProg (.assign "b" (.new 1 [[.int]] [.int 1])) [("b", [.cls 1 [[.int]]])]).check
#guard !(boxProg (.assign "b" (.new 1 [[.str]] [.str "x"])) [("b", [.cls 1 [[.int]]])]).check
-- Invariant: an `IntBox` is a `Box[Int]`, not a `Box[Object]`.
#guard (boxProg (.assign "b" (.new 2 [] [.int 1])) [("b", [.cls 1 [[.int]]])]).check
#guard !(boxProg (.assign "b" (.new 2 [] [.int 1])) [("b", [.cls 1 [[.cls 0 []]]])]).check
-- `is_a?(Box[Int])` on an `Object` cannot be checked at run time; on a
-- `Box[Int]?` it can, as can `is_a?(IntBox)` on anything. (A local is
-- read only once assigned: here from a built-in call of its type.)
def withLocal (x : String) (t : Ty) (body : Expr) : Expr := .seq (.assign x (.prim "h" [] [] t)) body
#guard !(boxProg (withLocal "o" [.cls 0 []] (.isA (.var "o" [.cls 0 []]) (.cls 1 [[.int]])))
  [("o", [.cls 0 []])]).check
#guard (boxProg (withLocal "b" [.cls 1 [[.int]], .nil] (.isA (.var "b" [.cls 1 [[.int]], .nil]) (.cls 1 [[.int]])))
  [("b", [.cls 1 [[.int]], .nil])]).check
#guard (boxProg (withLocal "o" [.cls 0 []] (.isA (.var "o" [.cls 0 []]) (.cls 2 [])))
  [("o", [.cls 0 []])]).check
-- A local of the class's type narrowed by the test: an `IntBox` below
-- it; `Box` without its argument is no test.
#guard (boxProg (withLocal "b" [.cls 1 [[.int]], .nil] (.ite (.isA (.var "b" [.cls 1 [[.int]], .nil]) (.cls 2 []))
    (.call (.var "b" [.cls 2 []]) "get" []) .nil)) [("b", [.cls 1 [[.int]], .nil])]).check
#guard !(boxProg (withLocal "b" [.cls 1 [[.int]], .nil] (.isA (.var "b" [.cls 1 [[.int]], .nil]) (.cls 1 [])))
  [("b", [.cls 1 [[.int]], .nil])]).check

/-! ### Variance (G1b)

OBox[out T] with `@v : T` and `get`; Cell[T] (invariant) with
`var @v : T` and `set`; Sink[in T] with `put(x: T)`. -/

def varClasses : ClassTable :=
  [object,
   ⟨"OBox", some 0, [⟨"v", [.param 0], false, none⟩], [.co], [], []⟩,
   ⟨"Cell", some 0, [⟨"v", [.param 0], true, none⟩], [.inv], [], []⟩,
   ⟨"Sink", some 0, [], [.contra], [], []⟩]

def varProg (body : Expr) (locals : List (String × Ty) := []) (extra : List Method := []) : Program :=
  ⟨varClasses,
   [⟨1, "get", [], [.param 0], none, [], .field "v" [.param 0]⟩,
    ⟨1, "initialize", [("v", [.param 0])], [.nil], none, [("v", [.param 0])],
      .setField "v" (.var "v" [.param 0])⟩,
    ⟨2, "get", [], [.param 0], none, [], .field "v" [.param 0]⟩,
    ⟨2, "set", [("x", [.param 0])], [.param 0], none, [("x", [.param 0])],
      .seq (.setField "v" (.var "x" [.param 0])) (.var "x" [.param 0])⟩,
    ⟨2, "initialize", [("v", [.param 0])], [.nil], none, [("v", [.param 0])],
      .setField "v" (.var "v" [.param 0])⟩,
    ⟨3, "put", [("x", [.param 0])], [.nil], none, [("x", [.param 0])], .nil⟩] ++ extra,
   ⟨0, "<main>", [], [.nil, .bool, .int, .str, .cls 0 []], none, locals, body⟩, []⟩

-- Covariant: an `OBox[Int]` is an `OBox[Int?]` and an `OBox[Object]`;
-- what it gives is then an `Int?`.
#guard (varProg (.assign "b" (.new 1 [[.int]] [.int 1])) [("b", [.cls 1 [[.int, .nil]]])]).check
#guard (varProg (.assign "b" (.new 1 [[.int]] [.int 1])) [("b", [.cls 1 [[.cls 0 []]]])]).check
#guard (varProg (.seq (.assign "b" (.new 1 [[.int]] [.int 1])) (.assign "x" (.call (.var "b" [.cls 1 [[.int, .nil]]]) "get" [])))
  [("b", [.cls 1 [[.int, .nil]]]), ("x", [.int, .nil])]).check
#guard match run (varProg (.seq (.assign "b" (.new 1 [[.int]] [.int 1])) (.call (.var "b" [.cls 1 [[.int, .nil]]]) "get" []))
    [("b", [.cls 1 [[.int, .nil]]])]) noPrim 100 with
  | .ok (.int 1) _ => true | _ => false
-- but not the other way.
#guard !(varProg (.assign "b" (.new 1 [[.int, .nil]] [.int 1])) [("b", [.cls 1 [[.int]]])]).check
-- Invariant: a `Cell[Int]` is no `Cell[Object]` (its `set` would take a
-- `Str`), but a `Cell[Int | Nil]` is a `Cell[Nil | Int]`.
#guard !(varProg (.assign "c" (.new 2 [[.int]] [.int 1])) [("c", [.cls 2 [[.cls 0 []]]])]).check
#guard (varProg (.assign "c" (.new 2 [[.int, .nil]] [.int 1])) [("c", [.cls 2 [[.nil, .int]]])]).check
-- Contravariant: a `Sink[Object]` is a `Sink[Int]`, not the other way.
#guard (varProg (.assign "k" (.new 3 [[.cls 0 []]] [])) [("k", [.cls 3 [[.int]]])]).check
#guard !(varProg (.assign "k" (.new 3 [[.int]] [])) [("k", [.cls 3 [[.cls 0 []]]])]).check
-- The variance check: a covariant parameter taken by a method, or a
-- contravariant one given back, is rejected.
#guard !(varProg .nil [] [⟨1, "put", [("x", [.param 0])], [.nil], none, [("x", [.param 0])], .nil⟩]).check
#guard !(varProg .nil [] [⟨3, "back", [], [.param 0, .nil], none, [], .nil⟩]).check
-- `is_a?(OBox[Object])` holds of every `OBox`: checkable from `Object`;
-- `is_a?(Cell[Object])` is not.
#guard (varProg (withLocal "o" [.cls 0 []] (.isA (.var "o" [.cls 0 []]) (.cls 1 [[.cls 0 []]])))
  [("o", [.cls 0 []])]).check
#guard !(varProg (withLocal "o" [.cls 0 []] (.isA (.var "o" [.cls 0 []]) (.cls 2 [[.cls 0 []]])))
  [("o", [.cls 0 []])]).check
-- The model's range: a superclass's arguments take no arguments.
#guard !(Program.wfClasses ⟨varClasses ++ [⟨"Deep", some 1, [], [], [[.cls 1 [[.int]]]], []⟩],
  [], ⟨0, "<main>", [], [.nil], none, [], .nil⟩, []⟩)
#guard (Program.wfClasses ⟨varClasses ++ [⟨"IntOBox", some 1, [], [], [[.int, .nil]], []⟩],
  [], ⟨0, "<main>", [], [.nil], none, [], .nil⟩, []⟩)

/-! ### Bounds (G1c)

Shp with `@n : Int` and `sides -> Int`; Sq < Shp; Hold[T <: Shp] with
`@v : T`, `get -> T`, `shape -> Shp` (`@v` given back at the bound) and
`sides -> Int` (`@v.sides`, the bound's method). -/

def boundClasses : ClassTable :=
  [object,
   ⟨"Shp", some 0, [⟨"n", [.int], false, none⟩], [], [], []⟩,
   ⟨"Sq", some 1, [], [], [], []⟩,
   ⟨"Hold", some 0, [⟨"v", [.param 0], false, none⟩], [.inv], [], [[.cls 1 []]]⟩]

def boundProg (body : Expr) (locals : List (String × Ty) := []) (extra : List Method := []) : Program :=
  ⟨boundClasses,
   [⟨1, "initialize", [("n", [.int])], [.nil], none, [("n", [.int])], .setField "n" (.var "n" [.int])⟩,
    ⟨1, "sides", [], [.int], none, [], .int 0⟩,
    ⟨2, "sides", [], [.int], none, [], .int 4⟩,
    ⟨3, "initialize", [("v", [.param 0])], [.nil], none, [("v", [.param 0])],
      .setField "v" (.var "v" [.param 0])⟩,
    ⟨3, "get", [], [.param 0], none, [], .field "v" [.param 0]⟩,
    ⟨3, "shape", [], [.cls 1 []], none, [], .field "v" [.param 0]⟩,
    ⟨3, "sides", [], [.int], none, [], .call (.field "v" [.param 0]) "sides" []⟩] ++ extra,
   ⟨0, "<main>", [], [.nil, .bool, .int, .str, .cls 0 []], none, locals, body⟩, []⟩

-- `Hold[Sq].new(Sq.new(1)).sides` runs `Sq#sides` through the bound.
#guard (boundProg (.call (.new 3 [[.cls 2 []]] [.new 2 [] [.int 1]]) "sides" [])).check
#guard match run (boundProg (.call (.new 3 [[.cls 2 []]] [.new 2 [] [.int 1]]) "sides" [])) noPrim 100 with
  | .ok (.int 4) _ => true | _ => false
-- An argument outside the bound is rejected at `new`.
#guard !(boundProg (.new 3 [[.int]] [.int 1])).check
-- Without the bound, `@v.sides` and giving `@v` back as a `Shp` are not
-- allowed.
def unboundHold : Class := ⟨"Hold", some 0, [⟨"v", [.param 0], false, none⟩], [.inv], [], []⟩
#guard !(Program.check { boundProg .nil with classes := boundClasses.set 3 unboundHold })

end QuarzCore.Examples
