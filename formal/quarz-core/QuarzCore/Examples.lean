/-
Small programs, checked and run (`lake build` runs the `#guard`s).
-/

import QuarzCore.Program
import QuarzCore.Semantics

namespace QuarzCore.Examples

def object : Class := ⟨"Object", none, []⟩

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
def eqClass : Class := ⟨"E", some 0, []⟩

def eqMethod : Method :=
  ⟨1, "==", [("o", [.cls 0])], [.bool], none, [("o", [.cls 0])], .tru⟩

def equalNil (ann : Ty) : Program :=
  ⟨[object, eqClass], [eqMethod], ⟨0, "<main>", [], [.cls 1, .nil], none, [("c", [.cls 1, .nil])],
    .seq (.assign "c" (.new 1 []))
      (.ite (.eqNil (.var "c" [.cls 1, .nil])) (.var "c" ann) .nil)⟩, []⟩

#guard (equalNil [.cls 1, .nil]).check
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
  ⟨"P", some 0, [⟨"x", [.int], false, none⟩, ⟨"lbl", [.str], false, some 0⟩] ++ extra⟩

def initMethod (body : Expr) : Method :=
  ⟨1, "initialize", [("v", [.int])], [.nil], none, [("v", [.int])], body⟩

def getx : Method := ⟨1, "getx", [], [.int], none, [], .field "x" [.int]⟩

def setx : Method := ⟨1, "setx", [], [.int], none, [], .setField "x" (.int 1)⟩

def initProg (body : Expr) (main : Expr := .call (.new 1 [.int 3]) "getx" [])
    (extra : List Method := []) (fields : List Field := []) (defaults : List Expr := [.str "p"]) :
    Program :=
  ⟨[object, initClass fields], [initMethod body, getx] ++ extra,
    ⟨0, "<main>", [], [.nil, .bool, .int, .str, .cls 0], none, [], main⟩, defaults⟩

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
#guard !(initProg assignX (main := .call (.new 1 [.int 3]) "initialize" [.int 4])).check

end QuarzCore.Examples
