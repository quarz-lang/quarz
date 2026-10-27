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
    .seq (.assign "x" .nil) (.ite (.var "x" [.int, .nil]) (.var "x" [.int]) (.int 0))⟩⟩

#guard narrowed.check
#guard match run narrowed noPrim 100 with | .ok (.int 0) _ => true | _ => false

/-- The same read, but not narrowed: annotating it `Int` is rejected. -/
def unnarrowed : Program :=
  ⟨[object], [], ⟨0, "<main>", [], [.int, .nil], none, [("x", [.int, .nil])],
    .seq (.assign "x" .nil) (.var "x" [.int])⟩⟩

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
      (.ite (.eqNil (.var "c" [.cls 1, .nil])) (.var "c" ann) .nil)⟩⟩

#guard (equalNil [.cls 1, .nil]).check
#guard !(equalNil [.nil]).check
#guard match run (equalNil [.nil]) noPrim 100 with | .stuck => true | _ => false

/-- A loop un-narrows what it assigns: `x` may be `nil` again at the
test (docs/02 §6). -/
def loop (ann : Ty) : Program :=
  ⟨[object], [], ⟨0, "<main>", [], [.nil], none, [("x", [.int, .nil])],
    .seq (.assign "x" (.int 1))
      (.while (.var "x" ann) (.assign "x" .nil))⟩⟩

#guard (loop [.int, .nil]).check
#guard !(loop [.int]).check

end QuarzCore.Examples
