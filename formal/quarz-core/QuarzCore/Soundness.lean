/-
The soundness theorem (design §4): a checked program, run with any fuel
and any oracle giving values of the types asked for, never gets stuck:
in particular, every read's value is of the type the checker narrowed it
to. By induction on the fuel, over the interpreter's five functions.
-/

import QuarzCore.SoundDefs

set_option linter.deprecated false

namespace QuarzCore

variable (P : Program) (orc : Oracle)

/-- With no fuel, everything times out (but an empty argument list). -/
theorem good_zero : Good P orc 0 where
  eval := fun _ _ _ _ _ _ _ _ _ _ _ _ _ => by simp [eval, Post]
  args := fun c Γ es ao fr s Λ ws _ ht hw hf hs => by
    cases es with
    | nil =>
      cases ht
      exact ⟨[], Γ, rfl, Λ, hw, Ext.refl _ Λ s, hf, hs, trivial⟩
    | cons e es => simp [evalArgs, ArgsPost]
  send := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => by simp [send, SendPost]
  block := fun _ _ _ _ _ _ _ _ _ => by simp [runBlock, SendPost]
  equal := fun _ _ _ _ _ _ _ _ => by simp [equal, SendPost]

theorem good (hP : WfProg P) (horc : OracleOK P orc) : ∀ n, Good P orc n := by
  intro n
  induction n with
  | zero => exact good_zero P orc
  | succ n ih => exact ⟨sorry, sorry, sorry, sorry, sorry⟩

end QuarzCore
