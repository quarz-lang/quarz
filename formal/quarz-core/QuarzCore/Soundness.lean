/-
The soundness theorem (design §4): a checked program, run with any fuel
and any oracle giving values of the types asked for, never gets stuck:
in particular, every read's value is of the type the checker narrowed it
to. By induction on the fuel, over the interpreter's five functions.
-/

import QuarzCore.StepCases
import QuarzCore.Check

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
  send := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ => by simp [send, SendPost]
  block := fun _ _ _ _ _ _ _ _ _ => by simp [runBlock, SendPost]
  equal := fun _ _ _ _ _ _ _ _ => by simp [equal, SendPost]

theorem good (hP : WfProg P) (horc : OracleOK P orc) : ∀ n, Good P orc n := by
  intro n
  induction n with
  | zero => exact good_zero P orc
  | succ n ih => exact ⟨eval_succ hP horc ih, args_succ hP horc ih, send_succ hP horc ih,
      block_succ hP horc ih, equal_succ hP horc ih⟩

variable {P orc}

theorem Program.checkMethod_typed {mt : Method} (h : P.checkMethod mt = true) :
    ∃ o, Typed ⟨P, mt, false⟩ (mt.params.map fun (x, t) => (.local x, t)) mt.body o ∧
      (o.out = none ∨ o.ty.le P.classes mt.ret = true) := by
  unfold Program.checkMethod at h
  dsimp only at h
  split at h
  · rename_i o ho
    refine ⟨o, check_typed ho, ?_⟩
    simp only [Bool.or_eq_true, Option.isNone_iff_eq_none] at h
    exact h
  · cases h

/-- What a checked program gives the soundness proof. -/
theorem Program.check_wf (h : P.check = true) :
    WfProg P ∧ P.main.owner < P.classes.length ∧ (P.classes.allFields P.main.owner).isEmpty ∧
      P.main.params = [] ∧ P.main.block = none ∧ P.wfMethod P.main = true ∧
      ∃ o, Typed ⟨P, P.main, false⟩ [] P.main.body o ∧
        (o.out = none ∨ o.ty.le P.classes P.main.ret = true) := by
  simp only [Program.check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.isEmpty_iff, Option.isNone_iff_eq_none] at h
  obtain ⟨⟨hc, ⟨⟨⟨hown, hf⟩, hp⟩, hb⟩⟩, hall⟩ := h
  have hm := hall P.main (List.mem_cons_self ..)
  obtain ⟨o, ho, hret⟩ := Program.checkMethod_typed hm.2
  rw [hp] at ho
  exact ⟨⟨Program.wfClasses_sound hc, fun mt hmt =>
      ⟨(hall mt (List.mem_cons_of_mem _ hmt)).1,
        Program.checkMethod_typed (hall mt (List.mem_cons_of_mem _ hmt)).2⟩⟩,
    hown, by simpa using hf, hp, hb, hm.1, o, ho, hret⟩

/-- **Soundness** (design §4): a checked program, run with any fuel and
any oracle giving values of the types asked for, never gets stuck. In
particular every read of a local or of an immutable field gives a value
of the type it is annotated with (`eval` checks it), which `check`
accepts only when it is at least what the rules narrow the path to there:
annotated with the types the Rust checker gave (conformance.sh), those
are what compiled code relies on. (Writes are not checked by `eval`: an
ill-typed write would show at its read.) -/
theorem run_sound (h : P.check = true) (horc : OracleOK P orc) (fuel : Nat) :
    run P orc fuel ≠ .stuck := by
  obtain ⟨hP, hown, hnf, hpar, hblk, hwfm, o, ho, _⟩ := Program.check_wf h
  have hwf := hP.classes
  simp only [List.isEmpty_iff] at hnf
  simp only [Program.wfMethod, Bool.and_eq_true, decide_eq_true_eq] at hwfm
  obtain ⟨⟨⟨⟨⟨_, _⟩, hnd⟩, _⟩, _⟩, _⟩ := hwfm
  -- The top level's frame: its locals at fresh locations, `self` an
  -- instance of its class.
  let s0 : Store := ⟨[], [⟨P.main.owner, []⟩]⟩
  let names := P.main.locals.map (·.1)
  let Λ := P.main.locals.map (·.2)
  have hw : WfStore P Λ (s0.alloc names).1 := ⟨by simp [Store.alloc, Λ, names, s0], fun l o ho => by
    have : (s0.alloc names).1.objs = [⟨P.main.owner, []⟩] := rfl
    rw [this] at ho
    cases l with
    | zero =>
      simp at ho; subst ho
      exact ⟨hown, by simp [hnf], fun i v f h1 _ => by simp at h1⟩
    | succ l => simp at ho⟩
  have hcl : ∀ x d, (⟨P, P.main, false⟩ : Ctx).decl x = some d →
      ∃ j, P.main.locals[j]? = some (x, d) := fun x d hd => by
    simp only [Ctx.decl, Option.map_eq_some_iff] at hd
    obtain ⟨⟨y, d'⟩, hf, hd'⟩ := hd
    simp at hd'; subst hd'
    have hp := List.find?_some hf
    simp at hp; subst hp
    exact List.mem_iff_getElem?.mp (List.mem_of_find?_eq_some hf)
  have hcore : FrameCore P ⟨P, P.main, false⟩ Λ (s0.alloc names).2 (.obj 0) (s0.alloc names).1 := by
    refine ⟨fun x d hd => ?_, fun x y l hx hy => ?_, fun x l hm => ?_, ?_, ⟨0, rfl⟩⟩
    · obtain ⟨j, hj⟩ := hcl x d hd
      refine ⟨j, by simpa [Store.alloc, s0] using lookupVar_alloc (base := 0) hnd (by simp [names, hj]), ?_⟩
      simp [Λ, hj]
    · obtain ⟨jx, hjx, rfl⟩ := lookupVar_alloc_inv hx
      obtain ⟨jy, hjy, hjj⟩ := lookupVar_alloc_inv hy
      have : jx = jy := by omega
      subst this; rw [hjx] at hjy; cases hjy; rfl
    · have := mem_allocVars hm; simp [Store.alloc, s0, names] at this ⊢; omega
    · exact hasTy_iff.mpr ⟨.cls P.main.owner, by simp [Store.typeOf, Store.alloc, s0],
        .cls P.main.owner, List.mem_singleton.mpr rfl, Atom.le_refl hwf _⟩
  have hf : FrameOK P ⟨P, P.main, false⟩ Λ ⟨(s0.alloc names).2, .obj 0, none⟩ (s0.alloc names).1 [] :=
    ⟨hcore, by simp [hblk, ChainAt], fun _ _ _ h => by simp [chainLocs] at h,
      fun _ h => by simp [chainLocs] at h⟩
  have hs : Sat P ⟨P, P.main, false⟩ [] ⟨(s0.alloc names).2, .obj 0, none⟩ (s0.alloc names).1 :=
    fun _ _ h => by simp [Env.get] at h
  have := (good P orc hP horc fuel).eval ⟨P, P.main, false⟩ [] P.main.body o _ _ Λ [] rfl ho hw hf hs
  have key : ∀ r : Result, Post P ⟨P, P.main, false⟩ o ⟨(s0.alloc names).2, .obj 0, none⟩ [] Λ
      (s0.alloc names).1 (evalW ⟨(s0.alloc names).2, .obj 0, none⟩ P.main.body) r →
      (match r with
        | .returned v s => Result.ok v s
        | r => r) ≠ .stuck := by
    intro r hr
    cases r <;> simp_all [Post]
  exact key _ this

end QuarzCore
