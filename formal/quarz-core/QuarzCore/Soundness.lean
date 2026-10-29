/-
The soundness theorem (design §4): a checked program, run with any fuel
and any oracle giving values of the types asked for, never gets stuck:
in particular, every read's value is of the type the checker narrowed it
to, and no field is read before it is set (an object's immutable fields
only after its defaults or `initialize` assigned them). By induction on the fuel, over
the interpreter's functions.
-/

import QuarzCore.ConstructCases
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
      exact ⟨[], Γ, rfl, Λ, hw, Ext.refl _ _ Λ s, hf, hs, trivial⟩
    | cons e es => simp [evalArgs, ArgsPost]
  send := by unfold SendGood; intros; simp [send, SendPost]
  block := by unfold BlockGood; intros; simp [runBlock, SendPost]
  equal := by unfold EqualGood; intros; simp [equal, SendPost]
  construct := by unfold ConstructGood; intros; simp [construct, ConstructPost]

/-- By induction on the fuel, for all fuel up to it (the defaults run
with less and less of it). -/
theorem good (hP : WfProg P) (horc : OracleOK P orc) : ∀ n, Good P orc n := by
  have : ∀ n, ∀ m, m ≤ n → Good P orc m := by
    intro n
    induction n with
    | zero => intro m hm; rw [Nat.le_zero.mp hm]; exact good_zero P orc
    | succ n ih =>
      intro m hm
      rcases Nat.lt_or_eq_of_le hm with hm | rfl
      · exact ih m (by omega)
      · have ihn := ih n (Nat.le_refl n)
        exact ⟨eval_succ hP horc ihn, args_succ hP horc ihn, send_succ hP horc ihn,
          block_succ hP horc ihn, equal_succ hP horc ihn, construct_succ hP ih⟩
  exact fun n => this n n (Nat.le_refl n)

variable {P orc}

theorem Program.checkMethod_typed {mt : Method} (h : P.checkMethod mt = true) :
    ∃ o, Typed ⟨P, mt, false, false⟩ (mt.params.map (fun (x, t) => (.local x, t)) ++
        (if mt.name == "initialize" then Program.heldEnv P.classes (Ctx.fields ⟨P, mt, false, false⟩) else []))
      mt.body o ∧
      (mt.name ≠ "initialize" → o.out = none ∨ o.ty.le P.classes mt.ret = true) ∧
      (mt.name = "initialize" → o.out.all (Ctx.allSet ⟨P, mt, false, false⟩ ·) = true) := by
  unfold Program.checkMethod at h
  dsimp only at h
  split at h
  · rename_i o ho
    refine ⟨o, check_typed ho, ?_⟩
    simp only [Bool.and_eq_true, Bool.or_eq_true, Option.isNone_iff_eq_none, Bool.not_eq_true',
      Ctx.inInit, beq_iff_eq] at h
    refine ⟨fun hn => ?_, fun hn => ?_⟩
    · rcases h.1 with (h1 | h1) | h1
      · exact absurd h1 hn
      · exact .inl h1
      · exact .inr h1
    rcases h.2 with h2 | h2
    · simp [hn] at h2
    · exact h2
  · cases h

/-- The defaults, as `checkDefaults` checks them. -/
theorem Program.checkDefaults_typed {k : Nat} (h : P.checkDefaults k = true) :
    ∀ j f d, (P.classes.allFieldsAt k (P.classes.selfArgs k))[j]? = some f → f.default = some d →
      ∃ e o, P.defaults[d]? = some e ∧
      Typed (P.defaultCtx k f.ty)
        (Program.heldEnv P.classes ((P.classes.allFieldsAt k (P.classes.selfArgs k)).take j)) e o ∧
      o.ty.le P.classes f.ty = true := by
  intro j f d hf hd
  unfold Program.checkDefaults at h
  have := List.all_eq_true.mp h (f, j) (List.mem_zipIdx_iff_getElem?.mpr hf)
  simp only [hd] at this
  split at this
  · rename_i e he
    split at this
    · rename_i o ho
      exact ⟨e, o, he, check_typed ho, this⟩
    · cases this
  · cases this

/-- What a checked program gives the soundness proof. -/
theorem Program.check_wf (h : P.check = true) :
    WfProg P ∧ P.main.owner < P.classes.length ∧ (P.classes.allFields P.main.owner).isEmpty ∧
      (((P.classes[P.main.owner]?).map (·.params)).getD []) = [] ∧
      P.main.params = [] ∧ P.main.block = none ∧ P.wfMethod P.main = true ∧
      ∃ o, Typed ⟨P, P.main, false, false⟩ [] P.main.body o ∧
        (P.main.name ≠ "initialize" → o.out = none ∨ o.ty.le P.classes P.main.ret = true) := by
  simp only [Program.check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.isEmpty_iff, Option.isNone_iff_eq_none, List.mem_range] at h
  obtain ⟨⟨⟨hc, ⟨⟨⟨⟨hown, hf⟩, hmp⟩, hp⟩, hb⟩⟩, hall⟩, hcls⟩ := h
  have hm := hall P.main (List.mem_cons_self ..)
  obtain ⟨o, ho, hret, _⟩ := Program.checkMethod_typed hm.2
  rw [hp] at ho
  have hfields : Ctx.fields ⟨P, P.main, false, false⟩ = [] := by
    apply List.eq_nil_of_length_eq_zero
    show (P.classes.allFieldsAt P.main.owner _).length = 0
    rw [ClassTable.allFieldsAt_length, hf]; rfl
  rw [hfields] at ho
  simp [Program.heldEnv] at ho
  exact ⟨⟨Program.wfClasses_sound hc, fun mt hmt =>
      ⟨(hall mt (List.mem_cons_of_mem _ hmt)).1,
        Program.checkMethod_typed (hall mt (List.mem_cons_of_mem _ hmt)).2⟩,
      fun k hk => (hcls k hk).1.1, fun k hk => Program.checkDefaults_typed (hcls k hk).1.2⟩,
    hown, by simpa using hf, hmp, hp, hb, hm.1, o, ho, hret⟩

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
  obtain ⟨hP, hown, hnf, hmp, hpar, hblk, hwfm, o, ho, _⟩ := Program.check_wf h
  have hwf := hP.classes
  simp only [List.isEmpty_iff] at hnf
  simp only [Program.wfMethod, Bool.and_eq_true, decide_eq_true_eq] at hwfm
  obtain ⟨⟨⟨⟨⟨_, _⟩, hnd⟩, _⟩, _⟩, _⟩ := hwfm
  -- The top level's frame: its locals at fresh locations, `self` an
  -- instance of its class (without parameters: the frame's arguments
  -- are none).
  let s0 : Store := ⟨[], [⟨P.main.owner, [], [], []⟩]⟩
  let names := P.main.locals.map (·.1)
  let Λ := P.main.locals.map fun x => x.2.subst []
  have hw : WfStore P Λ (s0.alloc names).1 := ⟨by simp [Store.alloc, Λ, names, s0], fun l o ho => by
    have : (s0.alloc names).1.objs = [⟨P.main.owner, [], [], []⟩] := rfl
    rw [this] at ho
    cases l with
    | zero =>
      simp at ho; subst ho
      exact ⟨hown, rfl, by simp [hmp], by simp [hnf], rfl, fun i v f h1 _ => by simp at h1⟩
    | succ l => simp at ho⟩
  have hcl : ∀ x d, (⟨P, P.main, false, false⟩ : Ctx).decl x = some d →
      ∃ j, P.main.locals[j]? = some (x, d) := fun x d hd => by
    simp only [Ctx.decl, Option.map_eq_some_iff] at hd
    obtain ⟨⟨y, d'⟩, hf, hd'⟩ := hd
    simp at hd'; subst hd'
    have hp := List.find?_some hf
    simp at hp; subst hp
    exact List.mem_iff_getElem?.mp (List.mem_of_find?_eq_some hf)
  have hcore : FrameCore P ⟨P, P.main, false, false⟩ Λ (s0.alloc names).2 (.obj 0) []
      (s0.alloc names).1 := by
    refine ⟨fun x d hd => ?_, fun x y l hx hy => ?_, fun x l hm => ?_, fun _ => ?_,
      fun _ => ⟨0, ⟨P.main.owner, [], [], []⟩, rfl, rfl, ClassTable.mem_ancestors_self hwf _,
        fun i _ h => by simp at h, fun i f hf _ _ => by
          have := (List.getElem?_eq_some_iff.mp hf).1
          rw [ClassTable.allFieldsAt_length] at this
          simp [hnf] at this⟩,
      ⟨0, rfl, by simp [Store.argsFor, Store.alloc, s0, ClassTable.ancestorArgs_self hwf]⟩, rfl⟩
    · obtain ⟨j, hj⟩ := hcl x d hd
      refine ⟨j, by simpa [Store.alloc, s0] using lookupVar_alloc (base := 0) hnd (by simp [names, hj]), ?_⟩
      simp [Λ, hj]
    · obtain ⟨jx, hjx, rfl⟩ := lookupVar_alloc_inv hx
      obtain ⟨jy, hjy, hjj⟩ := lookupVar_alloc_inv hy
      have : jx = jy := by omega
      subst this; rw [hjx] at hjy; cases hjy; rfl
    · have := mem_allocVars hm; simp [Store.alloc, s0, names] at this ⊢; omega
    · exact hasTy_iff.mpr ⟨.cls P.main.owner [], typeOf_obj_of (o := ⟨P.main.owner, [], [], []⟩) rfl rfl,
        .cls P.main.owner [], List.mem_singleton.mpr rfl, Atom.le_refl hwf _⟩
  have hf : FrameOK P ⟨P, P.main, false, false⟩ Λ ⟨(s0.alloc names).2, .obj 0, [], none⟩
      (s0.alloc names).1 [] :=
    ⟨hcore, by simp [hblk, ChainAt], fun _ _ _ h => by simp [chainLocs] at h,
      fun _ h => by simp [chainLocs] at h, fun _ _ => rfl⟩
  have hs : Sat P ⟨P, P.main, false, false⟩ [] ⟨(s0.alloc names).2, .obj 0, [], none⟩ (s0.alloc names).1 :=
    fun _ _ h => by simp [Env.get] at h
  have := (good P orc hP horc fuel).eval ⟨P, P.main, false, false⟩ [] P.main.body o _ _ Λ [] rfl ho hw hf hs
  have key : ∀ r : Result, Post P ⟨P, P.main, false, false⟩ o ⟨(s0.alloc names).2, .obj 0, [], none⟩ [] Λ
      (s0.alloc names).1 (evalW ⟨(s0.alloc names).2, .obj 0, [], none⟩ P.main.body) r →
      (match r with
        | .returned v s => Result.ok v s
        | r => r) ≠ .stuck := by
    intro r hr
    cases r <;> simp_all [Post]
  exact key _ this

end QuarzCore
