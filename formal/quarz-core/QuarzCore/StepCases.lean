/-
evalArgs, send, runBlock and equal with fuel `n + 1`, from the five
functions with fuel `n` (Good).
-/

import QuarzCore.EvalCases

set_option linter.deprecated false

namespace QuarzCore

variable {P : Program} {orc : Oracle}

theorem ArgsPost.extend_other {c : Ctx} {ao ao' : ArgsOut} {fr : Frame}
    {ws : List (Ctx × Env × Out)} {Λ Λ1 : List Ty} {s s1 : Store} {W1 W2 W : Nat → Prop}
    {r : Result} (h : ArgsPost P c ao fr ws Λ1 s1 W2 (.other r)) (he : Ext P W1 Λ Λ1 s s1)
    (hw : WfStore P Λ s) (h1 : ∀ l, W1 l → W l) (h2 : ∀ l, W2 l → W l) :
    ArgsPost P c ao' fr ws Λ s W (.other r) := by
  cases r with
  | ok => exact absurd h id
  | stuck => exact h
  | returned v s' =>
    obtain ⟨Λ', a, e, f, g, i⟩ := h
    exact ⟨Λ', a, (he.trans e hw).mono fun l hl => hl.elim (h1 l) (h2 l), f, g, i⟩
  | raised => trivial
  | timeout => trivial

theorem evalWs_cons_left {fr : Frame} {e : Expr} {es : List Expr} :
    ∀ l, evalW fr e l → evalWs fr (e :: es) l := by
  rintro l (⟨x, hx, hl⟩ | h)
  · exact .inl ⟨e, List.mem_cons_self .., x, hx, hl⟩
  · exact .inr h

theorem evalWs_cons_right {fr : Frame} {e : Expr} {es : List Expr} :
    ∀ l, evalWs fr es l → evalWs fr (e :: es) l := by
  rintro l (⟨e', he', h⟩ | h)
  · exact .inl ⟨e', List.mem_cons_of_mem _ he', h⟩
  · exact .inr h

/-- What `wfMethod` says of an `==`. -/
theorem Program.wfMethod_eq {mt : Method} (h : P.wfMethod mt = true) (hn : mt.name = "==") :
    mt.ret.le P.classes [.bool] = true ∧ mt.block = none ∧
      ∃ x t, mt.params = [(x, t)] ∧ Ty.le P.classes [.nil, .bool] t = true := by
  simp only [Program.wfMethod, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, hn,
    not_true_eq_false, false_or] at h
  obtain ⟨_, ⟨⟨hret, hblk⟩, hp⟩⟩ := h
  refine ⟨hret, by simpa using hblk, ?_⟩
  revert hp
  match mt.params with
  | [(x, t)] => exact fun hp => ⟨x, t, rfl, hp⟩
  | [] => simp
  | _ :: _ :: _ => simp

theorem SendPost.weaken {ret ret' : Ty} {sig : Option BlockSig} {blk : Option Closure}
    {ws : List (Ctx × Env × Out)} {Λ : List Ty} {s : Store} {r : Result}
    (hwf : WfClasses P.classes) (h : SendPost P ret sig blk ws Λ s r)
    (hle : ret.le P.classes ret' = true) : SendPost P ret' sig blk ws Λ s r := by
  cases r with
  | ok v s' =>
    obtain ⟨Λ', a, b, d, e⟩ := h
    exact ⟨Λ', a, b, hasTy_le hwf d hle, e⟩
  | stuck => exact h
  | returned => exact h
  | raised => trivial
  | timeout => trivial

variable (hP : WfProg P) (horc : OracleOK P orc) {n : Nat} (ih : Good P orc n)
include hP horc ih

theorem args_succ : ArgsGood P orc (n + 1) := by
  intro c Γ es ao fr s Λ ws hc ht hw hf hs
  subst hc
  cases ht with
  | nil => exact ⟨[], Γ, rfl, Λ, hw, Ext.refl _ Λ s, hf, hs, trivial⟩
  | cons he hout hes =>
    simp only [evalArgs]
    have := ih.eval _ _ _ _ fr s Λ ws rfl he hw hf hs
    revert this
    generalize eval c.prog orc n fr s _ = r
    intro this
    cases r with
    | ok v s1 =>
      dsimp only
      obtain ⟨Λ1, hw1, he1, hf1, hv1, ho1, _, _⟩ := this
      obtain ⟨Δ1, hΔ, hs1⟩ := ho1
      rw [hout] at hΔ; cases hΔ
      have := ih.args _ _ _ _ fr s1 Λ1 ws rfl hes hw1 hf1 hs1
      revert this
      generalize evalArgs c.prog orc n fr s1 _ = ar
      intro this
      cases ar with
      | ok vs s2 =>
        obtain ⟨tys', Δ2, hao, Λ2, hw2, he2, hf2, hs2, hvs⟩ := this
        cases hao
        exact ⟨_, _, rfl, Λ2, hw2, (he1.trans he2 hw).mono fun l hl =>
          hl.elim (evalWs_cons_left l) (evalWs_cons_right l), hf2, hs2, he2.hasTy hv1, hvs⟩
      | other r => exact this.extend_other he1 hw evalWs_cons_left evalWs_cons_right
    | returned v s1 =>
      obtain ⟨Λ1, a, e, f, g, i⟩ := this
      exact ⟨Λ1, a, e.mono evalWs_cons_left, f, g, i⟩
    | raised => trivial
    | timeout => trivial
    | stuck => exact this
  | consDead he hout =>
    simp only [evalArgs]
    have := ih.eval _ _ _ _ fr s Λ ws rfl he hw hf hs
    revert this
    generalize eval c.prog orc n fr s _ = r
    intro this
    cases r with
    | ok v s1 =>
      obtain ⟨_, _, _, _, _, ho1, _, _⟩ := this
      obtain ⟨_, hΔ, _⟩ := ho1
      rw [hout] at hΔ; cases hΔ
    | returned v s1 =>
      obtain ⟨Λ1, a, e, f, g, i⟩ := this
      exact ⟨Λ1, a, e.mono evalWs_cons_left, f, g, i⟩
    | raised => trivial
    | timeout => trivial
    | stuck => exact this
  | restDead he hout hes =>
    simp only [evalArgs]
    have := ih.eval _ _ _ _ fr s Λ ws rfl he hw hf hs
    revert this
    generalize eval c.prog orc n fr s _ = r
    intro this
    cases r with
    | ok v s1 =>
      dsimp only
      obtain ⟨Λ1, hw1, he1, hf1, hv1, ho1, _, _⟩ := this
      obtain ⟨Δ1, hΔ, hs1⟩ := ho1
      rw [hout] at hΔ; cases hΔ
      have := ih.args _ _ _ _ fr s1 Λ1 ws rfl hes hw1 hf1 hs1
      revert this
      generalize evalArgs c.prog orc n fr s1 _ = ar
      intro this
      cases ar with
      | ok vs s2 => obtain ⟨_, _, hao, _⟩ := this; cases hao
      | other r => exact this.extend_other he1 hw evalWs_cons_left evalWs_cons_right
    | returned v s1 =>
      obtain ⟨Λ1, a, e, f, g, i⟩ := this
      exact ⟨Λ1, a, e.mono evalWs_cons_left, f, g, i⟩
    | raised => trivial
    | timeout => trivial
    | stuck => exact this

end QuarzCore

namespace QuarzCore

variable {P : Program} {orc : Oracle}
variable (hP : WfProg P) (horc : OracleOK P orc) {n : Nat} (ih : Good P orc n)
include hP horc ih

theorem equal_succ : EqualGood P orc (n + 1) := by
  intro s Λ v w t hw hv hw'
  have hwf := hP.classes
  have hnone : BlkGiven P Λ s [] none none := ⟨trivial, fun l h => by simp [chainLocs] at h⟩
  have plain : ∀ b : Bool, SendPost P [.bool] none none [] Λ s (.ok (.bool b) s) :=
    fun b => ⟨Λ, hw, Ext.refl _ Λ s, hasTy_lit_bool, hnone⟩
  cases v with
  | obj l =>
    simp only [equal]
    cases ho : s.objs[l]? with
    | none => exact plain false
    | some o =>
      simp only [Option.bind_some]
      cases hl : P.lookup o.cls "==" with
      | none => exact plain false
      | some mt =>
        dsimp only
        obtain ⟨hmem, _, hname⟩ := Program.lookup_spec hl
        obtain ⟨hret, hblk, x, pt, hps, hpt⟩ :=
          Program.wfMethod_eq (hP.methods mt hmem).1 hname
        have hargs : AllTy P s [w] (mt.params.map (·.2)) := by
          rw [hps]
          refine ⟨?_, trivial⟩
          rcases hw' with rfl | rfl | rfl
          · exact hasTy_le hwf hasTy_lit_nil (Ty.le_trans hwf (Ty.le_append_left hwf [.nil] [.bool]) hpt)
          · exact hasTy_le hwf hasTy_lit_bool (Ty.le_trans hwf (Ty.le_append_right hwf [.nil] [.bool]) hpt)
          · exact hasTy_le hwf hasTy_lit_bool (Ty.le_trans hwf (Ty.le_append_right hwf [.nil] [.bool]) hpt)
        have := ih.send s Λ (.obj l) o.cls "==" mt [w] none [] hw
          ⟨l, o, rfl, ho, ClassTable.mem_ancestors_self hwf _⟩ hl hargs (by rw [hblk]; exact hnone)
        rw [hblk] at this
        exact this.weaken hwf hret
  | _ => exact plain _

end QuarzCore
