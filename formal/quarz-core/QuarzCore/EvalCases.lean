/-
`eval` with fuel `n + 1`, from the five functions with fuel `n` (Good):
case by case, as `Typed` derives the expression.
-/

import QuarzCore.SoundDefs

set_option linter.deprecated false

namespace QuarzCore

variable {P : Program} {orc : Oracle}

/-! ### Values and the tests' types -/

theorem hasTy_lit_nil {s : Store} : s.hasTy P .nil [.nil] := by
  simp [Store.hasTy, Store.hasType, Store.typeOf, Ty.le, Atom.le]
theorem hasTy_lit_bool {s : Store} {b : Bool} : s.hasTy P (.bool b) [.bool] := by
  simp [Store.hasTy, Store.hasType, Store.typeOf, Ty.le, Atom.le]
theorem hasTy_lit_int {s : Store} {k : Int} : s.hasTy P (.int k) [.int] := by
  simp [Store.hasTy, Store.hasType, Store.typeOf, Ty.le, Atom.le]
theorem hasTy_lit_str {s : Store} {k : String} : s.hasTy P (.str k) [.str] := by
  simp [Store.hasTy, Store.hasType, Store.typeOf, Ty.le, Atom.le]

theorem ne_nil_of_hasTy {s : Store} {v : Value} {t : Ty} (h : s.hasTy P v t) : t ≠ [] := by
  rintro rfl; exact not_hasTy_nil h

theorem narrow_eq (Γ : Env) (p : Path) {t : Ty} (h : t ≠ []) : narrow Γ p t = some (Γ.set p t) := by
  simp [narrow, List.isEmpty_iff, h]

/-- A truthy value of `u` is of `u` without `nil`. -/
theorem hasTy_truthy {s : Store} {v : Value} {u : Ty} (h : s.hasTy P v u) (ht : v.truthy = true) :
    s.hasTy P v (truthyTy u) := by
  rw [hasTy_iff] at *
  obtain ⟨a, ha, b, hb, hab⟩ := h
  refine ⟨a, ha, b, ?_, hab⟩
  unfold truthyTy Ty.remove
  refine List.mem_filter.mpr ⟨hb, ?_⟩
  -- Only `nil` is below `nil`, and `nil` is not truthy.
  cases b <;> simp
  cases a <;> simp_all [Atom.le]
  cases v <;> simp_all [Store.typeOf, Value.truthy]

/-- A falsy value of `u` is `nil` or `false`, which `u` holds. -/
theorem hasTy_falsy {s : Store} {v : Value} {u : Ty} (h : s.hasTy P v u) (hf : v.truthy = false) :
    s.hasTy P v (falsyTy P.classes u) := by
  have hv : v = .nil ∨ v = .bool false := by
    cases v with
    | nil => exact .inl rfl
    | bool b => cases b <;> simp_all [Value.truthy]
    | _ => simp [Value.truthy] at hf
  rw [hasTy_iff] at h
  obtain ⟨a, ha, b, hb, hab⟩ := h
  rcases hv with rfl | rfl
  · simp [Store.typeOf] at ha; subst ha
    refine hasTy_iff.mpr ⟨.nil, rfl, .nil, ?_, by simp [Atom.le]⟩
    simp [falsyTy, Ty.le]; exact ⟨b, hb, hab⟩
  · simp [Store.typeOf] at ha; subst ha
    refine hasTy_iff.mpr ⟨.bool, rfl, .bool, ?_, by simp [Atom.le]⟩
    simp [falsyTy, Ty.le]; exact ⟨b, hb, hab⟩

/-- An expression giving a value and telling nothing. -/
theorem post_plain {c : Ctx} {Γ : Env} {fr : Frame} {Λ : List Ty} {s : Store} {W : Nat → Prop}
    {v : Value} {t : Ty} (hw : WfStore P Λ s) (hf : FrameOK P c Λ fr s) (hs : Sat P c Γ fr s)
    (hv : s.hasTy P v t) : Post P c (.plain t Γ) fr Λ s W (.ok v s) :=
  ⟨Λ, hw, Ext.refl _ Λ s, hf, hv, ⟨Γ, rfl, hs⟩, fun _ => ⟨Γ, rfl, hs⟩, fun _ => ⟨Γ, rfl, hs⟩⟩

theorem evalW_mono {fr : Frame} {e e' : Expr} (h : ∀ x ∈ e.assigned, x ∈ e'.assigned) :
    ∀ l, evalW fr e l → evalW fr e' l := by
  rintro l (⟨x, hx, hl⟩ | hb)
  · exact .inl ⟨x, h x hx, hl⟩
  · exact .inr hb

theorem OutOK.join_left (hwf : WfClasses P.classes) {c : Ctx} {g h : Option Env} {fr : Frame}
    {s : Store} (hg : OutOK P c g fr s) : OutOK P c (ojoin g h) fr s := by
  obtain ⟨Γ, rfl, hs⟩ := hg
  cases h with
  | none => exact ⟨Γ, rfl, hs⟩
  | some Δ => exact ⟨_, rfl, hs.join_left hwf⟩

theorem OutOK.join_right (hwf : WfClasses P.classes) {c : Ctx} {g h : Option Env} {fr : Frame}
    {s : Store} (hh : OutOK P c h fr s) : OutOK P c (ojoin g h) fr s := by
  obtain ⟨Δ, rfl, hs⟩ := hh
  cases g with
  | none => exact ⟨Δ, rfl, hs⟩
  | some Γ => exact ⟨_, rfl, hs.join_right hwf⟩

/-- A `Post` for a wider `Out`. -/
theorem Post.weaken {c : Ctx} {o o' : Out} {fr : Frame} {Λ : List Ty} {s : Store}
    {W : Nat → Prop} {r : Result} (h : Post P c o fr Λ s W r)
    (hty : ∀ (s : Store) (v : Value), s.hasTy P v o.ty → s.hasTy P v o'.ty)
    (hout : ∀ s : Store, OutOK P c o.out fr s → OutOK P c o'.out fr s)
    (htt : ∀ s : Store, OutOK P c o.tt fr s → OutOK P c o'.tt fr s)
    (hff : ∀ s : Store, OutOK P c o.ff fr s → OutOK P c o'.ff fr s) : Post P c o' fr Λ s W r := by
  cases r with
  | ok v s' =>
    obtain ⟨Λ', a, e, f, g, i, j, k⟩ := h
    exact ⟨Λ', a, e, f, hty _ _ g, hout _ i, fun x => htt _ (j x), fun x => hff _ (k x)⟩
  | returned => exact h
  | raised => trivial
  | timeout => trivial
  | stuck => exact h

/-- Assigning `x`: it holds the value, the other paths what they held. -/
theorem Sat.assign {c : Ctx} {Δ : Env} {fr : Frame} {Λ : List Ty} {s : Store} {x : String}
    {l : Nat} {d t : Ty} {v : Value} (hs : Sat P c Δ fr s) (hcore : FrameCore P c Λ fr.vars fr.self s)
    (hl : lookupVar fr.vars x = some l) (hd : c.decl x = some d) (hlen : l < s.locs.length)
    (hvt : s.hasTy P v t) (hvd : s.hasTy P v d) :
    Sat P c (Δ.set (.local x) t) fr (s.setLoc l v) := by
  intro p u hp
  rw [Env.get_set] at hp
  split at hp
  · rename_i hpx; subst hpx; cases hp
    exact ⟨l, v, d, hl, by simp [Store.setLoc, hlen], hd, hvt, hvd⟩
  · rename_i hpx
    cases p with
    | «local» y =>
      obtain ⟨ly, w, dy, h1, h2, h3, h4, h5⟩ := hs _ _ hp
      have hne : ly ≠ l := fun e => hpx (by rw [hcore.inj y x l (e ▸ h1) hl])
      exact ⟨ly, w, dy, h1, by simpa [Store.setLoc, List.getElem?_set_ne (Ne.symm hne)] using h2,
        h3, h4, h5⟩
    | field f =>
      obtain ⟨lo, o, fd, i, w, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hs _ _ hp
      exact ⟨lo, o, fd, i, w, h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- A write to the frame's own locals misses the blocks below it. -/
theorem FrameOK.own_not_chain {c : Ctx} {Λ : List Ty} {fr : Frame} {s : Store} (hf : FrameOK P c Λ fr s)
    {x : String} {l : Nat} (hl : lookupVar fr.vars x = some l) : ∀ l', chainLocs fr.blk l' → ¬ l' = l := by
  rintro l' hc rfl
  exact Nat.lt_irrefl _ (hf.above _ _ ⟨x, lookupVar_mem hl⟩ hc)

variable (hP : WfProg P) (horc : OracleOK P orc) {n : Nat} (ih : Good P orc n)
include hP horc ih

theorem eval_succ : EvalGood P orc (n + 1) := by
  intro c Γ e o fr s Λ hc ht hw hf hs
  subst hc
  have hwf := hP.classes
  cases ht with
  | nil => exact post_plain hw hf hs hasTy_lit_nil
  | tru => exact post_plain hw hf hs hasTy_lit_bool
  | fls => exact post_plain hw hf hs hasTy_lit_bool
  | int => exact post_plain hw hf hs hasTy_lit_int
  | str => exact post_plain hw hf hs hasTy_lit_str
  | self => exact post_plain hw hf hs hf.core.self
  | raise => trivial
  | var hu hle =>
    obtain ⟨l, v, d, hl, hv, hd, hvu, hvd⟩ := hs _ _ hu
    have hvt := hasTy_le hwf hvu hle
    simp only [eval, hl, Option.bind_some, hv]
    simp only [Store.hasTy] at hvt
    rw [if_pos hvt]
    refine ⟨Λ, hw, Ext.refl _ Λ s, hf, hvt, ⟨Γ, rfl, hs⟩, fun htr => ?_, fun hfa => ?_⟩
    · have h1 := hasTy_truthy hvu htr
      exact ⟨_, narrow_eq Γ _ (ne_nil_of_hasTy h1), hs.set ⟨l, v, d, hl, hv, hd, h1, hvd⟩⟩
    · have h1 := hasTy_falsy hvu hfa
      exact ⟨_, narrow_eq Γ _ (ne_nil_of_hasTy h1), hs.set ⟨l, v, d, hl, hv, hd, h1, hvd⟩⟩
  | seq ha hout hb =>
    simp only [eval]
    refine (ih.eval _ _ _ _ fr s Λ rfl ha hw hf hs).bind
      (evalW_mono (by simp [Expr.assigned]; intros; simp_all)) ?_
    intro v s1 Λ1 hw1 he1 hf1 _ ho1 _ _
    obtain ⟨Δ', hΔ, hs1⟩ := ho1
    rw [hout] at hΔ; cases hΔ
    exact (ih.eval _ _ _ _ fr s1 Λ1 rfl hb hw1 hf1 hs1).extend he1 hw
      (evalW_mono (by simp [Expr.assigned]; intros; simp_all))
      (evalW_mono (by simp [Expr.assigned]; intros; simp_all))
  | seqDead ha hout =>
    simp only [eval]
    refine (ih.eval _ _ _ _ fr s Λ rfl ha hw hf hs).bind
      (evalW_mono (by simp [Expr.assigned]; intros; simp_all)) ?_
    intro v s1 Λ1 _ _ _ _ ho1 _ _
    obtain ⟨_, hΔ, _⟩ := ho1
    rw [hout] at hΔ; cases hΔ
  | ret hib he hle =>
    simp only [eval]
    have := ih.eval _ _ _ _ fr s Λ rfl he hw hf hs
    revert this
    generalize eval c.prog orc n fr s _ = r
    intro this
    cases r with
    | ok v s1 =>
      obtain ⟨Λ1, a, b, d, g, _⟩ := this
      exact ⟨Λ1, a, b.mono (evalW_mono (by simp [Expr.assigned])), d, hasTy_le hwf g hle, hib⟩
    | returned v s1 =>
      obtain ⟨Λ1, a, b, d, g, i⟩ := this
      exact ⟨Λ1, a, b.mono (evalW_mono (by simp [Expr.assigned])), d, g, i⟩
    | raised => trivial
    | timeout => trivial
    | stuck => exact this
  | not ha =>
    simp only [eval]
    refine (ih.eval _ _ _ _ fr s Λ rfl ha hw hf hs).bind
      (evalW_mono (by simp [Expr.assigned])) ?_
    intro v s1 Λ1 hw1 he1 hf1 _ ho1 htt hff
    refine ⟨Λ1, hw1, he1.mono (evalW_mono (by simp [Expr.assigned])), hf1, hasTy_lit_bool, ho1,
      fun h => ?_, fun h => ?_⟩
    · cases hv : v.truthy <;> simp_all [Value.truthy]
    · cases hv : v.truthy <;> simp_all [Value.truthy]
  | @ite _ _ cnd oc t ot e oe hc hbt hbe =>
    simp only [eval]
    refine (ih.eval _ _ _ _ fr s Λ rfl hc hw hf hs).bind
      (evalW_mono (by simp [Expr.assigned]; intros; simp_all)) ?_
    intro v s1 Λ1 hw1 he1 hf1 _ _ htt hff
    cases hv : v.truthy
    · rw [if_neg (by simp)]
      obtain ⟨Δ, hΔ, hs1⟩ := hff hv
      rw [hΔ] at hbe
      cases hbe with
      | live he =>
        refine ((ih.eval _ _ _ _ fr s1 Λ1 rfl he hw1 hf1 hs1).extend he1 hw
          (evalW_mono (by simp [Expr.assigned]; intros; simp_all))
          (evalW_mono (by simp [Expr.assigned]; intros; simp_all))).weaken
          (fun _ _ h => hasTy_append_right hwf _ h) (fun _ h => h.join_right hwf)
          (fun _ h => h.join_right hwf) (fun _ h => h.join_right hwf)
    · rw [if_pos rfl]
      obtain ⟨Δ, hΔ, hs1⟩ := htt hv
      rw [hΔ] at hbt
      cases hbt with
      | live ht' =>
        refine ((ih.eval _ _ _ _ fr s1 Λ1 rfl ht' hw1 hf1 hs1).extend he1 hw
          (evalW_mono (by simp [Expr.assigned]; intros; simp_all))
          (evalW_mono (by simp [Expr.assigned]; intros; simp_all))).weaken
          (fun _ _ h => hasTy_append_left hwf _ h) (fun _ h => h.join_left hwf)
          (fun _ h => h.join_left hwf) (fun _ h => h.join_left hwf)
  | @and _ _ a oa b ob ha hbb =>
    simp only [eval]
    refine (ih.eval _ _ _ _ fr s Λ rfl ha hw hf hs).bind
      (evalW_mono (by simp [Expr.assigned]; intros; simp_all)) ?_
    intro v s1 Λ1 hw1 he1 hf1 hv1 _ htt hff
    cases hv : v.truthy
    · rw [if_neg (by simp)]
      have hfo := hff hv
      exact ⟨Λ1, hw1, he1.mono (evalW_mono (by simp [Expr.assigned]; intros; simp_all)), hf1,
        hasTy_append_left hwf _ hv1, hfo.join_left hwf, fun h => absurd (hv.symm.trans h) (by simp),
        fun _ => hfo.join_left hwf⟩
    · rw [if_pos rfl]
      obtain ⟨Δ, hΔ, hs1⟩ := htt hv
      rw [hΔ] at hbb
      cases hbb with
      | live hb =>
        refine ((ih.eval _ _ _ _ fr s1 Λ1 rfl hb hw1 hf1 hs1).extend he1 hw
          (evalW_mono (by simp [Expr.assigned]; intros; simp_all))
          (evalW_mono (by simp [Expr.assigned]; intros; simp_all))).weaken
          (fun _ _ h => hasTy_append_right hwf _ h) (fun _ h => h.join_right hwf)
          (fun _ h => h) (fun _ h => h.join_right hwf)
  | @or _ _ a oa b ob ha hbb =>
    simp only [eval]
    refine (ih.eval _ _ _ _ fr s Λ rfl ha hw hf hs).bind
      (evalW_mono (by simp [Expr.assigned]; intros; simp_all)) ?_
    intro v s1 Λ1 hw1 he1 hf1 hv1 _ htt hff
    cases hv : v.truthy
    · rw [if_neg (by simp)]
      obtain ⟨Δ, hΔ, hs1⟩ := hff hv
      rw [hΔ] at hbb
      cases hbb with
      | live hb =>
        refine ((ih.eval _ _ _ _ fr s1 Λ1 rfl hb hw1 hf1 hs1).extend he1 hw
          (evalW_mono (by simp [Expr.assigned]; intros; simp_all))
          (evalW_mono (by simp [Expr.assigned]; intros; simp_all))).weaken
          (fun _ _ h => hasTy_append_right hwf _ h) (fun _ h => h.join_right hwf)
          (fun _ h => h.join_right hwf) (fun _ h => h)
    · rw [if_pos rfl]
      have hto := htt hv
      exact ⟨Λ1, hw1, he1.mono (evalW_mono (by simp [Expr.assigned]; intros; simp_all)), hf1,
        hasTy_append_left hwf _ hv1, hto.join_left hwf, fun _ => hto.join_left hwf,
        fun h => absurd (hv.symm.trans h) (by simp)⟩
  | whileNever h0 hc htt =>
    simp only [eval]
    subst h0
    refine (ih.eval _ _ _ _ fr s Λ rfl hc hw hf hs.reset).bind
      (evalW_mono (by simp [Expr.assigned]; intros; simp_all)) ?_
    intro v s1 Λ1 hw1 he1 hf1 _ _ hvt hvf
    cases hv : v.truthy
    · rw [if_neg (by simp)]
      have := hvf hv
      exact ⟨Λ1, hw1, he1.mono (evalW_mono (by simp [Expr.assigned]; intros; simp_all)), hf1,
        hasTy_lit_nil, this, fun _ => this, fun _ => this⟩
    · obtain ⟨_, h, _⟩ := hvt hv; rw [htt] at h; cases h
  | «while» h0 hc htt hb himp =>
    simp only [eval]
    subst h0
    have hTy := Typed.while (Ctx.reset_idem _ _ _) hc htt hb himp
    refine (ih.eval _ _ _ _ fr s Λ rfl hc hw hf hs.reset).bind
      (evalW_mono (by simp [Expr.assigned]; intros; simp_all)) ?_
    intro v s1 Λ1 hw1 he1 hf1 _ _ hvt hvf
    cases hv : v.truthy
    · rw [if_neg (by simp)]
      have := hvf hv
      exact ⟨Λ1, hw1, he1.mono (evalW_mono (by simp [Expr.assigned]; intros; simp_all)), hf1,
        hasTy_lit_nil, this, fun _ => this, fun _ => this⟩
    · rw [if_pos rfl]
      obtain ⟨Δ', hΔ, hs1⟩ := hvt hv
      rw [htt] at hΔ; cases hΔ
      refine ((ih.eval _ _ _ _ fr s1 Λ1 rfl hb hw1 hf1 hs1).bind
        (evalW_mono (by simp [Expr.assigned]; intros; simp_all)) ?_).extend he1 hw
        (evalW_mono (by simp [Expr.assigned]; intros; simp_all)) (fun _ h => h)
      intro _ s2 Λ2 hw2 he2 hf2 _ ho2 _ _
      obtain ⟨Γb, hΓb, hs2⟩ := ho2
      have hs0 := hs2.implies hwf (by rw [hΓb] at himp; simpa [Ctx.ct] using himp)
      exact (ih.eval _ _ _ _ fr s2 Λ2 rfl hTy hw2 hf2 hs0).extend he2 hw1
        (evalW_mono (by simp [Expr.assigned]; intros; simp_all)) (fun _ h => h)
  | assign he hd hle hout =>
    rename_i e o' x d Δ
    simp only [eval]
    refine (ih.eval _ _ _ _ fr s Λ rfl he hw hf hs).bind
      (evalW_mono (by simp [Expr.assigned]; intros; simp_all)) ?_
    intro v s1 Λ1 hw1 he1 hf1 hv1 ho1 _ _
    obtain ⟨Δ', hΔ, hs1⟩ := ho1
    rw [hout] at hΔ; cases hΔ
    obtain ⟨l, hl, hΛ⟩ := hf1.core.decls x d hd
    have hlen := hf1.core.inStore x l (lookupVar_mem hl)
    simp only [hl]
    have hvd := hasTy_le hwf hv1 hle
    have he2 : Ext c.prog (fun l' => l' = l) Λ1 Λ1 s1 (s1.setLoc l v) :=
      Ext.setLoc hlen hΛ hvd rfl
    refine ⟨Λ1, hw1.setLoc l v, (he1.trans he2 hw).mono ?_, hf1.stable he2 (hf1.own_not_chain hl),
      hv1, ⟨_, rfl, hs1.assign hf1.core hl hd hlen hv1 hvd⟩, fun _ => ⟨_, rfl,
      hs1.assign hf1.core hl hd hlen hv1 hvd⟩, fun _ => ⟨_, rfl, hs1.assign hf1.core hl hd hlen hv1 hvd⟩⟩
    rintro l' (h | rfl)
    · exact evalW_mono (by simp [Expr.assigned]; intros; simp_all) l' h
    · exact .inl ⟨x, by simp [Expr.assigned], hl⟩
  | assignDead he hd hle hout =>
    simp only [eval]
    refine (ih.eval _ _ _ _ fr s Λ rfl he hw hf hs).bind
      (evalW_mono (by simp [Expr.assigned]; intros; simp_all)) ?_
    intro v s1 Λ1 _ _ _ _ ho1 _ _
    obtain ⟨_, hΔ, _⟩ := ho1
    rw [hout] at hΔ; cases hΔ
  | _ => sorry

end QuarzCore
