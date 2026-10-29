/-
`eval` with fuel `n + 1`, from the six functions with fuel `n` (Good):
case by case, as `Typed` derives the expression.
-/

import QuarzCore.FrameLemmas
import QuarzCore.TestLemmas

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

theorem hasTy_lit_flt {s : Store} {k : String} : s.hasTy P (.flt k) [.float] := by
  simp [Store.hasTy, Store.hasType, Store.typeOf, Ty.le, Atom.le]

theorem ne_nil_of_hasTy {s : Store} {v : Value} {t : Ty} (h : s.hasTy P v t) : t ≠ [] := by
  rintro rfl; exact not_hasTy_nil h

theorem narrow_eq (Γ : Env) (p : Path) {t : Ty} (h : t ≠ []) : narrow Γ p t = some (Γ.set p t) := by
  simp [narrow, List.isEmpty_iff, h]

/-- A type whose substitution has an atom has one. -/
theorem Ty.ne_nil_of_subst {σ : List Ty} {t : Ty} (h : Ty.subst σ t ≠ []) : t ≠ [] := by
  rintro rfl; exact h rfl

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
  cases v with
  | obj l => obtain ⟨_, _, _, h⟩ := typeOf_obj ha; cases h
  | proc i => obtain ⟨_, _, h⟩ := typeOf_proc ha; cases h
  | _ => simp_all [Store.typeOf, Value.truthy]

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
    simp [falsyTy, Ty.le]; exact Or.inr ⟨b, hb, hab⟩
  · simp [Store.typeOf] at ha; subst ha
    refine hasTy_iff.mpr ⟨.bool, rfl, .bool, ?_, by simp [Atom.le]⟩
    simp [falsyTy, Ty.le]; exact Or.inr ⟨b, hb, hab⟩

/-- An expression giving a value and telling nothing. -/
theorem post_plain {c : Ctx} {Γ : Env} {fr : Frame} {Λ : List Ty} {s : Store} {W : Nat → Prop}
    {v : Value} {t : Ty} (hw : WfStore P Λ s) {ws : List (Ctx × Env × Out)} (hf : FrameOK P c Λ fr s ws) (hs : Sat P c Γ fr s)
    (hv : s.hasTy P v (t.subst fr.selfArgs)) : Post P c (.plain t Γ) fr ws Λ s W (.ok v s) :=
  ⟨Λ, hw, Ext.refl _ _ Λ s, hf, hv, ⟨Γ, rfl, hs⟩, fun _ => ⟨Γ, rfl, hs⟩, fun _ => ⟨Γ, rfl, hs⟩⟩

theorem truthy_bool (b : Bool) : (Value.bool b).truthy = b := by cases b <;> rfl

theorem frameW_left {vars : List (String × Nat)} {xs ys : List String} {l : Nat}
    (h : frameW vars xs l) : frameW vars (xs ++ ys) l := by
  obtain ⟨x, hx, hl⟩ := h; exact ⟨x, List.mem_append_left _ hx, hl⟩

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

/-- `new`: what the arguments' evaluation left, after the object is made. -/
theorem Post.ofConstruct {c : Ctx} {Δ : Env} {fr : Frame} {ws : List (Ctx × Env × Out)}
    {Λ Λ1 : List Ty} {s s1 : Store} {W : Nat → Prop} {k : Nat} {targs : List Ty} {r : Result}
    (hc : c.prog = P)
    (h : ConstructPost P k (Ty.substArgs fr.selfArgs targs) Λ1 s1 r)
    (he1 : Ext P W (initW c fr) Λ Λ1 s s1) (hw : WfStore P Λ s)
    (hf1 : FrameOK P c Λ1 fr s1 ws) (hs1 : Sat P c Δ fr s1) :
    Post P c (.plain [.cls k targs] (c.afterCall Δ)) fr ws Λ s W r := by
  subst hc
  cases r with
  | ok v s2 =>
    obtain ⟨Λ2, hw2, he2, hv⟩ := h
    have hs2 := (hs1.reset (xs := c.pinned) : Sat _ c (c.afterCall Δ) fr s1).stable he2 (fun _ _ h => h)
      (fun _ _ h => h) hf1.core (pinsDecl_reset fun _ h => h)
    exact ⟨Λ2, hw2, (he1.transF he2 hw).monoW (fun l h => h.elim id False.elim),
      hf1.stable he2 (fun _ _ h => h) (fun _ h => h.elim), by simpa [Out.plain] using hv, ⟨_, rfl, hs2⟩,
      fun _ => ⟨_, rfl, hs2⟩, fun _ => ⟨_, rfl, hs2⟩⟩
  | stuck => exact h.elim
  | returned => exact h.elim
  | raised v s2 =>
    obtain ⟨Λ2, hw2, he2, hv⟩ := h
    exact ⟨Λ2, hw2, (he1.transF he2 hw).monoW (fun l h => h.elim id False.elim),
      hf1.stable he2 (fun _ _ h => h) (fun _ h => h.elim), hv⟩
  | timeout => trivial

/-- A `Post` for a wider `Out`. -/
theorem Post.weaken {c : Ctx} {o o' : Out} {fr : Frame} {ws : List (Ctx × Env × Out)} {Λ : List Ty}
    {s : Store} {W : Nat → Prop} {r : Result} (h : Post P c o fr ws Λ s W r)
    (hty : ∀ (s : Store) (v : Value), s.hasTy P v (o.ty.subst fr.selfArgs) →
      s.hasTy P v (o'.ty.subst fr.selfArgs))
    (hout : ∀ s : Store, OutOK P c o.out fr s → OutOK P c o'.out fr s)
    (htt : ∀ s : Store, OutOK P c o.tt fr s → OutOK P c o'.tt fr s)
    (hff : ∀ s : Store, OutOK P c o.ff fr s → OutOK P c o'.ff fr s) : Post P c o' fr ws Λ s W r := by
  cases r with
  | ok v s' =>
    obtain ⟨Λ', a, e, f, g, i, j, k⟩ := h
    exact ⟨Λ', a, e, f, hty _ _ g, hout _ i, fun x => htt _ (j x), fun x => hff _ (k x)⟩
  | returned => exact h
  | raised => trivial
  | timeout => trivial
  | stuck => exact h

theorem Env.set_set (Γ : Env) (p : Path) (t t' : Ty) : (Γ.set p t).set p t' = Γ.set p t' := by
  simp [Env.set, List.filter_filter]

/-- Assigning `x`: it holds the value, the other paths what they held. -/
theorem Sat.assign {c : Ctx} {Δ : Env} {fr : Frame} {Λ : List Ty} {s : Store} {x : String}
    {l : Nat} {d t : Ty} {v : Value} (hs : Sat P c Δ fr s)
    (hcore : FrameCore P c Λ fr.vars fr.self fr.selfArgs s)
    (hl : lookupVar fr.vars x = some l) (hd : c.decl x = some d) (hlen : l < s.locs.length)
    (hvt : s.hasTy P v (t.subst fr.selfArgs)) (hvd : s.hasTy P v (d.subst fr.selfArgs)) :
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
      obtain ⟨lo, o, fd, i, h1, h2, h3, h4, h5, h6, h7⟩ := hs _ _ hp
      exact ⟨lo, o, fd, i, h1, h2, h3, h4, h5, h6, h7⟩

/-- The un-narrowed environment of what `xs` names holds after writes of
values of their declared types to those locals only. -/
theorem Sat.reset_typed {c : Ctx} {Δ : Env} {xs : List String} {fr : Frame} {Λ Λ' : List Ty}
    {s s' : Store} {W : Nat → Prop} (hs : Sat P c (c.reset Δ xs) fr s)
    (hcore : FrameCore P c Λ fr.vars fr.self fr.selfArgs s) (he : Ext P W (fun _ => False) Λ Λ' s s')
    (hW : ∀ l, W l → frameLocs fr.vars l → frameW fr.vars xs l) (hpx : ∀ x ∈ c.pinned, x ∈ xs) :
    Sat P c (c.reset Δ xs) fr s' := by
  intro p t hp
  cases p with
  | field f =>
    obtain ⟨l, o, fd, i, h1, h2, h3, h4, h5, h6, h7⟩ := hs _ _ hp
    obtain ⟨o', ho', hc, ha, _, hs'⟩ := he.grow l o h2
    refine ⟨l, o', fd, i, h1, ho', h3, by rw [hc]; exact h4, by rw [hc, ha]; exact h5, hs' i h6,
      fun hv => ?_⟩
    obtain ⟨v, h8, h9⟩ := h7 hv
    obtain ⟨d, f0, _, hf0, hf⟩ := ClassTable.allFieldsAt_some P.classes h5
    have hv0 : f0.var = false := by have := congrArg Field.var hf; simpa [hv] using this.symm
    exact ⟨v, by rw [he.imm l o o' h2 ho' id i f0 hf0 hv0]; exact h8, he.hasTy h9⟩
  | «local» x =>
    obtain ⟨l, v, d, h1, h2, h3, h4, h5⟩ := hs _ _ hp
    obtain ⟨v', hv', hch⟩ := he.locs l v h2
    rcases hch with rfl | ⟨hwl, t', ht', hty⟩
    · exact ⟨l, _, d, h1, hv', h3, he.hasTy h4, he.hasTy h5⟩
    · obtain ⟨y, hy, hyl⟩ : frameW fr.vars xs l := hwl.elim (fun h => hW l h ⟨x, lookupVar_mem h1⟩)
        fun hpn => ⟨x, hpx x ((hcore.pins x l h1).mp hpn), h1⟩
      have hyx := hcore.inj y x l hyl h1
      subst hyx
      obtain ⟨u, _, hif⟩ := Ctx.reset_get_local hp
      rw [if_pos hy, h3] at hif
      cases hif
      obtain ⟨l', hl', hΛ⟩ := hcore.decls y _ h3
      rw [h1] at hl'; cases hl'
      rw [hΛ] at ht'; cases ht'
      exact ⟨l, v', _, h1, hv', h3, hty, hty⟩

/-- What `takeFrom` has for a path: `Δe`'s type for a local in `xs`, `Δ`'s
for the rest. -/
theorem Env.get_takeFrom {Δe : Env} {xs : List String} {p : Path} {t : Ty} :
    ∀ {Δ : Env}, (Δ.takeFrom Δe xs).get p = some t →
      (∃ x, p = .local x ∧ x ∈ xs ∧ Δe.get p = some t) ∨
      ((∀ x, p = .local x → x ∉ xs) ∧ Δ.get p = some t)
  | [], h => by simp [Env.takeFrom, Env.get] at h
  | (q, u) :: Δ, h => by
    have ih := @Env.get_takeFrom Δe xs p t Δ
    simp only [Env.takeFrom, List.filterMap_cons] at h
    have rest : Env.get (Env.takeFrom Δ Δe xs) p = some t → ¬ (q = p) →
        (∃ x, p = .local x ∧ x ∈ xs ∧ Env.get Δe p = some t) ∨
        ((∀ x, p = .local x → x ∉ xs) ∧ Env.get ((q, u) :: Δ) p = some t) := fun h hq => by
      rcases ih h with h' | ⟨hn, h'⟩
      · exact .inl h'
      · exact .inr ⟨hn, by simp [Env.get, hq, h']⟩
    cases q with
    | field f =>
      simp only [Env.get] at h
      by_cases hq : Path.field f = p
      · rw [if_pos hq] at h; cases h; subst hq
        exact .inr ⟨fun x hx => (by cases hx), by simp [Env.get]⟩
      · rw [if_neg hq] at h; exact rest h hq
    | «local» y =>
      by_cases hy : y ∈ xs
      · simp only [if_pos hy] at h
        cases hg : Δe.get (.local y) with
        | none =>
          rw [hg] at h; simp only [Option.map_none] at h
          rcases ih h with h' | ⟨hn, h'⟩
          · exact .inl h'
          · exact .inr ⟨hn, by simp [Env.get, h', show ¬ Path.local y = p from by rintro rfl; exact hn y rfl hy]⟩
        | some w =>
          rw [hg] at h; simp only [Option.map_some, Env.get] at h
          by_cases hq : Path.local y = p
          · rw [if_pos hq] at h; cases h; subst hq
            exact .inl ⟨y, rfl, hy, hg⟩
          · rw [if_neg hq] at h; exact rest h hq
      · simp only [if_neg hy, Env.get] at h
        by_cases hq : Path.local y = p
        · rw [if_pos hq] at h; cases h; subst hq
          exact .inr ⟨fun x hx => (by cases hx; exact hy), by simp [Env.get]⟩
        · rw [if_neg hq] at h; exact rest h hq

/-- After `ensure` (writing only the locals `xs` of the frame): its end's
types for them, what held before for the rest. -/
theorem Sat.takeFrom {c : Ctx} {Δ Δe : Env} {xs : List String} {fr : Frame} {Λ Λ' : List Ty}
    {s s' : Store} {W : Nat → Prop} (hs : Sat P c Δ fr s)
    (hcore : FrameCore P c Λ fr.vars fr.self fr.selfArgs s) (he : Ext P W (fun _ => False) Λ Λ' s s')
    (hW : ∀ l, W l → frameLocs fr.vars l → frameW fr.vars xs l) (hpx : ∀ x ∈ c.pinned, x ∈ xs)
    (hse : Sat P c Δe fr s') :
    Sat P c (Δ.takeFrom Δe xs) fr s' := by
  intro p t hp
  rcases Env.get_takeFrom hp with ⟨x, rfl, _, h⟩ | ⟨hn, h⟩
  · exact hse _ _ h
  · cases p with
    | field f =>
      obtain ⟨l, o, fd, i, h1, h2, h3, h4, h5, h6, h7⟩ := hs _ _ h
      obtain ⟨o', ho', hc, ha, _, hs'⟩ := he.grow l o h2
      refine ⟨l, o', fd, i, h1, ho', h3, by rw [hc]; exact h4, by rw [hc, ha]; exact h5, hs' i h6,
        fun hv => ?_⟩
      obtain ⟨v, h8, h9⟩ := h7 hv
      obtain ⟨d, f0, _, hf0, hf⟩ := ClassTable.allFieldsAt_some P.classes h5
      have hv0 : f0.var = false := by have := congrArg Field.var hf; simpa [hv] using this.symm
      exact ⟨v, by rw [he.imm l o o' h2 ho' id i f0 hf0 hv0]; exact h8, he.hasTy h9⟩
    | «local» x =>
      obtain ⟨l, v, d, h1, h2, h3, h4, h5⟩ := hs _ _ h
      obtain ⟨v', hv', hch⟩ := he.locs l v h2
      rcases hch with rfl | ⟨hwl, _, _, _⟩
      · exact ⟨l, _, d, h1, hv', h3, he.hasTy h4, he.hasTy h5⟩
      · obtain ⟨y, hy, hyl⟩ : frameW fr.vars xs l := hwl.elim (fun h => hW l h ⟨x, lookupVar_mem h1⟩)
          fun hpn => ⟨x, hpx x ((hcore.pins x l h1).mp hpn), h1⟩
        have hyx := hcore.inj y x l hyl h1
        subst hyx
        exact absurd hy (hn y rfl)

/-- A write to the frame's own locals misses the blocks below it. -/
theorem FrameOK.own_not_chain {c : Ctx} {Λ : List Ty} {fr : Frame} {s : Store} {ws : List (Ctx × Env × Out)} (hf : FrameOK P c Λ fr s ws)
    {x : String} {l : Nat} (hl : lookupVar fr.vars x = some l) : ∀ l', chainLocs fr.blk l' → ¬ l' = l := by
  rintro l' hc rfl
  exact Nat.lt_irrefl _ (hf.above _ _ ⟨x, lookupVar_mem hl⟩ hc)

/-- The arguments did not all give values: what the call gives. -/
theorem ArgsPost.other {c : Ctx} {ao : ArgsOut} {fr : Frame} {ws : List (Ctx × Env × Out)}
    {Λ : List Ty} {s : Store} {W W' : Nat → Prop} {r : Result} {o : Out}
    (h : ArgsPost P c ao fr ws Λ s W (.other r)) (hW : ∀ l, W l → W' l) : Post P c o fr ws Λ s W' r := by
  cases r with
  | ok => exact absurd h id
  | stuck => exact h
  | returned v s' =>
    obtain ⟨Λ', a, e, f, g, i⟩ := h
    exact ⟨Λ', a, e.mono hW (fun _ h => h), f, g, i⟩
  | raised v s' =>
    obtain ⟨Λ', a, e, f, g⟩ := h
    exact ⟨Λ', a, e.mono hW (fun _ h => h), f, g⟩
  | timeout => trivial

theorem mem_assignedArgs {es : List Expr} {e : Expr} {x : String} (he : e ∈ es)
    (hx : x ∈ e.assigned) : x ∈ Expr.assigned.assignedArgs es := by
  induction es with
  | nil => cases he
  | cons e' es ih =>
    simp only [Expr.assigned.assignedArgs, List.mem_append]
    rcases List.mem_cons.mp he with rfl | he
    · exact .inl hx
    · exact .inr (ih he)

theorem evalWs_mono {fr : Frame} {es : List Expr} {e : Expr}
    (h : ∀ x, x ∈ Expr.assigned.assignedArgs es → x ∈ e.assigned) :
    ∀ l, evalWs fr es l → evalW fr e l := by
  rintro l (⟨e', he', x, hx, hl⟩ | hb)
  · exact .inl ⟨x, h x (mem_assignedArgs he' hx), hl⟩
  · exact .inr hb

theorem AllTy.length {s : Store} : ∀ {vs : List Value} {ts : List Ty}, AllTy P s vs ts →
    vs.length = ts.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, ⟨_, h⟩ => by simp [AllTy.length h]

theorem AllTy.get {s : Store} : ∀ {vs : List Value} {ts : List Ty}, AllTy P s vs ts →
    ∀ (i : Nat) (v : Value) (t : Ty), vs[i]? = some v → ts[i]? = some t → s.hasTy P v t
  | [], [], _, _, _, _, h, _ => by simp at h
  | v :: vs, t :: ts, ⟨h1, h2⟩, 0, w, u, hv, ht => by simp at hv ht; subst hv ht; exact h1
  | v :: vs, t :: ts, ⟨_, h2⟩, i + 1, w, u, hv, ht => AllTy.get h2 i w u (by simpa using hv)
      (by simpa using ht)

theorem AllTy.mono {s s' : Store} (h : ObjsGrow s s') (hp : s.procs <+: s'.procs)
    (hb : s.builts <+: s'.builts) :
    ∀ {vs : List Value} {ts : List Ty}, AllTy P s vs ts → AllTy P s' vs ts
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨h1, h2⟩ => ⟨hasTy_mono h hp hb h1, AllTy.mono h hp hb h2⟩

theorem objs_append_mono {s : Store} (o : Obj) : ObjsGrow s { s with objs := s.objs ++ [o] } :=
  fun l o' h => ⟨o', by
    show (s.objs ++ [o])[l]? = some o'
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]; exact h, rfl, rfl, rfl,
    fun _ h => h⟩

/-- `self`: an object of the method's class or a subclass, the frame's
`selfArgs` what it gives the method's owner. -/
theorem self_obj (hwf : WfClasses P.classes) {c : Ctx} {Λ : List Ty} {fr : Frame} {s : Store}
    (hc : c.prog = P) {ws : List (Ctx × Env × Out)} (hf : FrameOK P c Λ fr s ws)
    (hw : WfStore P Λ s) :
    ∃ l o, fr.self = .obj l ∧ s.objs[l]? = some o ∧ c.meth.owner ∈ P.classes.ancestors o.cls ∧
      fr.selfArgs = s.argsFor P.classes l c.meth.owner := by
  subst hc
  obtain ⟨l, hl, hsa⟩ := hf.core.selfObj
  cases hi : c.inInit
  · have hself := hf.core.self hi
    rw [hl, hasTy_iff] at hself
    obtain ⟨a, ha, b, hb, hab⟩ := hself
    obtain ⟨o, ho, _, rfl⟩ := typeOf_obj ha
    simp at hb; subst hb
    refine ⟨l, o, hl, ho, ?_, hsa⟩
    rw [Atom.le_cls_iff hwf] at hab
    rcases hab with ⟨h0, _⟩ | ⟨_, hab, _⟩
    · rw [h0]; exact ClassTable.root_mem_ancestors hwf _ (hw.objs l o ho).1
    · exact ClassTable.ancestorArgs_mem hwf _ _ _ _ hab
  · obtain ⟨l', o, h1, h2, h3, _⟩ := hf.core.selfInit hi
    rw [hl] at h1; cases h1
    exact ⟨l, o, hl, h2, h3, hsa⟩

/-- `self`'s type as the body names it, with the frame's `selfArgs`: the
owner given those arguments (as many as its parameters). -/
theorem selfTy_subst (hwf : WfClasses P.classes) {c : Ctx} {Λ : List Ty} {fr : Frame} {s : Store}
    (hc : c.prog = P) {ws : List (Ctx × Env × Out)} (hf : FrameOK P c Λ fr s ws)
    (hw : WfStore P Λ s) : Ty.subst fr.selfArgs c.selfTy = [.cls c.meth.owner fr.selfArgs] := by
  obtain ⟨l, o, hl, ho, hsub, hsa⟩ := self_obj hwf hc hf hw
  subst hc
  obtain ⟨_, _, hlen, _, _, _⟩ := hw.objs l o ho
  obtain ⟨σ, hσ⟩ := ClassTable.ancestorArgs_of_mem hwf o.cls o.args c.meth.owner hsub
  have hsa' : fr.selfArgs = σ := by rw [hsa]; simp [Store.argsFor, ho, hσ]
  have hσl := ClassTable.ancestorArgs_length hwf o.cls o.args c.meth.owner σ hσ hlen
  simp only [Ctx.selfTy, Ty.subst_cons, Ty.subst_nil, Atom.subst_cls, List.append_nil, Ctx.selfArgs,
    Ctx.ct]
  rw [hsa', substArgs_selfArgs c.prog.classes hσl]

/-- Outside `initialize`, `self` is made: every field set. -/
theorem self_made {c : Ctx} {Λ : List Ty} {fr : Frame} {s : Store} {ws : List (Ctx × Env × Out)}
    (hf : FrameOK P c Λ fr s ws) (hi : c.inInit = false) {l : Nat} {o : Obj}
    (hl : fr.self = .obj l) (ho : s.objs[l]? = some o) : o.set.all id = true := by
  have hself := hf.core.self hi
  rw [hl, hasTy_iff] at hself
  obtain ⟨a, ha, _⟩ := hself
  obtain ⟨o', ho', hall, _⟩ := typeOf_obj ha
  rw [ho] at ho'; cases ho'; exact hall

/-- A field of `self`, as the method's class sees it: where the object
has it, and as the object's class sees it (its type with the frame's
`selfArgs` substituted). -/
theorem self_field (hwf : WfClasses P.classes) {c : Ctx} {Λ : List Ty} {fr : Frame} {s : Store}
    (hc : c.prog = P) {ws : List (Ctx × Env × Out)} (hf : FrameOK P c Λ fr s ws) (hw : WfStore P Λ s) {f : String} {fd : Field}
    (hfd : c.field? f = some fd) :
    ∃ l o i, fr.self = .obj l ∧ s.objs[l]? = some o ∧ fieldIndex P.classes o.cls f = some i ∧
      (P.classes.allFieldsAt o.cls o.args)[i]? = some { fd with ty := fd.ty.subst fr.selfArgs } ∧
      (∃ fd0, (P.classes.allFields o.cls)[i]? = some fd0 ∧ fd0.var = fd.var) ∧
      i < o.fields.length ∧ i < o.set.length := by
  obtain ⟨l, o, hl, ho, hsub, hsa⟩ := self_obj hwf hc hf hw
  subst hc
  obtain ⟨i, hi, hfi, fd0, hfo, _, _, hvar, _⟩ := fieldAt_in_subclass hwf hsub hfd
  obtain ⟨_, _, hlen', hlen, hslen, _⟩ := hw.objs l o ho
  obtain ⟨σ, hσ⟩ := ClassTable.ancestorArgs_of_mem hwf o.cls o.args c.meth.owner hsub
  have hsa' : fr.selfArgs = σ := by rw [hsa]; simp [Store.argsFor, ho, hσ]
  have hil : i < o.fields.length := by rw [hlen]; exact (List.getElem?_eq_some_iff.mp hfo).1
  refine ⟨l, o, i, hl, ho, hi, ?_, ⟨fd0, hfo, hvar⟩, hil, hslen ▸ hil⟩
  rw [hsa']
  exact fieldAt_coherent hwf hlen' hσ hfi

/-- `self` may be used (in `initialize`, once every field is set): it is
of the method's class. -/
theorem self_typed (hwf : WfClasses P.classes) {c : Ctx} {Γ : Env} {Λ : List Ty} {fr : Frame}
    {s : Store} {ws : List (Ctx × Env × Out)} (hc : c.prog = P) (hf : FrameOK P c Λ fr s ws)
    (hw : WfStore P Λ s) (hs : Sat P c Γ fr s) (ha : (!c.inInit || c.allSet Γ) = true) :
    s.hasTy P fr.self [.cls c.meth.owner fr.selfArgs] := by
  subst hc
  cases hi : c.inInit
  · exact hf.core.self hi
  · rw [hi] at ha; simp only [Bool.not_true, Bool.false_or] at ha
    obtain ⟨l, o, hl, ho, hsub, hbeyond, _⟩ := hf.core.selfInit hi
    obtain ⟨l', hl', hsa⟩ := hf.core.selfObj
    rw [hl] at hl'; cases hl'
    obtain ⟨hcls, _, _, _, _, _⟩ := hw.objs l o ho
    have hall : o.set.all id = true := all_id_iff.mpr fun i hi' => by
      by_cases hlt : i < (c.ct.allFields c.meth.owner).length
      · have hlt' : i < c.fields.length := by
          rwa [Ctx.fields, ClassTable.allFieldsAt_length]
        have hfi : c.fields[i]? = some c.fields[i] := by simp [hlt']
        unfold Ctx.allSet at ha
        have := List.all_eq_true.mp ha _ (List.getElem_mem hlt')
        obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp this
        obtain ⟨l', o', fd, j, h1, h2, _, h4, _, h6, _⟩ := hs _ _ ht
        rw [hl] at h1; cases h1; rw [ho] at h2; cases h2
        obtain ⟨d, f0, _, hf0, hff⟩ := ClassTable.allFieldsAt_some c.prog.classes hfi
        obtain ⟨rest, hr⟩ := allFields_prefix hwf hsub
        simp only [Ctx.ct] at hlt
        have hfi' : (c.prog.classes.allFields o.cls)[i]? = some f0 := by
          rw [hr, List.getElem?_append_left hlt]; exact hf0
        have hname : c.fields[i].name = f0.name := by rw [hff]
        rw [hname, fieldIndex_at hwf hcls hfi'] at h4; cases h4; exact h6
      · exact hbeyond i (by simp [Ctx.ct] at hlt ⊢; omega) hi'
    obtain ⟨σ, hσ⟩ := ClassTable.ancestorArgs_of_mem hwf o.cls o.args c.meth.owner hsub
    have hsa' : fr.selfArgs = σ := by rw [hsa]; simp [Store.argsFor, ho, hσ]
    rw [hsa']
    exact hasTy_iff.mpr ⟨.cls o.cls o.args, by rw [hl]; exact typeOf_obj_of ho hall, .cls _ _,
      List.mem_singleton.mpr rfl, Atom.le_of_ancestorArgs hwf hσ⟩

theorem Store.setField_objs (s : Store) (l i : Nat) (v : Value) (l' : Nat) :
    (s.setField l i v).objs[l']? =
      if l' = l then (s.objs[l']?).map fun o => { o with fields := o.fields.set i v, set := o.set.set i true }
      else s.objs[l']? := by
  unfold Store.setField
  by_cases h : l' = l
  · subst h; simp [List.getElem?_modify]
  · simp [List.getElem?_modify, h, Ne.symm h]

theorem setField_grow {s : Store} {l i : Nat} {v : Value} : ObjsGrow s (s.setField l i v) :=
  fun l' o' h => by
    rw [Store.setField_objs]
    by_cases hl : l' = l
    · subst hl
      refine ⟨{ o' with fields := o'.fields.set i v, set := o'.set.set i true }, by simp [h], rfl, rfl,
        by simp, fun j hj => ?_⟩
      by_cases hji : j = i
      · subst hji
        have : j < o'.set.length := (List.getElem?_eq_some_iff.mp hj).1
        simp [this]
      · show (o'.set.set i true)[j]? = some true
        rw [List.getElem?_set_ne (Ne.symm hji)]; exact hj
    · exact ⟨o', by simp [hl, h], rfl, rfl, rfl, fun _ h => h⟩

/-- Assigning a field: a `var` one, or one of an object `Wo` allows. -/
theorem Ext.setField {W Wo : Nat → Prop} {Λ : List Ty} {s : Store} {l i : Nat} {v : Value} {o : Obj}
    {fd : Field} (ho : s.objs[l]? = some o) (hfi : (P.classes.allFields o.cls)[i]? = some fd)
    (hvar : fd.var = false → Wo l) : Ext P W Wo Λ Λ s (s.setField l i v) where
  tys := List.prefix_refl Λ
  procs := List.prefix_refl _
  pins := List.prefix_refl _
  builts := List.prefix_refl _
  locs := fun _ w h => ⟨w, h, .inl rfl⟩
  grow := setField_grow
  imm := fun l' o1 o2 h1 h2 hn j f hj hfv => by
    rw [Store.setField_objs] at h2
    by_cases hl : l' = l
    · subst hl; rw [if_pos rfl, h1] at h2; cases h2
      rw [ho] at h1; cases h1
      have hji : j ≠ i := by
        rintro rfl; rw [hfi] at hj; cases hj; exact hn (hvar hfv)
      exact List.getElem?_set_ne (Ne.symm hji)
    · rw [if_neg hl, h1] at h2; cases h2; rfl

theorem WfStore.setField {Λ : List Ty} {s : Store} (hw : WfStore P Λ s)
    {l i : Nat} {v : Value} {o : Obj} {fd : Field} (ho : s.objs[l]? = some o)
    (hfi : (P.classes.allFieldsAt o.cls o.args)[i]? = some fd)
    (hv : s.hasTy P v fd.ty) : WfStore P Λ (s.setField l i v) where
  len := hw.len
  pinsLen := hw.pinsLen
  builts := hw.builts
  procs := fun j p hp => by
    obtain ⟨_, f0, _, hf0, _⟩ := ClassTable.allFieldsAt_some P.classes hfi
    exact (hw.procs j p hp).stable
      (Ext.setField (W := fun _ => False) (Wo := fun _ => True) ho hf0 (fun _ => trivial))
  bounds := fun l' o' h => by
    rw [Store.setField_objs] at h
    by_cases hl : l' = l
    · subst hl; rw [if_pos rfl, ho] at h; cases h; exact hw.bounds l' o ho
    · rw [if_neg hl] at h; exact hw.bounds l' o' h
  noEnum := fun l' o' h => by
    rw [Store.setField_objs] at h
    by_cases hl : l' = l
    · subst hl; rw [if_pos rfl, ho] at h; cases h; exact hw.noEnum l' o ho
    · rw [if_neg hl] at h; exact hw.noEnum l' o' h
  objs := fun l' o' h => by
    have mono : ∀ {w : Value} {t : Ty}, s.hasTy P w t → (s.setField l i v).hasTy P w t :=
      fun hw' => hasTy_mono setField_grow (List.prefix_refl _) (List.prefix_refl _) hw'
    rw [Store.setField_objs] at h
    by_cases hl : l' = l
    · subst hl; rw [if_pos rfl, ho] at h; cases h
      obtain ⟨a, a1, a2, b, b2, d⟩ := hw.objs l' o ho
      refine ⟨a, a1, a2, by simp [b], by simp [b2], fun j w f hs hj hf => ?_⟩
      by_cases hji : j = i
      · subst hji; rw [hfi] at hf; cases hf
        have : j < o.fields.length := by
          rw [b, ← ClassTable.allFieldsAt_length P.classes o.cls o.args]
          exact (List.getElem?_eq_some_iff.mp hfi).1
        simp [this] at hj; subst hj; exact mono hv
      · simp only at hs hj
        rw [List.getElem?_set_ne (Ne.symm hji)] at hs hj
        exact mono (d j w f hs hj hf)
    · rw [if_neg hl] at h
      obtain ⟨a, a1, a2, b, b2, d⟩ := hw.objs l' o' h
      exact ⟨a, a1, a2, b, b2, fun j w f hs hj hf => mono (d j w f hs hj hf)⟩

/-- A field read where the checker allows it: the field set, its value
of its declared type. -/
theorem self_field_read (hwf : WfClasses P.classes) {c : Ctx} {Γ : Env} {Λ : List Ty} {fr : Frame}
    {s : Store} (hc : c.prog = P) {ws : List (Ctx × Env × Out)} (hf : FrameOK P c Λ fr s ws)
    (hw : WfStore P Λ s) (hs : Sat P c Γ fr s) {f : String} {fd : Field} (hfd : c.field? f = some fd)
    (hin : (!c.inInit || (Γ.get (.field f)).isSome) = true) :
    ∃ l o i v, fr.self = .obj l ∧ s.objs[l]? = some o ∧ fieldIndex P.classes o.cls f = some i ∧
      (P.classes.allFieldsAt o.cls o.args)[i]? = some { fd with ty := fd.ty.subst fr.selfArgs } ∧
      o.set[i]? = some true ∧ o.fields[i]? = some v ∧
      s.hasTy P v (fd.ty.subst fr.selfArgs) := by
  obtain ⟨l, o, i, hl, ho, hi, hfi, _, hil, hsl⟩ := self_field hwf hc hf hw hfd
  have hset : o.set[i]? = some true := by
    cases hii : c.inInit
    · exact all_id_iff.mp (self_made hf hii hl ho) i hsl
    · rw [hii] at hin; simp only [Bool.not_true, Bool.false_or] at hin
      obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hin
      obtain ⟨l', o', _, j, h1, h2, _, h4, _, h6, _⟩ := hs _ _ ht
      rw [hl] at h1; cases h1; rw [ho] at h2; cases h2; rw [hi] at h4; cases h4; exact h6
  exact ⟨l, o, i, o.fields[i], hl, ho, hi, hfi, hset, by simp [hil],
    (hw.objs l o ho).2.2.2.2.2 i _ _ hset (by simp [hil]) hfi⟩

theorem findIdx?_true {α} {p : α → Bool} {l : List α} {i : Nat} (h : l.findIdx? p = some i) :
    ∃ a, l[i]? = some a ∧ p a = true := by
  obtain ⟨hi, hp, _⟩ := List.findIdx?_eq_some_iff_getElem.mp h
  exact ⟨l[i], by simp [hi], hp⟩

/-- Two fields at one index are one. -/
theorem fieldIndex_inj {k : Nat} {f g : String} {i : Nat} (hf : fieldIndex P.classes k f = some i)
    (hg : fieldIndex P.classes k g = some i) : f = g := by
  obtain ⟨a, ha, hpa⟩ := findIdx?_true hf
  obtain ⟨b, hb, hpb⟩ := findIdx?_true hg
  rw [ha] at hb; cases hb
  simp at hpa hpb; rw [← hpa, ← hpb]

/-- After assigning field `f` of `self`: each path holds what it held, but
`f`, which is set and holds what it is given. -/
theorem PathHolds.setField {c : Ctx} {fr : Frame} {s : Store} {l i : Nat} {o : Obj} {v : Value}
    {f : String} {fd : Field} (hl : fr.self = .obj l) (ho : s.objs[l]? = some o)
    (hi : fieldIndex P.classes o.cls f = some i) (hfd : c.field? f = some fd) :
    ∀ {p : Path} {u : Ty}, PathHolds P c fr s p u →
      (p = .field f → fd.var = false → s.hasTy P v (u.subst fr.selfArgs)) →
      PathHolds P c fr (s.setField l i v) p u
  | .local x, u, ⟨l', w, d, h1, h2, h3, h4, h5⟩, _ =>
    ⟨l', w, d, h1, h2, h3, hasTy_mono setField_grow (List.prefix_refl _) (List.prefix_refl _) h4, hasTy_mono setField_grow (List.prefix_refl _) (List.prefix_refl _) h5⟩
  | .field g, u, ⟨l', o', fd', j, h1, h2, h3, h4, h5, h6, h7⟩, hnew => by
    rw [hl] at h1; cases h1; rw [ho] at h2; cases h2
    refine ⟨l, { o with fields := o.fields.set i v, set := o.set.set i true }, fd', j, hl,
      by rw [Store.setField_objs, if_pos rfl, ho]; rfl, h3, h4, h5, ?_, fun hv => ?_⟩
    · by_cases hji : j = i
      · subst hji
        have : j < o.set.length := (List.getElem?_eq_some_iff.mp h6).1
        simp [this]
      · show (o.set.set i true)[j]? = some true
        rw [List.getElem?_set_ne (Ne.symm hji)]; exact h6
    · by_cases hji : j = i
      · subst hji
        have hgf := fieldIndex_inj h4 hi; subst hgf
        rw [hfd] at h3; cases h3
        obtain ⟨_, h8, _⟩ := h7 hv
        have : j < o.fields.length := (List.getElem?_eq_some_iff.mp h8).1
        exact ⟨v, by simp [this], hasTy_mono setField_grow (List.prefix_refl _) (List.prefix_refl _) (hnew rfl hv)⟩
      · obtain ⟨w, h8, h9⟩ := h7 hv
        exact ⟨w, by show (o.fields.set i v)[j]? = some w; rw [List.getElem?_set_ne (Ne.symm hji)]; exact h8,
          hasTy_mono setField_grow (List.prefix_refl _) (List.prefix_refl _) h9⟩

/-- The field assigned: set, holding the value. -/
theorem PathHolds.setField_self {c : Ctx} {fr : Frame} {s : Store} {l i : Nat} {o : Obj} {v : Value}
    {f : String} {fd : Field} {u : Ty} (ho : s.objs[l]? = some o) (hl : fr.self = .obj l)
    (hi : fieldIndex P.classes o.cls f = some i)
    (hfi : (P.classes.allFieldsAt o.cls o.args)[i]? = some { fd with ty := fd.ty.subst fr.selfArgs })
    (hfd : c.field? f = some fd) (hsl : i < o.set.length) (hfl : i < o.fields.length)
    (hv : fd.var = false → s.hasTy P v (u.subst fr.selfArgs)) :
    PathHolds P c fr (s.setField l i v) (.field f) u :=
  ⟨l, { o with fields := o.fields.set i v, set := o.set.set i true }, fd, i, hl,
    by rw [Store.setField_objs, if_pos rfl, ho]; rfl, hfd, hi, hfi, by simp [hsl],
    fun h => ⟨v, by simp [hfl], hasTy_mono setField_grow (List.prefix_refl _) (List.prefix_refl _) (hv h)⟩⟩

/-- A path's value in a frame. -/
def PathVal (P : Program) (fr : Frame) (s : Store) : Path → Value → Prop
  | .local x, v => ∃ l, lookupVar fr.vars x = some l ∧ s.locs[l]? = some v
  | .field f, v => ∃ l o i, fr.self = .obj l ∧ s.objs[l]? = some o ∧
      fieldIndex P.classes o.cls f = some i ∧ o.set[i]? = some true ∧ o.fields[i]? = some v

/-- A read gives its path's value, and changes nothing. -/
theorem eval_read {e : Expr} {p : Path} (hp : e.path? = some p) {n : Nat} {fr : Frame} {s s1 : Store}
    {v : Value} (h : eval P orc n fr s e = .ok v s1) : s1 = s ∧ PathVal P fr s p v := by
  cases n with
  | zero => simp [eval] at h
  | succ n =>
    cases e <;> simp [Expr.path?] at hp <;> subst hp
    · simp only [eval] at h
      split at h
      · rename_i w hw
        split at h
        · cases h
          simp [Option.bind_eq_some_iff] at hw
          obtain ⟨l, hl, hv⟩ := hw
          exact ⟨rfl, l, hl, hv⟩
        · cases h
      · cases h
    · simp only [eval] at h
      split at h
      · rename_i l hl
        split at h
        · rename_i o ho
          split at h
          · rename_i w hw
            split at h
            · cases h
              simp only [Option.bind_eq_some_iff] at hw
              obtain ⟨i, hi, hv⟩ := hw
              split at hv
              · exact ⟨rfl, l, o, i, hl, ho, hi, by assumption, hv⟩
              · cases hv
            · cases h
          · cases h
        · cases h
      · cases h

/-- A path's value, of what the environment says it holds, and of any
type it is narrowed to that it has. -/
theorem pathHolds_of_val (hwf : WfClasses P.classes) {c : Ctx} {Δ : Env} {fr : Frame} {Λ : List Ty}
    {s : Store} (hc : c.prog = P) (hs : Sat P c Δ fr s) {ws : List (Ctx × Env × Out)} (hf : FrameOK P c Λ fr s ws)
    (hw : WfStore P Λ s) {p : Path} {t : Ty} (ht : c.pathTy Δ p = some t) {v : Value}
    (hv : PathVal P fr s p v) :
    s.hasTy P v (t.subst fr.selfArgs) ∧
      ∀ t', s.hasTy P v (t'.subst fr.selfArgs) → PathHolds P c fr s p t' := by
  cases p with
  | «local» x =>
    obtain ⟨l, hl, hlv⟩ := hv
    obtain ⟨l', w, d, h1, h2, h3, h4, h5⟩ := hs _ _ ht
    rw [hl] at h1; cases h1; rw [hlv] at h2; cases h2
    exact ⟨h4, fun t' h => ⟨l, v, d, hl, hlv, h3, h, h5⟩⟩
  | field f =>
    obtain ⟨l, o, i, hl, ho, hi, hset, hfv⟩ := hv
    simp only [Ctx.pathTy] at ht
    cases hfd : c.field? f with
    | none => rw [hfd] at ht; cases ht
    | some fd =>
      rw [hfd] at ht
      cases hvar : fd.var
      · simp [hvar] at ht
        obtain ⟨l', o', i', h1, h2, h3, h4, _, _, _⟩ := self_field hwf hc hf hw hfd
        rw [hl] at h1; cases h1; rw [ho] at h2; cases h2; rw [hi] at h3; cases h3
        refine ⟨?_, fun t' h => ⟨l, o, fd, i, hl, ho, hfd, hi, h4, hset, fun _ => ⟨v, hfv, h⟩⟩⟩
        cases hg : Δ.get (.field f) with
        | none =>
          rw [hg] at ht; simp at ht; subst ht
          exact (hw.objs l o ho).2.2.2.2.2 i v _ hset hfv h4
        | some u =>
          rw [hg] at ht; simp at ht; subst ht
          obtain ⟨_, _, _, _, k1, k2, k3, k4, _, _, k7⟩ := hs _ _ hg
          rw [hl] at k1; cases k1; rw [ho] at k2; cases k2; rw [hi] at k4; cases k4
          rw [hfd] at k3; cases k3
          obtain ⟨w, k8, k9⟩ := k7 hvar
          rw [hfv] at k8; cases k8; exact k9
      · simp [hvar] at ht

/-- `==` against `nil`, `true` or `false` of a value that is no object:
built-in equality. -/
theorem equal_nonobj {n : Nat} {s : Store} {v w : Value} (hv : ∀ l, v ≠ .obj l) :
    equal P orc n s v w = .timeout ∨ equal P orc n s v w = .ok (.bool (v == w)) s := by
  cases n with
  | zero => exact .inl rfl
  | succ n =>
    right
    cases v with
    | obj l => exact absurd rfl (hv l)
    | _ => rfl

/-- `v == w` (`w` no object) on a value of final atoms: the built-in
comparison. -/
theorem equal_finalIn {n : Nat} {s : Store} {v w : Value} (hw : ∀ l, w ≠ .obj l)
    (h : (∀ l, v ≠ .obj l) ∨ ∃ l o, v = .obj l ∧ s.objs[l]? = some o ∧ P.lookup o.cls "==" = none) :
    equal P orc n s v w = .timeout ∨ equal P orc n s v w = .ok (.bool (v == w)) s := by
  rcases h with h | ⟨l, o, rfl, ho, hl⟩
  · exact equal_nonobj h
  · cases n with
    | zero => exact .inl rfl
    | succ n =>
      right
      cases w
      case obj l' => exact absurd rfl (hw l')
      all_goals simp [equal, ho, hl]

/-- `e == w` that calls no method (`eqNoCall`): the built-in comparison,
the store as it was. -/
theorem eq_noCall_equal (hwf : WfClasses P.classes) {c : Ctx} {Δ : Env} {e : Expr} {t : Ty} {fr : Frame}
    {Λ : List Ty} {ws : List (Ctx × Env × Out)} {s : Store} {v w : Value} {n : Nat}
    (hc : c.prog = P) (hs : Sat P c Δ fr s) (hf : FrameOK P c Λ fr s ws) (hw : WfStore P Λ s)
    (hv : s.hasTy P v (t.subst fr.selfArgs)) (hval : ∀ p, e.path? = some p → PathVal P fr s p v)
    (hww : ∀ l, w ≠ .obj l) (hnc : eqNoCall c Δ e t = true) :
    equal P orc n s v w = .timeout ∨ equal P orc n s v w = .ok (.bool (v == w)) s := by
  subst hc
  unfold eqNoCall at hnc
  cases hp : e.path? with
  | none =>
    simp only [hp, Option.bind_none, Option.getD_none] at hnc
    exact equal_finalIn hww (value_finalIn hwf (by rwa [Ty.subst_of_allFinalIn _ hnc] at hv) hnc)
  | some p =>
    cases ht : c.pathTy Δ p with
    | none =>
      simp only [hp, ht, Option.bind_some, Option.getD_none] at hnc
      exact equal_finalIn hww (value_finalIn hwf (by rwa [Ty.subst_of_allFinalIn _ hnc] at hv) hnc)
    | some T =>
      simp only [hp, ht, Option.bind_some, Option.getD_some] at hnc
      have hvt := (pathHolds_of_val hwf rfl hs hf hw ht (hval p hp)).1
      exact equal_finalIn hww (value_finalIn hwf (by rwa [Ty.subst_of_allFinalIn _ hnc] at hvt) hnc)

/-- `e == w` that may call a method: nothing narrowed, the pinned locals
un-narrowed after it. -/
theorem post_eqCall {c : Ctx} {Δ : Env} {fr : Frame} {ws : List (Ctx × Env × Out)} {Λ Λ1 : List Ty}
    {s s1 : Store} {W : Nat → Prop} {v w : Value} {t : Ty} {n : Nat}
    (hc : c.prog = P) (hq : EqualGood P orc n) (hw : WfStore P Λ s) (he1 : Ext P W (initW c fr) Λ Λ1 s s1)
    (hw1 : WfStore P Λ1 s1) (hf1 : FrameOK P c Λ1 fr s1 ws) (hs1 : Sat P c Δ fr s1)
    (hv1 : s1.hasTy P v t) (hwv : w = .nil ∨ w = .bool true ∨ w = .bool false) :
    Post P c (Out.plain [.bool] (c.afterCall Δ)) fr ws Λ s W (equal P orc n s1 v w) := by
  subst hc
  have := hq s1 Λ1 v w t hw1 hv1 hwv
  revert this
  generalize equal c.prog orc n s1 v w = r
  intro this
  cases r with
  | ok r s2 =>
    obtain ⟨Λ2, hw2, he2, hr2, _⟩ := this
    have hs2 : Sat c.prog c (c.afterCall Δ) fr s2 :=
      (hs1.reset (xs := c.pinned)).stable he2 (fun _ _ h => by simp [blkW] at h) (fun _ _ h => h)
        hf1.core (pinsDecl_reset fun _ h => h)
    exact ⟨Λ2, hw2, (he1.transF he2 hw).monoW (fun l h => h.elim id (by simp [blkW])),
      hf1.stable he2 (fun _ _ h => by simp [blkW] at h) (fun _ h => h.elim), hr2,
      ⟨_, rfl, hs2⟩, fun _ => ⟨_, rfl, hs2⟩, fun _ => ⟨_, rfl, hs2⟩⟩
  | stuck => exact this
  | returned => exact this.elim
  | raised r s2 =>
    obtain ⟨Λ2, hw2, he2, hr2, _⟩ := this
    exact ⟨Λ2, hw2, (he1.transF he2 hw).monoW (fun l h => h.elim id (by simp [blkW])),
      hf1.stable he2 (fun _ _ h => by simp [blkW] at h) (fun _ h => h.elim), hr2⟩
  | timeout => trivial

/-- `!=`: what `==` gave, negated, a boolean all the same. -/
theorem Post.plain_bindNot {c : Ctx} {Γ : Env} {fr : Frame} {ws : List (Ctx × Env × Out)} {Λ : List Ty}
    {s : Store} {W : Nat → Prop} {r : Result} (h : Post P c (Out.plain [.bool] Γ) fr ws Λ s W r) :
    Post P c (Out.plain [.bool] Γ) fr ws Λ s W (r.bind fun r s => .ok (.bool (!r.truthy)) s) := by
  cases r with
  | ok v s' =>
    obtain ⟨Λ', a, b, d, _, e, _, _⟩ := h
    exact ⟨Λ', a, b, d, hasTy_lit_bool, e, fun _ => e, fun _ => e⟩
  | _ => exact h

theorem finalRead_eq {c : Ctx} {Δ : Env} {e : Expr} {p : Path} {t : Ty} (hp : e.path? = some p)
    (ht : c.pathTy Δ p = some t) : finalRead c Δ e = t.allFinalIn c.prog := by
  simp [finalRead, hp, ht]

theorem OutOK.stable {c : Ctx} {g : Option Env} {fr : Frame} {s s' : Store} {W Wo : Nat → Prop}
    {Λ Λ' : List Ty} (h : OutOK P c g fr s) (he : Ext P W Wo Λ Λ' s s')
    (hw : ∀ l, frameLocs fr.vars l → ¬ W l) (hwo : ∀ l, fr.self = .obj l → ¬ Wo l)
    (hcore : FrameCore P c Λ fr.vars fr.self fr.selfArgs s) (hpd : ∀ Γ, g = some Γ → PinsDecl c Γ) :
    OutOK P c g fr s' := by
  obtain ⟨Γ, rfl, hs⟩ := h
  exact ⟨Γ, rfl, hs.stable he hw hwo hcore (hpd Γ rfl)⟩

theorem testOut_ty (c : Ctx) (e : Expr) (Δ : Env) (T F : Ty → Ty) :
    (testOut c e Δ T F).ty = [.bool] := by
  unfold testOut; split <;> rfl

/-- A test's environments where its value says so, given what each side
tells of the value tested. -/
theorem testOut_ok (hwf : WfClasses P.classes) {c : Ctx} {e : Expr} {Δ : Env} {fr : Frame}
    {Λ : List Ty} {s : Store} (hc : c.prog = P) (hs : Sat P c Δ fr s) {ws : List (Ctx × Env × Out)} (hf : FrameOK P c Λ fr s ws)
    (hw : WfStore P Λ s) {tyT tyF : Ty → Ty} {v : Value} {b : Bool}
    (hval : ∀ p, e.path? = some p → PathVal P fr s p v)
    (hT : ∀ p t, e.path? = some p → c.pathTy Δ p = some t → s.hasTy P v (t.subst fr.selfArgs) →
      b = true → s.hasTy P v ((tyT t).subst fr.selfArgs))
    (hF : ∀ p t, e.path? = some p → c.pathTy Δ p = some t → s.hasTy P v (t.subst fr.selfArgs) →
      b = false → s.hasTy P v ((tyF t).subst fr.selfArgs)) :
    OutOK P c (testOut c e Δ tyT tyF).out fr s ∧
    (b = true → OutOK P c (testOut c e Δ tyT tyF).tt fr s) ∧
    (b = false → OutOK P c (testOut c e Δ tyT tyF).ff fr s) := by
  unfold testOut
  split
  · rename_i p t hpt
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hpt
    obtain ⟨p', hp', t', ht', heq⟩ := hpt
    cases heq
    obtain ⟨hvt, hre⟩ := pathHolds_of_val hwf hc hs hf hw ht' (hval _ hp')
    refine ⟨⟨Δ, rfl, hs⟩, fun hb => ?_, fun hb => ?_⟩
    · have h := hT _ _ hp' ht' hvt hb
      exact ⟨_, narrow_eq Δ _ (Ty.ne_nil_of_subst (ne_nil_of_hasTy h)), hs.set (hre _ h)⟩
    · have h := hF _ _ hp' ht' hvt hb
      exact ⟨_, narrow_eq Δ _ (Ty.ne_nil_of_subst (ne_nil_of_hasTy h)), hs.set (hre _ h)⟩
  · exact ⟨⟨Δ, rfl, hs⟩, fun _ => ⟨Δ, rfl, hs⟩, fun _ => ⟨Δ, rfl, hs⟩⟩

theorem resolve_mem {κ : List Ty} {t : Ty} {m : String} {ms : List Method}
    (h : P.resolve κ t m = some ms) {b : Atom} (hb : b ∈ Ty.expand κ t) :
    ∃ k as mt, b = .cls k as ∧ (k ≠ 0 ∧ P.classes.kindOf k ≠ .proc ∧ P.classes.kindOf k ≠ .builtin) ∧ P.lookupAt k as m = some mt ∧
      mt ∈ ms := by
  unfold Program.resolve at h
  split at h
  · cases h
  clear ‹¬_›
  generalize Ty.expand κ t = t at h hb
  induction t generalizing ms with
  | nil => cases hb
  | cons a t ih =>
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff] at h
    obtain ⟨mt0, h0, ms', h', hms⟩ := h
    simp [pure] at hms; subst hms
    rcases List.mem_cons.mp hb with rfl | hb
    · cases b with
      | cls k as =>
        by_cases hk : k = 0 ∨ P.classes.kindOf k = .proc ∨ P.classes.kindOf k = .builtin
        · rcases hk with hk | hk | hk <;> simp [hk] at h0
        · simp only [not_or] at hk
          simp [hk.1, hk.2.1, hk.2.2] at h0
          exact ⟨k, as, mt0, rfl, hk, h0, by simp⟩
      | _ => simp at h0
    · obtain ⟨k, as, mt, h1, h2, h3, h4⟩ := ih h' hb
      exact ⟨k, as, mt, h1, h2, h3, List.mem_cons_of_mem _ h4⟩

/-- No call reaches `initialize`. -/
theorem resolve_not_init {κ : List Ty} {t : Ty} {m : String} {ms : List Method}
    (h : P.resolve κ t m = some ms) :
    m ≠ "initialize" := by
  rintro rfl; simp [Program.resolve] at h

theorem AllTy.le (hwf : WfClasses P.classes) {s : Store} :
    ∀ {vs : List Value} {ts us : List Ty}, AllTy P s vs ts → ts.length = us.length →
      ((ts.zip us).all fun (t, u) => t.le P.classes [] u) = true → AllTy P s vs us
  | [], [], [], _, _, _ => trivial
  | _ :: _, _ :: _, _ :: _, ⟨h1, h2⟩, hl, ha => by
    simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at ha
    exact ⟨hasTy_le hwf h1 ha.1, AllTy.le hwf h2 (by simpa using hl) ha.2⟩
  | [], [], _ :: _, _, hl, _ => by simp at hl
  | [], _ :: _, _, h, _, _ => h.elim
  | _ :: _, [], _, h, _, _ => h.elim
  | _ :: _, _ :: _, [], _, hl, _ => by simp at hl

/-- Arguments of types fitting the parameters (`argsOk`). -/
theorem AllTy.le_params (hwf : WfClasses P.classes) {s : Store} :
    ∀ {vs : List Value} {ts : List Ty} {ps : List (String × Ty)}, AllTy P s vs ts →
      ts.length = ps.length → ((ts.zip ps).all fun (t, (_, u)) => t.le P.classes [] u) = true →
      AllTy P s vs (ps.map (·.2))
  | [], [], [], _, _, _ => trivial
  | _ :: _, _ :: _, _ :: _, ⟨h1, h2⟩, hl, ha => by
    simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at ha
    exact ⟨hasTy_le hwf h1 ha.1, AllTy.le_params hwf h2 (by simpa using hl) ha.2⟩
  | [], [], _ :: _, _, hl, _ => by simp at hl
  | [], _ :: _, _, h, _, _ => h.elim
  | _ :: _, [], _, h, _, _ => h.elim
  | _ :: _, _ :: _, [], _, hl, _ => by simp at hl

/-- `zip_val` for arguments typed by the parameters' types substituted. -/
theorem zip_val_subst {s : Store} {σ : List Ty} {vs : List Value} {ps : List (String × Ty)}
    (h : AllTy P s vs ((ps.map (·.2)).map (Ty.subst σ))) (x : String) (t : Ty)
    (hm : (x, t) ∈ (ps.map (·.1)).zip (ps.map (·.2))) :
    ∃ v, (x, v) ∈ (ps.map (·.1)).zip vs ∧ s.hasTy P v (t.subst σ) := by
  have h' : AllTy P s vs ((ps.map fun (x, t) => (x, t.subst σ)).map (·.2)) := by
    simpa [List.map_map, Function.comp_def] using h
  have hm' : (x, t.subst σ) ∈ ((ps.map fun (x, t) => (x, t.subst σ)).map (·.1)).zip
      ((ps.map fun (x, t) => (x, t.subst σ)).map (·.2)) := by
    rw [zip_fst_snd] at hm ⊢
    exact List.mem_map.mpr ⟨(x, t), hm, rfl⟩
  obtain ⟨v, hvm, hvt⟩ := zip_val h' x (t.subst σ) hm'
  refine ⟨v, ?_, hvt⟩
  simpa [List.map_map, Function.comp_def] using hvm

theorem hasTy_flatMap {s : Store} {v : Value} {ms : List Method} {mt : Method} (hm : mt ∈ ms)
    (h : s.hasTy P v mt.ret) : s.hasTy P v (ms.flatMap (·.ret)) := by
  rw [hasTy_iff] at *
  obtain ⟨a, ha, b, hb, hab⟩ := h
  exact ⟨a, ha, b, List.mem_flatMap.mpr ⟨mt, hm, hb⟩, hab⟩

/-- A value of a class other than `Object`: an object of a subclass. -/
theorem obj_of_hasTy_cls (hwf : WfClasses P.classes) {Λ : List Ty} {s : Store} (hw : WfStore P Λ s)
    {v : Value} {k : Nat} {as : List Ty}
    (hv : s.hasTy P v [.cls k as]) (hk : k ≠ 0 ∧ P.classes.kindOf k ≠ .proc ∧ P.classes.kindOf k ≠ .builtin) :
    ∃ l o, v = .obj l ∧ s.objs[l]? = some o ∧ k ∈ P.classes.ancestors o.cls := by
  rw [hasTy_iff] at hv
  obtain ⟨a, ha, b, hb, hab⟩ := hv
  simp at hb; subst hb
  cases v with
  | obj l =>
    obtain ⟨o, ho, _, rfl⟩ := typeOf_obj ha
    rw [Atom.le_cls_iff hwf] at hab
    rcases hab with ⟨h0, _⟩ | ⟨_, hab, _⟩
    · exact absurd h0 hk.1
    · exact ⟨l, o, rfl, ho, ClassTable.ancestorArgs_mem hwf _ _ _ _ hab⟩
  | proc i =>
    -- A procedure is of a procedures' class, right below `Object`.
    obtain ⟨kp, asp, rfl, hkp⟩ := typeOf_proc_kind hw ha
    rw [Atom.le_cls_iff hwf] at hab
    rcases hab with ⟨h0, _⟩ | ⟨_, hab, _⟩
    · exact absurd h0 hk.1
    · have hmem := ClassTable.ancestorArgs_mem hwf _ _ _ _ hab
      rw [proc_ancestors hwf hkp] at hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl
      · exact absurd hkp hk.2.1
      · exact absurd rfl hk.1
  | builtin i =>
    -- A built-in value is of a built-in generic class, right below `Object`.
    obtain ⟨kp, asp, rfl, hkp⟩ := typeOf_builtin_kind hw ha
    rw [Atom.le_cls_iff hwf] at hab
    rcases hab with ⟨h0, _⟩ | ⟨_, hab, _⟩
    · exact absurd h0 hk.1
    · have hmem := ClassTable.ancestorArgs_mem hwf _ _ _ _ hab
      rw [builtin_ancestors hwf hkp] at hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl
      · exact absurd hkp hk.2.2
      · exact absurd rfl hk.1
  | _ => simp [Store.typeOf] at ha; subst ha; simp [Atom.le] at hab; exact absurd hab.1 hk.1

/-- A value of a procedures' class: a procedure, of that class with
arguments as its variances allow (no object is of it, nor of a class below
it: it has none). -/
theorem proc_of_hasTy (hwf : WfClasses P.classes) {Λ : List Ty} {s : Store} (hw : WfStore P Λ s)
    {v : Value} {k : Nat} {as : List Ty} (hv : s.hasTy P v [.cls k as])
    (hk : P.classes.kindOf k = .proc) :
    ∃ i p, v = .proc i ∧ s.procs[i]? = some p ∧ ∃ args', p.ty = .cls k args' ∧
      argsLeWith (Atom.le P.classes []) (P.classes.variances k) args' as = true := by
  have hk0 : k ≠ 0 := by
    rintro rfl
    cases h0 : P.classes[0]? with
    | none => simp [ClassTable.kindOf, h0] at hk
    | some k0 => simp [ClassTable.kindOf, h0, hwf.rootKind k0 h0] at hk
  rw [hasTy_iff] at hv
  obtain ⟨a, ha, b, hb, hab⟩ := hv
  simp at hb; subst hb
  cases v with
  | obj l =>
    exfalso
    obtain ⟨o, ho, _, rfl⟩ := typeOf_obj ha
    rw [Atom.le_cls_iff hwf] at hab
    rcases hab with ⟨h0, _⟩ | ⟨x, hx, _⟩
    · exact hk0 h0
    by_cases hne : o.cls = k
    · exact (hw.noEnum l o ho).2.1 (hne ▸ hk)
    · obtain ⟨V, kv, hkv, hsv, _, _⟩ := ancestorArgs_child hwf o.cls o.args x hx hne
      exact hwf.procLeaf V kv k hkv hsv hk
  | proc i =>
    obtain ⟨kp, asp, rfl, hkp⟩ := typeOf_proc_kind hw ha
    rw [Atom.le_cls_iff hwf] at hab
    rcases hab with ⟨h0, _⟩ | ⟨x, hx, hle⟩
    · exact absurd h0 hk0
    have hmem := ClassTable.ancestorArgs_mem hwf _ _ _ _ hx
    rw [proc_ancestors hwf hkp] at hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl
    · rw [ClassTable.ancestorArgs_self hwf] at hx; cases hx
      simp only [Store.typeOf, Option.bind_eq_some_iff] at ha
      obtain ⟨p, hp, h⟩ := ha
      refine ⟨i, p, rfl, hp, asp, ?_, hle⟩
      revert h; cases p.ty <;> simp
    · exact absurd rfl hk0
  | builtin i =>
    exfalso
    obtain ⟨kp, asp, rfl, hkp⟩ := typeOf_builtin_kind hw ha
    rw [Atom.le_cls_iff hwf] at hab
    rcases hab with ⟨h0, _⟩ | ⟨x, hx, _⟩
    · exact hk0 h0
    have hmem := ClassTable.ancestorArgs_mem hwf _ _ _ _ hx
    rw [builtin_ancestors hwf hkp] at hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl
    · rw [hkp] at hk; cases hk
    · exact hk0 rfl
  | _ => simp [Store.typeOf] at ha; subst ha; simp [Atom.le] at hab; exact absurd hab.1 hk0

/-- The receiver of a call (through the frame's arguments `σ`): of the
class the method was found in, given the arguments its view of the
receiver has substituted, where the method found is that view's
instantiated. -/
theorem recv_of (hwf : WfClasses P.classes) {κ σ : List Ty} (hσ : ArgsIn P.classes κ σ)
    {s : Store} {v : Value} {t : Ty} {m : String} {ms : List Method}
    (hv : s.hasTy P v (t.subst σ)) (hres : P.resolve κ t m = some ms) :
    ∃ k as mt, (k ≠ 0 ∧ P.classes.kindOf k ≠ .proc ∧ P.classes.kindOf k ≠ .builtin) ∧ P.lookupAt k (Ty.substArgs σ as) m = some (mt.inst σ) ∧ mt ∈ ms ∧
      s.hasTy P v [.cls k (Ty.substArgs σ as)] := by
  rw [hasTy_iff] at hv
  obtain ⟨a, ha, b', hb', hab⟩ := hv
  obtain ⟨b, hb, hbb'⟩ := Ty.mem_subst.mp hb'
  cases b
  case param i =>
    -- What the parameter stands for is within its bound: the value is of
    -- one of the bound's (closed) atoms, whose method the call runs.
    simp only [Atom.subst] at hbb'
    obtain ⟨β, hβ, hbβ⟩ := Ty.le_iff.mp (hσ i) b' hbb'
    have hβt : β ∈ Ty.expand κ t := List.mem_flatMap.mpr ⟨.param i, hb, hβ⟩
    obtain ⟨k, as, mt, rfl, hk, hl, hm⟩ := resolve_mem hres hβt
    have hc : Ty.closedArgs as = true := by
      have := (Ty.boundOf_mem hβ).1; simpa [Atom.closed] using this
    refine ⟨k, as, mt, hk, Program.lookupAt_subst σ hl, hm, ?_⟩
    rw [Ty.substArgs_closed_id σ as hc]
    exact hasTy_iff.mpr ⟨a, ha, .cls k as, List.mem_singleton.mpr rfl, Atom.le_trans hwf hab hbβ⟩
  case cls c0 as0 =>
    obtain ⟨k, as, mt, hbk, hk, hl, hm⟩ := resolve_mem hres
      (List.mem_flatMap.mpr ⟨_, hb, List.mem_singleton.mpr rfl⟩)
    cases hbk
    simp at hbb'; subst hbb'
    exact ⟨c0, as0, mt, hk, Program.lookupAt_subst σ hl, hm,
      hasTy_iff.mpr ⟨a, ha, .cls c0 _, List.mem_singleton.mpr rfl, hab⟩⟩
  all_goals
    obtain ⟨k, as, mt, hbk, _⟩ := resolve_mem hres
      (List.mem_flatMap.mpr ⟨_, hb, List.mem_singleton.mpr rfl⟩)
    cases hbk

/-- A value of a method's result type, substituted, is of the union of the
candidates' results, substituted. -/
theorem hasTy_flatMap_subst {s : Store} {v : Value} {σ : List Ty} {ms : List Method} {mt : Method}
    (hm : mt ∈ ms) (h : s.hasTy P v (mt.ret.subst σ)) :
    s.hasTy P v (Ty.subst σ (ms.flatMap (·.ret))) := by
  rw [hasTy_iff] at *
  obtain ⟨a, ha, b, hb, hab⟩ := h
  refine ⟨a, ha, b, ?_, hab⟩
  obtain ⟨b0, hb0, hbb⟩ := Ty.mem_subst.mp hb
  exact Ty.mem_subst.mpr ⟨b0, List.mem_flatMap.mpr ⟨mt, hm, hb0⟩, hbb⟩

theorem blkW_chain : ∀ {blk : Option Closure} {l : Nat}, blkW blk l → chainLocs blk l
  | none, _, h => by simp [blkW] at h
  | some (.mk vars me sa outer ps body), l, h => by
    simp only [blkW, chainLocs] at h ⊢
    rcases h with ⟨x, _, hx⟩ | h
    · exact .inl ⟨x, lookupVar_mem hx⟩
    · exact .inr (blkW_chain h)

/-- What a frame's block writes misses the frame. -/
theorem FrameOK.blk_not_own {c : Ctx} {Λ : List Ty} {fr : Frame} {s : Store} {ws : List (Ctx × Env × Out)} (hf : FrameOK P c Λ fr s ws) :
    ∀ l, frameLocs fr.vars l → ¬ blkW fr.blk l := fun l hl hb =>
  Nat.lt_irrefl _ (hf.above l l hl (blkW_chain hb))

/-! ### `initialize` run on an object (`new`, `super`) -/

variable (P) in
/-- What running `initialize`'s body on object `l` gives: never stuck;
when it ends (with a value or a `return`), the object made, no location
of `s` written, and no immutable field but the object's. -/
def InitPost (l : Nat) (Λ : List Ty) (s : Store) : Result → Prop
  | .ok _ s' | .returned _ s' => ∃ Λ', WfStore P Λ' s' ∧ Ext P (fun _ => False) (· = l) Λ Λ' s s' ∧
      (s'.typeOf (.obj l)).isSome = true
  | .raised v s' => ∃ Λ', WfStore P Λ' s' ∧ Ext P (fun _ => False) (· = l) Λ Λ' s s' ∧
      s'.hasTy P v [.cls P.exn []]
  | .stuck => False
  | _ => True

/-- Setting paths one after another, each holding its type. -/
theorem Sat.foldl_set {c : Ctx} {fr : Frame} {s : Store} :
    ∀ (ps : List (String × Ty)) {Γ : Env}, Sat P c Γ fr s →
      (∀ x t, (x, t) ∈ ps → PathHolds P c fr s (.local x) t) →
      Sat P c (ps.foldl (fun g (x, t) => g.set (.local x) t) Γ) fr s
  | [], _, h, _ => h
  | (x, t) :: ps, Γ, h, hp => by
    simp only [List.foldl_cons]
    exact Sat.foldl_set ps (h.set (hp x t (List.mem_cons_self ..)))
      fun y u hy => hp y u (List.mem_cons_of_mem _ hy)

/-- Locals looked up in a frame made of two lists: the first's, else the
second's. -/
theorem lookupVar_append (a b : List (String × Nat)) (x : String) :
    lookupVar (a ++ b) x = match lookupVar a x with
      | some l => some l
      | none => lookupVar b x := by
  unfold lookupVar
  rw [List.find?_append]
  cases a.find? (·.1 == x) <;> rfl

/-- The first local of a name, in a list of distinct names. -/
theorem find_local_of_mem {ls rest : List (String × Ty)} (hnd : (ls.map (·.1)).Nodup) {x : String}
    {t : Ty} (hm : (x, t) ∈ ls) : ((ls ++ rest).find? (·.1 == x)).map (·.2) = some t := by
  rw [List.find?_append]
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hm
  clear hm
  have hf : ls.find? (·.1 == x) = some (x, t) := by
    induction ls generalizing j with
    | nil => simp at hj
    | cons y ys ih =>
      simp only [List.map_cons, List.nodup_cons] at hnd
      cases j with
      | zero => simp at hj; subst hj; simp
      | succ j =>
        simp at hj
        have hyx : y.1 ≠ x := fun e => hnd.1 (by
          rw [e]; exact List.mem_map.mpr ⟨(x, t), List.mem_of_getElem? hj, rfl⟩)
        simp [hyx, ih hnd.2 j hj]
  simp [hf]

/-- In a lambda's body, a name not of its own is the method's. -/
theorem lambdaCtx_decl_outer {c : Ctx} {ps own : List (String × Ty)} {x : String}
    (hx : x ∉ (ps ++ own).map (·.1)) : (c.lambdaCtx ps own).decl x = c.decl x := by
  simp only [Ctx.decl, Ctx.lambdaCtx]
  rw [List.find?_append]
  rw [List.find?_eq_none.mpr (fun q hq h => hx (by simp at h; exact List.mem_map.mpr ⟨q, hq, h⟩))]
  rfl

/-- In a lambda's body, its own locals as it declares them. -/
theorem lambdaCtx_decl_own {c : Ctx} {ps own : List (String × Ty)}
    (hnd : ((ps ++ own).map (·.1)).Nodup) {x : String} {t : Ty} (hm : (x, t) ∈ ps ++ own) :
    (c.lambdaCtx ps own).decl x = some t := by
  simp only [Ctx.decl, Ctx.lambdaCtx]
  exact find_local_of_mem (rest := c.meth.locals) hnd hm

/-- What a lambda's body declares: one of its own locals, or the method's. -/
theorem lambdaCtx_decl {c : Ctx} {ps own : List (String × Ty)} {x : String} {d : Ty}
    (hd : (c.lambdaCtx ps own).decl x = some d) :
    (∃ j : Nat, (ps ++ own)[j]? = some (x, d)) ∨ (x ∉ (ps ++ own).map (·.1) ∧ c.decl x = some d) := by
  by_cases hx : x ∈ (ps ++ own).map (·.1)
  · left
    simp only [Ctx.decl, Ctx.lambdaCtx, Option.map_eq_some_iff] at hd
    obtain ⟨q, hf, rfl⟩ := hd
    rw [List.find?_append] at hf
    obtain ⟨q0, hq0, hq0x⟩ := List.mem_map.mp hx
    cases hf1 : (ps ++ own).find? (·.1 == x) with
    | none =>
      exact absurd (by simpa using hq0x) (List.find?_eq_none.mp hf1 q0 hq0)
    | some q' =>
      rw [hf1] at hf; simp at hf; subst hf
      have hp := List.find?_some hf1
      simp at hp
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp (List.mem_of_find?_eq_some hf1)
      refine ⟨j, ?_⟩
      cases q'; simp at hp; subst hp; exact hj
  · right
    exact ⟨hx, by rw [← lambdaCtx_decl_outer hx]; exact hd⟩

/-- A procedure run (design §13.8, §13.10): its parameters and own locals
at fresh locations, the captured locals as they are; it gives a value of
its result type (through its frame's arguments), and writes no location
there before but marked ones (the pinned locals it assigns). -/
theorem proc_run (hP : WfProg P) {n : Nat} (ihe : EvalGood P orc n) {Λ : List Ty} {s : Store}
    (hw : WfStore P Λ s) {c : Ctx} {Γ : Env} {ps own : List (String × Ty)} {ret : Ty} {body : Expr}
    {vars : List (String × Nat)} {me : Value} {sa : List Ty} {ob : Out}
    (hc : c.prog = P) (hni : c.inInit = false) (hok : c.lambdaOk ps own body = true)
    (hcore : FrameCore P c Λ vars me sa s) (hsd : Sat P c (c.declEnv Γ) ⟨vars, me, sa, none⟩ s)
    (hty : Typed (c.lambdaCtx ps own) (c.lambdaEnv Γ ps) body ob)
    (hret : ob.ty.le c.ct c.bounds ret = true)
    {vs : List Value} (hvs : AllTy P s vs ((ps.map (·.2)).map (Ty.subst sa))) :
    SendPost P (ret.subst sa) none none [] Λ s
      (match bindAll ⟨s.locs ++ ((ps ++ own).map (·.1)).map (fun _ => .nil), s.objs, s.procs,
            s.pins ++ ((ps ++ own).map (·.1)).map (fun x => decide (x ∈ (ps ++ own).map (·.1))), s.builts⟩
          (Store.allocVars s.locs.length ((ps ++ own).map (·.1))) (ps.map (·.1)) vs with
       | some s2 =>
         match eval P orc n ⟨Store.allocVars s.locs.length ((ps ++ own).map (·.1)) ++ vars, me, sa, none⟩
           s2 body with
         | .returned _ _ => .stuck
         | r => r
       | none => .stuck) := by
  have hwf := hP.classes
  -- What `lambdaOk` says.
  simp only [Ctx.lambdaOk, Bool.and_eq_true] at hok
  obtain ⟨hok, hpin⟩ := hok
  simp only [List.all_eq_true, decide_eq_true_eq] at hpin
  have hpinN : ∀ x ∈ (ps ++ own).map (·.1), x ∈ c.pinned := fun x hx =>
    hpin x (List.mem_append_left _ (List.mem_append_left _ hx))
  have hpinA : ∀ x ∈ body.assigned, x ∈ c.pinned := fun x hx =>
    hpin x (List.mem_append_left _ (List.mem_append_right _ hx))
  obtain ⟨⟨hnd, hdisj⟩, _⟩ := hok
  simp only [decide_eq_true_eq] at hnd
  simp only [List.all_eq_true, Option.isNone_iff_eq_none] at hdisj
  generalize hnames : (ps ++ own).map (·.1) = names at hnd hpinN ⊢
  have hnot : ∀ x, x ∈ names → ∀ d, c.decl x = some d → False := by
    intro x hx d hd
    rw [← hnames] at hx
    obtain ⟨⟨y, u⟩, hm, rfl⟩ := List.mem_map.mp hx
    simp only [Ctx.decl, Option.map_eq_some_iff] at hd
    obtain ⟨_, hf, _⟩ := hd
    have := hdisj (y, u) hm
    rw [this] at hf; cases hf
  -- Fresh locations; the parameters bound.
  have hlenv : vs.length = ps.length := by
    have := hvs.length; simpa using this
  have hpnames : ∀ x ∈ ps.map (·.1), x ∈ names := fun x hx => by
    rw [← hnames, List.map_append]; exact List.mem_append_left _ hx
  have hlook : ∀ x ∈ names, ∃ l, lookupVar (Store.allocVars s.locs.length names) x = some l := fun x hx => by
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hx
    exact ⟨_, lookupVar_alloc hnd hj⟩
  obtain ⟨s2, hb⟩ := bindAll_some (vars := (Store.allocVars s.locs.length names)) (xs := ps.map (·.1)) (vs := vs) (⟨s.locs ++ names.map (fun _ => .nil), s.objs, s.procs, s.pins ++ names.map (fun x => decide (x ∈ names)), s.builts⟩ : Store) (by simp [hlenv])
    fun x hx => hlook x (hpnames x hx)
  obtain ⟨hobjs, hlen2, hsame⟩ := bindAll_same hb
  have hprocs := bindAll_procs hb
  have hpins := bindAll_pins hb
  have hbts := bindAll_builts hb
  simp only at hpins
  have hpinsO : ∀ l, l < s.pins.length → s2.pins[l]? = s.pins[l]? := fun l hl => by
    rw [hpins, List.getElem?_append_left hl]
  simp only [hb]
  simp only [List.length_append, List.length_map] at hlen2
  have hge : ∀ x l', lookupVar (Store.allocVars s.locs.length names) x = some l' → s.locs.length ≤ l' ∧ l' < s.locs.length + names.length :=
    fun x l' h => by have := mem_allocVars (lookupVar_mem h); simpa using this
  have hnone : ∀ x, x ∉ names → lookupVar (Store.allocVars s.locs.length names) x = none := fun x hx => by
    cases h : lookupVar (Store.allocVars s.locs.length names) x with
    | none => rfl
    | some l => obtain ⟨j, hj, _⟩ := lookupVar_alloc_inv h; exact absurd (List.mem_of_getElem? hj) hx
  have hlv : ∀ x, x ∉ names → lookupVar ((Store.allocVars s.locs.length names) ++ vars) x = lookupVar vars x := fun x hx => by
    rw [lookupVar_append, hnone x hx]
  have hln : ∀ x l, lookupVar (Store.allocVars s.locs.length names) x = some l → lookupVar ((Store.allocVars s.locs.length names) ++ vars) x = some l := fun x l h => by
    rw [lookupVar_append, h]
  -- The types of the fresh locations.
  have mono : ∀ {v : Value} {t : Ty}, s.hasTy P v t → s2.hasTy P v t := fun h => by
    unfold Store.hasTy Store.hasType Store.typeOf at *; rw [hobjs, hprocs, hbts]; exact h
  have he12 : Ext P (fun _ => False) (fun _ => False) Λ (Λ ++ (ps ++ own).map (fun (p : String × Ty) => Ty.subst sa p.2)) s s2 := by
    refine ⟨List.prefix_append _ _, fun l' v hv => ⟨v, ?_, .inl rfl⟩, fun l' o' ho' =>
      ⟨o', by rw [hobjs]; exact ho', rfl, rfl, rfl, fun _ h => h⟩,
      fun _ o1 o2 h1 h2 _ _ _ _ _ => by rw [hobjs, h1] at h2; cases h2; rfl,
      by rw [hprocs]; exact List.prefix_refl _, by rw [hpins]; exact List.prefix_append _ _, by rw [hbts]; exact List.prefix_refl _⟩
    have hl' := (List.getElem?_eq_some_iff.mp hv).1
    rw [hsame l' fun x _ hx => by have := (hge x l' hx).1; omega]
    simp [List.getElem?_append_left hl', hv]
  have hlenΛ : (Λ ++ (ps ++ own).map (fun (p : String × Ty) => Ty.subst sa p.2)).length = s2.locs.length := by
    simp [hw.len, hlen2, ← hnames]
  have hw2 : WfStore P (Λ ++ (ps ++ own).map (fun (p : String × Ty) => Ty.subst sa p.2)) s2 :=
    ⟨hlenΛ, by rw [hpins, hlen2]; simp [hw.pinsLen], fun l' o' ho' => by
      rw [hobjs] at ho'
      obtain ⟨a, a1, a2, b, b2, d⟩ := hw.objs l' o' ho'
      exact ⟨a, a1, a2, b, b2, fun i v f h0 h1 h2 => mono (d i v f h0 h1 h2)⟩,
      fun l' o' ho' => by rw [hobjs] at ho'; exact hw.noEnum l' o' ho',
      fun l' o' ho' => by rw [hobjs] at ho'; exact hw.bounds l' o' ho',
      fun i p hp => by rw [hprocs] at hp; exact (hw.procs i p hp).stable he12,
      fun i k as h' => by rw [hbts] at h'; exact hw.builts i k as h'⟩
  -- The body's context: the method's, with the lambda's locals first.
  have hdecl' : ∀ x d, (c.lambdaCtx ps own).decl x = some d →
      (∃ j : Nat, (ps ++ own)[j]? = some (x, d)) ∨ (x ∉ names ∧ c.decl x = some d) := by
    intro x d hd
    have := lambdaCtx_decl hd
    rwa [hnames] at this
  have hfresh : ∀ x d, (ps ++ own).find? (·.1 == x) = some (x, d) ∨ ((x, d) ∈ ps ++ own) →
      ∃ j : Nat, (ps ++ own)[j]? = some (x, d) := fun x d h => by
    rcases h with h | h
    · exact List.mem_iff_getElem?.mp (List.mem_of_find?_eq_some h)
    · exact List.mem_iff_getElem?.mp h
  have hjloc : ∀ (j : Nat) x d, (ps ++ own)[j]? = some (x, d) →
      lookupVar ((Store.allocVars s.locs.length names) ++ vars) x = some (s.locs.length + j) ∧ (Λ ++ (ps ++ own).map (fun (p : String × Ty) => Ty.subst sa p.2))[s.locs.length + j]? = some (d.subst sa) := by
    intro j x d hj
    have hnj : names[j]? = some x := by rw [← hnames, List.getElem?_map, hj]; rfl
    refine ⟨hln x _ (lookupVar_alloc hnd hnj), ?_⟩
    rw [List.getElem?_append_right (by rw [hw.len]; omega), hw.len, Nat.add_sub_cancel_left,
      List.getElem?_map, hj]
    rfl
  have hcore' : FrameCore P (c.lambdaCtx ps own) (Λ ++ (ps ++ own).map (fun (p : String × Ty) => Ty.subst sa p.2)) ((Store.allocVars s.locs.length names) ++ vars) me sa s2 := by
    refine ⟨fun x d hd => ?_, fun x y l' hx hy => ?_, fun x l' hm => ?_, fun hi => ?_,
      fun hi => absurd hi (by simpa [Ctx.lambdaCtx, Ctx.inInit] using hni), ?_, hcore.closed, hcore.bounded,
      fun x l' hl' => ?_, fun x l' hl' => ?_⟩
    · rcases hdecl' x d hd with ⟨j, hj⟩ | ⟨hx, hd0⟩
      · exact ⟨_, hjloc j x d hj⟩
      · obtain ⟨l, h1, h2⟩ := hcore.decls x d hd0
        exact ⟨l, by rw [hlv x hx]; exact h1, prefix_getElem? he12.tys h2⟩
    · by_cases hxn : x ∈ names <;> by_cases hyn : y ∈ names
      · obtain ⟨lx, hlx⟩ := hlook x hxn
        obtain ⟨ly, hly⟩ := hlook y hyn
        rw [hln x lx hlx] at hx; cases hx
        rw [hln y ly hly] at hy; cases hy
        obtain ⟨jx, hjx, rfl⟩ := lookupVar_alloc_inv hlx
        obtain ⟨jy, hjy, hjj⟩ := lookupVar_alloc_inv hly
        have : jx = jy := by omega
        subst this; rw [hjx] at hjy; cases hjy; rfl
      · obtain ⟨lx, hlx⟩ := hlook x hxn
        rw [hln x lx hlx] at hx; cases hx
        rw [hlv y hyn] at hy
        have := hcore.inStore y _ (lookupVar_mem hy)
        have := (hge x _ hlx).1; omega
      · obtain ⟨ly, hly⟩ := hlook y hyn
        rw [hln y ly hly] at hy; cases hy
        rw [hlv x hxn] at hx
        have := hcore.inStore x _ (lookupVar_mem hx)
        have := (hge y _ hly).1; omega
      · rw [hlv x hxn] at hx; rw [hlv y hyn] at hy
        exact hcore.inj x y l' hx hy
    · rcases List.mem_append.mp hm with hm | hm
      · have := mem_allocVars hm; omega
      · have := hcore.inStore x l' hm; omega
    · exact mono (hcore.self (by simpa [Ctx.lambdaCtx, Ctx.inInit] using hi))
    · obtain ⟨l, hl, hsa⟩ := hcore.selfObj
      refine ⟨l, hl, ?_⟩
      rw [hsa]; simp [Store.argsFor, hobjs]; rfl
    · -- The lambda's context pins what the method does.
      show s2.pins[l']? = some true ↔ x ∈ c.pinned
      by_cases hxn : x ∈ names
      · obtain ⟨lx, hlx⟩ := hlook x hxn
        rw [hln x lx hlx] at hl'; cases hl'
        exact ⟨fun _ => hpinN x hxn, fun _ => (fresh_pins hw.pinsLen hpins hlx).1.mpr hxn⟩
      · rw [hlv x hxn] at hl'
        rw [hpinsO l' (hcore.pinsIn x l' hl')]
        exact hcore.pins x l' hl'
    · by_cases hxn : x ∈ names
      · obtain ⟨lx, hlx⟩ := hlook x hxn
        rw [hln x lx hlx] at hl'; cases hl'
        exact (fresh_pins hw.pinsLen hpins hlx).2
      · rw [hlv x hxn] at hl'
        have := hcore.pinsIn x l' hl'
        rw [hpins]; simp; omega
  have hf2 : FrameOK P (c.lambdaCtx ps own) (Λ ++ (ps ++ own).map (fun (p : String × Ty) => Ty.subst sa p.2)) ⟨(Store.allocVars s.locs.length names) ++ vars, me, sa, none⟩ s2 [] :=
    ⟨hcore', by simp [ChainAt, Ctx.lambdaCtx], fun _ _ _ h => by simp [chainLocs] at h,
      fun _ h => by simp [chainLocs] at h, fun _ _ => rfl⟩
  have hs2 : Sat P (c.lambdaCtx ps own) (c.lambdaEnv Γ ps) ⟨(Store.allocVars s.locs.length names) ++ vars, me, sa, none⟩ s2 := by
    unfold Ctx.lambdaEnv
    refine Sat.foldl_set ps (fun p t hp => ?_) fun x t hm => ?_
    · obtain ⟨x, rfl, hd, _⟩ := Ctx.get_declEnv hp
      have hx : x ∉ names := fun hx => hnot x hx t hd
      obtain ⟨l, v, d, h1, h2, h3, h4, h5⟩ := (hsd.declStable hcore he12) _ _ hp
      refine ⟨l, v, d, by rw [hlv x hx]; exact h1, h2, ?_, h4, h5⟩
      rcases hdecl' x d (by
        simp only [Ctx.decl, Ctx.lambdaCtx] at h3 ⊢
        rw [List.find?_append]
        rw [List.find?_eq_none.mpr (fun q hq h => hx (by
          rw [← hnames]; simp at h; exact List.mem_map.mpr ⟨q, hq, h⟩))]
        exact h3) with ⟨j, hj⟩ | ⟨_, hd'⟩
      · exact absurd (by rw [← hnames]; exact List.mem_map.mpr ⟨(x, d), List.mem_of_getElem? hj, rfl⟩) hx
      · simp only [Ctx.decl, Ctx.lambdaCtx]
        rw [List.find?_append]
        rw [List.find?_eq_none.mpr (fun q hq h => hx (by
          rw [← hnames]; simp at h; exact List.mem_map.mpr ⟨q, hq, h⟩))]
        exact hd'
    · obtain ⟨v, hvm, hvt⟩ := zip_val_subst hvs x t (by rw [zip_fst_snd]; exact hm)
      have hninj : ∀ x y l, lookupVar (Store.allocVars s.locs.length names) x = some l → lookupVar (Store.allocVars s.locs.length names) y = some l → x = y := by
        intro x y l hx hy
        obtain ⟨jx, hjx, rfl⟩ := lookupVar_alloc_inv hx
        obtain ⟨jy, hjy, hjj⟩ := lookupVar_alloc_inv hy
        have : jx = jy := by omega
        subst this; rw [hjx] at hjy; cases hjy; rfl
      have hpnd : (ps.map (·.1)).Nodup := by
        rw [← hnames, List.map_append] at hnd; exact hnd.sublist (List.sublist_append_left _ _)
      obtain ⟨lx, hlx, hv⟩ := bindAll_val hninj hb hpnd
        (fun y _ l' hl' => by have := hge y l' hl'; simp; omega) x v hvm
      have hd : (c.lambdaCtx ps own).decl x = some t := by
        simp only [Ctx.decl, Ctx.lambdaCtx]
        rw [List.append_assoc]
        have hnd2 : ((ps ++ own).map (·.1)).Nodup := by rw [hnames]; exact hnd
        have := find_local_of_mem (rest := c.meth.locals) hnd2 (List.mem_append_left _ hm)
        rwa [List.append_assoc] at this
      exact ⟨lx, v, t, hln x lx hlx, hv, hd, mono hvt, mono hvt⟩
  have := ihe (c.lambdaCtx ps own) _ body ob _ s2 (Λ ++ (ps ++ own).map (fun (p : String × Ty) => Ty.subst sa p.2)) [] hc hty hw2 hf2 hs2
  revert this
  generalize eval P orc n _ s2 body = r
  intro hpost
  -- Writes: the body's own locals (fresh), and the method's it assigns
  -- (pinned, so marked).
  have hrestrict : ∀ l', l' < s.locs.length →
      (False ∨ evalW ⟨(Store.allocVars s.locs.length names) ++ vars, me, sa, none⟩ body l') →
      blkW none l' ∨ s.pins[l']? = some true := by
    rintro l' hl' (h | ⟨x, hx, hxl⟩ | h)
    · simp [blkW] at h
    · right
      by_cases hxn : x ∈ names
      · obtain ⟨lx, hlx⟩ := hlook x hxn
        rw [hln x lx hlx] at hxl; cases hxl
        have := (hge x _ hlx).1; omega
      · rw [hlv x hxn] at hxl
        exact (hcore.pins x l' hxl).mpr (hpinA x hx)
    · simp [blkW] at h
  have hnoW : ∀ l, initW (c.lambdaCtx ps own) ⟨(Store.allocVars s.locs.length names) ++ vars, me, sa, none⟩ l → False :=
    fun _ ⟨hi, _⟩ => by simp [Ctx.lambdaCtx, Ctx.inInit] at hi; simp [Ctx.inInit, hi] at hni
  cases r with
  | ok w s3 =>
    obtain ⟨Λ3, hw3, he3, _, hv3, _⟩ := hpost
    have he3 := he3.mono (Wo' := fun _ => False) (fun _ h => h) (fun l h => (hnoW l h).elim)
    refine ⟨Λ3, hw3, ((he12.trans he3 hw).mono (fun _ h => h) (fun _ h => h.elim id id)).restrictP
      hrestrict, ?_, by simp [BlkGiven, ChainAt, chainLocs]⟩
    have hct : c.ct = P.classes := by simp [Ctx.ct, hc]
    rw [hct] at hret
    exact hasTy_le hwf hv3 (Ty.subst_leK hwf sa hcore.bounded hret)
  | raised w s3 =>
    obtain ⟨Λ3, hw3, he3, _, hv3⟩ := hpost
    have he3 := he3.mono (Wo' := fun _ => False) (fun _ h => h) (fun l h => (hnoW l h).elim)
    exact ⟨Λ3, hw3, ((he12.trans he3 hw).mono (fun _ h => h) (fun _ h => h.elim id id)).restrictP
      hrestrict, hv3, by simp [BlkGiven, ChainAt, chainLocs]⟩
  | returned w s3 =>
    obtain ⟨_, _, _, _, _, hib, _⟩ := hpost
    simp [Ctx.lambdaCtx] at hib
  | timeout => trivial
  | stuck => exact hpost

/-- `initialize` (`mi`) run on object `l`, every field of which is set but
those of `mi`'s class to assign: its frame (as `send_succ` builds one),
then its body. -/
theorem init_run (hP : WfProg P) {n : Nat} (ihe : EvalGood P orc n) {s : Store} {Λ : List Ty}
    {mi : Method} {vs : List Value} {l : Nat} {o : Obj} (hw : WfStore P Λ s)
    (hmem : mi ∈ P.methods) (hname : mi.name = "initialize") (hblk : mi.block = none)
    (hvs : AllTy P s vs ((mi.params.map (·.2)).map (Ty.subst (s.argsFor P.classes l mi.owner))))
    (ho : s.objs[l]? = some o)
    (hsub : mi.owner ∈ P.classes.ancestors o.cls)
    (hset : ∀ i f, (P.classes.allFieldsAt o.cls o.args)[i]? = some f →
      ((P.classes.allFields mi.owner).length ≤ i ∨ f.required P.classes = false) →
      o.set[i]? = some true) :
    vs.length = mi.params.length ∧ ∃ s3, bindAll ⟨s.locs ++ (mi.locals.map (·.1)).map (fun _ => .nil), s.objs, s.procs,
      s.pins ++ (mi.locals.map (·.1)).map (fun x => decide (x ∈ mi.body.procAssigned)), s.builts⟩
        (Store.allocVars s.locs.length (mi.locals.map (·.1))) (mi.params.map (·.1)) vs = some s3 ∧
      s3.argsFor P.classes l mi.owner = s.argsFor P.classes l mi.owner ∧
      InitPost P l Λ s
        (eval P orc n ⟨Store.allocVars s.locs.length (mi.locals.map (·.1)), .obj l,
          s.argsFor P.classes l mi.owner, none⟩ s3 mi.body) := by
  have hwf := hP.classes
  obtain ⟨_, hclosed, hlen', hflen, hslen, _⟩ := hw.objs l o ho
  obtain ⟨σ, hσ⟩ := ClassTable.ancestorArgs_of_mem hwf o.cls o.args mi.owner hsub
  have hsa : s.argsFor P.classes l mi.owner = σ := by simp [Store.argsFor, ho, hσ]
  rw [hsa] at hvs ⊢
  obtain ⟨hwfm, oB, hty, _, hallset⟩ := hP.methods mi hmem
  have hni : (mi.name == "initialize") = true := by simp [hname]
  have hinInit : (⟨P, mi, false, false⟩ : Ctx).inInit = true := hni
  rw [hni] at hty
  simp only [if_true] at hty
  have hlenv : vs.length = mi.params.length := by rw [hvs.length]; simp
  refine ⟨hlenv, ?_⟩
  -- The frame: `initialize`'s locals at fresh locations.
  have hwfm' := hwfm
  simp only [Program.wfMethod, Bool.and_eq_true, decide_eq_true_eq] at hwfm'
  obtain ⟨⟨⟨⟨⟨_, hplen⟩, hnd⟩, hpre⟩, _⟩, _⟩ := hwfm'
  have hcl : ∀ x d, (⟨P, mi, false, false⟩ : Ctx).decl x = some d →
      ∃ j, mi.locals[j]? = some (x, d) := fun x d hd => by
    simp only [Ctx.decl, Option.map_eq_some_iff] at hd
    obtain ⟨⟨y, d'⟩, hf, hd'⟩ := hd
    simp at hd'; subst hd'
    have hp := List.find?_some hf
    simp at hp; subst hp
    exact List.mem_iff_getElem?.mp (List.mem_of_find?_eq_some hf)
  have hlookj : ∀ j x d, mi.locals[j]? = some (x, d) →
      lookupVar (Store.allocVars s.locs.length (mi.locals.map (·.1))) x = some (s.locs.length + j) :=
    fun j x d hj => lookupVar_alloc hnd (by simp [hj])
  have hptake : mi.params = mi.locals.take mi.params.length := by
    apply List.ext_getElem (by simp; omega)
    intro i h1 h2
    have hil : i < mi.locals.length := by omega
    have hz : (mi.params.zip mi.locals)[i]? = some (mi.params[i], mi.locals[i]) := by
      simp [List.zip, List.getElem?_zipWith, h1, hil]
    have := List.all_eq_true.mp hpre _ (List.mem_iff_getElem?.mpr ⟨i, hz⟩)
    simp at this; simp [this]
  have hpnd : (mi.params.map (·.1)).Nodup := by
    rw [hptake, List.map_take]; exact hnd.sublist (List.take_sublist _ _)
  have hexists : ∀ x ∈ mi.params.map (·.1),
      ∃ l, lookupVar (Store.allocVars s.locs.length (mi.locals.map (·.1))) x = some l := by
    intro x hx
    obtain ⟨⟨y, t⟩, hm, rfl⟩ := List.mem_map.mp hx
    obtain ⟨j, hj⟩ := hcl y t (decl_param hwfm hm)
    exact ⟨_, hlookj j y t hj⟩
  obtain ⟨s3, hb⟩ := bindAll_some (vars := Store.allocVars s.locs.length (mi.locals.map (·.1)))
    ⟨s.locs ++ (mi.locals.map (·.1)).map (fun _ => .nil), s.objs, s.procs,
      s.pins ++ (mi.locals.map (·.1)).map (fun x => decide (x ∈ mi.body.procAssigned)), s.builts⟩ (by rw [List.length_map, hlenv])
    hexists
  obtain ⟨hobjs, hlen3, hsame⟩ := bindAll_same hb
  have hprocs := bindAll_procs hb
  have hpins := bindAll_pins hb
  have hbts := bindAll_builts hb
  simp only at hpins
  refine ⟨s3, hb, by simp only [Store.argsFor, hobjs, ho, Option.bind_some, hσ, Option.getD_some], ?_⟩
  simp only [List.length_append, List.length_map] at hlen3
  have hge : ∀ x l', lookupVar (Store.allocVars s.locs.length (mi.locals.map (·.1))) x = some l' →
      s.locs.length ≤ l' ∧ l' < s.locs.length + mi.locals.length := fun x l' h => by
    have := mem_allocVars (lookupVar_mem h); simpa using this
  have mono : ∀ {v : Value} {t : Ty}, s.hasTy P v t → s3.hasTy P v t := fun h => by
    unfold Store.hasTy Store.hasType Store.typeOf at *; rw [hobjs, hprocs, hbts]; exact h
  have he23 : Ext P (fun _ => False) (fun _ => False) Λ (Λ ++ (mi.locals.map (·.2)).map (Ty.subst σ)) s s3 := by
    refine ⟨List.prefix_append _ _, fun l' v hv => ⟨v, ?_, .inl rfl⟩, fun l' o' ho' =>
      ⟨o', by rw [hobjs]; exact ho', rfl, rfl, rfl, fun _ h => h⟩,
      fun _ o1 o2 h1 h2 _ _ _ _ _ => by rw [hobjs, h1] at h2; cases h2; rfl,
      by rw [hprocs]; exact List.prefix_refl _, by rw [hpins]; exact List.prefix_append _ _, by rw [hbts]; exact List.prefix_refl _⟩
    have hl' := (List.getElem?_eq_some_iff.mp hv).1
    rw [hsame l' fun x _ hx => by have := (hge x l' hx).1; omega]
    simp [List.getElem?_append_left hl', hv]
  have hw3 : WfStore P (Λ ++ (mi.locals.map (·.2)).map (Ty.subst σ)) s3 :=
    ⟨by simp [hw.len, hlen3], by rw [hpins, hlen3]; simp [hw.pinsLen], fun l' o' ho' => by
      rw [hobjs] at ho'
      obtain ⟨a, a1, a2, b, b2, d⟩ := hw.objs l' o' ho'
      exact ⟨a, a1, a2, b, b2, fun i v f h0 h1 h2 => mono (d i v f h0 h1 h2)⟩,
    fun l' o' ho' => by rw [hobjs] at ho'; exact hw.noEnum l' o' ho',
    fun l' o' ho' => by rw [hobjs] at ho'; exact hw.bounds l' o' ho',
    fun i p hp => by rw [hprocs] at hp; exact (hw.procs i p hp).stable he23,
      fun i k as h' => by rw [hbts] at h'; exact hw.builts i k as h'⟩
  have ho3 : s3.objs[l]? = some o := by rw [hobjs]; exact ho
  obtain ⟨rest, hrest⟩ := allFields_prefix hwf hsub
  have hsa3 : s3.argsFor P.classes l mi.owner = σ := by simp [Store.argsFor, ho3, hσ]
  have hcore : FrameCore P ⟨P, mi, false, false⟩ (Λ ++ (mi.locals.map (·.2)).map (Ty.subst σ))
      (Store.allocVars s.locs.length (mi.locals.map (·.1))) (.obj l) σ s3 := by
    refine ⟨fun x d hd => ?_, fun x y l' hx hy => ?_, fun x l' hm => ?_,
      fun h => (by rw [hinInit] at h; cases h),
      fun _ => ⟨l, o, rfl, ho3, hsub, fun i h1 h2 => ?_, fun i f hf _ hr => hset i f hf (.inr hr)⟩,
      ⟨l, rfl, hsa3.symm⟩, ClassTable.ancestorArgs_closed P.classes hσ hclosed,
      ClassTable.ancestorArgs_in hwf hσ hlen' (hw.bounds l o ho),
      fun x l' hl' => (fresh_pins hw.pinsLen hpins hl').1, fun x l' hl' => (fresh_pins hw.pinsLen hpins hl').2⟩
    · obtain ⟨j, hj⟩ := hcl x d hd
      refine ⟨_, hlookj j x d hj, ?_⟩
      have hjl := (List.getElem?_eq_some_iff.mp hj).1
      rw [List.getElem?_append_right (by rw [hw.len]; omega)]
      simp [hw.len, hj]
    · obtain ⟨jx, hjx, rfl⟩ := lookupVar_alloc_inv hx
      obtain ⟨jy, hjy, hjj⟩ := lookupVar_alloc_inv hy
      have : jx = jy := by omega
      subst this; rw [hjx] at hjy; cases hjy; rfl
    · have := mem_allocVars hm; simp [hlen3] at this ⊢; omega
    · -- A field past `initialize`'s class: set.
      have hi : i < (P.classes.allFieldsAt o.cls o.args).length := by
        rw [ClassTable.allFieldsAt_length]; omega
      exact hset i _ (List.getElem?_eq_getElem hi) (.inl h1)
  have hf3 : FrameOK P ⟨P, mi, false, false⟩ (Λ ++ (mi.locals.map (·.2)).map (Ty.subst σ))
      ⟨Store.allocVars s.locs.length (mi.locals.map (·.1)), .obj l, σ, none⟩ s3 [] :=
    ⟨hcore, by simp [ChainAt, hblk], fun _ _ _ h => by simp [chainLocs] at h,
      fun _ h => by simp [chainLocs] at h, fun _ _ => rfl⟩
  have hs3 : Sat P ⟨P, mi, false, false⟩ (mi.params.map (fun (x, t) => (.local x, t)) ++
      Program.heldEnv P.classes (Ctx.fields ⟨P, mi, false, false⟩))
      ⟨Store.allocVars s.locs.length (mi.locals.map (·.1)), .obj l, σ, none⟩ s3 := by
    intro p t hp
    rw [Env.get_append] at hp
    split at hp
    · cases hp
      rename_i hp
      obtain ⟨x, rfl, hm⟩ := params_get hp
      have hd := decl_param hwfm hm
      obtain ⟨v, hvm, hvt⟩ := zip_val_subst hvs x t (by rw [zip_fst_snd]; exact hm)
      obtain ⟨lx, hlx, hv⟩ := bindAll_val hcore.inj hb hpnd
        (fun y _ l' hl' => by have := hge y l' hl'; simp; omega) x v hvm
      exact ⟨lx, v, t, hlx, hv, hd, mono hvt, mono hvt⟩
    · have := sat_held (c := ⟨P, mi, false, false⟩) (j := (Ctx.fields ⟨P, mi, false, false⟩).length) hwf rfl
        hw3 (fr := ⟨Store.allocVars s.locs.length (mi.locals.map (·.1)), .obj l, σ, none⟩) rfl ho3 hsub
        hsa3.symm
        (fun i hi f hf hr => hset i _ (fieldAt_coherent hwf hlen' hσ hf)
          (.inr (required_subst hwf σ hr)))
      rw [List.take_length] at this
      exact this p t hp
  have := ihe ⟨P, mi, false, false⟩ _ mi.body oB _ s3 _ [] rfl hty hw3 hf3 hs3
  revert this
  generalize eval P orc n _ s3 mi.body = r
  intro this
  -- No location of `s` written, only the object's immutable fields.
  have hfin : ∀ {Λ4 : List Ty} {s4 : Store},
      Ext P (evalW ⟨Store.allocVars s.locs.length (mi.locals.map (·.1)), .obj l, σ, none⟩ mi.body)
        (initW ⟨P, mi, false, false⟩ ⟨Store.allocVars s.locs.length (mi.locals.map (·.1)), .obj l, σ, none⟩)
        (Λ ++ (mi.locals.map (·.2)).map (Ty.subst σ)) Λ4 s3 s4 →
      Ext P (fun _ => False) (· = l) Λ Λ4 s s4 := fun he4 =>
    ((he23.trans he4 hw).mono (fun _ h => h) (fun l' h => h.elim False.elim fun ⟨_, _, h⟩ => by
      cases h; rfl)).restrict fun l' hl' h => by
        rcases h with h | ⟨x, _, hx⟩ | h
        · exact h
        · have := (hge x l' hx).1; omega
        · simp [blkW] at h
  cases r with
  | ok v s4 =>
    obtain ⟨Λ4, hw4, he4, hf4, _, ⟨Γ4, hΓ4, hs4⟩, _⟩ := this
    refine ⟨Λ4, hw4, hfin he4, ?_⟩
    have hall := hallset hname
    rw [hΓ4] at hall
    have := self_typed hwf rfl hf4 hw4 hs4 (by simpa [hinInit] using hall)
    obtain ⟨_, ha, _⟩ := hasTy_iff.mp this
    simp [ha]
  | returned v s4 =>
    obtain ⟨Λ4, hw4, he4, _, _, _, hmade⟩ := this
    exact ⟨Λ4, hw4, hfin he4, hmade hinInit⟩
  | stuck => exact (this : False).elim
  | raised v s4 =>
    obtain ⟨Λ4, hw4, he4, _, hv⟩ := this
    exact ⟨Λ4, hw4, hfin he4, hv⟩
  | timeout => trivial

/-! ### `super` -/

/-- After setting each field to its type: a field's entry is its type, the
other paths' what they were. -/
theorem Env.get_foldl_set_field : ∀ (fs : List Field) (Δ : Env) (p : Path) (t : Ty),
    (fs.foldl (fun Δ f => Δ.set (.field f.name) f.ty) Δ).get p = some t →
    (∃ f ∈ fs, p = .field f.name ∧ t = f.ty) ∨ ((∀ f ∈ fs, p ≠ .field f.name) ∧ Δ.get p = some t)
  | [], _, _, _, h => .inr ⟨fun _ h => (by cases h), h⟩
  | f :: fs, Δ, p, t, h => by
    simp only [List.foldl_cons] at h
    rcases Env.get_foldl_set_field fs _ p t h with ⟨g, hg, h1, h2⟩ | ⟨hne, h'⟩
    · exact .inl ⟨g, List.mem_cons_of_mem _ hg, h1, h2⟩
    · rw [Env.get_set] at h'
      split at h'
      · rename_i hp; cases h'; exact .inl ⟨f, List.mem_cons_self .., hp, rfl⟩
      · rename_i hp
        exact .inr ⟨fun g hg => (List.mem_cons.mp hg).elim (fun e => e ▸ hp) (hne g), h'⟩

/-- A class's superclass is above it. -/
theorem super_mem_ancestors {ct : ClassTable} (hwf : WfClasses ct) {k d : Nat}
    (h : (ct[k]?).bind (·.super) = some d) : d ∈ ct.ancestors k := by
  rw [ClassTable.ancestors_eq hwf]
  have : ClassTable.superOf ct k = some d := h
  simp [this, ClassTable.mem_ancestors_self hwf]

/-- Before `super` into `d`, the superclass of the method's class: each
field (as the class sees it) holds a value, or is one of `d`'s layout,
to assign. -/
theorem preSuper_field (hwf : WfClasses P.classes) {c : Ctx} (hc : c.prog = P) {d : Nat} {Γ : Env}
    (hd : (P.classes[c.meth.owner]?).bind (·.super) = some d) (hpre : c.preSuper d Γ = true)
    {i : Nat} {f : Field} (hf : c.fields[i]? = some f) :
    (Γ.get (.field f.name)).isSome = true ∨
      (i < (P.classes.allFields d).length ∧ f.required P.classes = true) := by
  subst hc
  unfold Ctx.preSuper at hpre
  simp only [Ctx.ct] at hpre
  have := List.all_eq_true.mp hpre f (List.mem_of_getElem? hf)
  simp only [Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true, beq_iff_eq] at this
  rcases this with ⟨⟨g, hg, hgn⟩, hreq⟩ | h
  · refine .inr ⟨?_, hreq⟩
    have hk : c.meth.owner < c.prog.classes.length := by
      cases h : c.prog.classes[c.meth.owner]? with
      | none => rw [h] at hd; cases hd
      | some _ => exact (List.getElem?_eq_some_iff.mp h).1
    obtain ⟨rest, hrest⟩ := allFields_prefix hwf (super_mem_ancestors hwf hd)
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hg
    have hjl := (List.getElem?_eq_some_iff.mp hj).1
    have hjk : (c.prog.classes.allFields c.meth.owner)[j]? = some g := by
      rw [hrest, List.getElem?_append_left hjl]; exact hj
    -- The field at `i` as declared has `f`'s name, so it is at `j`.
    obtain ⟨d', f0, _, hf0, hff⟩ := ClassTable.allFieldsAt_some c.prog.classes hf
    have hname : f0.name = f.name := by rw [hff]
    have h1 := fieldIndex_at hwf hk hf0
    have h2 := fieldIndex_at hwf hk hjk
    rw [hgn, ← hname, h1] at h2; cases h2
    exact hjl
  · exact .inl h

/-- A field with an entry in an environment that held is set, and stays
so as objects grow. -/
theorem Sat.field_set (hwf : WfClasses P.classes) {c : Ctx} (hc : c.prog = P) {Γ : Env}
    {fr : Frame} {s s1 : Store} (hs : Sat P c Γ fr s) (hg : ObjsGrow s s1) {l i : Nat} {o1 : Obj}
    {f : Field} (hl : fr.self = .obj l) (ho1 : s1.objs[l]? = some o1)
    (hcls : o1.cls < P.classes.length) (hf : (P.classes.allFields o1.cls)[i]? = some f)
    (hin : (Γ.get (.field f.name)).isSome = true) : o1.set[i]? = some true := by
  subst hc
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hin
  obtain ⟨l', o, _, j, h1, h2, _, h4, _, h6, _⟩ := hs _ _ ht
  rw [hl] at h1; cases h1
  obtain ⟨o1', ho1', hc1, _, _, hs1⟩ := hg l o h2
  rw [ho1] at ho1'; cases ho1'
  rw [← hc1, fieldIndex_at hwf hcls hf] at h4; cases h4
  exact hs1 _ h6

/-- At `super` into `d` (its arguments evaluated, objects grown): each
field of `self` (as the object has it) is set, or one of `d`'s layout
that the class sees as one to assign. -/
theorem super_pre (hwf : WfClasses P.classes) {c : Ctx} (hc : c.prog = P) {d : Nat} {Γ : Env}
    {fr : Frame} {Λ1 : List Ty} {s s1 : Store} (hgo : c.superOk d Γ = true) (hs : Sat P c Γ fr s)
    (hg : ObjsGrow s s1) (hw1 : WfStore P Λ1 s1) {l : Nat} {o1 : Obj} (hl : fr.self = .obj l)
    (ho1 : s1.objs[l]? = some o1) (hk1 : c.meth.owner ∈ P.classes.ancestors o1.cls)
    (hbeyond : ∀ i, (P.classes.allFields c.meth.owner).length ≤ i → i < o1.set.length →
      o1.set[i]? = some true) :
    ∀ (i : Nat) (f : Field), (P.classes.allFieldsAt o1.cls o1.args)[i]? = some f →
      o1.set[i]? = some true ∨
        (i < (P.classes.allFields d).length ∧ ∃ fs, c.fields[i]? = some fs ∧ fs.required P.classes = true) := by
  subst hc
  simp only [Ctx.superOk, Bool.and_eq_true, beq_iff_eq] at hgo
  obtain ⟨⟨_, hsup⟩, hpre⟩ := hgo
  obtain ⟨hcls, _, _, hflen, hslen, _⟩ := hw1.objs l o1 ho1
  obtain ⟨rest, hrest⟩ := allFields_prefix hwf hk1
  intro i f hf
  by_cases hik : i < (c.prog.classes.allFields c.meth.owner).length
  · have hik' : i < c.fields.length := by rwa [Ctx.fields, ClassTable.allFieldsAt_length]
    have hfs : c.fields[i]? = some c.fields[i] := by simp [hik']
    obtain ⟨d', f0, _, hf0, hff⟩ := ClassTable.allFieldsAt_some c.prog.classes hfs
    have hfo : (c.prog.classes.allFields o1.cls)[i]? = some f0 := by
      rw [hrest, List.getElem?_append_left hik]; exact hf0
    rcases preSuper_field hwf rfl hsup hpre hfs with hin | h
    · have hname : c.fields[i].name = f0.name := by rw [hff]
      rw [hname] at hin
      exact .inl (hs.field_set hwf rfl hg hl ho1 hcls hfo hin)
    · exact .inr ⟨h.1, _, hfs, h.2⟩
  · have := (List.getElem?_eq_some_iff.mp hf).1
    rw [ClassTable.allFieldsAt_length] at this
    exact .inl (hbeyond i (by omega) (by omega))

/-- After `super`, `self` made: each field at its declared type (as the
class sees it, with the frame's arguments), the locals as before. -/
theorem Sat.afterSuper (hwf : WfClasses P.classes) {c : Ctx} (hc : c.prog = P) {Δ : Env}
    {fr : Frame} {Λ Λ' : List Ty} {s s' : Store} {Wo : Nat → Prop} {l : Nat} {o : Obj}
    (hs : Sat P c Δ fr s) (he : Ext P (fun _ => False) Wo Λ Λ' s s') (hw' : WfStore P Λ' s')
    (hcore : FrameCore P c Λ fr.vars fr.self fr.selfArgs s) (hpd : PinsDecl c Δ)
    (hl : fr.self = .obj l) (ho : s.objs[l]? = some o) (hk : c.meth.owner ∈ P.classes.ancestors o.cls)
    (hsa : fr.selfArgs = s.argsFor P.classes l c.meth.owner)
    (hmade : (s'.typeOf (.obj l)).isSome = true) : Sat P c (c.afterSuper Δ) fr s' := by
  subst hc
  intro p t hp
  rcases Env.get_foldl_set_field _ Δ p t hp with ⟨f, hf, rfl, rfl⟩ | ⟨hne, hp'⟩
  · obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hmade
    obtain ⟨o', ho', hall, _⟩ := typeOf_obj ha
    obtain ⟨o'', ho'', hc', ha', _, _⟩ := he.grow l o ho
    rw [ho'] at ho''; cases ho''
    obtain ⟨hcls, _, hlen', hflen, hslen, hty⟩ := hw'.objs l o' ho'
    have hk' : c.meth.owner ∈ c.prog.classes.ancestors o'.cls := by rw [hc']; exact hk
    have hown : c.meth.owner < c.prog.classes.length :=
      Nat.lt_of_le_of_lt (ClassTable.ancestors_le hwf _ _ hk') hcls
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hf
    obtain ⟨d, f0, _, hf0, hff⟩ := ClassTable.allFieldsAt_some c.prog.classes hj
    obtain ⟨rest, hrest⟩ := allFields_prefix hwf hk'
    have hjl := (List.getElem?_eq_some_iff.mp hf0).1
    have hfo : (c.prog.classes.allFields o'.cls)[j]? = some f0 := by
      rw [hrest, List.getElem?_append_left hjl]; exact hf0
    have hname : f.name = f0.name := by rw [hff]
    have hfl : j < o'.fields.length := by rw [hflen]; exact (List.getElem?_eq_some_iff.mp hfo).1
    have hset : o'.set[j]? = some true := all_id_iff.mp hall j (by omega)
    obtain ⟨σ, hσ⟩ := ClassTable.ancestorArgs_of_mem hwf o'.cls o'.args c.meth.owner hk'
    have hsa' : fr.selfArgs = σ := by
      rw [hsa]; simp [Store.argsFor, ho, ← hc', ← ha', hσ]
    have hfat := fieldAt_coherent hwf hlen' hσ hj
    refine ⟨l, o', f, j, hl, ho', fieldAt?_at hwf hown _ hj, by rw [hname]; exact fieldIndex_at hwf hcls hfo,
      by rw [hsa']; exact hfat, hset, fun _ => ⟨o'.fields[j], by simp [hfl], ?_⟩⟩
    rw [hsa']
    exact hty j _ _ hset (by simp [hfl]) hfat
  · cases p with
    | «local» x =>
      exact (hs _ _ hp').local_stable he (fun _ _ h => h) hcore (hpd x t hp')
    | field g =>
      obtain ⟨_, _, fd, _, _, _, h3, _⟩ := hs _ _ hp'
      simp only [Ctx.field?, ClassTable.fieldAt?] at h3
      have hn := List.find?_some h3
      simp only [beq_iff_eq] at hn
      exact absurd (by rw [hn]) (hne fd (List.mem_of_find?_eq_some h3))

/-- What `super` gives once `d`'s `initialize` (if any) made `self`. -/
theorem Post.ofSuper (hwf : WfClasses P.classes) {c : Ctx} (hc : c.prog = P) {d : Nat} {args : List Expr} {Δ : Env}
    {fr : Frame} {ws : List (Ctx × Env × Out)} {Λ Λ1 Λ4 : List Ty} {s s1 s4 : Store} {l : Nat}
    {o1 : Obj} (hii : c.inInit = true) (hib : c.inBlock = false) (hw : WfStore P Λ s)
    (he1 : Ext P (evalWs fr args) (initW c fr) Λ Λ1 s s1) (hf1 : FrameOK P c Λ1 fr s1 ws)
    (hs1 : Sat P c Δ fr s1) (hl : fr.self = .obj l) (ho1 : s1.objs[l]? = some o1)
    (hk1 : c.meth.owner ∈ P.classes.ancestors o1.cls)
    (hsa : fr.selfArgs = s1.argsFor P.classes l c.meth.owner) (hw4 : WfStore P Λ4 s4)
    (he4 : Ext P (fun _ => False) (· = l) Λ1 Λ4 s1 s4) (hmade : (s4.typeOf (.obj l)).isSome = true) :
    Post P c (.plain [.nil] (c.afterSuper (c.afterCall Δ))) fr ws Λ s (evalW fr (.superInit d args)) (.ok .nil s4) := by
  subst hc
  have hs4 := (hs1.reset (xs := c.pinned) : Sat _ c (c.afterCall Δ) fr s1).afterSuper hwf rfl he4 hw4 hf1.core
    (pinsDecl_reset fun _ h => h) hl ho1 hk1 hsa hmade
  exact ⟨Λ4, hw4, (he1.trans he4 hw).mono
      (fun l' h => h.elim (evalWs_mono (by simp [Expr.assigned]) l') False.elim)
      (fun l' h => h.elim id fun h => h ▸ ⟨hii, hib, hl⟩),
    hf1.stable he4 (fun _ _ h => h) (fun _ _ => hf1.initBlk hii hib), hasTy_lit_nil,
    ⟨_, rfl, hs4⟩, fun _ => ⟨_, rfl, hs4⟩, fun _ => ⟨_, rfl, hs4⟩⟩

/-- The arguments the superclass `d` gets, as the body names them, with the
frame's arguments: what the object's class gives `d`; and through `d` to
the owner of the `initialize` found there. -/
theorem superArgs_runtime (hwf : WfClasses P.classes) {c : Ctx} (hc : c.prog = P) {d : Nat}
    (hsup : (P.classes[c.meth.owner]?).bind (·.super) = some d) {Λ : List Ty} {s : Store}
    (hw : WfStore P Λ s) {l : Nat} {o : Obj} (ho : s.objs[l]? = some o)
    (hk : c.meth.owner ∈ P.classes.ancestors o.cls) {sa : List Ty}
    (hsa : sa = s.argsFor P.classes l c.meth.owner) {owner0 : Nat} {bs : List Ty}
    (hbs : P.classes.ancestorArgs d (c.superArgs d) owner0 = some bs) :
    s.argsFor P.classes l owner0 = Ty.substArgs sa bs := by
  subst hc
  obtain ⟨_, _, hlen, _, _, _⟩ := hw.objs l o ho
  obtain ⟨σ, hσ⟩ := ClassTable.ancestorArgs_of_mem hwf o.cls o.args c.meth.owner hk
  have hsa' : sa = σ := by rw [hsa]; simp [Store.argsFor, ho, hσ]
  subst hsa'
  have hσl := ClassTable.ancestorArgs_length hwf o.cls o.args c.meth.owner sa hσ hlen
  have hd : d ∈ c.prog.classes.ancestors c.meth.owner := super_mem_ancestors hwf hsup
  obtain ⟨τ, hτ⟩ := ClassTable.ancestorArgs_of_mem hwf c.meth.owner (c.prog.classes.selfArgs c.meth.owner) d hd
  have hτ' : c.superArgs d = τ := by simp [Ctx.superArgs, Ctx.selfArgs, Ctx.ct, hτ]
  rw [hτ'] at hbs
  -- Through the frame's arguments, `d`'s arguments from the object.
  have h1 : c.prog.classes.ancestorArgs c.meth.owner sa d = some (Ty.substArgs sa τ) := by
    have := ClassTable.ancestorArgs_subst c.prog.classes sa hτ
    rwa [substArgs_selfArgs c.prog.classes hσl] at this
  have h2 := ClassTable.ancestorArgs_trans hwf hσ h1
  have h3 := ClassTable.ancestorArgs_subst c.prog.classes sa hbs
  have h4 := ClassTable.ancestorArgs_trans hwf h2 h3
  simp [Store.argsFor, ho, h4]

/-- `new`'s type arguments, through the frame's arguments: within the
class's bounds, as the checker compared them. -/
theorem argsWf_in (hwf : WfClasses P.classes) {c : Ctx} (hc : c.prog = P) {k : Nat} {targs : List Ty}
    (h : c.argsWf k targs = true) {σ : List Ty} (hσ : ArgsIn P.classes c.bounds σ) :
    ArgsIn P.classes (P.classes.boundsOf k) (Ty.substArgs σ targs) := by
  subst hc
  unfold Ctx.argsWf at h
  cases hk : c.ct[k]? with
  | none => rw [hk] at h; cases h
  | some cl =>
    rw [hk] at h
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
    obtain ⟨⟨⟨⟨⟨hlen, _⟩, hall⟩, _⟩, _⟩, _⟩ := h
    have hk' : c.prog.classes[k]? = some cl := hk
    have hb : c.prog.classes.boundsOf k = cl.bounds := by simp [ClassTable.boundsOf, hk']
    rw [hb]
    intro i
    cases hi : targs[i]? with
    | none =>
      have : (Ty.substArgs σ targs)[i]? = none := by rw [Ty.substArgs_getElem?, hi]; rfl
      rw [this, Ty.boundOf_out]
      · exact Ty.le_top hwf _
      · have hbl := hwf.boundsLen k cl (by simpa [Ctx.ct] using hk)
        have := List.getElem?_eq_none_iff.mp hi
        omega
    | some t =>
      rw [Ty.substArgs_getElem?, hi]
      simp only [Option.map_some, Option.getD_some]
      have := Ty.subst_leK hwf σ hσ (hall (t, i) (List.mem_zipIdx_iff_getElem?.mpr hi))
      rwa [Ty.subst_closed_id σ _ (Ty.boundOf_closed _ _)] at this

/-- A built-in call's result of a built-in generic class, through the
frame's arguments: a class, its arguments as many as its parameters and
within their bounds. -/
theorem builtinOk_facts (hwf : WfClasses P.classes) {c : Ctx} (hc : c.prog = P) {k : Nat}
    {targs : List Ty} (h : c.builtinOk [.cls k targs] = true) (hkb : P.classes.kindOf k = .builtin)
    {σ : List Ty} (hσ : ArgsIn P.classes c.bounds σ) :
    k < P.classes.length ∧
      (Ty.substArgs σ targs).length = (((P.classes[k]?).map (·.params)).getD []).length ∧
      ArgsIn P.classes (P.classes.boundsOf k) (Ty.substArgs σ targs) := by
  subst hc
  unfold Ctx.builtinOk at h
  simp only [hkb, bne_self_eq_false, Bool.false_or] at h
  cases hk : c.ct[k]? with
  | none => rw [hk] at h; cases h
  | some cl =>
    rw [hk] at h
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
    obtain ⟨⟨hlen, _⟩, hall⟩ := h
    have hk' : c.prog.classes[k]? = some cl := hk
    refine ⟨(List.getElem?_eq_some_iff.mp hk').1, by rw [Ty.substArgs_length]; simp [hk', hlen], ?_⟩
    have hb : c.prog.classes.boundsOf k = cl.bounds := by simp [ClassTable.boundsOf, hk']
    rw [hb]
    intro i
    cases hi : targs[i]? with
    | none =>
      have : (Ty.substArgs σ targs)[i]? = none := by rw [Ty.substArgs_getElem?, hi]; rfl
      rw [this, Ty.boundOf_out]
      · exact Ty.le_top hwf _
      · have hbl := hwf.boundsLen k cl (by simpa [Ctx.ct] using hk)
        have := List.getElem?_eq_none_iff.mp hi
        omega
    | some t =>
      rw [Ty.substArgs_getElem?, hi]
      simp only [Option.map_some, Option.getD_some]
      have := Ty.subst_leK hwf σ hσ (hall (t, i) (List.mem_zipIdx_iff_getElem?.mpr hi))
      rwa [Ty.subst_closed_id σ _ (Ty.boundOf_closed _ _)] at this

/-- `new` makes no object of an `enum` itself, nor of a procedures'
class, nor of a built-in one. -/
theorem argsWf_kind {c : Ctx} {k : Nat} {targs : List Ty} (h : c.argsWf k targs = true) :
    c.prog.classes.kindOf k ≠ .enumC ∧ c.prog.classes.kindOf k ≠ .proc ∧
      c.prog.classes.kindOf k ≠ .builtin := by
  unfold Ctx.argsWf at h
  cases hk : c.ct[k]? with
  | none => rw [hk] at h; cases h
  | some cl =>
    rw [hk] at h
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    have hk' : c.prog.classes[k]? = some cl := hk
    exact ⟨by simp [ClassTable.kindOf, hk', h.1.1.2], by simp [ClassTable.kindOf, hk', h.1.2],
      by simp [ClassTable.kindOf, hk', h.2]⟩

/-- A comparison the checker made (with the method's class's bounds),
through the frame's arguments (within them). -/
theorem FrameOK.substLe {c : Ctx} {Λ : List Ty} {fr : Frame} {s : Store} {ws : List (Ctx × Env × Out)}
    (hwf : WfClasses c.prog.classes) (hf : FrameOK c.prog c Λ fr s ws) {t u : Ty}
    (h : Ty.le c.ct c.bounds t u = true) :
    Ty.le c.prog.classes [] (t.subst fr.selfArgs) (u.subst fr.selfArgs) = true :=
  Ty.subst_leK hwf fr.selfArgs hf.core.bounded h

/-- Values of types below others, both seen through the frame's arguments. -/
theorem AllTy.le_subst (hwf : WfClasses P.classes) {s : Store} {σ κ : List Ty}
    (hσ : ArgsIn P.classes κ σ) {vs : List Value} {ts us : List Ty}
    (h : AllTy P s vs (ts.map (Ty.subst σ))) (hl : ts.length = us.length)
    (ha : ((ts.zip us).all fun (t, u) => t.le P.classes κ u) = true) :
    AllTy P s vs (us.map (Ty.subst σ)) := by
  induction ts generalizing vs us with
  | nil => cases us with
    | nil => cases vs with
      | nil => trivial
      | cons => exact h.elim
    | cons => simp at hl
  | cons t ts ih =>
    cases us with
    | nil => simp at hl
    | cons u us =>
      cases vs with
      | nil => exact h.elim
      | cons v vs =>
        simp only [List.map_cons, AllTy] at h ⊢
        simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at ha
        exact ⟨hasTy_le hwf h.1 (Ty.subst_leK hwf σ hσ ha.1), ih h.2 (by simpa using hl) ha.2⟩

/-- Arguments of types fitting the parameters (`argsOk`), both seen through
the frame's arguments. -/
theorem AllTy.le_params_subst (hwf : WfClasses P.classes) {s : Store} {σ κ : List Ty}
    (hσ : ArgsIn P.classes κ σ) {vs : List Value} {ts : List Ty} {ps : List (String × Ty)}
    (h : AllTy P s vs (ts.map (Ty.subst σ))) (hl : ts.length = ps.length)
    (ha : ((ts.zip ps).all fun (t, (_, u)) => t.le P.classes κ u) = true) :
    AllTy P s vs ((ps.map (·.2)).map (Ty.subst σ)) := by
  induction ts generalizing vs ps with
  | nil => cases ps with
    | nil => cases vs with
      | nil => trivial
      | cons => exact h.elim
    | cons => simp at hl
  | cons t ts ih =>
    cases ps with
    | nil => simp at hl
    | cons p ps =>
      cases vs with
      | nil => exact h.elim
      | cons v vs =>
        simp only [List.map_cons, AllTy] at h ⊢
        simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at ha
        exact ⟨hasTy_le hwf h.1 (Ty.subst_leK hwf σ hσ ha.1), ih h.2 (by simpa using hl) ha.2⟩

/-- What `argsWf` says: the class is one, with as many parameters as
arguments. -/
theorem argsWf_facts {c : Ctx} {k : Nat} {targs : List Ty} (h : c.argsWf k targs = true) :
    k < c.prog.classes.length ∧ targs.length = (((c.prog.classes[k]?).map (·.params)).getD []).length := by
  unfold Ctx.argsWf at h
  cases hk : c.ct[k]? with
  | none => rw [hk] at h; cases h
  | some cl =>
    rw [hk] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨(List.getElem?_eq_some_iff.mp hk).1, by simp [Ctx.ct] at hk; simp [hk, h.1]⟩

variable (hP : WfProg P) (horc : OracleOK P orc) {n : Nat} (ih : Good P orc n)
include hP horc ih

theorem eval_succ : EvalGood P orc (n + 1) := by
  intro c Γ e o fr s Λ ws hc ht hw hf hs
  subst hc
  have hwf := hP.classes
  cases ht with
  | nil => exact post_plain hw hf hs hasTy_lit_nil
  | tru => exact post_plain hw hf hs hasTy_lit_bool
  | fls => exact post_plain hw hf hs hasTy_lit_bool
  | int => exact post_plain hw hf hs hasTy_lit_int
  | str => exact post_plain hw hf hs hasTy_lit_str
  | flt => exact post_plain hw hf hs hasTy_lit_flt
  | self ha =>
    simp only [Bool.and_eq_true] at ha
    refine post_plain hw hf hs ?_
    rw [selfTy_subst hwf rfl hf hw]
    exact self_typed hwf rfl hf hw hs ha.2
  | raise he hle =>
    -- The exception's value, of the exception class, is raised.
    simp only [eval]
    have := ih.eval _ _ _ _ fr s Λ ws rfl he hw hf hs
    revert this
    generalize eval c.prog orc n fr s _ = r
    intro this
    cases r with
    | ok v s1 =>
      obtain ⟨Λ1, a, b, d, g, _⟩ := this
      refine ⟨Λ1, a, b.monoW (evalW_mono (by simp [Expr.assigned])), d, ?_⟩
      have := hasTy_le hwf g (hf.substLe hwf hle)
      simpa [Ty.subst, Atom.subst, Ty.substArgs] using this
    | returned v s1 =>
      obtain ⟨Λ1, a, b, d, g, i⟩ := this
      exact ⟨Λ1, a, b.monoW (evalW_mono (by simp [Expr.assigned])), d, g, i⟩
    | raised v s1 =>
      obtain ⟨Λ1, a, b, d, g⟩ := this
      exact ⟨Λ1, a, b.monoW (evalW_mono (by simp [Expr.assigned])), d, g⟩
    | stuck => exact this
    | timeout => trivial
  | rescue hg hx hb hbe hh =>
    rename_i b ob els oe x hd oh
    have hni : c.inInit = false := by simp at hg; cases h : c.inInit <;> simp_all
    -- The body writes no immutable field (not in `initialize`).
    have hnoI : ∀ {W : Nat → Prop} {Λ' : List Ty} {s' : Store}, Ext c.prog W (initW c fr) Λ Λ' s s' →
        Ext c.prog W (fun _ => False) Λ Λ' s s' :=
      fun h => h.mono (fun _ h => h) fun _ ⟨hi, _⟩ => by rw [hni] at hi; cases hi
    simp only [eval]
    have := ih.eval _ _ _ _ fr s Λ ws rfl hb hw hf hs
    revert this
    generalize eval c.prog orc n fr s _ = r
    intro this
    cases r with
    | ok v s1 =>
      obtain ⟨Λ1, hw1, he1, hf1, _, ho1, _, _⟩ := this
      obtain ⟨Δ, hΔ, hs1⟩ := ho1
      rw [hΔ] at hbe
      cases hbe with
      | live he =>
        exact ((ih.eval _ _ _ _ fr s1 Λ1 ws rfl he hw1 hf1 hs1).extend he1 hw
          (evalW_mono (by simp [Expr.assigned]; intros; simp_all))
          (evalW_mono (by simp [Expr.assigned]; intros; simp_all))).weaken
          (fun _ _ h => (by rw [Ty.subst_append]; exact hasTy_append_left hwf _ h)) (fun _ h => h.join_left hwf)
          (fun _ h => h.join_left hwf) (fun _ h => h.join_left hwf)
    | raised v s1 =>
      obtain ⟨Λ1, hw1, he1, hf1, hv1⟩ := this
      obtain ⟨l, hl, hΛ⟩ := hf1.core.decls _ _ hx
      simp only [hl]
      have hlen := hf1.core.inStore x l (lookupVar_mem hl)
      have hvd : s1.hasTy c.prog v (Ty.subst fr.selfArgs [Atom.cls c.prog.exn []]) := by
        simpa [Ty.subst, Atom.subst, Ty.substArgs] using hv1
      have he2 : Ext c.prog (fun l' => l' = l) (fun _ => False) Λ1 Λ1 s1 (s1.setLoc l v) :=
        Ext.setLoc hlen hΛ hvd rfl
      -- What held before the body, what it assigns un-narrowed.
      have hR : Sat c.prog c (c.reset Γ (b.assigned ++ c.pinned)) fr s1 :=
        (hs.reset).reset_typed hf.core (hnoI he1) (fun l' hW hfl => by
          rcases hW with h | h
          · exact frameW_left h
          · obtain ⟨y, hy⟩ := hfl
            exact absurd (hf.above l' l' ⟨y, hy⟩ (blkW_chain h)) (Nat.lt_irrefl _))
          (fun _ h => List.mem_append_right _ h)
      have hs2 := hR.assign hf1.core hl hx hlen hvd hvd
      have hf2 := hf1.stable he2 (hf1.own_not_chain hl) (fun _ h => h.elim)
      refine ((ih.eval _ _ _ _ fr _ Λ1 ws rfl hh (hw1.setLoc hlen hΛ hvd) hf2 hs2).extend
          ((hnoI he1).transF he2 hw |>.mono (fun _ h => h) (fun _ h => h.elim)) hw ?_
          (evalW_mono (by simp [Expr.assigned]; intros; simp_all))).weaken
          (fun _ _ h => (by rw [Ty.subst_append]; exact hasTy_append_right hwf _ h)) (fun _ h => h.join_right hwf)
          (fun _ h => h.join_right hwf) (fun _ h => h.join_right hwf)
      rintro l' (h | rfl)
      · exact evalW_mono (by simp [Expr.assigned]; intros; simp_all) l' h
      · exact .inl ⟨_, by simp [Expr.assigned], hl⟩
    | returned v s1 =>
      obtain ⟨Λ1, a, e, f, g, i⟩ := this
      exact ⟨Λ1, a, e.monoW (evalW_mono (by simp [Expr.assigned]; intros; simp_all)), f, g, i⟩
    | timeout => trivial
    | stuck => exact this
  | ensure hg hb he hout =>
    rename_i b ob e oe Δe
    have hni : c.inInit = false := by simp at hg; cases h : c.inInit <;> simp_all
    have hnoI : ∀ {W : Nat → Prop} {Λa Λb : List Ty} {sa sb : Store},
        Ext c.prog W (initW c fr) Λa Λb sa sb → Ext c.prog W (fun _ => False) Λa Λb sa sb :=
      fun h => h.mono (fun _ h => h) fun _ ⟨hi, _⟩ => by rw [hni] at hi; cases hi
    have hWb : ∀ l, evalW fr b l → frameLocs fr.vars l → frameW fr.vars (b.assigned ++ c.pinned) l := fun l hW hfl => by
      rcases hW with h | h
      · exact frameW_left h
      · obtain ⟨y, hy⟩ := hfl
        exact absurd (hf.above l l ⟨y, hy⟩ (blkW_chain h)) (Nat.lt_irrefl _)
    have hWe : ∀ l, evalW fr e l → frameLocs fr.vars l → frameW fr.vars (e.assigned ++ c.pinned) l := fun l hW hfl => by
      rcases hW with h | h
      · exact frameW_left h
      · obtain ⟨y, hy⟩ := hfl
        exact absurd (hf.above l l ⟨y, hy⟩ (blkW_chain h)) (Nat.lt_irrefl _)
    simp only [eval]
    have := ih.eval _ _ _ _ fr s Λ ws rfl hb hw hf hs
    revert this
    generalize eval c.prog orc n fr s b = r
    intro hB
    cases r with
    | ok v s1 =>
      obtain ⟨Λ1, hw1, he1, hf1, hv1, ho1, _, _⟩ := hB
      have hR : Sat c.prog c (c.reset Γ (b.assigned ++ c.pinned)) fr s1 := (hs.reset).reset_typed hf.core (hnoI he1) hWb (fun _ h => List.mem_append_right _ h)
      refine (Post.bind (ih.eval _ _ _ _ fr s1 Λ1 ws rfl he hw1 hf1 hR) (fun _ h => h) ?_).extend he1 hw
        (evalW_mono (by simp [Expr.assigned]; intros; simp_all))
        (evalW_mono (by simp [Expr.assigned]; intros; simp_all))
      intro w s2 Λ2 hw2 he2 hf2 _ ho2 _ _
      obtain ⟨Δ2, hΔ2, hs2⟩ := ho2
      rw [hout] at hΔ2; cases hΔ2
      obtain ⟨Δ, hΔ, hs1⟩ := ho1
      have hT := hs1.takeFrom hf1.core (hnoI he2) (hWe) (fun _ h => List.mem_append_right _ h) hs2
      exact ⟨Λ2, hw2, he2.monoW (fun _ h => h), hf2, he2.hasTy hv1, ⟨_, by rw [hΔ]; rfl, hT⟩,
        fun _ => ⟨_, by rw [hΔ]; rfl, hT⟩, fun _ => ⟨_, by rw [hΔ]; rfl, hT⟩⟩
    | returned v s1 =>
      obtain ⟨Λ1, hw1, he1, hf1, g, hib, _⟩ := hB
      have hR : Sat c.prog c (c.reset Γ (b.assigned ++ c.pinned)) fr s1 := (hs.reset).reset_typed hf.core (hnoI he1) hWb (fun _ h => List.mem_append_right _ h)
      refine (Post.bind (ih.eval _ _ _ _ fr s1 Λ1 ws rfl he hw1 hf1 hR) (fun _ h => h) ?_).extend he1 hw
        (evalW_mono (by simp [Expr.assigned]; intros; simp_all))
        (evalW_mono (by simp [Expr.assigned]; intros; simp_all))
      intro w s2 Λ2 hw2 he2 hf2 _ _ _ _
      exact ⟨Λ2, hw2, he2.monoW (fun _ h => h), hf2, he2.hasTy g, hib, fun hi => by rw [hni] at hi; cases hi⟩
    | raised v s1 =>
      obtain ⟨Λ1, hw1, he1, hf1, hv1⟩ := hB
      have hR : Sat c.prog c (c.reset Γ (b.assigned ++ c.pinned)) fr s1 := (hs.reset).reset_typed hf.core (hnoI he1) hWb (fun _ h => List.mem_append_right _ h)
      refine (Post.bind (ih.eval _ _ _ _ fr s1 Λ1 ws rfl he hw1 hf1 hR) (fun _ h => h) ?_).extend he1 hw
        (evalW_mono (by simp [Expr.assigned]; intros; simp_all))
        (evalW_mono (by simp [Expr.assigned]; intros; simp_all))
      intro w s2 Λ2 hw2 he2 hf2 _ _ _ _
      exact ⟨Λ2, hw2, he2.monoW (fun _ h => h), hf2, he2.hasTy hv1⟩
    | timeout => trivial
    | stuck => exact hB
  | ensureDead hg hb he hout =>
    rename_i b ob e oe 
    have hni : c.inInit = false := by simp at hg; cases h : c.inInit <;> simp_all
    have hnoI : ∀ {W : Nat → Prop} {Λa Λb : List Ty} {sa sb : Store},
        Ext c.prog W (initW c fr) Λa Λb sa sb → Ext c.prog W (fun _ => False) Λa Λb sa sb :=
      fun h => h.mono (fun _ h => h) fun _ ⟨hi, _⟩ => by rw [hni] at hi; cases hi
    have hWb : ∀ l, evalW fr b l → frameLocs fr.vars l → frameW fr.vars (b.assigned ++ c.pinned) l := fun l hW hfl => by
      rcases hW with h | h
      · exact frameW_left h
      · obtain ⟨y, hy⟩ := hfl
        exact absurd (hf.above l l ⟨y, hy⟩ (blkW_chain h)) (Nat.lt_irrefl _)
    have hWe : ∀ l, evalW fr e l → frameLocs fr.vars l → frameW fr.vars (e.assigned ++ c.pinned) l := fun l hW hfl => by
      rcases hW with h | h
      · exact frameW_left h
      · obtain ⟨y, hy⟩ := hfl
        exact absurd (hf.above l l ⟨y, hy⟩ (blkW_chain h)) (Nat.lt_irrefl _)
    simp only [eval]
    have := ih.eval _ _ _ _ fr s Λ ws rfl hb hw hf hs
    revert this
    generalize eval c.prog orc n fr s b = r
    intro hB
    cases r with
    | ok v s1 =>
      obtain ⟨Λ1, hw1, he1, hf1, hv1, ho1, _, _⟩ := hB
      have hR : Sat c.prog c (c.reset Γ (b.assigned ++ c.pinned)) fr s1 := (hs.reset).reset_typed hf.core (hnoI he1) hWb (fun _ h => List.mem_append_right _ h)
      refine (Post.bind (ih.eval _ _ _ _ fr s1 Λ1 ws rfl he hw1 hf1 hR) (fun _ h => h) ?_).extend he1 hw
        (evalW_mono (by simp [Expr.assigned]; intros; simp_all))
        (evalW_mono (by simp [Expr.assigned]; intros; simp_all))
      intro w s2 Λ2 hw2 he2 hf2 _ ho2 _ _
      obtain ⟨Δ2, hΔ2, hs2⟩ := ho2
      rw [hout] at hΔ2; cases hΔ2
    | returned v s1 =>
      obtain ⟨Λ1, hw1, he1, hf1, g, hib, _⟩ := hB
      have hR : Sat c.prog c (c.reset Γ (b.assigned ++ c.pinned)) fr s1 := (hs.reset).reset_typed hf.core (hnoI he1) hWb (fun _ h => List.mem_append_right _ h)
      refine (Post.bind (ih.eval _ _ _ _ fr s1 Λ1 ws rfl he hw1 hf1 hR) (fun _ h => h) ?_).extend he1 hw
        (evalW_mono (by simp [Expr.assigned]; intros; simp_all))
        (evalW_mono (by simp [Expr.assigned]; intros; simp_all))
      intro w s2 Λ2 hw2 he2 hf2 _ _ _ _
      exact ⟨Λ2, hw2, he2.monoW (fun _ h => h), hf2, he2.hasTy g, hib, fun hi => by rw [hni] at hi; cases hi⟩
    | raised v s1 =>
      obtain ⟨Λ1, hw1, he1, hf1, hv1⟩ := hB
      have hR : Sat c.prog c (c.reset Γ (b.assigned ++ c.pinned)) fr s1 := (hs.reset).reset_typed hf.core (hnoI he1) hWb (fun _ h => List.mem_append_right _ h)
      refine (Post.bind (ih.eval _ _ _ _ fr s1 Λ1 ws rfl he hw1 hf1 hR) (fun _ h => h) ?_).extend he1 hw
        (evalW_mono (by simp [Expr.assigned]; intros; simp_all))
        (evalW_mono (by simp [Expr.assigned]; intros; simp_all))
      intro w s2 Λ2 hw2 he2 hf2 _ _ _ _
      exact ⟨Λ2, hw2, he2.monoW (fun _ h => h), hf2, he2.hasTy hv1⟩
    | timeout => trivial
    | stuck => exact hB
  | var hu hle =>
    obtain ⟨l, v, d, hl, hv, hd, hvu, hvd⟩ := hs _ _ hu
    have hvt := hasTy_le hwf hvu (hf.substLe hwf hle)
    simp only [eval, hl, Option.bind_some, hv]
    simp only [Store.hasTy] at hvt
    rw [if_pos hvt]
    refine ⟨Λ, hw, Ext.refl _ _ Λ s, hf, hvt, ⟨Γ, rfl, hs⟩, fun htr => ?_, fun hfa => ?_⟩
    · have h1 := hasTy_truthy_subst hvu htr
      exact ⟨_, narrow_eq Γ _ (Ty.ne_nil_of_subst (ne_nil_of_hasTy h1)),
        hs.set ⟨l, v, d, hl, hv, hd, h1, hvd⟩⟩
    · have h1 := hasTy_falsy_subst hwf hvu hfa
      exact ⟨_, narrow_eq Γ _ (Ty.ne_nil_of_subst (ne_nil_of_hasTy h1)),
        hs.set ⟨l, v, d, hl, hv, hd, h1, hvd⟩⟩
  | seq ha hout hb =>
    simp only [eval]
    refine (ih.eval _ _ _ _ fr s Λ ws rfl ha hw hf hs).bind
      (evalW_mono (by simp [Expr.assigned]; intros; simp_all)) ?_
    intro v s1 Λ1 hw1 he1 hf1 _ ho1 _ _
    obtain ⟨Δ', hΔ, hs1⟩ := ho1
    rw [hout] at hΔ; cases hΔ
    exact (ih.eval _ _ _ _ fr s1 Λ1 ws rfl hb hw1 hf1 hs1).extend he1 hw
      (evalW_mono (by simp [Expr.assigned]; intros; simp_all))
      (evalW_mono (by simp [Expr.assigned]; intros; simp_all))
  | seqDead ha hout =>
    simp only [eval]
    refine (ih.eval _ _ _ _ fr s Λ ws rfl ha hw hf hs).bind
      (evalW_mono (by simp [Expr.assigned]; intros; simp_all)) ?_
    intro v s1 Λ1 _ _ _ _ ho1 _ _
    obtain ⟨_, hΔ, _⟩ := ho1
    rw [hout] at hΔ; cases hΔ
  | ret hib he hle hall =>
    simp only [eval]
    have := ih.eval _ _ _ _ fr s Λ ws rfl he hw hf hs
    revert this
    generalize eval c.prog orc n fr s _ = r
    intro this
    cases r with
    | ok v s1 =>
      obtain ⟨Λ1, a, b, d, g, ⟨Γ1, hΓ1, hs1⟩, _⟩ := this
      refine ⟨Λ1, a, b.monoW (evalW_mono (by simp [Expr.assigned])), d,
        hasTy_le hwf g (hf.substLe hwf hle), hib, fun hi => ?_⟩
      rw [hΓ1, hi] at hall
      have := self_typed hwf rfl d a hs1 (by simpa [hi] using hall)
      obtain ⟨_, ha, _⟩ := hasTy_iff.mp this
      simp [ha]
    | returned v s1 =>
      obtain ⟨Λ1, a, b, d, g, i⟩ := this
      exact ⟨Λ1, a, b.monoW (evalW_mono (by simp [Expr.assigned])), d, g, i⟩
    | raised => trivial
    | timeout => trivial
    | stuck => exact this
  | not ha =>
    simp only [eval]
    refine (ih.eval _ _ _ _ fr s Λ ws rfl ha hw hf hs).bind
      (evalW_mono (by simp [Expr.assigned])) ?_
    intro v s1 Λ1 hw1 he1 hf1 _ ho1 htt hff
    refine ⟨Λ1, hw1, he1.monoW (evalW_mono (by simp [Expr.assigned])), hf1, hasTy_lit_bool, ho1,
      fun h => ?_, fun h => ?_⟩
    · cases hv : v.truthy <;> simp_all [Value.truthy]
    · cases hv : v.truthy <;> simp_all [Value.truthy]
  | @ite _ _ cnd oc t ot e oe hc hbt hbe =>
    simp only [eval]
    refine (ih.eval _ _ _ _ fr s Λ ws rfl hc hw hf hs).bind
      (evalW_mono (by simp [Expr.assigned]; intros; simp_all)) ?_
    intro v s1 Λ1 hw1 he1 hf1 _ _ htt hff
    cases hv : v.truthy
    · rw [if_neg (by simp)]
      obtain ⟨Δ, hΔ, hs1⟩ := hff hv
      rw [hΔ] at hbe
      cases hbe with
      | live he =>
        refine ((ih.eval _ _ _ _ fr s1 Λ1 ws rfl he hw1 hf1 hs1).extend he1 hw
          (evalW_mono (by simp [Expr.assigned]; intros; simp_all))
          (evalW_mono (by simp [Expr.assigned]; intros; simp_all))).weaken
          (fun _ _ h => (by rw [Ty.subst_append]; exact hasTy_append_right hwf _ h)) (fun _ h => h.join_right hwf)
          (fun _ h => h.join_right hwf) (fun _ h => h.join_right hwf)
    · rw [if_pos rfl]
      obtain ⟨Δ, hΔ, hs1⟩ := htt hv
      rw [hΔ] at hbt
      cases hbt with
      | live ht' =>
        refine ((ih.eval _ _ _ _ fr s1 Λ1 ws rfl ht' hw1 hf1 hs1).extend he1 hw
          (evalW_mono (by simp [Expr.assigned]; intros; simp_all))
          (evalW_mono (by simp [Expr.assigned]; intros; simp_all))).weaken
          (fun _ _ h => (by rw [Ty.subst_append]; exact hasTy_append_left hwf _ h)) (fun _ h => h.join_left hwf)
          (fun _ h => h.join_left hwf) (fun _ h => h.join_left hwf)
  | @and _ _ a oa b ob ha hbb =>
    simp only [eval]
    refine (ih.eval _ _ _ _ fr s Λ ws rfl ha hw hf hs).bind
      (evalW_mono (by simp [Expr.assigned]; intros; simp_all)) ?_
    intro v s1 Λ1 hw1 he1 hf1 hv1 _ htt hff
    cases hv : v.truthy
    · rw [if_neg (by simp)]
      have hfo := hff hv
      exact ⟨Λ1, hw1, he1.monoW (evalW_mono (by simp [Expr.assigned]; intros; simp_all)), hf1,
        (by rw [Ty.subst_append]; exact hasTy_append_left hwf _ (hasTy_falsy_subst hwf hv1 hv)), hfo.join_left hwf, fun h => absurd (hv.symm.trans h) (by simp),
        fun _ => hfo.join_left hwf⟩
    · rw [if_pos rfl]
      obtain ⟨Δ, hΔ, hs1⟩ := htt hv
      rw [hΔ] at hbb
      cases hbb with
      | live hb =>
        refine ((ih.eval _ _ _ _ fr s1 Λ1 ws rfl hb hw1 hf1 hs1).extend he1 hw
          (evalW_mono (by simp [Expr.assigned]; intros; simp_all))
          (evalW_mono (by simp [Expr.assigned]; intros; simp_all))).weaken
          (fun _ _ h => (by rw [Ty.subst_append]; exact hasTy_append_right hwf _ h)) (fun _ h => h.join_right hwf)
          (fun _ h => h) (fun _ h => h.join_right hwf)
  | @or _ _ a oa b ob ha hbb =>
    simp only [eval]
    refine (ih.eval _ _ _ _ fr s Λ ws rfl ha hw hf hs).bind
      (evalW_mono (by simp [Expr.assigned]; intros; simp_all)) ?_
    intro v s1 Λ1 hw1 he1 hf1 hv1 _ htt hff
    cases hv : v.truthy
    · rw [if_neg (by simp)]
      obtain ⟨Δ, hΔ, hs1⟩ := hff hv
      rw [hΔ] at hbb
      cases hbb with
      | live hb =>
        refine ((ih.eval _ _ _ _ fr s1 Λ1 ws rfl hb hw1 hf1 hs1).extend he1 hw
          (evalW_mono (by simp [Expr.assigned]; intros; simp_all))
          (evalW_mono (by simp [Expr.assigned]; intros; simp_all))).weaken
          (fun _ _ h => (by rw [Ty.subst_append]; exact hasTy_append_right hwf _ h)) (fun _ h => h.join_right hwf)
          (fun _ h => h.join_right hwf) (fun _ h => h)
    · rw [if_pos rfl]
      have hto := htt hv
      exact ⟨Λ1, hw1, he1.monoW (evalW_mono (by simp [Expr.assigned]; intros; simp_all)), hf1,
        (by rw [Ty.subst_append]; exact hasTy_append_left hwf _ (hasTy_truthy_subst hv1 hv)), hto.join_left hwf, fun _ => hto.join_left hwf,
        fun h => absurd (hv.symm.trans h) (by simp)⟩
  | whileNever h0 hc htt =>
    simp only [eval]
    subst h0
    refine (ih.eval _ _ _ _ fr s Λ ws rfl hc hw hf hs.reset).bind
      (evalW_mono (by simp [Expr.assigned]; intros; simp_all)) ?_
    intro v s1 Λ1 hw1 he1 hf1 _ _ hvt hvf
    cases hv : v.truthy
    · rw [if_neg (by simp)]
      have := hvf hv
      exact ⟨Λ1, hw1, he1.monoW (evalW_mono (by simp [Expr.assigned]; intros; simp_all)), hf1,
        hasTy_lit_nil, this, fun _ => this, fun _ => this⟩
    · obtain ⟨_, h, _⟩ := hvt hv; rw [htt] at h; cases h
  | «while» h0 hc htt hb himp =>
    simp only [eval]
    subst h0
    have hTy := Typed.while (Ctx.reset_idem _ _ _) hc htt hb himp
    refine (ih.eval _ _ _ _ fr s Λ ws rfl hc hw hf hs.reset).bind
      (evalW_mono (by simp [Expr.assigned]; intros; simp_all)) ?_
    intro v s1 Λ1 hw1 he1 hf1 _ _ hvt hvf
    cases hv : v.truthy
    · rw [if_neg (by simp)]
      have := hvf hv
      exact ⟨Λ1, hw1, he1.monoW (evalW_mono (by simp [Expr.assigned]; intros; simp_all)), hf1,
        hasTy_lit_nil, this, fun _ => this, fun _ => this⟩
    · rw [if_pos rfl]
      obtain ⟨Δ', hΔ, hs1⟩ := hvt hv
      rw [htt] at hΔ; cases hΔ
      refine ((ih.eval _ _ _ _ fr s1 Λ1 ws rfl hb hw1 hf1 hs1).bind
        (evalW_mono (by simp [Expr.assigned]; intros; simp_all)) ?_).extend he1 hw
        (evalW_mono (by simp [Expr.assigned]; intros; simp_all)) (fun _ h => h)
      intro _ s2 Λ2 hw2 he2 hf2 _ ho2 _ _
      obtain ⟨Γb, hΓb, hs2⟩ := ho2
      have hs0 := hs2.implies hwf (by rw [hΓb] at himp; simpa [Ctx.ct] using himp)
      exact (ih.eval _ _ _ _ fr s2 Λ2 ws rfl hTy hw2 hf2 hs0).extend he2 hw1
        (evalW_mono (by simp [Expr.assigned]; intros; simp_all)) (fun _ h => h)
  | assign he hd hle hout =>
    rename_i e o' x d Δ
    simp only [eval]
    refine (ih.eval _ _ _ _ fr s Λ ws rfl he hw hf hs).bind
      (evalW_mono (by simp [Expr.assigned]; intros; simp_all)) ?_
    intro v s1 Λ1 hw1 he1 hf1 hv1 ho1 _ _
    obtain ⟨Δ', hΔ, hs1⟩ := ho1
    rw [hout] at hΔ; cases hΔ
    obtain ⟨l, hl, hΛ⟩ := hf1.core.decls x d hd
    have hlen := hf1.core.inStore x l (lookupVar_mem hl)
    simp only [hl]
    have hvd := hasTy_le hwf hv1 (hf.substLe hwf hle)
    have he2 : Ext c.prog (fun l' => l' = l) (fun _ => False) Λ1 Λ1 s1 (s1.setLoc l v) :=
      Ext.setLoc hlen hΛ hvd rfl
    -- The value's test narrows `x` too.
    have hnar : ∀ {t' : Ty}, s1.hasTy c.prog v (t'.subst fr.selfArgs) →
        OutOK c.prog c (narrow (Δ.set (.local x) o'.ty) (.local x) t') fr (s1.setLoc l v) := by
      intro t' ht'
      unfold narrow
      split
      · rename_i hem
        rw [List.isEmpty_iff.mp hem] at ht'
        simp [hasTy_iff, Ty.subst] at ht'
      · refine ⟨_, rfl, ?_⟩
        rw [Env.set_set]
        exact hs1.assign hf1.core hl hd hlen ht' hvd
    refine ⟨Λ1, hw1.setLoc hlen hΛ hvd, (he1.transF he2 hw).monoW ?_,
      hf1.stable he2 (hf1.own_not_chain hl) (fun _ h => h.elim),
      hv1, ⟨_, rfl, hs1.assign hf1.core hl hd hlen hv1 hvd⟩, fun ht => hnar (hasTy_truthy_subst hv1 ht),
      fun ht => hnar (hasTy_falsy_subst hwf hv1 ht)⟩
    rintro l' (h | rfl)
    · exact evalW_mono (by simp [Expr.assigned]; intros; simp_all) l' h
    · exact .inl ⟨x, by simp [Expr.assigned], hl⟩
  | assignDead he hd hle hout =>
    simp only [eval]
    refine (ih.eval _ _ _ _ fr s Λ ws rfl he hw hf hs).bind
      (evalW_mono (by simp [Expr.assigned]; intros; simp_all)) ?_
    intro v s1 Λ1 _ _ _ _ ho1 _ _
    obtain ⟨_, hΔ, _⟩ := ho1
    rw [hout] at hΔ; cases hΔ
  | prim hargs hlen hall hbo =>
    rename_i ret _
    simp only [eval]
    have := ih.args _ _ _ _ fr s Λ ws rfl hargs hw hf hs
    revert this
    generalize evalArgs c.prog orc n fr s _ = ar
    intro this
    cases ar with
    | other r => exact this.other (evalWs_mono (by simp [Expr.assigned]))
    | ok vs s1 =>
      obtain ⟨tys', Δ', hao, Λ1, hw1, he1, hf1, hs1, _⟩ := this
      cases hao
      dsimp only
      cases hbt : c.prog.builtinOf ret with
      | some kas =>
        -- A value of a built-in generic class: made here.
        obtain ⟨k, targs⟩ := kas
        simp only
        have hret : ret = [.cls k targs] ∧ c.prog.classes.kindOf k = .builtin := by
          unfold Program.builtinOf at hbt
          split at hbt
          · split at hbt
            · rename_i hkb; cases hbt; exact ⟨rfl, by simpa using hkb⟩
            · cases hbt
          · cases hbt
        obtain ⟨hr0, hkb⟩ := hret
        subst hr0
        obtain ⟨hklt, hlenk, hin⟩ := builtinOk_facts hwf rfl hbo hkb hf1.core.bounded
        let s2 : Store := { s1 with builts := s1.builts ++ [(k, Ty.substArgs fr.selfArgs targs)] }
        have he2 : Ext c.prog (fun _ => False) (fun _ => False) Λ1 Λ1 s1 s2 :=
          ⟨List.prefix_refl _, fun _ v h => ⟨v, h, .inl rfl⟩, ObjsGrow.refl s1,
            fun _ o1 o2 h1 h2 _ _ _ _ _ => by simp only [s2] at h2; rw [h1] at h2; cases h2; rfl,
            List.prefix_refl _, List.prefix_refl _, List.prefix_append _ _⟩
        have hw2 : WfStore c.prog Λ1 s2 :=
          ⟨hw1.len, hw1.pinsLen, fun l o ho => by
            obtain ⟨a, a1, a2, b, b2, d⟩ := hw1.objs l o ho
            exact ⟨a, a1, a2, b, b2, fun i v f h0 h1 h2 => he2.hasTy (d i v f h0 h1 h2)⟩,
            fun l o ho => hw1.noEnum l o ho, fun l o ho => hw1.bounds l o ho,
            fun i p hp => (hw1.procs i p hp).stable he2,
            fun i k' as' h' => by
              by_cases hi : i < s1.builts.length
              · simp only [s2] at h'
                rw [List.getElem?_append_left hi] at h'
                exact hw1.builts i k' as' h'
              · have : i = s1.builts.length := by
                  have := (List.getElem?_eq_some_iff.mp h').1; simp [s2] at this; omega
                subst this
                simp [s2] at h'
                obtain ⟨rfl, rfl⟩ := h'
                exact ⟨hklt, hkb, Ty.substArgs_closed _ hf1.core.closed _, hlenk, hin⟩⟩
        have hs2 := (hs1.reset (xs := c.pinned)).stable_locs he2 (fun _ _ h => h) hf1.core rfl
        refine ⟨Λ1, hw2, (he1.transF he2 hw).monoW (fun l h => h.elim
            (evalWs_mono (by simp [Expr.assigned]) l) False.elim),
          hf1.stable he2 (fun _ _ h => h) (fun _ h => h.elim), ?_,
          ⟨_, rfl, hs2⟩, fun _ => ⟨_, rfl, hs2⟩, fun _ => ⟨_, rfl, hs2⟩⟩
        show s2.hasTy c.prog (.builtin s1.builts.length) (Ty.subst fr.selfArgs [.cls k targs])
        simp only [Ty.subst, Atom.subst, List.flatMap_cons, List.flatMap_nil, List.append_nil]
        refine hasTy_iff.mpr ⟨.cls k (Ty.substArgs fr.selfArgs targs), ?_, _, List.mem_singleton.mpr rfl,
          Atom.le_refl hwf _⟩
        simp [Store.typeOf, s2]
      | none =>
      simp only
      cases ho : orc n s1 _ with
      | none =>
        dsimp only
        split
        · rename_i e he
          exact ⟨Λ1, hw1, he1.monoW (evalWs_mono (by simp [Expr.assigned])), hf1, horc _ _ _ _ he⟩
        · trivial
      | some v =>
        dsimp only
        exact ⟨Λ1, hw1, he1.monoW (evalWs_mono (by simp [Expr.assigned])), hf1, horc _ _ _ _ ho,
          ⟨_, rfl, hs1.reset⟩, fun _ => ⟨_, rfl, hs1.reset⟩, fun _ => ⟨_, rfl, hs1.reset⟩⟩
  | primDead hargs =>
    simp only [eval]
    have := ih.args _ _ _ _ fr s Λ ws rfl hargs hw hf hs
    revert this
    generalize evalArgs c.prog orc n fr s _ = ar
    intro this
    cases ar with
    | other r => exact this.other (evalWs_mono (by simp [Expr.assigned]))
    | ok vs s1 => obtain ⟨_, _, hao, _⟩ := this; cases hao
  | superInit hg hargs hmi hok =>
    rename_i args tys Δ d mi
    simp only [eval]
    have := ih.args _ _ _ _ fr s Λ ws rfl hargs hw hf hs
    revert this
    generalize evalArgs c.prog orc n fr s _ = ar
    intro this
    cases ar with
    | other r => exact this.other (evalWs_mono (by simp [Expr.assigned]))
    | ok vs s1 =>
      obtain ⟨tys', Δ', hao, Λ1, hw1, he1, hf1, hs1, hvs⟩ := this
      cases hao
      dsimp only
      simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, argsOk, beq_iff_eq] at hok
      obtain ⟨hblk, hlen, hall⟩ := hok
      have hg' := hg
      simp only [Ctx.superOk, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hg'
      obtain ⟨⟨⟨⟨hii, hib⟩, _⟩, hsup⟩, _⟩ := hg'
      obtain ⟨l, o1, hl, ho1, hk1, hbeyond, hheld⟩ := hf1.core.selfInit hii
      obtain ⟨l', hl', hsa⟩ := hf1.core.selfObj
      rw [hl] at hl'; cases hl'
      have hpre := super_pre hwf rfl hg hs he1.grow hw1 hl ho1 hk1 hbeyond
      -- The `initialize` found, as declared, with the arguments `d` gives its owner.
      obtain ⟨mi0, bs, hmi0, hbs, rfl⟩ := Program.lookupAt_spec hmi
      obtain ⟨hmem, howner, hname⟩ := Program.lookup_spec hmi0
      obtain ⟨rest, hrest, hrestnr⟩ := init_beyond hwf hP.inits hmi0
      have hblk0 : mi0.block = none := (Method.inst_block_none mi0 bs).mp hblk
      have hargs0 := superArgs_runtime hwf rfl hsup hw1 ho1 hk1 hsa hbs
      -- Every field set but those `d`'s `initialize` assigns.
      obtain ⟨hlen', s3, hb, hargs3, hpost⟩ := init_run hP ih.eval hw1 hmem hname hblk0
        (by
          rw [hargs0]
          have := AllTy.le_params_subst hwf hf.core.bounded hvs hlen hall
          rwa [Method.inst_params_snd, Ty.substArgs_comp_fun] at this)
        ho1
        (ClassTable.ancestors_trans hwf _ _ _ hk1
          (ClassTable.ancestors_trans hwf _ _ _ (super_mem_ancestors hwf hsup) howner))
        fun i f hf hor => by
          rcases hpre i f hf with h | ⟨hfd, fs, hfs, hreq⟩
          · exact h
          · rcases hor with h | h
            · -- Between the `initialize`'s class and `d`: not to assign.
              exfalso
              obtain ⟨d', f0, _, hf0, hff⟩ := ClassTable.allFieldsAt_some c.prog.classes hfs
              have hf0' : (c.prog.classes.allFields d)[i]? = some f0 := by
                obtain ⟨r2, hr2⟩ := allFields_prefix hwf (super_mem_ancestors hwf hsup)
                rw [hr2, List.getElem?_append_left hfd] at hf0; exact hf0
              rw [hrest, List.getElem?_append_right h] at hf0'
              have := required_subst hwf ((c.prog.classes.ancestorArgs c.meth.owner c.selfArgs d').getD [])
                (hrestnr f0 (List.mem_of_getElem? hf0'))
              rw [← hff] at this; rw [this] at hreq; cases hreq
            · -- Statically required: no default, so set from the start if
              -- the object's arguments make it admit `nil`.
              refine hheld i f hf ?_ h
              obtain ⟨_, _, halen, _⟩ := hw1.objs l o1 ho1
              rw [(fieldAt_default hwf halen hk1 hf hfs).1]
              simp only [Field.required, Bool.and_eq_true, Option.isNone_iff_eq_none] at hreq
              exact hreq.1
      simp only [hmi0]
      rw [if_neg (by simp [hlen']), hl]
      simp only [Store.alloc, hb, hargs3]
      revert hpost
      generalize eval c.prog orc n _ s3 mi0.body = r
      intro hpost
      cases r with
      | ok v s4 =>
        obtain ⟨Λ4, hw4, he4, hmade⟩ := hpost
        exact Post.ofSuper hwf rfl hii hib hw (he1.monoW fun _ h => h) hf1 hs1 hl ho1 hk1 hsa hw4 he4 hmade
      | returned v s4 =>
        obtain ⟨Λ4, hw4, he4, hmade⟩ := hpost
        exact Post.ofSuper hwf rfl hii hib hw (he1.monoW fun _ h => h) hf1 hs1 hl ho1 hk1 hsa hw4 he4 hmade
      | stuck => exact (hpost : False).elim
      | raised v s4 =>
        obtain ⟨Λ4, hw4, he4, hv⟩ := hpost
        exact ⟨Λ4, hw4, (he1.trans he4 hw).mono
            (fun l' h => h.elim (evalWs_mono (by simp [Expr.assigned]) l') False.elim)
            (fun l' h => h.elim id fun h => h ▸ ⟨hii, hib, hl⟩),
          hf1.stable he4 (fun _ _ h => h) (fun _ _ => hf1.initBlk hii hib), hv⟩
      | timeout => trivial
  | superNoInit hg hargs hmi hnil =>
    rename_i args tys Δ d
    simp only [eval]
    have := ih.args _ _ _ _ fr s Λ ws rfl hargs hw hf hs
    revert this
    generalize evalArgs c.prog orc n fr s _ = ar
    intro this
    cases ar with
    | other r => exact this.other (evalWs_mono (by simp [Expr.assigned]))
    | ok vs s1 =>
      obtain ⟨tys', Δ', hao, Λ1, hw1, he1, hf1, hs1, hvs⟩ := this
      cases hao
      dsimp only
      have hvs0 : vs = [] := by
        have := hvs.length; simp only [List.isEmpty_iff] at hnil; subst hnil
        exact List.length_eq_zero_iff.mp this
      subst hvs0
      have hg' := hg
      simp only [Ctx.superOk, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hg'
      obtain ⟨⟨⟨⟨hii, hib⟩, _⟩, hsup⟩, _⟩ := hg'
      obtain ⟨l, o1, hl, ho1, hk1, hbeyond, _⟩ := hf1.core.selfInit hii
      obtain ⟨l', hl', hsa⟩ := hf1.core.selfObj
      rw [hl] at hl'; cases hl'
      have hpre := super_pre hwf rfl hg hs he1.grow hw1 hl ho1 hk1 hbeyond
      have hmi0 : c.prog.lookup d "initialize" = none := (Program.lookupAt_none_iff hwf _ _ _).mp hmi
      -- No `initialize` above: no field to assign there, so every field set.
      obtain ⟨_, _, _, hflen, hslen, _⟩ := hw1.objs l o1 ho1
      have hall : o1.set.all id = true := all_id_iff.mpr fun i hi => by
        have hil : i < (c.prog.classes.allFieldsAt o1.cls o1.args).length := by
          rw [ClassTable.allFieldsAt_length]; omega
        have hfi : (c.prog.classes.allFieldsAt o1.cls o1.args)[i]? =
            some (c.prog.classes.allFieldsAt o1.cls o1.args)[i] := List.getElem?_eq_getElem hil
        rcases hpre i _ hfi with h | ⟨hfd, fs, hfs, hreq⟩
        · exact h
        · exfalso
          obtain ⟨d', f0, _, hf0, hff⟩ := ClassTable.allFieldsAt_some c.prog.classes hfs
          have hown : c.meth.owner < c.prog.classes.length := by
            obtain ⟨hcls, _⟩ := hw1.objs l o1 ho1
            exact Nat.lt_of_le_of_lt (ClassTable.ancestors_le hwf _ _ hk1) hcls
          obtain ⟨r2, hr2⟩ := allFields_prefix hwf (super_mem_ancestors hwf hsup)
          have hf0' : (c.prog.classes.allFields d)[i]? = some f0 := by
            rw [hr2, List.getElem?_append_left hfd] at hf0; exact hf0
          have := required_subst hwf ((c.prog.classes.ancestorArgs c.meth.owner c.selfArgs d').getD [])
            (no_init_fields hP.inits hmi0 _ (List.mem_of_getElem? hf0'))
          rw [← hff] at this; rw [this] at hreq; cases hreq
      simp only [hmi0, List.isEmpty_nil, if_true]
      exact Post.ofSuper hwf rfl hii hib hw (he1.monoW fun _ h => h) hf1 hs1 hl ho1 hk1 hsa hw1
        (Ext.refl _ _ Λ1 s1) (by rw [typeOf_obj_of ho1 hall]; rfl)
  | superDead hg hargs =>
    simp only [eval]
    have := ih.args _ _ _ _ fr s Λ ws rfl hargs hw hf hs
    revert this
    generalize evalArgs c.prog orc n fr s _ = ar
    intro this
    cases ar with
    | other r => exact this.other (evalWs_mono (by simp [Expr.assigned]))
    | ok vs s1 => obtain ⟨_, _, hao, _⟩ := this; cases hao
  | new hk hargs hmi hok =>
    rename_i args tys Δ k targs mi
    simp only [eval]
    have := ih.args _ _ _ _ fr s Λ ws rfl hargs hw hf hs
    revert this
    generalize evalArgs c.prog orc n fr s _ = ar
    intro this
    cases ar with
    | other r => exact this.other (evalWs_mono (by simp [Expr.assigned]))
    | ok vs s1 =>
      obtain ⟨tys', Δ', hao, Λ1, hw1, he1, hf1, hs1, hvs⟩ := this
      cases hao
      dsimp only
      simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, argsOk, beq_iff_eq] at hok
      obtain ⟨hblk, hlen, hall⟩ := hok
      obtain ⟨hk', hlenk⟩ := argsWf_facts hk
      exact Post.ofConstruct rfl (ih.construct s1 Λ1 k _ vs hw1 hk'
          (Ty.substArgs_closed _ hf1.core.closed _) (by rw [Ty.substArgs_length]; exact hlenk)
          (argsWf_in hwf rfl hk hf.core.bounded) (argsWf_kind hk)
          (fun mi' h => by
            rw [Program.lookupAt_subst fr.selfArgs hmi] at h; cases h
            refine ⟨(Method.inst_block_none _ _).mpr hblk, ?_⟩
            rw [Method.inst_params_snd]
            exact AllTy.le_params_subst hwf hf.core.bounded hvs hlen hall)
          (fun h => by rw [Program.lookupAt_subst fr.selfArgs hmi] at h; cases h))
        (he1.monoW (evalWs_mono (by simp [Expr.assigned]))) hw hf1 hs1
  | newNoInit hk hargs hmi hnil =>
    rename_i args tys Δ k targs
    simp only [eval]
    have := ih.args _ _ _ _ fr s Λ ws rfl hargs hw hf hs
    revert this
    generalize evalArgs c.prog orc n fr s _ = ar
    intro this
    cases ar with
    | other r => exact this.other (evalWs_mono (by simp [Expr.assigned]))
    | ok vs s1 =>
      obtain ⟨tys', Δ', hao, Λ1, hw1, he1, hf1, hs1, hvs⟩ := this
      cases hao
      dsimp only
      obtain ⟨hk', hlenk⟩ := argsWf_facts hk
      have hmi' : c.prog.lookupAt k (Ty.substArgs fr.selfArgs targs) "initialize" = none :=
        (Program.lookupAt_none_iff hwf _ _ _).mpr ((Program.lookupAt_none_iff hwf _ _ _).mp hmi)
      exact Post.ofConstruct rfl (ih.construct s1 Λ1 k _ vs hw1 hk'
          (Ty.substArgs_closed _ hf1.core.closed _) (by rw [Ty.substArgs_length]; exact hlenk)
          (argsWf_in hwf rfl hk hf.core.bounded) (argsWf_kind hk)
          (fun mi' h => by rw [hmi'] at h; cases h)
          (fun _ => by
            have := hvs.length; simp only [List.isEmpty_iff] at hnil; subst hnil
            exact List.length_eq_zero_iff.mp this))
        (he1.monoW (evalWs_mono (by simp [Expr.assigned]))) hw hf1 hs1
  | newDead hk hargs =>
    simp only [eval]
    have := ih.args _ _ _ _ fr s Λ ws rfl hargs hw hf hs
    revert this
    generalize evalArgs c.prog orc n fr s _ = ar
    intro this
    cases ar with
    | other r => exact this.other (evalWs_mono (by simp [Expr.assigned]))
    | ok vs s1 => obtain ⟨_, _, hao, _⟩ := this; cases hao
  | fieldVar hfd hin hvar hle =>
    obtain ⟨l, o, i, v, hl, ho, hi, hfi, hset, hv, hty⟩ := self_field_read hwf rfl hf hw hs hfd hin
    have hvt := hasTy_le hwf hty (hf.substLe hwf hle)
    simp only [eval, hl, ho, hi, Option.bind_some, hset, if_true, hv]
    simp only [Store.hasTy] at hvt
    rw [if_pos hvt]
    exact post_plain hw hf hs hvt
  | fieldImm hfd hin hvar hu hle =>
    rename_i fd u f t
    obtain ⟨l, o, i, v, hl, ho, hi, hfi, hset, hv, hty⟩ := self_field_read hwf rfl hf hw hs hfd hin
    have hvu : s.hasTy c.prog v (u.subst fr.selfArgs) := by
      cases hg : Γ.get (.field f) with
      | none => rw [hg] at hu; simp at hu; subst hu; exact hty
      | some u' =>
        rw [hg] at hu; simp at hu; subst hu
        obtain ⟨l', o', fd', i', h1, h2, h3, h5, _, _, h7⟩ := hs _ _ hg
        rw [hl] at h1; cases h1; rw [ho] at h2; cases h2; rw [hi] at h5; cases h5
        rw [hfd] at h3; cases h3
        obtain ⟨w, h8, h9⟩ := h7 hvar
        rw [hv] at h8; cases h8; exact h9
    have hvt := hasTy_le hwf hvu (hf.substLe hwf hle)
    simp only [eval, hl, ho, hi, Option.bind_some, hset, if_true, hv]
    simp only [Store.hasTy] at hvt
    rw [if_pos hvt]
    refine ⟨Λ, hw, Ext.refl _ _ Λ s, hf, hvt, ⟨Γ, rfl, hs⟩, fun htr => ?_, fun hfa => ?_⟩
    · have h1 := hasTy_truthy_subst hvu htr
      exact ⟨_, narrow_eq Γ _ (Ty.ne_nil_of_subst (ne_nil_of_hasTy h1)),
        hs.set ⟨l, o, fd, i, hl, ho, hfd, hi, hfi, hset, fun _ => ⟨v, hv, h1⟩⟩⟩
    · have h1 := hasTy_falsy_subst hwf hvu hfa
      exact ⟨_, narrow_eq Γ _ (Ty.ne_nil_of_subst (ne_nil_of_hasTy h1)),
        hs.set ⟨l, o, fd, i, hl, ho, hfd, hi, hfi, hset, fun _ => ⟨v, hv, h1⟩⟩⟩
  | @setField fd _ _ e o' Δ f hfd hvar he hle hout =>
    simp only [eval]
    refine (ih.eval _ _ _ _ fr s Λ ws rfl he hw hf hs).bind
      (evalW_mono (by simp [Expr.assigned])) ?_
    intro v s1 Λ1 hw1 he1 hf1 hv1 ho1 _ _
    obtain ⟨Δ', hΔ, hs1⟩ := ho1
    rw [hout] at hΔ; cases hΔ
    obtain ⟨l, o, i, hl, ho, hi, hfi, ⟨fd0, hfo0, hvar0⟩, _, _⟩ := self_field hwf rfl hf1 hw1 hfd
    simp only [hl, ho, hi, Option.bind_some]
    -- An immutable field: in `initialize`, of its `self`.
    have hW : fd.var = false → initW c fr l := fun h => by
      rw [h] at hvar; simp only [Bool.false_or, Bool.and_eq_true, Bool.not_eq_true'] at hvar
      exact ⟨hvar.1, hvar.2, hl⟩
    have he2 : Ext c.prog (fun _ => False) (initW c fr) Λ1 Λ1 s1 (s1.setField l i v) :=
      Ext.setField ho hfo0 (fun h => hW (hvar0 ▸ h))
    have hvd := hasTy_le hwf hv1 (hf.substLe hwf hle)
    -- The environment after: `f` set, holding the value (if immutable).
    have hs2 : Sat c.prog c (if c.inInit then Δ.set (.field f) (if fd.var then fd.ty else o'.ty) else Δ)
        fr (s1.setField l i v) := by
      have hold : ∀ q u, Δ.get q = some u →
          (q = .field f → fd.var = false → s1.hasTy c.prog v (u.subst fr.selfArgs)) →
          PathHolds c.prog c fr (s1.setField l i v) q u :=
        fun q u hq hnew => PathHolds.setField hl ho hi hfd (hs1 q u hq) hnew
      cases hii : c.inInit
      · refine fun q u hq => hold q u hq fun _ h => ?_
        rw [h, hii] at hvar; simp at hvar
      · rw [if_pos rfl]
        exact Sat.set_of (fun q u hq hne => hold q u hq fun h => absurd h hne)
          (PathHolds.setField_self ho hl hi hfi hfd (by
            obtain ⟨_, hlen, hslen, _⟩ := hw1.objs l o ho
            have := (List.getElem?_eq_some_iff.mp hfi).1; omega) (by
            obtain ⟨_, hlen, _⟩ := hw1.objs l o ho
            have := (List.getElem?_eq_some_iff.mp hfi).1; omega)
            (fun h => by simp only [h]; exact hv1))
    refine ⟨Λ1, hw1.setField ho hfi hvd, (he1.trans he2 hw).mono (fun l h => h.elim id False.elim)
        (fun l h => h.elim id id),
      hf1.stable he2 (fun _ _ h => h) (fun _ ⟨hi, hb, _⟩ => hf1.initBlk hi hb), he2.hasTy hv1,
      ⟨_, rfl, hs2⟩, fun _ => ⟨_, rfl, hs2⟩, fun _ => ⟨_, rfl, hs2⟩⟩
  | setFieldDead hfd hvar he hle hout =>
    simp only [eval]
    refine (ih.eval _ _ _ _ fr s Λ ws rfl he hw hf hs).bind
      (evalW_mono (by simp [Expr.assigned])) ?_
    intro v s1 Λ1 _ _ _ _ ho1 _ _
    obtain ⟨_, hΔ, _⟩ := ho1
    rw [hout] at hΔ; cases hΔ
  | isNil he hout =>
    rename_i e o' Δ
    simp only [eval]
    refine (ih.eval _ _ _ _ fr s Λ ws rfl he hw hf hs).bindEq
      (evalW_mono (by simp [Expr.assigned])) ?_
    intro v s1 Λ1 hr hw1 he1 hf1 hv1 ho1 _ _
    obtain ⟨Δ', hΔ, hs1⟩ := ho1
    rw [hout] at hΔ; cases hΔ
    have hval : ∀ p, e.path? = some p → PathVal c.prog fr s1 p v := fun p hp => by
      obtain ⟨rfl, h⟩ := eval_read hp hr; exact h
    obtain ⟨h1, h2, h3⟩ := testOut_ok (b := v == .nil) hwf rfl hs1 hf1 hw1 hval
      (fun _ t _ _ ht hb => by simp at hb; subst hb; exact hasTy_nilTy_subst ht)
      (fun _ t _ _ ht hb => hasTy_remove_nil_subst ht (by simpa using hb))
    exact ⟨Λ1, hw1, he1.monoW (evalW_mono (by simp [Expr.assigned])), hf1, by rw [testOut_ty]; exact hasTy_lit_bool, h1,
      fun h => h2 (by rwa [truthy_bool] at h), fun h => h3 (by rwa [truthy_bool] at h)⟩
  | isA he hout hver =>
    rename_i e o' Δ a
    simp only [eval]
    refine (ih.eval _ _ _ _ fr s Λ ws rfl he hw hf hs).bindEq
      (evalW_mono (by simp [Expr.assigned])) ?_
    intro v s1 Λ1 hr hw1 he1 hf1 hv1 ho1 _ _
    obtain ⟨Δ', hΔ, hs1⟩ := ho1
    rw [hout] at hΔ; cases hΔ
    obtain ⟨u, hu, _⟩ := hasTy_iff.mp hv1
    simp only [hu]
    have hval : ∀ p, e.path? = some p → PathVal c.prog fr s1 p v := fun p hp => by
      obtain ⟨rfl, h⟩ := eval_read hp hr; exact h
    -- The run-time test (of the class alone) answers as `≤` does, the
    -- arguments following from the static type (`verifiable`).
    have hclosed : a.closed = true := by simp only [Bool.and_eq_true] at hver; exact hver.1.1
    have tail : ∀ bres : Bool, bres = u.le c.prog.classes [] a →
        Post c.prog c (testOut c e Δ (isATrue c.ct · a) (isAFalse c.ct · a)) fr ws Λ s
          (evalW fr (.isA e a)) (.ok (.bool bres) s1) := by
      intro bres hb; subst hb
      obtain ⟨h1, h2, h3⟩ := testOut_ok (b := u.le c.prog.classes [] a) hwf rfl hs1 hf1 hw1 hval
        (fun _ t _ _ ht hb => hasTy_isATrue_subst hwf hw1 hclosed ht hu hb)
        (fun _ t _ _ ht hb => hasTy_isAFalse_subst hwf hw1 hclosed ht hu hb)
      exact ⟨Λ1, hw1, he1.monoW (evalW_mono (by simp [Expr.assigned])), hf1,
        by rw [testOut_ty]; exact hasTy_lit_bool, h1,
        fun h => h2 (by rwa [truthy_bool] at h), fun h => h3 (by rwa [truthy_bool] at h)⟩
    cases u <;> cases a <;> first
      | exact tail _ (isA_class_test hwf hw1 hv1 hu hver)
      | exact tail _ rfl
  | testDead he hout hform =>
    rcases hform with rfl | ⟨a, rfl⟩ | rfl | rfl | rfl | rfl <;>
    · simp only [eval]
      refine (ih.eval _ _ _ _ fr s Λ ws rfl he hw hf hs).bind
        (evalW_mono (by simp [Expr.assigned])) ?_
      intro v s1 Λ1 _ _ _ _ ho1 _ _
      obtain ⟨_, hΔ, _⟩ := ho1
      rw [hout] at hΔ; cases hΔ
  | eqNil he hout =>
    rename_i e o' Δ
    simp only [eval]
    refine (ih.eval _ _ _ _ fr s Λ ws rfl he hw hf hs).bindEq
      (evalW_mono (by simp [Expr.assigned])) ?_
    intro v s1 Λ1 hr hw1 he1 hf1 hv1 ho1 _ _
    obtain ⟨Δ', hΔ, hs1⟩ := ho1
    rw [hout] at hΔ; cases hΔ
    have hval : ∀ p, e.path? = some p → PathVal c.prog fr s1 p v := fun p hp => by
      obtain ⟨rfl, h⟩ := eval_read hp hr; exact h
    unfold eqOut
    split
    · rename_i hnc
      rcases eq_noCall_equal (orc := orc) (n := n) (w := .nil) hwf rfl hs1 hf1 hw1 hv1 hval
          (fun _ h => by cases h) hnc with hq | hq
      · rw [hq]; trivial
      · rw [hq]
        obtain ⟨h1, h2, h3⟩ : OutOK c.prog c (testOut c e Δ (fun t => if finalRead c Δ e then t.keep [.nil] else t) (fun t => if finalRead c Δ e then t.remove .nil else t)).out fr s1 ∧ ((v == .nil) = true → OutOK c.prog c (testOut c e Δ (fun t => if finalRead c Δ e then t.keep [.nil] else t) (fun t => if finalRead c Δ e then t.remove .nil else t)).tt fr s1) ∧
            ((v == .nil) = false → OutOK c.prog c (testOut c e Δ (fun t => if finalRead c Δ e then t.keep [.nil] else t) (fun t => if finalRead c Δ e then t.remove .nil else t)).ff fr s1) := by
          by_cases hfin : ∃ p t, e.path? = some p ∧ c.pathTy Δ p = some t ∧ t.allFinalIn c.prog = true
          · obtain ⟨p, t, hp, ht, htf⟩ := hfin
            exact testOut_ok (b := v == .nil)
              (tyT := fun t => if finalRead c Δ e then t.keep [.nil] else t)
              (tyF := fun t => if finalRead c Δ e then t.remove .nil else t) hwf rfl hs1 hf1 hw1 hval
              (fun p' t' hp' ht' hvt' hb => by
                rw [hp] at hp'; cases hp'; rw [ht] at ht'; cases ht'
                rw [finalRead_eq hp ht, htf, if_pos rfl]
                simp at hb; subst hb
                rw [Ty.subst_of_allFinalIn fr.selfArgs (Ty.allFinalIn_keep htf _)]
                rw [Ty.subst_of_allFinalIn fr.selfArgs htf] at hvt'
                exact hasTy_keep hwf hvt' htf rfl rfl)
              (fun p' t' hp' ht' hvt' hb => by
                rw [hp] at hp'; cases hp'; rw [ht] at ht'; cases ht'
                rw [finalRead_eq hp ht, htf, if_pos rfl]
                rw [Ty.subst_of_allFinalIn fr.selfArgs (Ty.allFinalIn_remove htf _)]
                rw [Ty.subst_of_allFinalIn fr.selfArgs htf] at hvt'
                exact hasTy_remove_nil hvt' (by simpa using hb))
          · have hid : ∀ p t, e.path? = some p → c.pathTy Δ p = some t → finalRead c Δ e = false :=
              fun p t hp ht => by
                rw [finalRead_eq hp ht]
                cases h : t.allFinalIn c.prog
                · rfl
                · exact absurd ⟨p, t, hp, ht, h⟩ hfin
            exact testOut_ok (b := v == .nil)
              (tyT := fun t => if finalRead c Δ e then t.keep [.nil] else t)
              (tyF := fun t => if finalRead c Δ e then t.remove .nil else t) hwf rfl hs1 hf1 hw1 hval
                (fun p t hp ht hvt _ => by rw [hid p t hp ht]; simpa using hvt)
                (fun p t hp ht hvt _ => by rw [hid p t hp ht]; simpa using hvt)
        exact ⟨Λ1, hw1, he1.monoW (evalW_mono (by simp [Expr.assigned])), hf1,
          by rw [testOut_ty]; exact hasTy_lit_bool, h1, fun h => h2 (by rwa [truthy_bool] at h),
          fun h => h3 (by rwa [truthy_bool] at h)⟩
    · exact post_eqCall rfl ih.equal hw (he1.monoW (evalW_mono (by simp [Expr.assigned]))) hw1 hf1 hs1 hv1 (.inl rfl)
  | neNil he hout =>
    rename_i e o' Δ
    simp only [eval]
    refine (ih.eval _ _ _ _ fr s Λ ws rfl he hw hf hs).bindEq
      (evalW_mono (by simp [Expr.assigned])) ?_
    intro v s1 Λ1 hr hw1 he1 hf1 hv1 ho1 _ _
    obtain ⟨Δ', hΔ, hs1⟩ := ho1
    rw [hout] at hΔ; cases hΔ
    have hval : ∀ p, e.path? = some p → PathVal c.prog fr s1 p v := fun p hp => by
      obtain ⟨rfl, h⟩ := eval_read hp hr; exact h
    unfold eqOut
    split
    · rename_i hnc
      rcases eq_noCall_equal (orc := orc) (n := n) (w := .nil) hwf rfl hs1 hf1 hw1 hv1 hval
          (fun _ h => by cases h) hnc with hq | hq
      · rw [hq]; simp only [Result.bind]; trivial
      · rw [hq]
        simp only [Result.bind, truthy_bool]
        obtain ⟨h1, h2, h3⟩ : OutOK c.prog c (testOut c e Δ (fun t => if finalRead c Δ e then t.remove .nil else t) (fun t => if finalRead c Δ e then t.keep [.nil] else t)).out fr s1 ∧ ((!(v == .nil)) = true → OutOK c.prog c (testOut c e Δ (fun t => if finalRead c Δ e then t.remove .nil else t) (fun t => if finalRead c Δ e then t.keep [.nil] else t)).tt fr s1) ∧
            ((!(v == .nil)) = false → OutOK c.prog c (testOut c e Δ (fun t => if finalRead c Δ e then t.remove .nil else t) (fun t => if finalRead c Δ e then t.keep [.nil] else t)).ff fr s1) := by
          by_cases hfin : ∃ p t, e.path? = some p ∧ c.pathTy Δ p = some t ∧ t.allFinalIn c.prog = true
          · obtain ⟨p, t, hp, ht, htf⟩ := hfin
            exact testOut_ok (b := !(v == .nil))
              (tyT := fun t => if finalRead c Δ e then t.remove .nil else t)
              (tyF := fun t => if finalRead c Δ e then t.keep [.nil] else t) hwf rfl hs1 hf1 hw1 hval
              (fun p' t' hp' ht' hvt' hb => by
                rw [hp] at hp'; cases hp'; rw [ht] at ht'; cases ht'
                rw [finalRead_eq hp ht, htf, if_pos rfl]
                rw [Ty.subst_of_allFinalIn fr.selfArgs (Ty.allFinalIn_remove htf _)]
                rw [Ty.subst_of_allFinalIn fr.selfArgs htf] at hvt'
                exact hasTy_remove_nil hvt' (by simpa using hb))
              (fun p' t' hp' ht' hvt' hb => by
                rw [hp] at hp'; cases hp'; rw [ht] at ht'; cases ht'
                rw [finalRead_eq hp ht, htf, if_pos rfl]
                simp at hb; subst hb
                rw [Ty.subst_of_allFinalIn fr.selfArgs (Ty.allFinalIn_keep htf _)]
                rw [Ty.subst_of_allFinalIn fr.selfArgs htf] at hvt'
                exact hasTy_keep hwf hvt' htf rfl rfl)
          · have hid : ∀ p t, e.path? = some p → c.pathTy Δ p = some t → finalRead c Δ e = false :=
              fun p t hp ht => by
                rw [finalRead_eq hp ht]
                cases h : t.allFinalIn c.prog
                · rfl
                · exact absurd ⟨p, t, hp, ht, h⟩ hfin
            exact testOut_ok (b := !(v == .nil))
              (tyT := fun t => if finalRead c Δ e then t.remove .nil else t)
              (tyF := fun t => if finalRead c Δ e then t.keep [.nil] else t) hwf rfl hs1 hf1 hw1 hval
                (fun p t hp ht hvt _ => by rw [hid p t hp ht]; simpa using hvt)
                (fun p t hp ht hvt _ => by rw [hid p t hp ht]; simpa using hvt)
        exact ⟨Λ1, hw1, he1.monoW (evalW_mono (by simp [Expr.assigned])), hf1,
          by rw [testOut_ty]; exact hasTy_lit_bool, h1, fun h => h2 (by rwa [truthy_bool] at h),
          fun h => h3 (by rwa [truthy_bool] at h)⟩
    · refine Post.plain_bindNot ?_
      exact post_eqCall rfl ih.equal hw (he1.monoW (evalW_mono (by simp [Expr.assigned]))) hw1 hf1 hs1 hv1 (.inl rfl)
  | eqTrue he hout =>
    rename_i e o' Δ
    simp only [eval]
    refine (ih.eval _ _ _ _ fr s Λ ws rfl he hw hf hs).bindEq
      (evalW_mono (by simp [Expr.assigned])) ?_
    intro v s1 Λ1 hr hw1 he1 hf1 hv1 ho1 _ _
    obtain ⟨Δ', hΔ, hs1⟩ := ho1
    rw [hout] at hΔ; cases hΔ
    have hval : ∀ p, e.path? = some p → PathVal c.prog fr s1 p v := fun p hp => by
      obtain ⟨rfl, h⟩ := eval_read hp hr; exact h
    unfold eqOut
    split
    · rename_i hnc
      rcases eq_noCall_equal (orc := orc) (n := n) (w := (.bool true)) hwf rfl hs1 hf1 hw1 hv1 hval
          (fun _ h => by cases h) hnc with hq | hq
      · rw [hq]; trivial
      · rw [hq]
        obtain ⟨h1, h2, h3⟩ : OutOK c.prog c (testOut c e Δ (fun t => if finalRead c Δ e then t.keep [.bool] else t) (id)).out fr s1 ∧ ((v == (.bool true)) = true → OutOK c.prog c (testOut c e Δ (fun t => if finalRead c Δ e then t.keep [.bool] else t) (id)).tt fr s1) ∧
            ((v == (.bool true)) = false → OutOK c.prog c (testOut c e Δ (fun t => if finalRead c Δ e then t.keep [.bool] else t) (id)).ff fr s1) := by
          by_cases hfin : ∃ p t, e.path? = some p ∧ c.pathTy Δ p = some t ∧ t.allFinalIn c.prog = true
          · obtain ⟨p, t, hp, ht, htf⟩ := hfin
            exact testOut_ok (b := v == (.bool true))
              (tyT := fun t => if finalRead c Δ e then t.keep [.bool] else t)
              (tyF := id) hwf rfl hs1 hf1 hw1 hval
              (fun p' t' hp' ht' hvt' hb => by
                rw [hp] at hp'; cases hp'; rw [ht] at ht'; cases ht'
                rw [finalRead_eq hp ht, htf, if_pos rfl]
                simp at hb; subst hb
                rw [Ty.subst_of_allFinalIn fr.selfArgs (Ty.allFinalIn_keep htf _)]
                rw [Ty.subst_of_allFinalIn fr.selfArgs htf] at hvt'
                exact hasTy_keep hwf hvt' htf rfl rfl)
              (fun _ _ _ _ hvt' _ => hvt')
          · have hid : ∀ p t, e.path? = some p → c.pathTy Δ p = some t → finalRead c Δ e = false :=
              fun p t hp ht => by
                rw [finalRead_eq hp ht]
                cases h : t.allFinalIn c.prog
                · rfl
                · exact absurd ⟨p, t, hp, ht, h⟩ hfin
            exact testOut_ok (b := v == (.bool true))
              (tyT := fun t => if finalRead c Δ e then t.keep [.bool] else t)
              (tyF := id) hwf rfl hs1 hf1 hw1 hval
                (fun p t hp ht hvt _ => by rw [hid p t hp ht]; simpa using hvt)
              (fun _ _ _ _ hvt _ => hvt)
        exact ⟨Λ1, hw1, he1.monoW (evalW_mono (by simp [Expr.assigned])), hf1,
          by rw [testOut_ty]; exact hasTy_lit_bool, h1, fun h => h2 (by rwa [truthy_bool] at h),
          fun h => h3 (by rwa [truthy_bool] at h)⟩
    · exact post_eqCall rfl ih.equal hw (he1.monoW (evalW_mono (by simp [Expr.assigned]))) hw1 hf1 hs1 hv1 (.inr (.inl rfl))
  | eqFalse he hout =>
    rename_i e o' Δ
    simp only [eval]
    refine (ih.eval _ _ _ _ fr s Λ ws rfl he hw hf hs).bindEq
      (evalW_mono (by simp [Expr.assigned])) ?_
    intro v s1 Λ1 hr hw1 he1 hf1 hv1 ho1 _ _
    obtain ⟨Δ', hΔ, hs1⟩ := ho1
    rw [hout] at hΔ; cases hΔ
    have hval : ∀ p, e.path? = some p → PathVal c.prog fr s1 p v := fun p hp => by
      obtain ⟨rfl, h⟩ := eval_read hp hr; exact h
    unfold eqOut
    split
    · rename_i hnc
      rcases eq_noCall_equal (orc := orc) (n := n) (w := (.bool false)) hwf rfl hs1 hf1 hw1 hv1 hval
          (fun _ h => by cases h) hnc with hq | hq
      · rw [hq]; trivial
      · rw [hq]
        obtain ⟨h1, h2, h3⟩ : OutOK c.prog c (testOut c e Δ (fun t => if finalRead c Δ e then t.keep [.bool] else t) (id)).out fr s1 ∧ ((v == (.bool false)) = true → OutOK c.prog c (testOut c e Δ (fun t => if finalRead c Δ e then t.keep [.bool] else t) (id)).tt fr s1) ∧
            ((v == (.bool false)) = false → OutOK c.prog c (testOut c e Δ (fun t => if finalRead c Δ e then t.keep [.bool] else t) (id)).ff fr s1) := by
          by_cases hfin : ∃ p t, e.path? = some p ∧ c.pathTy Δ p = some t ∧ t.allFinalIn c.prog = true
          · obtain ⟨p, t, hp, ht, htf⟩ := hfin
            exact testOut_ok (b := v == (.bool false))
              (tyT := fun t => if finalRead c Δ e then t.keep [.bool] else t)
              (tyF := id) hwf rfl hs1 hf1 hw1 hval
              (fun p' t' hp' ht' hvt' hb => by
                rw [hp] at hp'; cases hp'; rw [ht] at ht'; cases ht'
                rw [finalRead_eq hp ht, htf, if_pos rfl]
                simp at hb; subst hb
                rw [Ty.subst_of_allFinalIn fr.selfArgs (Ty.allFinalIn_keep htf _)]
                rw [Ty.subst_of_allFinalIn fr.selfArgs htf] at hvt'
                exact hasTy_keep hwf hvt' htf rfl rfl)
              (fun _ _ _ _ hvt' _ => hvt')
          · have hid : ∀ p t, e.path? = some p → c.pathTy Δ p = some t → finalRead c Δ e = false :=
              fun p t hp ht => by
                rw [finalRead_eq hp ht]
                cases h : t.allFinalIn c.prog
                · rfl
                · exact absurd ⟨p, t, hp, ht, h⟩ hfin
            exact testOut_ok (b := v == (.bool false))
              (tyT := fun t => if finalRead c Δ e then t.keep [.bool] else t)
              (tyF := id) hwf rfl hs1 hf1 hw1 hval
                (fun p t hp ht hvt _ => by rw [hid p t hp ht]; simpa using hvt)
              (fun _ _ _ _ hvt _ => hvt)
        exact ⟨Λ1, hw1, he1.monoW (evalW_mono (by simp [Expr.assigned])), hf1,
          by rw [testOut_ty]; exact hasTy_lit_bool, h1, fun h => h2 (by rwa [truthy_bool] at h),
          fun h => h3 (by rwa [truthy_bool] at h)⟩
    · exact post_eqCall rfl ih.equal hw (he1.monoW (evalW_mono (by simp [Expr.assigned]))) hw1 hf1 hs1 hv1 (.inr (.inr rfl))
  | call hr hout hargs hres hall =>
    simp only [eval]
    refine (ih.eval _ _ _ _ fr s Λ ws rfl hr hw hf hs).bind
      (evalW_mono (by simp [Expr.assigned]; intros; simp_all)) ?_
    intro v s1 Λ1 hw1 he1 hf1 hv1 ho1 _ _
    obtain ⟨Δ1, hΔ, hs1⟩ := ho1
    rw [hout] at hΔ; cases hΔ
    have := ih.args _ _ _ _ fr s1 Λ1 ws rfl hargs hw1 hf1 hs1
    revert this
    generalize evalArgs c.prog orc n fr s1 _ = ar
    intro this
    cases ar with
    | other r =>
      exact (this.other (evalWs_mono (by simp [Expr.assigned]; intros; simp_all))).extend he1 hw
        (evalW_mono (by simp [Expr.assigned]; intros; simp_all)) (fun _ h => h)
    | ok vs s2 =>
      obtain ⟨tys', Δ2, hao, Λ2, hw2, he2, hf2, hs2, hvs⟩ := this
      cases hao
      dsimp only
      obtain ⟨k, as, mt, hk, hl, hmem, hrecv⟩ := recv_of hwf hf.core.bounded (he2.hasTy hv1) hres
      have hmt := List.all_eq_true.mp hall mt hmem
      simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hmt
      obtain ⟨hblk, hok⟩ := hmt
      unfold argsOk at hok
      simp only [Bool.and_eq_true, beq_iff_eq] at hok
      have hvs' : AllTy c.prog s2 vs ((mt.inst fr.selfArgs).params.map (·.2)) := by
        rw [Method.inst_params_snd]; exact AllTy.le_params_subst hwf hf.core.bounded hvs hok.1 hok.2
      have hsend := ih.send s2 Λ2 v k _ _ (mt.inst fr.selfArgs) vs none [] hw2
        (obj_of_hasTy_cls hwf hw2 hrecv hk) hrecv (resolve_not_init hres) hl hvs'
        (by
          rw [show (mt.inst fr.selfArgs).block = none from (Method.inst_block_none _ _).mpr hblk]
          exact ⟨trivial, fun l h => by simp [chainLocs] at h⟩)
      revert hsend
      generalize send c.prog orc n s2 v _ vs none = r
      intro hsend
      cases r with
      | ok w s3 =>
        obtain ⟨Λ3, hw3, he3, hw', _⟩ := hsend
        have hno : ∀ l, frameLocs fr.vars l → ¬ blkW none l := fun _ _ h => by simp [blkW] at h
        refine ⟨Λ3, hw3, ((he1.transW he2 hw).transF he3 (by exact hw)).monoW ?_,
          hf2.stable he3 (fun _ _ h => by simp [blkW] at h) (fun _ h => h.elim),
          hasTy_flatMap_subst hmem (by rw [Method.inst_ret] at hw'; exact hw'),
          ⟨_, rfl, (hs2.reset (xs := c.pinned)).stable he3 hno (fun _ _ h => h) hf2.core (pinsDecl_reset fun _ h => h)⟩, fun _ => ⟨_, rfl, (hs2.reset (xs := c.pinned)).stable he3 hno (fun _ _ h => h) hf2.core (pinsDecl_reset fun _ h => h)⟩,
          fun _ => ⟨_, rfl, (hs2.reset (xs := c.pinned)).stable he3 hno (fun _ _ h => h) hf2.core (pinsDecl_reset fun _ h => h)⟩⟩
        rintro l ((h | h) | h)
        · exact evalW_mono (by simp [Expr.assigned]; intros; simp_all) l h
        · exact evalWs_mono (by simp [Expr.assigned]; intros; simp_all) l h
        · simp [blkW] at h
      | stuck => exact hsend
      | returned => exact hsend.elim
      | raised w s3 =>
        obtain ⟨Λ3, hw3, he3, hw', _⟩ := hsend
        refine ⟨Λ3, hw3, ((he1.transW he2 hw).transF he3 (by exact hw)).monoW ?_,
          hf2.stable he3 (fun _ _ h => by simp [blkW] at h) (fun _ h => h.elim), hw'⟩
        rintro l ((h | h) | h)
        · exact evalW_mono (by simp [Expr.assigned]; intros; simp_all) l h
        · exact evalWs_mono (by simp [Expr.assigned]; intros; simp_all) l h
        · simp [blkW] at h
      | timeout => trivial
  | callDeadRecv hr hout =>
    simp only [eval]
    refine (ih.eval _ _ _ _ fr s Λ ws rfl hr hw hf hs).bind
      (evalW_mono (by simp [Expr.assigned]; intros; simp_all)) ?_
    intro v s1 Λ1 _ _ _ _ ho1 _ _
    obtain ⟨_, hΔ, _⟩ := ho1
    rw [hout] at hΔ; cases hΔ
  | callDeadArgs hr hout hargs =>
    simp only [eval]
    refine (ih.eval _ _ _ _ fr s Λ ws rfl hr hw hf hs).bind
      (evalW_mono (by simp [Expr.assigned]; intros; simp_all)) ?_
    intro v s1 Λ1 hw1 he1 hf1 _ ho1 _ _
    obtain ⟨Δ1, hΔ, hs1⟩ := ho1
    rw [hout] at hΔ; cases hΔ
    have := ih.args _ _ _ _ fr s1 Λ1 ws rfl hargs hw1 hf1 hs1
    revert this
    generalize evalArgs c.prog orc n fr s1 _ = ar
    intro this
    cases ar with
    | other r =>
      exact (this.other (evalWs_mono (by simp [Expr.assigned]; intros; simp_all))).extend he1 hw
        (evalW_mono (by simp [Expr.assigned]; intros; simp_all)) (fun _ h => h)
    | ok vs s2 => obtain ⟨_, _, hao, _⟩ := this; cases hao
  | lambda hg hk hn hok hb hret =>
    rename_i k body ob ret ps own
    have hni : c.inInit = false := by simp at hg; cases h : c.inInit <;> simp_all
    have hnd : c.inDefault = false := by simp at hg; cases h : c.inDefault <;> simp_all
    simp only [eval, hk]
    -- The procedure, as checked here.
    have hpo : ProcOK c.prog Λ s ⟨.mk fr.vars fr.self fr.selfArgs none (ps.map (·.1)) body,
        (ps ++ own).map (·.1), .cls k (Ty.substArgs fr.selfArgs (ps.map (·.2) ++ [ret]))⟩ :=
      ⟨c, Γ, ps, own, ret, body, fr.vars, fr.self, fr.selfArgs, k, ob, rfl, rfl, hni, hnd, hk, hn, hok,
        hf.core, hs.toDecl, hb, hret⟩
    have he := Ext.newProc (P := c.prog) (W := fun _ => False) (Wo := fun _ => False)
      (Λ := Λ) (s := s) ⟨.mk fr.vars fr.self fr.selfArgs none (ps.map (·.1)) body,
        (ps ++ own).map (·.1), .cls k (Ty.substArgs fr.selfArgs (ps.map (·.2) ++ [ret]))⟩
    have hs' := hs.stable_locs he (fun _ _ h => h) hf.core rfl
    refine ⟨Λ, hw.newProc hpo, he.mono (fun _ h => h.elim) (fun _ h => h.elim),
      hf.stable he (fun _ _ h => h) (fun _ h => h.elim), ?_,
      ⟨_, rfl, hs'⟩, fun _ => ⟨_, rfl, hs'⟩, fun _ => ⟨_, rfl, hs'⟩⟩
    -- Of its type: `ProcN` with the lambda's types, through the frame's arguments.
    refine hasTy_iff.mpr ⟨.cls k (Ty.substArgs fr.selfArgs (ps.map (·.2) ++ [ret])), ?_, _,
      by simp [Out.plain, Ty.subst, Atom.subst], Atom.le_refl hwf _⟩
    simp [Store.typeOf]
  | callProc hr hout hargs hty hk hlen hall =>
    rename_i f o Δ args tys Δ' k as
    simp only [eval]
    refine (ih.eval _ _ _ _ fr s Λ ws rfl hr hw hf hs).bind
      (evalW_mono (by simp [Expr.assigned]; intros; simp_all)) ?_
    intro v s1 Λ1 hw1 he1 hf1 hv1 ho1 _ _
    obtain ⟨Δ1, hΔ, hs1⟩ := ho1
    rw [hout] at hΔ; cases hΔ
    have := ih.args _ _ _ _ fr s1 Λ1 ws rfl hargs hw1 hf1 hs1
    revert this
    generalize evalArgs c.prog orc n fr s1 _ = ar
    intro this
    cases ar with
    | other r =>
      exact (this.other (evalWs_mono (by simp [Expr.assigned]; intros; simp_all))).extend he1 hw
        (evalW_mono (by simp [Expr.assigned]; intros; simp_all)) (fun _ h => h)
    | ok vs s2 =>
      obtain ⟨tys', Δ2, hao, Λ2, hw2, he2, hf2, hs2, hvs⟩ := this
      cases hao
      dsimp only
      obtain ⟨hkp, hkn⟩ := procClass_kind hk
      -- The value called: a procedure of that class.
      have hv2 := he2.hasTy hv1
      rw [hty] at hv2
      simp only [Ty.subst, List.flatMap_cons, List.flatMap_nil, Atom.subst, List.append_nil] at hv2
      obtain ⟨i, p, rfl, hp, args', hpty, hle⟩ := proc_of_hasTy hwf hw2 hv2 hkp
      obtain ⟨c0, Γ0, ps, own, ret, body, vars, me, sa, k0, ob, hc0, rfl, hni0, _, hk0, hn0, hok0,
        hcore0, hsd0, hty0, hret0⟩ := hw2.procs i _ hp
      simp only at hpty
      cases hpty
      simp only [hp]
      -- Its variances: its parameters in, its result out.
      have hshape : c.prog.classes.variances k = List.replicate ps.length .contra ++ [.co] := by
        cases hck : c.prog.classes[k]? with
        | none => simp [ClassTable.kindOf, hck] at hkp
        | some cl =>
          have hkind : cl.kind = .proc := by simpa [ClassTable.kindOf, hck] using hkp
          obtain ⟨_, _, _, hpar⟩ := hwf.procShape k cl hck hkind
          simp [hck] at hn0
          simp [ClassTable.variances, hck]
          rw [hpar, hn0]; simp
      have hlenas : as.length = ps.length + 1 := by
        have := argsLeWith_length hle
        simp [ClassTable.substArgs_length'] at this; omega
      -- The arguments, of the procedure's parameters' types.
      have hcmp : ∀ (j : Nat) (x y : Ty), (Ty.substArgs sa (ps.map (·.2) ++ [ret]))[j]? = some x →
          (Ty.substArgs fr.selfArgs as)[j]? = some y →
          ((c.prog.classes.variances k)[j]?.getD .inv).leWith (Atom.le c.prog.classes []) x y = true :=
        fun j x y hx hy => argsLeWith_getElem hle hx hy
      have hvs0 : AllTy c.prog s2 vs ((ps.map (·.2)).map (Ty.subst sa)) := by
        refine AllTy.le hwf hvs (by simp; omega) ?_
        simp only [List.all_eq_true]
        intro ⟨t, u⟩ hm
        obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hm
        rw [List.getElem?_zip_eq_some] at hj
        obtain ⟨htj, huj⟩ := hj
        rw [List.getElem?_map] at htj huj
        rw [List.getElem?_map] at huj
        cases ht0 : tys[j]? with
        | none => rw [ht0] at htj; cases htj
        | some t0 =>
          rw [ht0] at htj; cases htj
          cases hu0 : ps[j]? with
          | none => rw [hu0] at huj; cases huj
          | some q =>
            rw [hu0] at huj; cases huj
            have hjp : j < ps.length := (List.getElem?_eq_some_iff.mp hu0).1
            -- `t0` below `as[j]`, which is below the parameter (in).
            have hja : j < as.length := by omega
            have hta : (tys.zip as)[j]? = some (t0, as[j]) := by
              rw [List.getElem?_zip_eq_some]; exact ⟨ht0, List.getElem?_eq_getElem hja⟩
            have h1 := List.all_eq_true.mp hall _ (List.mem_of_getElem? hta)
            have h1' := hf2.substLe hwf h1
            have hx : (Ty.substArgs sa (ps.map (·.2) ++ [ret]))[j]? = some (Ty.subst sa q.2) := by
              rw [Ty.substArgs_getElem?, List.getElem?_append_left (by simp; omega)]
              simp [hu0]
            have hy : (Ty.substArgs fr.selfArgs as)[j]? = some (Ty.subst fr.selfArgs as[j]) := by
              rw [Ty.substArgs_getElem?, List.getElem?_eq_getElem hja]; rfl
            have h2 := hcmp j _ _ hx hy
            rw [hshape, List.getElem?_append_left (by simp; omega)] at h2
            simp only [List.getElem?_replicate, hjp, if_true, Option.getD_some,
              Variance.leWith] at h2
            exact Ty.le_trans hwf h1' h2
      -- The result: what the procedure gives, below its class's result
      -- (out).
      have hres : ∀ w : Value, ∀ s3 : Store, s3.hasTy c.prog w (Ty.subst sa ret) →
          s3.hasTy c.prog w ((Out.plain (as.getLast?.getD []) Δ').ty.subst fr.selfArgs) := by
        intro w s3 hw'
        have hn1 : ps.length < as.length := by omega
        have hx : (Ty.substArgs sa (ps.map (·.2) ++ [ret]))[ps.length]? = some (Ty.subst sa ret) := by
          rw [Ty.substArgs_getElem?, List.getElem?_append_right (by simp)]
          simp
        have hy : (Ty.substArgs fr.selfArgs as)[ps.length]? = some (Ty.subst fr.selfArgs as[ps.length]) := by
          rw [Ty.substArgs_getElem?, List.getElem?_eq_getElem hn1]; rfl
        have h2 := hcmp ps.length _ _ hx hy
        rw [hshape, List.getElem?_append_right (by simp)] at h2
        simp only [List.length_replicate, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some,
          Variance.leWith] at h2
        have hlast : as.getLast?.getD [] = as[ps.length] := by
          rw [List.getLast?_eq_getElem?]; simp [hlenas]
        simp only [Out.plain, hlast]
        exact hasTy_le hwf hw' h2
      have hrun := proc_run hP ih.eval hw2 hc0 hni0 hok0 hcore0 hsd0 hty0 hret0 hvs0
      simp only [Store.alloc]
      refine (?_ : ∀ r, SendPost c.prog (Ty.subst sa ret) none none [] Λ2 s2 r →
        Post c.prog c (Out.plain (as.getLast?.getD []) (c.afterCall Δ')) fr ws Λ s (evalW fr (f.callProc args)) r) _ hrun
      intro r hrun
      have hno : ∀ l, frameLocs fr.vars l → ¬ blkW none l := fun _ _ h => by simp [blkW] at h
      cases r with
      | ok w s3 =>
        obtain ⟨Λ3, hw3, he3, hw', _⟩ := hrun
        refine ⟨Λ3, hw3, ((he1.transW he2 hw).transF he3 (by exact hw)).monoW ?_,
          hf2.stable he3 (fun _ _ h => by simp [blkW] at h) (fun _ h => h.elim), hres w s3 hw',
          ⟨_, rfl, (hs2.reset (xs := c.pinned)).stable he3 hno (fun _ _ h => h) hf2.core (pinsDecl_reset fun _ h => h)⟩, fun _ => ⟨_, rfl, (hs2.reset (xs := c.pinned)).stable he3 hno (fun _ _ h => h) hf2.core (pinsDecl_reset fun _ h => h)⟩,
          fun _ => ⟨_, rfl, (hs2.reset (xs := c.pinned)).stable he3 hno (fun _ _ h => h) hf2.core (pinsDecl_reset fun _ h => h)⟩⟩
        rintro l ((h | h) | h)
        · exact evalW_mono (by simp [Expr.assigned]; intros; simp_all) l h
        · exact evalWs_mono (by simp [Expr.assigned]; intros; simp_all) l h
        · simp [blkW] at h
      | raised w s3 =>
        obtain ⟨Λ3, hw3, he3, hw', _⟩ := hrun
        refine ⟨Λ3, hw3, ((he1.transW he2 hw).transF he3 (by exact hw)).monoW ?_,
          hf2.stable he3 (fun _ _ h => by simp [blkW] at h) (fun _ h => h.elim), hw'⟩
        rintro l ((h | h) | h)
        · exact evalW_mono (by simp [Expr.assigned]; intros; simp_all) l h
        · exact evalWs_mono (by simp [Expr.assigned]; intros; simp_all) l h
        · simp [blkW] at h
      | returned => exact hrun.elim
      | stuck => exact hrun.elim
      | timeout => trivial
  | callProcDeadRecv hr hout =>
    simp only [eval]
    refine (ih.eval _ _ _ _ fr s Λ ws rfl hr hw hf hs).bind
      (evalW_mono (by simp [Expr.assigned]; intros; simp_all)) ?_
    intro v s1 Λ1 _ _ _ _ ho1 _ _
    obtain ⟨_, hΔ, _⟩ := ho1
    rw [hout] at hΔ; cases hΔ
  | callProcDeadArgs hr hout hargs =>
    simp only [eval]
    refine (ih.eval _ _ _ _ fr s Λ ws rfl hr hw hf hs).bind
      (evalW_mono (by simp [Expr.assigned]; intros; simp_all)) ?_
    intro v s1 Λ1 hw1 he1 hf1 _ ho1 _ _
    obtain ⟨Δ1, hΔ, hs1⟩ := ho1
    rw [hout] at hΔ; cases hΔ
    have := ih.args _ _ _ _ fr s1 Λ1 ws rfl hargs hw1 hf1 hs1
    revert this
    generalize evalArgs c.prog orc n fr s1 _ = ar
    intro this
    cases ar with
    | other r =>
      exact (this.other (evalWs_mono (by simp [Expr.assigned]; intros; simp_all))).extend he1 hw
        (evalW_mono (by simp [Expr.assigned]; intros; simp_all)) (fun _ h => h)
    | ok vs s2 => obtain ⟨_, _, hao, _⟩ := this; cases hao
  | callBlkDeadRecv hr hout =>
    simp only [eval]
    refine (ih.eval _ _ _ _ fr s Λ ws rfl hr hw hf hs).bind
      (evalW_mono (by simp [Expr.assigned]; intros; simp_all)) ?_
    intro v s1 Λ1 _ _ _ _ ho1 _ _
    obtain ⟨_, hΔ, _⟩ := ho1
    rw [hout] at hΔ; cases hΔ
  | callBlkDeadArgs hr hout hargs =>
    simp only [eval]
    refine (ih.eval _ _ _ _ fr s Λ ws rfl hr hw hf hs).bind
      (evalW_mono (by simp [Expr.assigned]; intros; simp_all)) ?_
    intro v s1 Λ1 hw1 he1 hf1 _ ho1 _ _
    obtain ⟨Δ1, hΔ, hs1⟩ := ho1
    rw [hout] at hΔ; cases hΔ
    have := ih.args _ _ _ _ fr s1 Λ1 ws rfl hargs hw1 hf1 hs1
    revert this
    generalize evalArgs c.prog orc n fr s1 _ = ar
    intro this
    cases ar with
    | other r =>
      exact (this.other (evalWs_mono (by simp [Expr.assigned]; intros; simp_all))).extend he1 hw
        (evalW_mono (by simp [Expr.assigned]; intros; simp_all)) (fun _ h => h)
    | ok vs s2 => obtain ⟨_, _, hao, _⟩ := this; cases hao
  | yieldDead hsig hargs =>
    simp only [eval]
    have := ih.args _ _ _ _ fr s Λ ws rfl hargs hw hf hs
    revert this
    generalize evalArgs c.prog orc n fr s _ = ar
    intro this
    cases ar with
    | other r => exact this.other (evalWs_mono (by simp [Expr.assigned]))
    | ok vs s1 => obtain ⟨_, _, hao, _⟩ := this; cases hao
  | «yield» hsig hargs hlen hall =>
    rename_i sig args tys Δ
    simp only [eval]
    have := ih.args _ _ _ _ fr s Λ ws rfl hargs hw hf hs
    revert this
    generalize evalArgs c.prog orc n fr s _ = ar
    intro this
    cases ar with
    | other r => exact this.other (evalWs_mono (by simp [Expr.assigned]))
    | ok vs s1 =>
      obtain ⟨tys', Δ', hao, Λ1, hw1, he1, hf1, hs1, hvs⟩ := this
      cases hao
      dsimp only
      have hch := hf1.chain
      rw [hsig] at hch
      cases hfb : fr.blk with
      | none => rw [hfb] at hch; simp [ChainAt] at hch
      | some clo =>
      rw [hfb] at hch
      dsimp only
      have hvs' : AllTy c.prog s1 vs (sig.subst fr.selfArgs).params :=
        AllTy.le_subst hwf hf.core.bounded hvs hlen hall
      have hres := ih.block s1 Λ1 clo (sig.subst fr.selfArgs) vs ws hw1
        ⟨hch, fun l hl => hf1.chainIn l (by rw [hfb]; exact hl)⟩ hvs'
      revert hres
      generalize runBlock c.prog orc n s1 clo vs = r
      intro hres
      cases r with
      | ok v s2 =>
        obtain ⟨Λ2, hw2, he2, hv2, hch2, hin2⟩ := hres
        have hno : ∀ l, frameLocs fr.vars l → ¬ blkW (some clo) l := by
          rw [← hfb]; exact hf1.blk_not_own
        refine ⟨Λ2, hw2, (he1.transF he2 hw).monoW ?_, ⟨hf1.core.stable he2,
          by rw [hfb, hsig]; exact hch2, hf1.above, fun l hl => hin2 l (by rw [← hfb]; exact hl),
          hf1.initBlk⟩,
          by simpa [Out.plain, BlockSig.subst] using hv2,
          ⟨_, rfl, (hs1.reset (xs := c.pinned)).stable he2 hno (fun _ _ h => h) hf1.core (pinsDecl_reset fun _ h => h)⟩, fun _ => ⟨_, rfl, (hs1.reset (xs := c.pinned)).stable he2 hno (fun _ _ h => h) hf1.core (pinsDecl_reset fun _ h => h)⟩,
          fun _ => ⟨_, rfl, (hs1.reset (xs := c.pinned)).stable he2 hno (fun _ _ h => h) hf1.core (pinsDecl_reset fun _ h => h)⟩⟩
        rintro l (h | h)
        · exact evalWs_mono (by simp [Expr.assigned]) l h
        · exact .inr (by rw [hfb]; exact h)
      | stuck => exact hres
      | returned => exact hres.elim
      | raised v s2 =>
        obtain ⟨Λ2, hw2, he2, hv2, hch2, hin2⟩ := hres
        refine ⟨Λ2, hw2, (he1.transF he2 hw).monoW ?_, ⟨hf1.core.stable he2,
          by rw [hfb, hsig]; exact hch2, hf1.above, fun l hl => hin2 l (by rw [← hfb]; exact hl),
          hf1.initBlk⟩, hv2⟩
        rintro l (h | h)
        · exact evalWs_mono (by simp [Expr.assigned]) l h
        · exact .inr (by rw [hfb]; exact h)
      | timeout => trivial
  | callBlk hr hout hargs hres hm0 hsig hall hps hb hret =>
    rename_i r o' Δ args tys Δ' m ms m0 sig ps body ob
    simp only [eval]
    refine (ih.eval _ _ _ _ fr s Λ ws rfl hr hw hf hs).bind
      (evalW_mono (by simp [Expr.assigned]; intros; simp_all)) ?_
    intro v s1 Λ1 hw1 he1 hf1 hv1 ho1 _ _
    obtain ⟨Δ1, hΔ, hs1⟩ := ho1
    rw [hout] at hΔ; cases hΔ
    have := ih.args _ _ _ _ fr s1 Λ1 ws rfl hargs hw1 hf1 hs1
    revert this
    generalize evalArgs c.prog orc n fr s1 _ = ar
    intro this
    cases ar with
    | other r =>
      exact (this.other (evalWs_mono (by simp [Expr.assigned]; intros; simp_all))).extend he1 hw
        (evalW_mono (by simp [Expr.assigned]; intros; simp_all)) (fun _ h => h)
    | ok vs s2 =>
      obtain ⟨tys', Δ2, hao, Λ2, hw2, he2, hf2, hs2, hvs⟩ := this
      cases hao
      dsimp only
      obtain ⟨k, as, mt, hk, hl, hmem, hrecv⟩ := recv_of hwf hf.core.bounded (he2.hasTy hv1) hres
      have hmt := List.all_eq_true.mp hall mt hmem
      simp only [Bool.and_eq_true, beq_iff_eq] at hmt
      obtain ⟨hblk, hok⟩ := hmt
      unfold argsOk at hok
      simp only [Bool.and_eq_true, beq_iff_eq] at hok
      have hvs' : AllTy c.prog s2 vs ((mt.inst fr.selfArgs).params.map (·.2)) := by
        rw [Method.inst_params_snd]; exact AllTy.le_params_subst hwf hf.core.bounded hvs hok.1 hok.2
      -- The block, as checked here: the method run sees its signature
      -- with this frame's arguments.
      have hat : ChainAt c.prog Λ2 s2 ((c, Δ', ob) :: ws)
          (some (.mk fr.vars fr.self fr.selfArgs fr.blk ps body)) (some (sig.subst fr.selfArgs)) := by
        simp only [ChainAt]
        exact ⟨trivial, hf2.core, hf2.chain, hf2.above, ⟨sig, BlockSig.le_refl hwf _, hps, hb, hret⟩, hs2.reset⟩
      have hin : ∀ l, chainLocs (some (.mk fr.vars fr.self fr.selfArgs fr.blk ps body)) l →
          l < s2.locs.length := by
        intro l hl
        simp only [chainLocs] at hl
        rcases hl with ⟨x, hx⟩ | hl
        · exact hf2.core.inStore x l hx
        · exact hf2.chainIn l hl
      have hblk' : (mt.inst fr.selfArgs).block = some (sig.subst fr.selfArgs) := by
        simp [Method.inst, hblk]
      have hsend := ih.send s2 Λ2 v k _ m (mt.inst fr.selfArgs) vs
        (some (.mk fr.vars fr.self fr.selfArgs fr.blk ps body))
        ((c, Δ', ob) :: ws) hw2 (obj_of_hasTy_cls hwf hw2 hrecv hk) hrecv (resolve_not_init hres) hl hvs'
        (by rw [hblk']; exact ⟨hat, hin⟩)
      revert hsend
      generalize send c.prog orc n s2 v m vs _ = r
      intro hsend
      cases r with
      | ok w s3 =>
        obtain ⟨Λ3, hw3, he3, hw', hg3⟩ := hsend
        rw [hblk'] at hg3
        obtain ⟨hat3, hin3⟩ := hg3
        simp only [ChainAt] at hat3
        obtain ⟨_, hcore3, hch3, _, _, hJ⟩ := hat3
        have hfr : (⟨fr.vars, fr.self, fr.selfArgs, fr.blk⟩ : Frame) = fr := rfl
        rw [hfr] at hJ
        have hf3 : FrameOK c.prog c Λ3 fr s3 ws :=
          ⟨hcore3, hch3, hf2.above, fun l hl => hin3 l (by simp only [chainLocs]; exact .inr hl),
            hf2.initBlk⟩
        refine ⟨Λ3, hw3, ((he1.transW he2 hw).transF he3 hw).monoW ?_, hf3,
          hasTy_flatMap_subst hmem (by rw [Method.inst_ret] at hw'; exact hw'),
          ⟨_, rfl, hJ⟩, fun _ => ⟨_, rfl, hJ⟩, fun _ => ⟨_, rfl, hJ⟩⟩
        rintro l ((h | h) | h)
        · exact evalW_mono (by simp [Expr.assigned]; intros; simp_all) l h
        · exact evalWs_mono (by simp [Expr.assigned]; intros; simp_all) l h
        · simp only [blkW] at h
          rcases h with ⟨x, hx, hl⟩ | h
          · refine .inl ⟨x, ?_, hl⟩
            simp only [Expr.assigned, List.mem_append] at hx ⊢
            rcases hx with hx | hx <;> simp [hx]
          · exact .inr h
      | stuck => exact hsend
      | returned => exact hsend.elim
      | raised w s3 =>
        obtain ⟨Λ3, hw3, he3, hw', hg3⟩ := hsend
        rw [hblk'] at hg3
        obtain ⟨hat3, hin3⟩ := hg3
        simp only [ChainAt] at hat3
        obtain ⟨_, hcore3, hch3, _, _, _⟩ := hat3
        have hf3 : FrameOK c.prog c Λ3 fr s3 ws :=
          ⟨hcore3, hch3, hf2.above, fun l hl => hin3 l (by simp only [chainLocs]; exact .inr hl),
            hf2.initBlk⟩
        refine ⟨Λ3, hw3, ((he1.transW he2 hw).transF he3 hw).monoW ?_, hf3, hw'⟩
        rintro l ((h | h) | h)
        · exact evalW_mono (by simp [Expr.assigned]; intros; simp_all) l h
        · exact evalWs_mono (by simp [Expr.assigned]; intros; simp_all) l h
        · simp only [blkW] at h
          rcases h with ⟨x, hx, hl⟩ | h
          · refine .inl ⟨x, ?_, hl⟩
            simp only [Expr.assigned, List.mem_append] at hx ⊢
            rcases hx with hx | hx <;> simp [hx]
          · exact .inr h
      | timeout => trivial

end QuarzCore
