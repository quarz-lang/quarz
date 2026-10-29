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
    Post P c (.plain [.cls k targs] Δ) fr ws Λ s W r := by
  subst hc
  cases r with
  | ok v s2 =>
    obtain ⟨Λ2, hw2, he2, hv⟩ := h
    have hs2 := hs1.stable he2 (fun _ _ h => h) (fun _ _ h => h)
    exact ⟨Λ2, hw2, (he1.transF he2 hw).monoW (fun l h => h.elim id False.elim),
      hf1.stable he2 (fun _ _ h => h) (fun _ h => h.elim), by simpa [Out.plain] using hv, ⟨_, rfl, hs2⟩,
      fun _ => ⟨_, rfl, hs2⟩, fun _ => ⟨_, rfl, hs2⟩⟩
  | stuck => exact h.elim
  | returned => exact h.elim
  | raised => trivial
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
  | raised => trivial
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

theorem AllTy.mono {s s' : Store} (h : ObjsGrow s s') :
    ∀ {vs : List Value} {ts : List Ty}, AllTy P s vs ts → AllTy P s' vs ts
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨h1, h2⟩ => ⟨hasTy_mono h h1, AllTy.mono h h2⟩

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
  bounds := fun l' o' h => by
    rw [Store.setField_objs] at h
    by_cases hl : l' = l
    · subst hl; rw [if_pos rfl, ho] at h; cases h; exact hw.bounds l' o ho
    · rw [if_neg hl] at h; exact hw.bounds l' o' h
  objs := fun l' o' h => by
    have mono : ∀ {w : Value} {t : Ty}, s.hasTy P w t → (s.setField l i v).hasTy P w t :=
      fun hw' => hasTy_mono setField_grow hw'
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
    ⟨l', w, d, h1, h2, h3, hasTy_mono setField_grow h4, hasTy_mono setField_grow h5⟩
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
        exact ⟨v, by simp [this], hasTy_mono setField_grow (hnew rfl hv)⟩
      · obtain ⟨w, h8, h9⟩ := h7 hv
        exact ⟨w, by show (o.fields.set i v)[j]? = some w; rw [List.getElem?_set_ne (Ne.symm hji)]; exact h8,
          hasTy_mono setField_grow h9⟩

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
    fun h => ⟨v, by simp [hfl], hasTy_mono setField_grow (hv h)⟩⟩

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

theorem finalRead_eq {c : Ctx} {Δ : Env} {e : Expr} {p : Path} {t : Ty} (hp : e.path? = some p)
    (ht : c.pathTy Δ p = some t) : finalRead c Δ e = t.allFinal := by
  simp [finalRead, hp, ht]

theorem OutOK.stable {c : Ctx} {g : Option Env} {fr : Frame} {s s' : Store} {W Wo : Nat → Prop}
    {Λ Λ' : List Ty} (h : OutOK P c g fr s) (he : Ext P W Wo Λ Λ' s s')
    (hw : ∀ l, frameLocs fr.vars l → ¬ W l) (hwo : ∀ l, fr.self = .obj l → ¬ Wo l) :
    OutOK P c g fr s' := by
  obtain ⟨Γ, rfl, hs⟩ := h
  exact ⟨Γ, rfl, hs.stable he hw hwo⟩

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
    ∃ k as mt, b = .cls k as ∧ k ≠ 0 ∧ P.lookupAt k as m = some mt ∧ mt ∈ ms := by
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
        by_cases hk : k = 0
        · simp [hk] at h0
        · simp [hk] at h0
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
theorem obj_of_hasTy_cls (hwf : WfClasses P.classes) {s : Store} {v : Value} {k : Nat} {as : List Ty}
    (hv : s.hasTy P v [.cls k as]) (hk : k ≠ 0) :
    ∃ l o, v = .obj l ∧ s.objs[l]? = some o ∧ k ∈ P.classes.ancestors o.cls := by
  rw [hasTy_iff] at hv
  obtain ⟨a, ha, b, hb, hab⟩ := hv
  simp at hb; subst hb
  cases v with
  | obj l =>
    obtain ⟨o, ho, _, rfl⟩ := typeOf_obj ha
    rw [Atom.le_cls_iff hwf] at hab
    rcases hab with ⟨h0, _⟩ | ⟨_, hab, _⟩
    · exact absurd h0 hk
    · exact ⟨l, o, rfl, ho, ClassTable.ancestorArgs_mem hwf _ _ _ _ hab⟩
  | _ => simp [Store.typeOf] at ha; subst ha; simp [Atom.le] at hab; exact absurd hab.1 hk

/-- The receiver of a call (through the frame's arguments `σ`): of the
class the method was found in, given the arguments its view of the
receiver has substituted, where the method found is that view's
instantiated. -/
theorem recv_of (hwf : WfClasses P.classes) {κ σ : List Ty} (hσ : ArgsIn P.classes κ σ)
    {s : Store} {v : Value} {t : Ty} {m : String} {ms : List Method}
    (hv : s.hasTy P v (t.subst σ)) (hres : P.resolve κ t m = some ms) :
    ∃ k as mt, k ≠ 0 ∧ P.lookupAt k (Ty.substArgs σ as) m = some (mt.inst σ) ∧ mt ∈ ms ∧
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
  | .stuck => False
  | _ => True

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
    vs.length = mi.params.length ∧ ∃ s3, bindAll ⟨s.locs ++ (mi.locals.map (·.1)).map fun _ => .nil, s.objs⟩
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
    ⟨s.locs ++ (mi.locals.map (·.1)).map fun _ => .nil, s.objs⟩ (by rw [List.length_map, hlenv])
    hexists
  obtain ⟨hobjs, hlen3, hsame⟩ := bindAll_same hb
  refine ⟨s3, hb, by simp only [Store.argsFor, hobjs, ho, Option.bind_some, hσ, Option.getD_some], ?_⟩
  simp only [List.length_append, List.length_map] at hlen3
  have hge : ∀ x l', lookupVar (Store.allocVars s.locs.length (mi.locals.map (·.1))) x = some l' →
      s.locs.length ≤ l' ∧ l' < s.locs.length + mi.locals.length := fun x l' h => by
    have := mem_allocVars (lookupVar_mem h); simpa using this
  have mono : ∀ {v : Value} {t : Ty}, s.hasTy P v t → s3.hasTy P v t := fun h => by
    unfold Store.hasTy Store.hasType Store.typeOf at *; rw [hobjs]; exact h
  have he23 : Ext P (fun _ => False) (fun _ => False) Λ (Λ ++ (mi.locals.map (·.2)).map (Ty.subst σ)) s s3 := by
    refine ⟨List.prefix_append _ _, fun l' v hv => ⟨v, ?_, .inl rfl⟩, fun l' o' ho' =>
      ⟨o', by rw [hobjs]; exact ho', rfl, rfl, rfl, fun _ h => h⟩,
      fun _ o1 o2 h1 h2 _ _ _ _ _ => by rw [hobjs, h1] at h2; cases h2; rfl⟩
    have hl' := (List.getElem?_eq_some_iff.mp hv).1
    rw [hsame l' fun x _ hx => by have := (hge x l' hx).1; omega]
    simp [List.getElem?_append_left hl', hv]
  have hw3 : WfStore P (Λ ++ (mi.locals.map (·.2)).map (Ty.subst σ)) s3 :=
    ⟨by simp [hw.len, hlen3], fun l' o' ho' => by
      rw [hobjs] at ho'
      obtain ⟨a, a1, a2, b, b2, d⟩ := hw.objs l' o' ho'
      exact ⟨a, a1, a2, b, b2, fun i v f h0 h1 h2 => mono (d i v f h0 h1 h2)⟩,
    fun l' o' ho' => by rw [hobjs] at ho'; exact hw.bounds l' o' ho'⟩
  have ho3 : s3.objs[l]? = some o := by rw [hobjs]; exact ho
  obtain ⟨rest, hrest⟩ := allFields_prefix hwf hsub
  have hsa3 : s3.argsFor P.classes l mi.owner = σ := by simp [Store.argsFor, ho3, hσ]
  have hcore : FrameCore P ⟨P, mi, false, false⟩ (Λ ++ (mi.locals.map (·.2)).map (Ty.subst σ))
      (Store.allocVars s.locs.length (mi.locals.map (·.1))) (.obj l) σ s3 := by
    refine ⟨fun x d hd => ?_, fun x y l' hx hy => ?_, fun x l' hm => ?_,
      fun h => (by rw [hinInit] at h; cases h),
      fun _ => ⟨l, o, rfl, ho3, hsub, fun i h1 h2 => ?_, fun i f hf _ hr => hset i f hf (.inr hr)⟩,
      ⟨l, rfl, hsa3.symm⟩, ClassTable.ancestorArgs_closed P.classes hσ hclosed,
      ClassTable.ancestorArgs_in hwf hσ hlen' (hw.bounds l o ho)⟩
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
  | raised => trivial
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
      obtain ⟨l0, v, d, h1, h2, h3, h4, h5⟩ := hs _ _ hp'
      exact ⟨l0, v, d, h1, he.loc_same h2 id, h3, he.hasTy h4, he.hasTy h5⟩
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
    Post P c (.plain [.nil] (c.afterSuper Δ)) fr ws Λ s (evalW fr (.superInit d args)) (.ok .nil s4) := by
  subst hc
  have hs4 := hs1.afterSuper hwf rfl he4 hw4 hl ho1 hk1 hsa hmade
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
    obtain ⟨⟨hlen, _⟩, hall⟩ := h
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
  | raise => trivial
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
        (by rw [Ty.subst_append]; exact hasTy_append_left hwf _ hv1), hfo.join_left hwf, fun h => absurd (hv.symm.trans h) (by simp),
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
        (by rw [Ty.subst_append]; exact hasTy_append_left hwf _ hv1), hto.join_left hwf, fun _ => hto.join_left hwf,
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
    refine ⟨Λ1, hw1.setLoc l v, (he1.transF he2 hw).monoW ?_,
      hf1.stable he2 (hf1.own_not_chain hl) (fun _ h => h.elim),
      hv1, ⟨_, rfl, hs1.assign hf1.core hl hd hlen hv1 hvd⟩, fun _ => ⟨_, rfl,
      hs1.assign hf1.core hl hd hlen hv1 hvd⟩, fun _ => ⟨_, rfl, hs1.assign hf1.core hl hd hlen hv1 hvd⟩⟩
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
  | prim hargs hlen hall =>
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
      cases ho : orc n s1 _ with
      | none => dsimp only; trivial
      | some v =>
        dsimp only
        exact ⟨Λ1, hw1, he1.monoW (evalWs_mono (by simp [Expr.assigned])), hf1, horc _ _ _ _ ho,
          ⟨_, rfl, hs1⟩, fun _ => ⟨_, rfl, hs1⟩, fun _ => ⟨_, rfl, hs1⟩⟩
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
      | raised => trivial
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
          (argsWf_in hwf rfl hk hf.core.bounded)
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
          (argsWf_in hwf rfl hk hf.core.bounded)
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
        (fun _ t _ _ ht hb => hasTy_isATrue_subst hwf hclosed ht hu hb)
        (fun _ t _ _ ht hb => hasTy_isAFalse_subst hwf hclosed ht hu hb)
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
    by_cases hfin : ∃ p t, e.path? = some p ∧ c.pathTy Δ p = some t ∧ t.allFinal = true
    · -- A read of final atoms: no object, the built-in `==`, which narrows.
      obtain ⟨p, t, hp, ht, htf⟩ := hfin
      have hvt := (pathHolds_of_val hwf rfl hs1 hf1 hw1 ht (hval p hp)).1
      rcases equal_nonobj (orc := orc) (n := n) (s := s1) (w := .nil) (not_obj_of_final (by rwa [Ty.subst_of_allFinal fr.selfArgs htf] at hvt) htf)
        with h | h
      · rw [h]; trivial
      · rw [h]
        obtain ⟨h1, h2, h3⟩ := testOut_ok (b := v == .nil)
          (tyT := fun t => if finalRead c Δ e then t.keep [.nil] else t)
          (tyF := fun t => if finalRead c Δ e then t.remove .nil else t) hwf rfl hs1 hf1 hw1 hval
          (fun p' t' hp' ht' hvt' hb => by
            rw [hp] at hp'; cases hp'; rw [ht] at ht'; cases ht'
            rw [finalRead_eq hp ht, htf, if_pos rfl]
            simp at hb; subst hb
            rw [Ty.subst_of_allFinal fr.selfArgs (Ty.allFinal_keep htf _)]
            rw [Ty.subst_of_allFinal fr.selfArgs htf] at hvt'
            exact hasTy_keep hvt' htf rfl)
          (fun p' t' hp' ht' hvt' hb => by
            rw [hp] at hp'; cases hp'; rw [ht] at ht'; cases ht'
            rw [finalRead_eq hp ht, htf, if_pos rfl]
            rw [Ty.subst_of_allFinal fr.selfArgs (Ty.allFinal_remove htf _)]
            rw [Ty.subst_of_allFinal fr.selfArgs htf] at hvt'
            exact hasTy_remove_nil hvt' (by simpa using hb))
        exact ⟨Λ1, hw1, he1.monoW (evalW_mono (by simp [Expr.assigned])), hf1,
          by rw [testOut_ty]; exact hasTy_lit_bool, h1, fun h => h2 (by rwa [truthy_bool] at h),
          fun h => h3 (by rwa [truthy_bool] at h)⟩
    · -- Otherwise the test narrows nothing.
      have hid : ∀ p t, e.path? = some p → c.pathTy Δ p = some t → finalRead c Δ e = false :=
        fun p t hp ht => by
          rw [finalRead_eq hp ht]
          cases h : t.allFinal
          · rfl
          · exact absurd ⟨p, t, hp, ht, h⟩ hfin
      obtain ⟨h1, h2, _⟩ := testOut_ok (b := true)
        (tyT := fun t => if finalRead c Δ e then t.keep [.nil] else t)
        (tyF := fun t => if finalRead c Δ e then t.remove .nil else t) hwf rfl hs1 hf1 hw1 hval
        (fun p t hp ht hvt _ => by rw [hid p t hp ht]; simpa using hvt)
        (fun _ _ _ _ _ hb => by cases hb)
      obtain ⟨_, _, h3⟩ := testOut_ok (b := false)
        (tyT := fun t => if finalRead c Δ e then t.keep [.nil] else t)
        (tyF := fun t => if finalRead c Δ e then t.remove .nil else t) hwf rfl hs1 hf1 hw1 hval
        (fun _ _ _ _ _ hb => by cases hb)
        (fun p t hp ht hvt _ => by rw [hid p t hp ht]; simpa using hvt)
      have := ih.equal s1 Λ1 v .nil _ hw1 hv1 (.inl rfl)
      revert this
      generalize equal c.prog orc n s1 v .nil = r
      intro this
      cases r with
      | ok r s2 =>
        obtain ⟨Λ2, hw2, he2, hr2, _⟩ := this
        have hno : ∀ l, frameLocs fr.vars l → ¬ blkW none l := fun _ _ h => by simp [blkW] at h
        refine ⟨Λ2, hw2, (he1.transF he2 hw).monoW ?_,
          hf1.stable he2 (fun _ _ h => by simp [blkW] at h) (fun _ h => h.elim),
          by rw [testOut_ty]; exact hr2, h1.stable he2 hno (fun _ _ h => h), fun _ => (h2 rfl).stable he2 hno (fun _ _ h => h),
          fun _ => (h3 rfl).stable he2 hno (fun _ _ h => h)⟩
        rintro l (h | h)
        · exact evalW_mono (by simp [Expr.assigned]) l h
        · simp [blkW] at h
      | stuck => exact this
      | returned => exact this.elim
      | raised => trivial
      | timeout => trivial
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
    by_cases hfin : ∃ p t, e.path? = some p ∧ c.pathTy Δ p = some t ∧ t.allFinal = true
    · -- A read of final atoms: no object, the built-in `==`, which narrows.
      obtain ⟨p, t, hp, ht, htf⟩ := hfin
      have hvt := (pathHolds_of_val hwf rfl hs1 hf1 hw1 ht (hval p hp)).1
      rcases equal_nonobj (orc := orc) (n := n) (s := s1) (w := .nil) (not_obj_of_final (by rwa [Ty.subst_of_allFinal fr.selfArgs htf] at hvt) htf)
        with h | h
      · rw [h]; trivial
      · rw [h]
        simp only [Result.bind, truthy_bool]
        obtain ⟨h1, h2, h3⟩ := testOut_ok (b := !(v == .nil))
          (tyT := fun t => if finalRead c Δ e then t.remove .nil else t)
          (tyF := fun t => if finalRead c Δ e then t.keep [.nil] else t) hwf rfl hs1 hf1 hw1 hval
          (fun p' t' hp' ht' hvt' hb => by
            rw [hp] at hp'; cases hp'; rw [ht] at ht'; cases ht'
            rw [finalRead_eq hp ht, htf, if_pos rfl]
            rw [Ty.subst_of_allFinal fr.selfArgs (Ty.allFinal_remove htf _)]
            rw [Ty.subst_of_allFinal fr.selfArgs htf] at hvt'
            exact hasTy_remove_nil hvt' (by simpa using hb))
          (fun p' t' hp' ht' hvt' hb => by
            rw [hp] at hp'; cases hp'; rw [ht] at ht'; cases ht'
            rw [finalRead_eq hp ht, htf, if_pos rfl]
            simp at hb; subst hb
            rw [Ty.subst_of_allFinal fr.selfArgs (Ty.allFinal_keep htf _)]
            rw [Ty.subst_of_allFinal fr.selfArgs htf] at hvt'
            exact hasTy_keep hvt' htf rfl)
        exact ⟨Λ1, hw1, he1.monoW (evalW_mono (by simp [Expr.assigned])), hf1,
          by rw [testOut_ty]; exact hasTy_lit_bool, h1, fun h => h2 (by rwa [truthy_bool] at h),
          fun h => h3 (by rwa [truthy_bool] at h)⟩
    · -- Otherwise the test narrows nothing.
      have hid : ∀ p t, e.path? = some p → c.pathTy Δ p = some t → finalRead c Δ e = false :=
        fun p t hp ht => by
          rw [finalRead_eq hp ht]
          cases h : t.allFinal
          · rfl
          · exact absurd ⟨p, t, hp, ht, h⟩ hfin
      obtain ⟨h1, h2, _⟩ := testOut_ok (b := true)
        (tyT := fun t => if finalRead c Δ e then t.remove .nil else t)
        (tyF := fun t => if finalRead c Δ e then t.keep [.nil] else t) hwf rfl hs1 hf1 hw1 hval
        (fun p t hp ht hvt _ => by rw [hid p t hp ht]; simpa using hvt)
        (fun _ _ _ _ _ hb => by cases hb)
      obtain ⟨_, _, h3⟩ := testOut_ok (b := false)
        (tyT := fun t => if finalRead c Δ e then t.remove .nil else t)
        (tyF := fun t => if finalRead c Δ e then t.keep [.nil] else t) hwf rfl hs1 hf1 hw1 hval
        (fun _ _ _ _ _ hb => by cases hb)
        (fun p t hp ht hvt _ => by rw [hid p t hp ht]; simpa using hvt)
      have := ih.equal s1 Λ1 v .nil _ hw1 hv1 (.inl rfl)
      revert this
      generalize equal c.prog orc n s1 v .nil = r
      intro this
      cases r with
      | ok r s2 =>
        simp only [Result.bind]
        obtain ⟨Λ2, hw2, he2, hr2, _⟩ := this
        have hno : ∀ l, frameLocs fr.vars l → ¬ blkW none l := fun _ _ h => by simp [blkW] at h
        refine ⟨Λ2, hw2, (he1.transF he2 hw).monoW ?_,
          hf1.stable he2 (fun _ _ h => by simp [blkW] at h) (fun _ h => h.elim),
          by rw [testOut_ty]; exact hasTy_lit_bool, h1.stable he2 hno (fun _ _ h => h), fun _ => (h2 rfl).stable he2 hno (fun _ _ h => h),
          fun _ => (h3 rfl).stable he2 hno (fun _ _ h => h)⟩
        rintro l (h | h)
        · exact evalW_mono (by simp [Expr.assigned]) l h
        · simp [blkW] at h
      | stuck => exact this
      | returned => exact this.elim
      | raised => trivial
      | timeout => trivial
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
    by_cases hfin : ∃ p t, e.path? = some p ∧ c.pathTy Δ p = some t ∧ t.allFinal = true
    · -- A read of final atoms: no object, the built-in `==`, which narrows.
      obtain ⟨p, t, hp, ht, htf⟩ := hfin
      have hvt := (pathHolds_of_val hwf rfl hs1 hf1 hw1 ht (hval p hp)).1
      rcases equal_nonobj (orc := orc) (n := n) (s := s1) (w := (.bool true)) (not_obj_of_final (by rwa [Ty.subst_of_allFinal fr.selfArgs htf] at hvt) htf)
        with h | h
      · rw [h]; trivial
      · rw [h]
        obtain ⟨h1, h2, h3⟩ := testOut_ok (b := v == (.bool true))
          (tyT := fun t => if finalRead c Δ e then t.keep [.bool] else t)
          (tyF := id) hwf rfl hs1 hf1 hw1 hval
          (fun p' t' hp' ht' hvt' hb => by
            rw [hp] at hp'; cases hp'; rw [ht] at ht'; cases ht'
            rw [finalRead_eq hp ht, htf, if_pos rfl]
            simp at hb; subst hb
            rw [Ty.subst_of_allFinal fr.selfArgs (Ty.allFinal_keep htf _)]
            rw [Ty.subst_of_allFinal fr.selfArgs htf] at hvt'
            exact hasTy_keep hvt' htf rfl)
          (fun _ _ _ _ hvt' _ => hvt')
        exact ⟨Λ1, hw1, he1.monoW (evalW_mono (by simp [Expr.assigned])), hf1,
          by rw [testOut_ty]; exact hasTy_lit_bool, h1, fun h => h2 (by rwa [truthy_bool] at h),
          fun h => h3 (by rwa [truthy_bool] at h)⟩
    · -- Otherwise the test narrows nothing.
      have hid : ∀ p t, e.path? = some p → c.pathTy Δ p = some t → finalRead c Δ e = false :=
        fun p t hp ht => by
          rw [finalRead_eq hp ht]
          cases h : t.allFinal
          · rfl
          · exact absurd ⟨p, t, hp, ht, h⟩ hfin
      obtain ⟨h1, h2, _⟩ := testOut_ok (b := true)
        (tyT := fun t => if finalRead c Δ e then t.keep [.bool] else t)
        (tyF := id) hwf rfl hs1 hf1 hw1 hval
        (fun p t hp ht hvt _ => by rw [hid p t hp ht]; simpa using hvt)
        (fun _ _ _ _ _ hb => by cases hb)
      obtain ⟨_, _, h3⟩ := testOut_ok (b := false)
        (tyT := fun t => if finalRead c Δ e then t.keep [.bool] else t)
        (tyF := id) hwf rfl hs1 hf1 hw1 hval
        (fun _ _ _ _ _ hb => by cases hb)
        (fun _ _ _ _ hvt _ => hvt)
      have := ih.equal s1 Λ1 v (.bool true) _ hw1 hv1 (.inr (.inl rfl))
      revert this
      generalize equal c.prog orc n s1 v (.bool true) = r
      intro this
      cases r with
      | ok r s2 =>
        obtain ⟨Λ2, hw2, he2, hr2, _⟩ := this
        have hno : ∀ l, frameLocs fr.vars l → ¬ blkW none l := fun _ _ h => by simp [blkW] at h
        refine ⟨Λ2, hw2, (he1.transF he2 hw).monoW ?_,
          hf1.stable he2 (fun _ _ h => by simp [blkW] at h) (fun _ h => h.elim),
          by rw [testOut_ty]; exact hr2, h1.stable he2 hno (fun _ _ h => h), fun _ => (h2 rfl).stable he2 hno (fun _ _ h => h),
          fun _ => (h3 rfl).stable he2 hno (fun _ _ h => h)⟩
        rintro l (h | h)
        · exact evalW_mono (by simp [Expr.assigned]) l h
        · simp [blkW] at h
      | stuck => exact this
      | returned => exact this.elim
      | raised => trivial
      | timeout => trivial
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
    by_cases hfin : ∃ p t, e.path? = some p ∧ c.pathTy Δ p = some t ∧ t.allFinal = true
    · -- A read of final atoms: no object, the built-in `==`, which narrows.
      obtain ⟨p, t, hp, ht, htf⟩ := hfin
      have hvt := (pathHolds_of_val hwf rfl hs1 hf1 hw1 ht (hval p hp)).1
      rcases equal_nonobj (orc := orc) (n := n) (s := s1) (w := (.bool false)) (not_obj_of_final (by rwa [Ty.subst_of_allFinal fr.selfArgs htf] at hvt) htf)
        with h | h
      · rw [h]; trivial
      · rw [h]
        obtain ⟨h1, h2, h3⟩ := testOut_ok (b := v == (.bool false))
          (tyT := fun t => if finalRead c Δ e then t.keep [.bool] else t)
          (tyF := id) hwf rfl hs1 hf1 hw1 hval
          (fun p' t' hp' ht' hvt' hb => by
            rw [hp] at hp'; cases hp'; rw [ht] at ht'; cases ht'
            rw [finalRead_eq hp ht, htf, if_pos rfl]
            simp at hb; subst hb
            rw [Ty.subst_of_allFinal fr.selfArgs (Ty.allFinal_keep htf _)]
            rw [Ty.subst_of_allFinal fr.selfArgs htf] at hvt'
            exact hasTy_keep hvt' htf rfl)
          (fun _ _ _ _ hvt' _ => hvt')
        exact ⟨Λ1, hw1, he1.monoW (evalW_mono (by simp [Expr.assigned])), hf1,
          by rw [testOut_ty]; exact hasTy_lit_bool, h1, fun h => h2 (by rwa [truthy_bool] at h),
          fun h => h3 (by rwa [truthy_bool] at h)⟩
    · -- Otherwise the test narrows nothing.
      have hid : ∀ p t, e.path? = some p → c.pathTy Δ p = some t → finalRead c Δ e = false :=
        fun p t hp ht => by
          rw [finalRead_eq hp ht]
          cases h : t.allFinal
          · rfl
          · exact absurd ⟨p, t, hp, ht, h⟩ hfin
      obtain ⟨h1, h2, _⟩ := testOut_ok (b := true)
        (tyT := fun t => if finalRead c Δ e then t.keep [.bool] else t)
        (tyF := id) hwf rfl hs1 hf1 hw1 hval
        (fun p t hp ht hvt _ => by rw [hid p t hp ht]; simpa using hvt)
        (fun _ _ _ _ _ hb => by cases hb)
      obtain ⟨_, _, h3⟩ := testOut_ok (b := false)
        (tyT := fun t => if finalRead c Δ e then t.keep [.bool] else t)
        (tyF := id) hwf rfl hs1 hf1 hw1 hval
        (fun _ _ _ _ _ hb => by cases hb)
        (fun _ _ _ _ hvt _ => hvt)
      have := ih.equal s1 Λ1 v (.bool false) _ hw1 hv1 (.inr (.inr rfl))
      revert this
      generalize equal c.prog orc n s1 v (.bool false) = r
      intro this
      cases r with
      | ok r s2 =>
        obtain ⟨Λ2, hw2, he2, hr2, _⟩ := this
        have hno : ∀ l, frameLocs fr.vars l → ¬ blkW none l := fun _ _ h => by simp [blkW] at h
        refine ⟨Λ2, hw2, (he1.transF he2 hw).monoW ?_,
          hf1.stable he2 (fun _ _ h => by simp [blkW] at h) (fun _ h => h.elim),
          by rw [testOut_ty]; exact hr2, h1.stable he2 hno (fun _ _ h => h), fun _ => (h2 rfl).stable he2 hno (fun _ _ h => h),
          fun _ => (h3 rfl).stable he2 hno (fun _ _ h => h)⟩
        rintro l (h | h)
        · exact evalW_mono (by simp [Expr.assigned]) l h
        · simp [blkW] at h
      | stuck => exact this
      | returned => exact this.elim
      | raised => trivial
      | timeout => trivial
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
        (obj_of_hasTy_cls hwf hrecv hk) hrecv (resolve_not_init hres) hl hvs'
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
          ⟨_, rfl, hs2.stable he3 hno (fun _ _ h => h)⟩, fun _ => ⟨_, rfl, hs2.stable he3 hno (fun _ _ h => h)⟩,
          fun _ => ⟨_, rfl, hs2.stable he3 hno (fun _ _ h => h)⟩⟩
        rintro l ((h | h) | h)
        · exact evalW_mono (by simp [Expr.assigned]; intros; simp_all) l h
        · exact evalWs_mono (by simp [Expr.assigned]; intros; simp_all) l h
        · simp [blkW] at h
      | stuck => exact hsend
      | returned => exact hsend.elim
      | raised => trivial
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
          ⟨_, rfl, hs1.stable he2 hno (fun _ _ h => h)⟩, fun _ => ⟨_, rfl, hs1.stable he2 hno (fun _ _ h => h)⟩,
          fun _ => ⟨_, rfl, hs1.stable he2 hno (fun _ _ h => h)⟩⟩
        rintro l (h | h)
        · exact evalWs_mono (by simp [Expr.assigned]) l h
        · exact .inr (by rw [hfb]; exact h)
      | stuck => exact hres
      | returned => exact hres.elim
      | raised => trivial
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
        refine ⟨trivial, hf2.core, hf2.chain, hf2.above, ⟨sig, BlockSig.le_refl hwf _, hps, hb, hret⟩, hs2.reset, ?_⟩
        cases ob.out with
        | none => exact hs2
        | some Γb => exact hs2.join_left hwf
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
        ((c, Δ', ob) :: ws) hw2 (obj_of_hasTy_cls hwf hrecv hk) hrecv (resolve_not_init hres) hl hvs'
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
        obtain ⟨_, hcore3, hch3, _, _, _, hJ⟩ := hat3
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
      | raised => trivial
      | timeout => trivial

end QuarzCore
