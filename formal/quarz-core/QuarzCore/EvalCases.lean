/-
`eval` with fuel `n + 1`, from the six functions with fuel `n` (Good):
case by case, as `Typed` derives the expression.
-/

import QuarzCore.SoundDefs
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
    simp [falsyTy, Ty.le]; exact ⟨b, hb, hab⟩
  · simp [Store.typeOf] at ha; subst ha
    refine hasTy_iff.mpr ⟨.bool, rfl, .bool, ?_, by simp [Atom.le]⟩
    simp [falsyTy, Ty.le]; exact ⟨b, hb, hab⟩

/-- An expression giving a value and telling nothing. -/
theorem post_plain {c : Ctx} {Γ : Env} {fr : Frame} {Λ : List Ty} {s : Store} {W : Nat → Prop}
    {v : Value} {t : Ty} (hw : WfStore P Λ s) {ws : List (Ctx × Env × Out)} (hf : FrameOK P c Λ fr s ws) (hs : Sat P c Γ fr s)
    (hv : s.hasTy P v t) : Post P c (.plain t Γ) fr ws Λ s W (.ok v s) :=
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
    {Λ Λ1 : List Ty} {s s1 : Store} {W : Nat → Prop} {k : Nat} {r : Result} (hc : c.prog = P)
    (h : ConstructPost P k Λ1 s1 r) (he1 : Ext P W (initW c fr) Λ Λ1 s s1) (hw : WfStore P Λ s)
    (hf1 : FrameOK P c Λ1 fr s1 ws) (hs1 : Sat P c Δ fr s1) :
    Post P c (.plain [.cls k] Δ) fr ws Λ s W r := by
  subst hc
  cases r with
  | ok v s2 =>
    obtain ⟨Λ2, hw2, he2, hv⟩ := h
    have hs2 := hs1.stable he2 (fun _ _ h => h) (fun _ _ h => h)
    exact ⟨Λ2, hw2, (he1.transF he2 hw).monoW (fun l h => h.elim id False.elim),
      hf1.stable he2 (fun _ _ h => h) (fun _ h => h.elim), hv, ⟨_, rfl, hs2⟩,
      fun _ => ⟨_, rfl, hs2⟩, fun _ => ⟨_, rfl, hs2⟩⟩
  | stuck => exact h.elim
  | returned => exact h.elim
  | raised => trivial
  | timeout => trivial

/-- A `Post` for a wider `Out`. -/
theorem Post.weaken {c : Ctx} {o o' : Out} {fr : Frame} {ws : List (Ctx × Env × Out)} {Λ : List Ty}
    {s : Store} {W : Nat → Prop} {r : Result} (h : Post P c o fr ws Λ s W r)
    (hty : ∀ (s : Store) (v : Value), s.hasTy P v o.ty → s.hasTy P v o'.ty)
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
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]; exact h, rfl, rfl,
    fun _ h => h⟩

/-- `self`: an object of the method's class or a subclass. -/
theorem self_obj {c : Ctx} {Λ : List Ty} {fr : Frame} {s : Store}
    (hc : c.prog = P) {ws : List (Ctx × Env × Out)} (hf : FrameOK P c Λ fr s ws) :
    ∃ l o, fr.self = .obj l ∧ s.objs[l]? = some o ∧ c.meth.owner ∈ P.classes.ancestors o.cls := by
  subst hc
  cases hi : c.inInit
  · obtain ⟨l, hl⟩ := hf.core.selfObj
    have hself := hf.core.self hi
    rw [hl, hasTy_iff] at hself
    obtain ⟨a, ha, b, hb, hab⟩ := hself
    obtain ⟨o, ho, _, rfl⟩ := typeOf_obj ha
    simp at hb; subst hb
    exact ⟨l, o, hl, ho, by simpa [Atom.le, ClassTable.subclass_iff] using hab⟩
  · obtain ⟨l, o, h1, h2, h3, _⟩ := hf.core.selfInit hi
    exact ⟨l, o, h1, h2, h3⟩

/-- Outside `initialize`, `self` is made: every field set. -/
theorem self_made {c : Ctx} {Λ : List Ty} {fr : Frame} {s : Store} {ws : List (Ctx × Env × Out)}
    (hf : FrameOK P c Λ fr s ws) (hi : c.inInit = false) {l : Nat} {o : Obj}
    (hl : fr.self = .obj l) (ho : s.objs[l]? = some o) : o.set.all id = true := by
  have hself := hf.core.self hi
  rw [hl, hasTy_iff] at hself
  obtain ⟨a, ha, _⟩ := hself
  obtain ⟨o', ho', hall, _⟩ := typeOf_obj ha
  rw [ho] at ho'; cases ho'; exact hall

/-- A field of `self`, as the method's class declares it: where the
object has it. -/
theorem self_field (hwf : WfClasses P.classes) {c : Ctx} {Λ : List Ty} {fr : Frame} {s : Store}
    (hc : c.prog = P) {ws : List (Ctx × Env × Out)} (hf : FrameOK P c Λ fr s ws) (hw : WfStore P Λ s) {f : String} {fd : Field}
    (hfd : c.field? f = some fd) :
    ∃ l o i, fr.self = .obj l ∧ s.objs[l]? = some o ∧ fieldIndex P.classes o.cls f = some i ∧
      (P.classes.allFields o.cls)[i]? = some fd ∧ i < o.fields.length ∧ i < o.set.length := by
  obtain ⟨l, o, hl, ho, hsub⟩ := self_obj hc hf
  subst hc
  obtain ⟨i, hi, hfi⟩ := field_in_subclass hwf hsub hfd
  obtain ⟨_, hlen, hslen, _⟩ := hw.objs l o ho
  have hil : i < o.fields.length := by rw [hlen]; exact (List.getElem?_eq_some_iff.mp hfi).1
  exact ⟨l, o, i, hl, ho, hi, hfi, hil, hslen ▸ hil⟩

theorem findIdx?_name {l : List Field} (hn : (l.map (·.name)).Nodup) {i : Nat} {f : Field}
    (hi : l[i]? = some f) : l.findIdx? (·.name == f.name) = some i := by
  obtain ⟨hil, rfl⟩ := List.getElem?_eq_some_iff.mp hi
  rw [List.findIdx?_eq_some_iff_getElem]
  refine ⟨hil, by simp, fun j hj => ?_⟩
  simp only [beq_iff_eq]
  intro he
  rw [List.nodup_iff_pairwise_ne, List.pairwise_iff_getElem] at hn
  exact hn j i (by simp; omega) (by simp; omega) hj (by simpa using he)

/-- A field's index is where it is (the names are distinct). -/
theorem fieldIndex_at (hwf : WfClasses P.classes) {k : Nat} (hk : k < P.classes.length) {i : Nat}
    {f : Field} (hi : (P.classes.allFields k)[i]? = some f) : fieldIndex P.classes k f.name = some i :=
  findIdx?_name (hwf.names k hk) hi

/-- `self` may be used (in `initialize`, once every field is set): it is
of the method's class. -/
theorem self_typed (hwf : WfClasses P.classes) {c : Ctx} {Γ : Env} {Λ : List Ty} {fr : Frame}
    {s : Store} {ws : List (Ctx × Env × Out)} (hc : c.prog = P) (hf : FrameOK P c Λ fr s ws)
    (hw : WfStore P Λ s) (hs : Sat P c Γ fr s) (ha : (!c.inInit || c.allSet Γ) = true) :
    s.hasTy P fr.self [.cls c.meth.owner] := by
  subst hc
  cases hi : c.inInit
  · exact hf.core.self hi
  · rw [hi] at ha; simp only [Bool.not_true, Bool.false_or] at ha
    obtain ⟨l, o, hl, ho, hsub, hbeyond⟩ := hf.core.selfInit hi
    obtain ⟨hcls, _, _, _⟩ := hw.objs l o ho
    have hall : o.set.all id = true := all_id_iff.mpr fun i hi' => by
      by_cases hlt : i < (c.ct.allFields c.meth.owner).length
      · have hfi : (c.ct.allFields c.meth.owner)[i]? = some (c.ct.allFields c.meth.owner)[i] := by
          simp [hlt]
        unfold Ctx.allSet at ha
        have := List.all_eq_true.mp ha _ (List.getElem_mem hlt)
        obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp this
        obtain ⟨l', o', fd, j, h1, h2, _, h4, _, h6, _⟩ := hs _ _ ht
        rw [hl] at h1; cases h1; rw [ho] at h2; cases h2
        obtain ⟨rest, hr⟩ := allFields_prefix hwf hsub
        simp only [Ctx.ct] at hlt hfi
        have hfi' : (c.prog.classes.allFields o.cls)[i]? = some (c.ct.allFields c.meth.owner)[i] := by
          rw [hr, List.getElem?_append_left hlt]; exact hfi
        rw [fieldIndex_at hwf hcls hfi'] at h4; cases h4; exact h6
      · exact hbeyond i (by simp [Ctx.ct] at hlt ⊢; omega) hi'
    exact hasTy_iff.mpr ⟨.cls o.cls, by rw [hl]; exact typeOf_obj_of ho hall, .cls _,
      List.mem_singleton.mpr rfl, by simpa [Atom.le, ClassTable.subclass_iff] using hsub⟩

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
      refine ⟨{ o' with fields := o'.fields.set i v, set := o'.set.set i true }, by simp [h], rfl,
        by simp, fun j hj => ?_⟩
      by_cases hji : j = i
      · subst hji
        have : j < o'.set.length := (List.getElem?_eq_some_iff.mp hj).1
        simp [this]
      · show (o'.set.set i true)[j]? = some true
        rw [List.getElem?_set_ne (Ne.symm hji)]; exact hj
    · exact ⟨o', by simp [hl, h], rfl, rfl, fun _ h => h⟩

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
    (hfi : (P.classes.allFields o.cls)[i]? = some fd)
    (hv : s.hasTy P v fd.ty) : WfStore P Λ (s.setField l i v) where
  len := hw.len
  objs := fun l' o' h => by
    have mono : ∀ {w : Value} {t : Ty}, s.hasTy P w t → (s.setField l i v).hasTy P w t :=
      fun hw' => hasTy_mono setField_grow hw'
    rw [Store.setField_objs] at h
    by_cases hl : l' = l
    · subst hl; rw [if_pos rfl, ho] at h; cases h
      obtain ⟨a, b, b2, d⟩ := hw.objs l' o ho
      refine ⟨a, by simp [b], by simp [b2], fun j w f hs hj hf => ?_⟩
      by_cases hji : j = i
      · subst hji; rw [hfi] at hf; cases hf
        have : j < o.fields.length := by rw [b]; exact (List.getElem?_eq_some_iff.mp hfi).1
        simp [this] at hj; subst hj; exact mono hv
      · simp only at hs hj
        rw [List.getElem?_set_ne (Ne.symm hji)] at hs hj
        exact mono (d j w f hs hj hf)
    · rw [if_neg hl] at h
      obtain ⟨a, b, b2, d⟩ := hw.objs l' o' h
      exact ⟨a, b, b2, fun j w f hs hj hf => mono (d j w f hs hj hf)⟩

/-- A field read where the checker allows it: the field set, its value
of its declared type. -/
theorem self_field_read (hwf : WfClasses P.classes) {c : Ctx} {Γ : Env} {Λ : List Ty} {fr : Frame}
    {s : Store} (hc : c.prog = P) {ws : List (Ctx × Env × Out)} (hf : FrameOK P c Λ fr s ws)
    (hw : WfStore P Λ s) (hs : Sat P c Γ fr s) {f : String} {fd : Field} (hfd : c.field? f = some fd)
    (hin : (!c.inInit || (Γ.get (.field f)).isSome) = true) :
    ∃ l o i v, fr.self = .obj l ∧ s.objs[l]? = some o ∧ fieldIndex P.classes o.cls f = some i ∧
      (P.classes.allFields o.cls)[i]? = some fd ∧ o.set[i]? = some true ∧ o.fields[i]? = some v ∧
      s.hasTy P v fd.ty := by
  obtain ⟨l, o, i, hl, ho, hi, hfi, hil, hsl⟩ := self_field hwf hc hf hw hfd
  have hset : o.set[i]? = some true := by
    cases hii : c.inInit
    · exact all_id_iff.mp (self_made hf hii hl ho) i hsl
    · rw [hii] at hin; simp only [Bool.not_true, Bool.false_or] at hin
      obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hin
      obtain ⟨l', o', _, j, h1, h2, _, h4, _, h6, _⟩ := hs _ _ ht
      rw [hl] at h1; cases h1; rw [ho] at h2; cases h2; rw [hi] at h4; cases h4; exact h6
  exact ⟨l, o, i, o.fields[i], hl, ho, hi, hfi, hset, by simp [hil],
    (hw.objs l o ho).2.2.2 i _ fd hset (by simp [hil]) hfi⟩

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
    ∀ {p : Path} {u : Ty}, PathHolds P c fr s p u → (p = .field f → fd.var = false → s.hasTy P v u) →
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
    (hi : fieldIndex P.classes o.cls f = some i) (hfi : (P.classes.allFields o.cls)[i]? = some fd)
    (hfd : c.field? f = some fd) (hsl : i < o.set.length) (hfl : i < o.fields.length)
    (hv : fd.var = false → s.hasTy P v u) : PathHolds P c fr (s.setField l i v) (.field f) u :=
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
    s.hasTy P v t ∧ ∀ t', s.hasTy P v t' → PathHolds P c fr s p t' := by
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
        obtain ⟨l', o', i', h1, h2, h3, h4, _, _⟩ := self_field hwf hc hf hw hfd
        rw [hl] at h1; cases h1; rw [ho] at h2; cases h2; rw [hi] at h3; cases h3
        refine ⟨?_, fun t' h => ⟨l, o, fd, i, hl, ho, hfd, hi, h4, hset, fun _ => ⟨v, hfv, h⟩⟩⟩
        cases hg : Δ.get (.field f) with
        | none => rw [hg] at ht; simp at ht; subst ht; exact (hw.objs l o ho).2.2.2 i v fd hset hfv h4
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
    (hT : ∀ p t, e.path? = some p → c.pathTy Δ p = some t → s.hasTy P v t → b = true →
      s.hasTy P v (tyT t))
    (hF : ∀ p t, e.path? = some p → c.pathTy Δ p = some t → s.hasTy P v t → b = false →
      s.hasTy P v (tyF t)) :
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
      exact ⟨_, narrow_eq Δ _ (ne_nil_of_hasTy h), hs.set (hre _ h)⟩
    · have h := hF _ _ hp' ht' hvt hb
      exact ⟨_, narrow_eq Δ _ (ne_nil_of_hasTy h), hs.set (hre _ h)⟩
  · exact ⟨⟨Δ, rfl, hs⟩, fun _ => ⟨Δ, rfl, hs⟩, fun _ => ⟨Δ, rfl, hs⟩⟩

theorem resolve_mem {t : Ty} {m : String} {ms : List Method} (h : P.resolve t m = some ms)
    {b : Atom} (hb : b ∈ t) : ∃ k mt, b = .cls k ∧ k ≠ 0 ∧ P.lookup k m = some mt ∧ mt ∈ ms := by
  unfold Program.resolve at h
  split at h
  · cases h
  clear ‹¬_›
  induction t generalizing ms with
  | nil => cases hb
  | cons a t ih =>
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff] at h
    obtain ⟨mt0, h0, ms', h', hms⟩ := h
    simp [pure] at hms; subst hms
    rcases List.mem_cons.mp hb with rfl | hb
    · cases b with
      | cls k =>
        by_cases hk : k = 0
        · simp [hk] at h0
        · simp [hk] at h0
          exact ⟨k, mt0, rfl, hk, h0, by simp⟩
      | _ => simp at h0
    · obtain ⟨k, mt, h1, h2, h3, h4⟩ := ih hb h'
      exact ⟨k, mt, h1, h2, h3, List.mem_cons_of_mem _ h4⟩

/-- No call reaches `initialize`. -/
theorem resolve_not_init {t : Ty} {m : String} {ms : List Method} (h : P.resolve t m = some ms) :
    m ≠ "initialize" := by
  rintro rfl; simp [Program.resolve] at h

theorem AllTy.le (hwf : WfClasses P.classes) {s : Store} :
    ∀ {vs : List Value} {ts us : List Ty}, AllTy P s vs ts → ts.length = us.length →
      ((ts.zip us).all fun (t, u) => t.le P.classes u) = true → AllTy P s vs us
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
      ts.length = ps.length → ((ts.zip ps).all fun (t, (_, u)) => t.le P.classes u) = true →
      AllTy P s vs (ps.map (·.2))
  | [], [], [], _, _, _ => trivial
  | _ :: _, _ :: _, _ :: _, ⟨h1, h2⟩, hl, ha => by
    simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at ha
    exact ⟨hasTy_le hwf h1 ha.1, AllTy.le_params hwf h2 (by simpa using hl) ha.2⟩
  | [], [], _ :: _, _, hl, _ => by simp at hl
  | [], _ :: _, _, h, _, _ => h.elim
  | _ :: _, [], _, h, _, _ => h.elim
  | _ :: _, _ :: _, [], _, hl, _ => by simp at hl

theorem hasTy_flatMap {s : Store} {v : Value} {ms : List Method} {mt : Method} (hm : mt ∈ ms)
    (h : s.hasTy P v mt.ret) : s.hasTy P v (ms.flatMap (·.ret)) := by
  rw [hasTy_iff] at *
  obtain ⟨a, ha, b, hb, hab⟩ := h
  exact ⟨a, ha, b, List.mem_flatMap.mpr ⟨mt, hm, hb⟩, hab⟩

/-- A value of a class other than `Object`: an object of a subclass. -/
theorem obj_of_hasTy_cls {s : Store} {v : Value} {k : Nat} (hv : s.hasTy P v [.cls k]) (hk : k ≠ 0) :
    ∃ l o, v = .obj l ∧ s.objs[l]? = some o ∧ k ∈ P.classes.ancestors o.cls := by
  rw [hasTy_iff] at hv
  obtain ⟨a, ha, b, hb, hab⟩ := hv
  simp at hb; subst hb
  cases v with
  | obj l =>
    obtain ⟨o, ho, _, rfl⟩ := typeOf_obj ha
    exact ⟨l, o, rfl, ho, by simpa [Atom.le, ClassTable.subclass_iff] using hab⟩
  | _ => simp [Store.typeOf] at ha; subst ha; simp [Atom.le] at hab; exact absurd hab hk

/-- The receiver of a call: of the class the method was found in. -/
theorem recv_of {s : Store} {v : Value} {t : Ty} {m : String} {ms : List Method}
    (hv : s.hasTy P v t) (hres : P.resolve t m = some ms) :
    ∃ k mt, k ≠ 0 ∧ P.lookup k m = some mt ∧ mt ∈ ms ∧ s.hasTy P v [.cls k] := by
  rw [hasTy_iff] at hv
  obtain ⟨a, ha, b, hb, hab⟩ := hv
  obtain ⟨k, mt, rfl, hk, hl, hm⟩ := resolve_mem hres hb
  exact ⟨k, mt, hk, hl, hm, hasTy_iff.mpr ⟨a, ha, .cls k, List.mem_singleton.mpr rfl, hab⟩⟩

theorem blkW_chain : ∀ {blk : Option Closure} {l : Nat}, blkW blk l → chainLocs blk l
  | none, _, h => by simp [blkW] at h
  | some (.mk vars me outer ps body), l, h => by
    simp only [blkW, chainLocs] at h ⊢
    rcases h with ⟨x, _, hx⟩ | h
    · exact .inl ⟨x, lookupVar_mem hx⟩
    · exact .inr (blkW_chain h)

/-- What a frame's block writes misses the frame. -/
theorem FrameOK.blk_not_own {c : Ctx} {Λ : List Ty} {fr : Frame} {s : Store} {ws : List (Ctx × Env × Out)} (hf : FrameOK P c Λ fr s ws) :
    ∀ l, frameLocs fr.vars l → ¬ blkW fr.blk l := fun l hl hb =>
  Nat.lt_irrefl _ (hf.above l l hl (blkW_chain hb))

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
  | self ha => exact post_plain hw hf hs (self_typed hwf rfl hf hw hs ha)
  | raise => trivial
  | var hu hle =>
    obtain ⟨l, v, d, hl, hv, hd, hvu, hvd⟩ := hs _ _ hu
    have hvt := hasTy_le hwf hvu hle
    simp only [eval, hl, Option.bind_some, hv]
    simp only [Store.hasTy] at hvt
    rw [if_pos hvt]
    refine ⟨Λ, hw, Ext.refl _ _ Λ s, hf, hvt, ⟨Γ, rfl, hs⟩, fun htr => ?_, fun hfa => ?_⟩
    · have h1 := hasTy_truthy hvu htr
      exact ⟨_, narrow_eq Γ _ (ne_nil_of_hasTy h1), hs.set ⟨l, v, d, hl, hv, hd, h1, hvd⟩⟩
    · have h1 := hasTy_falsy hvu hfa
      exact ⟨_, narrow_eq Γ _ (ne_nil_of_hasTy h1), hs.set ⟨l, v, d, hl, hv, hd, h1, hvd⟩⟩
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
      refine ⟨Λ1, a, b.monoW (evalW_mono (by simp [Expr.assigned])), d, hasTy_le hwf g hle, hib,
        fun hi => ?_⟩
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
          (fun _ _ h => hasTy_append_right hwf _ h) (fun _ h => h.join_right hwf)
          (fun _ h => h.join_right hwf) (fun _ h => h.join_right hwf)
    · rw [if_pos rfl]
      obtain ⟨Δ, hΔ, hs1⟩ := htt hv
      rw [hΔ] at hbt
      cases hbt with
      | live ht' =>
        refine ((ih.eval _ _ _ _ fr s1 Λ1 ws rfl ht' hw1 hf1 hs1).extend he1 hw
          (evalW_mono (by simp [Expr.assigned]; intros; simp_all))
          (evalW_mono (by simp [Expr.assigned]; intros; simp_all))).weaken
          (fun _ _ h => hasTy_append_left hwf _ h) (fun _ h => h.join_left hwf)
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
        hasTy_append_left hwf _ hv1, hfo.join_left hwf, fun h => absurd (hv.symm.trans h) (by simp),
        fun _ => hfo.join_left hwf⟩
    · rw [if_pos rfl]
      obtain ⟨Δ, hΔ, hs1⟩ := htt hv
      rw [hΔ] at hbb
      cases hbb with
      | live hb =>
        refine ((ih.eval _ _ _ _ fr s1 Λ1 ws rfl hb hw1 hf1 hs1).extend he1 hw
          (evalW_mono (by simp [Expr.assigned]; intros; simp_all))
          (evalW_mono (by simp [Expr.assigned]; intros; simp_all))).weaken
          (fun _ _ h => hasTy_append_right hwf _ h) (fun _ h => h.join_right hwf)
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
          (fun _ _ h => hasTy_append_right hwf _ h) (fun _ h => h.join_right hwf)
          (fun _ h => h.join_right hwf) (fun _ h => h)
    · rw [if_pos rfl]
      have hto := htt hv
      exact ⟨Λ1, hw1, he1.monoW (evalW_mono (by simp [Expr.assigned]; intros; simp_all)), hf1,
        hasTy_append_left hwf _ hv1, hto.join_left hwf, fun _ => hto.join_left hwf,
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
    have hvd := hasTy_le hwf hv1 hle
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
  | new hk hargs hmi hok =>
    rename_i k args tys Δ mi
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
      exact Post.ofConstruct rfl (ih.construct s1 Λ1 k vs hw1 hk
          (fun mi' h => by
            rw [hmi] at h; cases h
            exact ⟨hblk, AllTy.le_params hwf hvs hlen hall⟩)
          (fun h => by rw [hmi] at h; cases h))
        (he1.monoW (evalWs_mono (by simp [Expr.assigned]))) hw hf1 hs1
  | newNoInit hk hargs hmi hnil =>
    rename_i k args tys Δ
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
      exact Post.ofConstruct rfl (ih.construct s1 Λ1 k vs hw1 hk
          (fun mi' h => by rw [hmi] at h; cases h)
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
    have hvt := hasTy_le hwf hty hle
    simp only [eval, hl, ho, hi, Option.bind_some, hset, if_true, hv]
    simp only [Store.hasTy] at hvt
    rw [if_pos hvt]
    exact post_plain hw hf hs hvt
  | fieldImm hfd hin hvar hu hle =>
    rename_i fd u f t
    obtain ⟨l, o, i, v, hl, ho, hi, hfi, hset, hv, hty⟩ := self_field_read hwf rfl hf hw hs hfd hin
    have hvu : s.hasTy c.prog v u := by
      cases hg : Γ.get (.field f) with
      | none => rw [hg] at hu; simp at hu; subst hu; exact hty
      | some u' =>
        rw [hg] at hu; simp at hu; subst hu
        obtain ⟨l', o', fd', i', h1, h2, h3, h5, _, _, h7⟩ := hs _ _ hg
        rw [hl] at h1; cases h1; rw [ho] at h2; cases h2; rw [hi] at h5; cases h5
        rw [hfd] at h3; cases h3
        obtain ⟨w, h8, h9⟩ := h7 hvar
        rw [hv] at h8; cases h8; exact h9
    have hvt := hasTy_le hwf hvu hle
    simp only [eval, hl, ho, hi, Option.bind_some, hset, if_true, hv]
    simp only [Store.hasTy] at hvt
    rw [if_pos hvt]
    refine ⟨Λ, hw, Ext.refl _ _ Λ s, hf, hvt, ⟨Γ, rfl, hs⟩, fun htr => ?_, fun hfa => ?_⟩
    · have h1 := hasTy_truthy hvu htr
      exact ⟨_, narrow_eq Γ _ (ne_nil_of_hasTy h1), hs.set ⟨l, o, fd, i, hl, ho, hfd, hi,
        hfi, hset, fun _ => ⟨v, hv, h1⟩⟩⟩
    · have h1 := hasTy_falsy hvu hfa
      exact ⟨_, narrow_eq Γ _ (ne_nil_of_hasTy h1), hs.set ⟨l, o, fd, i, hl, ho, hfd, hi,
        hfi, hset, fun _ => ⟨v, hv, h1⟩⟩⟩
  | @setField fd _ _ e o' Δ f hfd hvar he hle hout =>
    simp only [eval]
    refine (ih.eval _ _ _ _ fr s Λ ws rfl he hw hf hs).bind
      (evalW_mono (by simp [Expr.assigned])) ?_
    intro v s1 Λ1 hw1 he1 hf1 hv1 ho1 _ _
    obtain ⟨Δ', hΔ, hs1⟩ := ho1
    rw [hout] at hΔ; cases hΔ
    obtain ⟨l, o, i, hl, ho, hi, hfi, _, _⟩ := self_field hwf rfl hf1 hw1 hfd
    simp only [hl, ho, hi, Option.bind_some]
    -- An immutable field: in `initialize`, of its `self`.
    have hW : fd.var = false → initW c fr l := fun h => by
      rw [h] at hvar; simp only [Bool.false_or, Bool.and_eq_true, Bool.not_eq_true'] at hvar
      exact ⟨hvar.1, hvar.2, hl⟩
    have he2 : Ext c.prog (fun _ => False) (initW c fr) Λ1 Λ1 s1 (s1.setField l i v) :=
      Ext.setField ho hfi hW
    have hvd := hasTy_le hwf hv1 hle
    -- The environment after: `f` set, holding the value (if immutable).
    have hs2 : Sat c.prog c (if c.inInit then Δ.set (.field f) (if fd.var then fd.ty else o'.ty) else Δ)
        fr (s1.setField l i v) := by
      have hold : ∀ q u, Δ.get q = some u → (q = .field f → fd.var = false → s1.hasTy c.prog v u) →
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
      (fun _ t _ _ ht hb => by simp at hb; subst hb; exact hasTy_nilTy ht)
      (fun _ t _ _ ht hb => hasTy_remove_nil ht (by simpa using hb))
    exact ⟨Λ1, hw1, he1.monoW (evalW_mono (by simp [Expr.assigned])), hf1, by rw [testOut_ty]; exact hasTy_lit_bool, h1,
      fun h => h2 (by rwa [truthy_bool] at h), fun h => h3 (by rwa [truthy_bool] at h)⟩
  | isA he hout =>
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
    obtain ⟨h1, h2, h3⟩ := testOut_ok (b := u.le c.prog.classes a) hwf rfl hs1 hf1 hw1 hval
      (fun _ t _ _ ht hb => hasTy_isATrue hwf ht hu hb)
      (fun _ t _ _ ht hb => hasTy_isAFalse hwf ht hu hb)
    exact ⟨Λ1, hw1, he1.monoW (evalW_mono (by simp [Expr.assigned])), hf1, by rw [testOut_ty]; exact hasTy_lit_bool, h1,
      fun h => h2 (by rwa [truthy_bool] at h), fun h => h3 (by rwa [truthy_bool] at h)⟩
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
      rcases equal_nonobj (orc := orc) (n := n) (s := s1) (w := .nil) (not_obj_of_final hvt htf)
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
            exact hasTy_keep hvt' htf rfl)
          (fun p' t' hp' ht' hvt' hb => by
            rw [hp] at hp'; cases hp'; rw [ht] at ht'; cases ht'
            rw [finalRead_eq hp ht, htf, if_pos rfl]
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
      rcases equal_nonobj (orc := orc) (n := n) (s := s1) (w := .nil) (not_obj_of_final hvt htf)
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
            exact hasTy_remove_nil hvt' (by simpa using hb))
          (fun p' t' hp' ht' hvt' hb => by
            rw [hp] at hp'; cases hp'; rw [ht] at ht'; cases ht'
            rw [finalRead_eq hp ht, htf, if_pos rfl]
            simp at hb; subst hb
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
      rcases equal_nonobj (orc := orc) (n := n) (s := s1) (w := (.bool true)) (not_obj_of_final hvt htf)
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
      rcases equal_nonobj (orc := orc) (n := n) (s := s1) (w := (.bool false)) (not_obj_of_final hvt htf)
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
      obtain ⟨k, mt, hk, hl, hmem, hrecv⟩ := recv_of (he2.hasTy hv1) hres
      have hmt := List.all_eq_true.mp hall mt hmem
      simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hmt
      obtain ⟨hblk, hok⟩ := hmt
      unfold argsOk at hok
      simp only [Bool.and_eq_true, beq_iff_eq] at hok
      have hvs' : AllTy c.prog s2 vs (mt.params.map (·.2)) := hvs.le_params hwf hok.1 hok.2
      have hsend := ih.send s2 Λ2 v k _ mt vs none [] hw2 (obj_of_hasTy_cls hrecv hk) hrecv
        (resolve_not_init hres) hl hvs'
        (by rw [hblk]; exact ⟨trivial, fun l h => by simp [chainLocs] at h⟩)
      revert hsend
      generalize send c.prog orc n s2 v _ vs none = r
      intro hsend
      cases r with
      | ok w s3 =>
        obtain ⟨Λ3, hw3, he3, hw', _⟩ := hsend
        have hno : ∀ l, frameLocs fr.vars l → ¬ blkW none l := fun _ _ h => by simp [blkW] at h
        refine ⟨Λ3, hw3, ((he1.transW he2 hw).transF he3 (by exact hw)).monoW ?_,
          hf2.stable he3 (fun _ _ h => by simp [blkW] at h) (fun _ h => h.elim), hasTy_flatMap hmem hw',
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
      have hvs' : AllTy c.prog s1 vs sig.params := hvs.le hwf hlen hall
      have hres := ih.block s1 Λ1 clo sig vs ws hw1
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
          hv2, ⟨_, rfl, hs1.stable he2 hno (fun _ _ h => h)⟩, fun _ => ⟨_, rfl, hs1.stable he2 hno (fun _ _ h => h)⟩,
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
      obtain ⟨k, mt, hk, hl, hmem, hrecv⟩ := recv_of (he2.hasTy hv1) hres
      have hmt := List.all_eq_true.mp hall mt hmem
      simp only [Bool.and_eq_true, beq_iff_eq] at hmt
      obtain ⟨hblk, hok⟩ := hmt
      unfold argsOk at hok
      simp only [Bool.and_eq_true, beq_iff_eq] at hok
      have hvs' : AllTy c.prog s2 vs (mt.params.map (·.2)) := hvs.le_params hwf hok.1 hok.2
      -- The block, as checked here.
      have hat : ChainAt c.prog Λ2 s2 ((c, Δ', ob) :: ws) (some (.mk fr.vars fr.self fr.blk ps body))
          (some sig) := by
        simp only [ChainAt]
        refine ⟨trivial, hf2.core, hf2.chain, hf2.above, hps, hb, hret, hs2.reset, ?_⟩
        cases ob.out with
        | none => exact hs2
        | some Γb => exact hs2.join_left hwf
      have hin : ∀ l, chainLocs (some (.mk fr.vars fr.self fr.blk ps body)) l → l < s2.locs.length := by
        intro l hl
        simp only [chainLocs] at hl
        rcases hl with ⟨x, hx⟩ | hl
        · exact hf2.core.inStore x l hx
        · exact hf2.chainIn l hl
      have hsend := ih.send s2 Λ2 v k m mt vs (some (.mk fr.vars fr.self fr.blk ps body))
        ((c, Δ', ob) :: ws) hw2 (obj_of_hasTy_cls hrecv hk) hrecv (resolve_not_init hres) hl hvs'
        (by rw [hblk]; exact ⟨hat, hin⟩)
      revert hsend
      generalize send c.prog orc n s2 v m vs _ = r
      intro hsend
      cases r with
      | ok w s3 =>
        obtain ⟨Λ3, hw3, he3, hw', hg3⟩ := hsend
        rw [hblk] at hg3
        obtain ⟨hat3, hin3⟩ := hg3
        simp only [ChainAt] at hat3
        obtain ⟨_, hcore3, hch3, _, _, _, _, _, hJ⟩ := hat3
        have hfr : (⟨fr.vars, fr.self, fr.blk⟩ : Frame) = fr := rfl
        rw [hfr] at hJ
        have hf3 : FrameOK c.prog c Λ3 fr s3 ws :=
          ⟨hcore3, hch3, hf2.above, fun l hl => hin3 l (by simp only [chainLocs]; exact .inr hl),
            hf2.initBlk⟩
        refine ⟨Λ3, hw3, ((he1.transW he2 hw).transF he3 hw).monoW ?_, hf3, hasTy_flatMap hmem hw',
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
