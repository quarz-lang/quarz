/-
Lemmas for the soundness proof: types and values, environments, stores.
-/

import QuarzCore.Invariants

set_option linter.deprecated false

namespace QuarzCore

variable {P : Program}

/-! ### Types -/

theorem Ty.le_iff {ct : ClassTable} {s t : Ty} :
    s.le ct t = true ↔ ∀ a ∈ s, ∃ b ∈ t, a.le ct b = true := by
  simp [Ty.le]

theorem Ty.le_refl {ct : ClassTable} (hwf : WfClasses ct) (t : Ty) : t.le ct t = true :=
  Ty.le_iff.mpr fun a ha => ⟨a, ha, Atom.le_refl hwf a⟩

theorem Ty.le_trans {ct : ClassTable} (hwf : WfClasses ct) {s t u : Ty}
    (h1 : s.le ct t = true) (h2 : t.le ct u = true) : s.le ct u = true := by
  rw [Ty.le_iff] at *
  intro a ha
  obtain ⟨b, hb, hab⟩ := h1 a ha
  obtain ⟨c, hc, hbc⟩ := h2 b hb
  exact ⟨c, hc, Atom.le_trans hwf hab hbc⟩

theorem Ty.le_of_subset {ct : ClassTable} (hwf : WfClasses ct) {s t : Ty}
    (h : ∀ a ∈ s, a ∈ t) : s.le ct t = true :=
  Ty.le_iff.mpr fun a ha => ⟨a, h a ha, Atom.le_refl hwf a⟩

theorem Ty.le_append_left {ct : ClassTable} (hwf : WfClasses ct) (s t : Ty) :
    s.le ct (s ++ t) = true := Ty.le_of_subset hwf fun a ha => List.mem_append_left _ ha

theorem Ty.le_append_right {ct : ClassTable} (hwf : WfClasses ct) (s t : Ty) :
    t.le ct (s ++ t) = true := Ty.le_of_subset hwf fun a ha => List.mem_append_right _ ha

theorem Ty.append_le {ct : ClassTable} {s t u : Ty} (h1 : s.le ct u = true)
    (h2 : t.le ct u = true) : (s ++ t).le ct u = true := by
  rw [Ty.le_iff] at *
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · exact h1 a ha
  · exact h2 a ha

/-! ### Substitution keeps the order -/

theorem Ty.mem_subst {σ : List Ty} : ∀ {s : Ty} {a' : Atom},
    a' ∈ Ty.subst σ s ↔ ∃ a ∈ s, a' ∈ a.subst σ := by
  intro s a'
  induction s with
  | nil => simp [Ty.subst]
  | cons a s ih =>
    simp only [Ty.subst, List.mem_append, ih, List.mem_cons]
    constructor
    · rintro (h | ⟨b, hb, h⟩)
      · exact ⟨a, Or.inl rfl, h⟩
      · exact ⟨b, Or.inr hb, h⟩
    · rintro ⟨b, rfl | hb, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨b, hb, h⟩

theorem Atom.subst_le {ct : ClassTable} (hwf : WfClasses ct) (σ : List Ty) {a b : Atom}
    (h : a.le ct b = true) : Ty.le ct (a.subst σ) (b.subst σ) = true := by
  cases b
  case cls d bs =>
    cases a
    -- Two classes: the top, or the chain's arguments substituted.
    case cls c as =>
      rw [Atom.le_cls_iff] at h
      rcases h with ⟨rfl, rfl⟩ | h
      · simp [Atom.subst, Ty.le, Atom.le]
      · simp only [Atom.subst, Ty.le, List.all_cons, List.all_nil, List.any_cons, List.any_nil,
          Bool.or_false, Bool.and_true]
        rw [(Atom.le_cls_iff c _ d _).mpr (Or.inr (ClassTable.ancestorArgs_subst ct σ h))]
    -- A parameter below `Object`: what it stands for is too.
    case param i =>
      simp only [Atom.le, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [Atom.subst]
      cases σ[i]? with
      | none => simp [Option.getD, Ty.le, Atom.le]
      | some t =>
        simp only [Option.getD, Ty.le]
        exact List.all_eq_true.mpr fun a _ => by simp [Atom.le_top]
    -- A value below `Object`.
    all_goals
      simp only [Atom.le, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [Atom.subst, Ty.le, Atom.le]
  case param j =>
    cases a
    case param i =>
      simp only [Atom.le, beq_iff_eq] at h
      subst h
      simp only [Atom.subst]
      cases σ[i]? with
      | none => simp [Option.getD, Ty.le, Atom.le]
      | some t => simp only [Option.getD]; exact Ty.le_refl hwf t
    all_goals simp_all [Atom.le]
  -- A value atom: only itself is below it.
  all_goals cases a <;> simp_all [Atom.le] <;> simp [Atom.subst, Ty.le, Atom.le]

theorem Ty.subst_le {ct : ClassTable} (hwf : WfClasses ct) (σ : List Ty) {s t : Ty}
    (h : s.le ct t = true) : Ty.le ct (s.subst σ) (t.subst σ) = true := by
  rw [Ty.le_iff] at h ⊢
  intro a' ha'
  obtain ⟨a, ha, ha'⟩ := Ty.mem_subst.mp ha'
  obtain ⟨b, hb, hab⟩ := h a ha
  have := Ty.le_iff.mp (Atom.subst_le hwf σ hab) a' ha'
  obtain ⟨b', hb', h'⟩ := this
  exact ⟨b', Ty.mem_subst.mpr ⟨b, hb, hb'⟩, h'⟩

/-! ### Values -/

theorem hasTy_iff {s : Store} {v : Value} {t : Ty} :
    s.hasTy P v t ↔ ∃ a, s.typeOf v = some a ∧ ∃ b ∈ t, a.le P.classes b = true := by
  unfold Store.hasTy Store.hasType
  cases h : s.typeOf v with
  | none => simp
  | some a => simp [Ty.le]

theorem hasTy_le (hwf : WfClasses P.classes) {s : Store} {v : Value} {t u : Ty}
    (h : s.hasTy P v t) (hle : t.le P.classes u = true) : s.hasTy P v u := by
  rw [hasTy_iff] at *
  obtain ⟨a, ha, b, hb, hab⟩ := h
  obtain ⟨c, hc, hbc⟩ := Ty.le_iff.mp hle b hb
  exact ⟨a, ha, c, hc, Atom.le_trans hwf hab hbc⟩

theorem hasTy_append_left (hwf : WfClasses P.classes) {s : Store} {v : Value} {t : Ty}
    (u : Ty) (h : s.hasTy P v t) : s.hasTy P v (t ++ u) :=
  hasTy_le hwf h (Ty.le_append_left hwf t u)

theorem hasTy_append_right (hwf : WfClasses P.classes) {s : Store} {v : Value} {u : Ty}
    (t : Ty) (h : s.hasTy P v u) : s.hasTy P v (t ++ u) :=
  hasTy_le hwf h (Ty.le_append_right hwf t u)

/-- A value of type `[]` there is none. -/
theorem not_hasTy_nil {s : Store} {v : Value} : ¬ s.hasTy P v [] := by
  simp [hasTy_iff]

/-- Every flag set, by index. -/
theorem all_id_iff {bs : List Bool} : bs.all id = true ↔ ∀ i, i < bs.length → bs[i]? = some true := by
  constructor
  · intro h i hi
    have := List.all_eq_true.mp h bs[i] (List.getElem_mem hi)
    simp at this; simp [hi, this]
  · intro h
    apply List.all_eq_true.mpr
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    have := h i hi; simp [hi] at this; simpa using this

/-- An object made (every field set) stays made. -/
theorem all_set_grow {o o' : Obj} (hl : o'.set.length = o.set.length)
    (hs : ∀ i : Nat, o.set[i]? = some true → o'.set[i]? = some true) (h : o.set.all id = true) :
    o'.set.all id = true :=
  all_id_iff.mpr fun i hi => hs i (all_id_iff.mp h i (hl ▸ hi))

theorem typeOf_obj {s : Store} {l : Nat} {a : Atom} (h : s.typeOf (.obj l) = some a) :
    ∃ o, s.objs[l]? = some o ∧ o.set.all id = true ∧ a = .cls o.cls o.args := by
  simp only [Store.typeOf, Option.bind_eq_some_iff] at h
  obtain ⟨o, ho, h⟩ := h
  split at h
  · cases h; exact ⟨o, ho, by assumption, rfl⟩
  · cases h

theorem typeOf_obj_of {s : Store} {l : Nat} {o : Obj} (ho : s.objs[l]? = some o)
    (h : o.set.all id = true) : s.typeOf (.obj l) = some (.cls o.cls o.args) := by
  simp only [Store.typeOf, ho, Option.bind_some, h, if_true]

/-- Objects keeping their classes and the fields set, values keep their
types. -/
theorem typeOf_mono {s s' : Store} (h : ObjsGrow s s')
    {v : Value} {a : Atom} (hv : s.typeOf v = some a) : s'.typeOf v = some a := by
  cases v with
  | obj l =>
    obtain ⟨o, ho, hall, rfl⟩ := typeOf_obj hv
    obtain ⟨o', ho', hc, ha, hl, hs⟩ := h l o ho
    rw [typeOf_obj_of ho' (all_set_grow hl hs hall), hc, ha]
  | _ => simpa [Store.typeOf] using hv

theorem hasTy_mono {s s' : Store} (h : ObjsGrow s s')
    {v : Value} {t : Ty} (hv : s.hasTy P v t) : s'.hasTy P v t := by
  rw [hasTy_iff] at *
  obtain ⟨a, ha, rest⟩ := hv
  exact ⟨a, typeOf_mono h ha, rest⟩

theorem Ext.hasTy {W Wo : Nat → Prop} {Λ Λ' : List Ty} {s s' : Store} (he : Ext P W Wo Λ Λ' s s')
    {v : Value} {t : Ty} (hv : s.hasTy P v t) : s'.hasTy P v t :=
  hasTy_mono he.grow hv

/-! ### Environments -/

namespace Env

theorem get_cons (p q : Path) (t : Ty) (Γ : Env) :
    get ((q, t) :: Γ) p = if q = p then some t else get Γ p := rfl

theorem get_filter_ne (Γ : Env) (p q : Path) (h : q ≠ p) :
    get (Γ.filter (·.1 != p)) q = get Γ q := by
  induction Γ with
  | nil => rfl
  | cons e Γ ih =>
    obtain ⟨r, u⟩ := e
    by_cases hr : r = p
    · subst hr
      have : (r != r) = false := by simp
      rw [List.filter_cons, this, if_neg (by simp), ih, get_cons, if_neg (fun e => h e.symm)]
    · have : (r != p) = true := by simpa using hr
      rw [List.filter_cons, this, if_pos rfl, get_cons, get_cons, ih]

theorem get_set (Γ : Env) (p q : Path) (t : Ty) :
    (Γ.set p t).get q = if q = p then some t else Γ.get q := by
  unfold set
  rw [get_cons]
  by_cases h : p = q
  · subst h; simp
  · rw [if_neg h, if_neg (fun e => h e.symm), get_filter_ne _ _ _ (fun e => h e.symm)]

theorem get_join {Γ Δ : Env} {p : Path} {t : Ty} (h : (Γ.join Δ).get p = some t) :
    ∃ t1 t2, Γ.get p = some t1 ∧ Δ.get p = some t2 ∧ t = t1 ++ t2 := by
  induction Γ with
  | nil => simp [join, get] at h
  | cons e Γ ih =>
    obtain ⟨q, u⟩ := e
    simp only [join] at h
    cases hd : Δ.get q with
    | none =>
      rw [hd] at h
      obtain ⟨t1, t2, h1, h2, h3⟩ := ih h
      by_cases hq : q = p
      · subst hq; rw [hd] at h2; cases h2
      · exact ⟨t1, t2, by rw [get_cons, if_neg hq]; exact h1, h2, h3⟩
    | some w =>
      rw [hd, get_cons] at h
      by_cases hq : q = p
      · subst hq; rw [if_pos rfl] at h; cases h
        exact ⟨u, w, by rw [get_cons, if_pos rfl], hd, rfl⟩
      · rw [if_neg hq] at h
        obtain ⟨t1, t2, h1, h2, h3⟩ := ih h
        exact ⟨t1, t2, by rw [get_cons, if_neg hq]; exact h1, h2, h3⟩

end Env

theorem Ctx.reset_get_field {c : Ctx} {Γ : Env} {xs : List String} {f : String} :
    (c.reset Γ xs).get (.field f) = Γ.get (.field f) := by
  induction Γ with
  | nil => rfl
  | cons e Γ ih =>
    obtain ⟨q, u⟩ := e
    cases q with
    | field g => simp only [Ctx.reset, Env.get_cons, ih]
    | «local» x =>
      have hne : Path.local x ≠ Path.field f := by simp
      by_cases hx : x ∈ xs
      · cases hd : c.decl x with
        | none => simp only [Ctx.reset, hx, if_true, hd, Env.get_cons, hne, if_false, ih]
        | some d => simp only [Ctx.reset, hx, if_true, hd, Env.get_cons, hne, if_false, ih]
      · simp only [Ctx.reset, hx, if_false, Env.get_cons, hne, ih]

theorem Ctx.reset_get_local {c : Ctx} {Γ : Env} {xs : List String} {x : String} {t : Ty}
    (h : (c.reset Γ xs).get (.local x) = some t) :
    ∃ u, Γ.get (.local x) = some u ∧ (if x ∈ xs then c.decl x = some t else u = t) := by
  induction Γ with
  | nil => simp [Ctx.reset, Env.get] at h
  | cons e Γ ih =>
    obtain ⟨q, u⟩ := e
    cases q with
    | field g =>
      simp only [Ctx.reset] at h
      rw [Env.get_cons, if_neg (by simp)] at h ⊢
      exact ih h
    | «local» y =>
      simp only [Ctx.reset] at h
      rw [Env.get_cons]
      by_cases hy : y = x
      · subst hy
        rw [if_pos rfl]
        by_cases hx : y ∈ xs
        · rw [if_pos hx] at h
          cases hd : c.decl y with
          | none =>
            rw [hd] at h
            -- The entry is dropped, and every later one for `y` too.
            obtain ⟨_, _, hdx⟩ := ih h; rw [if_pos hx, hd] at hdx; cases hdx
          | some d =>
            rw [hd, Env.get_cons, if_pos rfl] at h; cases h
            exact ⟨u, rfl, by simp [hx, hd]⟩
        · rw [if_neg hx, Env.get_cons, if_pos rfl] at h; cases h
          exact ⟨_, rfl, by rw [if_neg hx]⟩
      · have hne : Path.local y ≠ Path.local x := fun e => hy (by cases e; rfl)
        rw [if_neg hne]
        by_cases hyx : y ∈ xs
        · rw [if_pos hyx] at h
          cases hd : c.decl y with
          | none => rw [hd] at h; exact ih h
          | some d =>
            rw [hd, Env.get_cons, if_neg hne] at h
            exact ih h
        · rw [if_neg hyx, Env.get_cons, if_neg hne] at h
          exact ih h

theorem Ctx.reset_idem (c : Ctx) (Γ : Env) (xs : List String) :
    c.reset (c.reset Γ xs) xs = c.reset Γ xs := by
  induction Γ with
  | nil => rfl
  | cons e Γ ih =>
    obtain ⟨q, u⟩ := e
    cases q with
    | field f => simp only [Ctx.reset, ih]
    | «local» x =>
      by_cases hx : x ∈ xs
      · cases hd : c.decl x with
        | none => simp only [Ctx.reset, hx, if_true, hd, ih]
        | some d => simp only [Ctx.reset, hx, if_true, hd, ih]
      · simp only [Ctx.reset, hx, if_false, ih]

/-! ### What holds -/

section
variable {c : Ctx} {fr : Frame} {s : Store}

theorem PathHolds.le (hwf : WfClasses P.classes) {p : Path} {t u : Ty}
    (h : PathHolds P c fr s p t) (hle : t.le P.classes u = true) : PathHolds P c fr s p u := by
  have hle' := Ty.subst_le hwf fr.selfArgs hle
  cases p with
  | «local» x =>
    obtain ⟨l, v, d, h1, h2, h3, h4, h5⟩ := h
    exact ⟨l, v, d, h1, h2, h3, hasTy_le hwf h4 hle', h5⟩
  | field f =>
    obtain ⟨l, o, fd, i, h1, h2, h3, h4, h5, h6, h7⟩ := h
    exact ⟨l, o, fd, i, h1, h2, h3, h4, h5, h6, fun hv => by
      obtain ⟨v, h8, h9⟩ := h7 hv; exact ⟨v, h8, hasTy_le hwf h9 hle'⟩⟩

theorem Sat.join_left (hwf : WfClasses P.classes) {Γ Δ : Env} (h : Sat P c Γ fr s) :
    Sat P c (Γ.join Δ) fr s := by
  intro p t hp
  obtain ⟨t1, t2, h1, _, rfl⟩ := Env.get_join hp
  exact (h p t1 h1).le hwf (Ty.le_append_left hwf _ _)

theorem Sat.join_right (hwf : WfClasses P.classes) {Γ Δ : Env} (h : Sat P c Δ fr s) :
    Sat P c (Γ.join Δ) fr s := by
  intro p t hp
  obtain ⟨t1, t2, _, h2, rfl⟩ := Env.get_join hp
  exact (h p t2 h2).le hwf (Ty.le_append_right hwf _ _)

/-- `Γ.set p t` holds where `p` holds `t` and the rest of `Γ` does. -/
theorem Sat.set_of {Γ : Env} {p : Path} {t : Ty}
    (h : ∀ q u, Γ.get q = some u → q ≠ p → PathHolds P c fr s q u)
    (hp : PathHolds P c fr s p t) : Sat P c (Γ.set p t) fr s := by
  intro q u hq
  rw [Env.get_set] at hq
  split at hq
  · subst_vars; simp at hq; subst hq; exact hp
  · rename_i hne; exact h q u hq hne

theorem Sat.set {Γ : Env} {p : Path} {t : Ty} (h : Sat P c Γ fr s)
    (hp : PathHolds P c fr s p t) : Sat P c (Γ.set p t) fr s := by
  intro q u hq
  rw [Env.get_set] at hq
  split at hq
  · subst_vars; simp at hq; subst hq; exact hp
  · exact h q u hq

theorem Sat.reset {Γ : Env} {xs : List String} (h : Sat P c Γ fr s) :
    Sat P c (c.reset Γ xs) fr s := by
  intro p t hp
  cases p with
  | field f => rw [Ctx.reset_get_field] at hp; exact h _ _ hp
  | «local» x =>
    obtain ⟨u, hu, hx⟩ := Ctx.reset_get_local hp
    obtain ⟨l, v, d, h1, h2, h3, _, h5⟩ := h _ _ hu
    split at hx
    · rw [h3] at hx; cases hx; exact ⟨l, v, _, h1, h2, h3, h5, h5⟩
    · subst hx; exact h _ _ hu

theorem Env.implies_get {ct : ClassTable} {Γ Δ : Env} (hi : Γ.implies ct Δ = true) {p : Path}
    {t : Ty} (hp : Δ.get p = some t) : ∃ u, Γ.get p = some u ∧ u.le ct t = true := by
  unfold Env.implies at hi
  induction Δ with
  | nil => simp [Env.get] at hp
  | cons e Δ ih =>
    obtain ⟨q, w⟩ := e
    rw [List.all_cons, Bool.and_eq_true] at hi
    rw [Env.get_cons] at hp
    by_cases hq : q = p
    · subst hq; rw [if_pos rfl] at hp; cases hp
      have := hi.1
      simp only at this
      split at this
      · rename_i u hu; exact ⟨u, hu, this⟩
      · cases this
    · rw [if_neg hq] at hp; exact ih hi.2 hp

theorem Sat.implies (hwf : WfClasses P.classes) {Γ Δ : Env} (h : Sat P c Γ fr s)
    (hi : Γ.implies P.classes Δ = true) : Sat P c Δ fr s := by
  intro p t hp
  obtain ⟨u, hu, hle⟩ := Env.implies_get hi hp
  exact (h p u hu).le hwf hle

end

end QuarzCore
