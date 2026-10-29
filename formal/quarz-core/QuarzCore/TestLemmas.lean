/-
What the tests (`nil?`, `is_a?`, `==` against nil, true, false) tell of
a value: its type narrowed as design §2.1's table says.
-/

import QuarzCore.Lemmas

set_option linter.deprecated false

namespace QuarzCore

open ClassTable

variable {P : Program}

/-- `is_a?` false: of the atoms not below the class. -/
theorem hasTy_isAFalse (hwf : WfClasses P.classes) {s : Store} {v : Value} {t : Ty} {a u : Atom}
    (hv : s.hasTy P v t) (hu : s.typeOf v = some u) (hua : u.le P.classes a = false) :
    s.hasTy P v (isAFalse P.classes t a) := by
  rw [hasTy_iff] at hv ⊢
  obtain ⟨u', hu', b, hb, hub⟩ := hv
  rw [hu] at hu'; cases hu'
  refine ⟨u, hu, b, List.mem_filter.mpr ⟨hb, ?_⟩, hub⟩
  cases hba : b.le P.classes a
  · rfl
  · have := Atom.le_trans hwf hub hba; simp_all

/-! ### The tests, through a substitution of the enclosing class's parameters

A value's type is closed; the type the body names may have a parameter
in it, which the frame's arguments stand for. A test's narrowing keeps
the parameters (a parameter's value may be `nil` or `false`, or of the
class tested), so what holds of the value's atom holds through the
substitution. -/

/-- A value atom below an atom of `b` substituted is below `b` (a class
with arguments substituted is the root only if `b` is). -/
theorem Atom.le_subst_value {ct : ClassTable} {σ : List Ty} {a b b' : Atom}
    (ha : a.isParam = false ∧ a.classOf = none) (hb' : b' ∈ Atom.subst σ b)
    (hab : a.le ct b' = true) (hbp : b.isParam = false) : a.le ct b = true := by
  cases b with
  | param i => simp [Atom.isParam] at hbp
  | cls c args =>
    simp at hb'; subst hb'
    cases a <;> simp [Atom.isParam, Atom.classOf] at ha <;> simp [Atom.le] at hab ⊢ <;>
      (obtain ⟨rfl, h⟩ := hab; exact ⟨rfl, by cases args <;> simp_all [Ty.substArgs]⟩)
  | _ => simp at hb'; subst hb'; exact hab

/-- A truthy value of `u` (through `σ`) is of `u` without `nil`. -/
theorem hasTy_truthy_subst {s : Store} {v : Value} {σ : List Ty} {u : Ty}
    (h : s.hasTy P v (u.subst σ)) (ht : v.truthy = true) :
    s.hasTy P v ((truthyTy u).subst σ) := by
  rw [hasTy_iff] at *
  obtain ⟨a, ha, b', hb', hab⟩ := h
  refine ⟨a, ha, b', ?_, hab⟩
  obtain ⟨b, hb, hbb'⟩ := Ty.mem_subst.mp hb'
  refine Ty.mem_subst.mpr ⟨b, ?_, hbb'⟩
  unfold truthyTy Ty.remove
  refine List.mem_filter.mpr ⟨hb, ?_⟩
  -- `b` is not `nil`: `nil` substituted is `nil`, which only `nil` is below.
  cases b <;> simp
  simp at hbb'; subst hbb'
  cases a <;> simp_all [Atom.le]
  cases v with
  | obj l => obtain ⟨_, _, _, h⟩ := typeOf_obj ha; cases h
  | _ => simp_all [Store.typeOf, Value.truthy]

/-- A falsy value of `u` (through `σ`): `nil` or `false`, which `u` holds,
or of a parameter of `u`. -/
theorem hasTy_falsy_subst (hwf : WfClasses P.classes) {s : Store} {v : Value} {σ : List Ty} {u : Ty}
    (h : s.hasTy P v (u.subst σ)) (hf : v.truthy = false) :
    s.hasTy P v ((falsyTy P.classes u).subst σ) := by
  have hv : v = .nil ∨ v = .bool false := by
    cases v with
    | nil => exact .inl rfl
    | bool b => cases b <;> simp_all [Value.truthy]
    | _ => simp [Value.truthy] at hf
  rw [hasTy_iff] at h ⊢
  obtain ⟨a, ha, b', hb', hab⟩ := h
  obtain ⟨b, hb, hbb'⟩ := Ty.mem_subst.mp hb'
  cases b with
  | param i =>
    -- Of the parameter's argument: the parameter stays.
    exact ⟨a, ha, b', Ty.mem_subst.mpr ⟨.param i,
      List.mem_append_left _ (List.mem_filter.mpr ⟨hb, rfl⟩), hbb'⟩, hab⟩
  | _ =>
    -- `nil` or `false` itself, which `u` holds.
    rcases hv with rfl | rfl
    · simp [Store.typeOf] at ha; subst ha
      refine ⟨.nil, rfl, .nil, Ty.mem_subst.mpr ⟨.nil, List.mem_append_right _ ?_, by simp⟩,
        by simp [Atom.le]⟩
      refine List.mem_filter.mpr ⟨by simp, ?_⟩
      simp [Ty.le]
      exact ⟨_, hb, Atom.le_subst_value (by simp [Atom.isParam, Atom.classOf]) hbb' hab (by simp [Atom.isParam])⟩
    · simp [Store.typeOf] at ha; subst ha
      refine ⟨.bool, rfl, .bool, Ty.mem_subst.mpr ⟨.bool, List.mem_append_right _ ?_, by simp⟩,
        by simp [Atom.le]⟩
      refine List.mem_filter.mpr ⟨by simp, ?_⟩
      simp [Ty.le]
      exact ⟨_, hb, Atom.le_subst_value (by simp [Atom.isParam, Atom.classOf]) hbb' hab (by simp [Atom.isParam])⟩

/-- `nil` of `u` (through `σ`): `u` holds `nil` or has a parameter, so
`nilTy` is `nil`. -/
theorem hasTy_nilTy_subst {s : Store} {σ : List Ty} {u : Ty} (h : s.hasTy P .nil (u.subst σ)) :
    s.hasTy P .nil ((nilTy P.classes u).subst σ) := by
  rw [hasTy_iff] at h
  obtain ⟨a, ha, b', hb', hab⟩ := h
  simp [Store.typeOf] at ha; subst ha
  obtain ⟨b, hb, hbb'⟩ := Ty.mem_subst.mp hb'
  have hcond : (u.any Atom.isParam || Ty.le P.classes [.nil] u) = true := by
    simp only [Bool.or_eq_true, List.any_eq_true]
    cases b with
    | param i => exact Or.inl ⟨_, hb, rfl⟩
    | _ =>
      right
      simp [Ty.le]
      exact ⟨_, hb, Atom.le_subst_value (by simp [Atom.isParam, Atom.classOf]) hbb' hab (by simp [Atom.isParam])⟩
  simp only [nilTy, hcond, if_true]
  rw [Ty.subst_closed_id σ [.nil] rfl]
  exact hasTy_iff.mpr ⟨.nil, rfl, .nil, List.mem_singleton.mpr rfl, by simp [Atom.le]⟩

/-- What `verifiable` says of an atom of the class or a subclass: the
same arguments. -/
theorem verifiable_sub {ct : ClassTable} {t : Ty} {d : Nat} {args : List Ty}
    (hver : verifiable ct t (.cls d args) = true) {e : Nat} {bs : List Ty}
    (hb : Atom.cls e bs ∈ t) : (ct.subclass e d = true → ∃ as', ct.ancestorArgs e bs d = some as' ∧
        (argsLeWith (Atom.le ct) (ct.variances d) as' args = true ∨ objectArgs ct d args = true)) ∧
      (ct.subclass e d = false → objectArgs ct d args = true ∨ ct.subclass d e = false) := by
  simp only [verifiable, List.all_eq_true] at hver
  have := hver _ hb
  constructor
  · intro hed; simp only [hed, if_true] at this
    split at this
    · rename_i as' h'; exact ⟨as', h', by simpa using this⟩
    · simp at this
  · intro hed
    simp only [hed, Bool.false_eq_true, if_false, Bool.or_eq_true,
      Bool.not_eq_true'] at this
    exact this

/-- No parameter in a type a class test with arguments is verifiable on. -/
theorem verifiable_no_param {ct : ClassTable} {t : Ty} {d : Nat} {args : List Ty}
    (hver : verifiable ct t (.cls d args) = true) (hne : objectArgs ct d args = false) {i : Nat}
    (hb : Atom.param i ∈ t) : False := by
  simp only [verifiable, List.all_eq_true] at hver
  have := hver _ hb
  simp only at this
  rw [hne] at this; cases this

/-- `Object` arguments for covariant parameters are above any. -/
theorem objectArgs_le {ct : ClassTable} (hwf : WfClasses ct) : ∀ {vs : List Variance} {args bs : List Ty},
    args.length = vs.length →
    ((args.zip vs).all fun (t, v) => t == [.cls 0 []] && v == .co) = true →
    bs.length = vs.length → argsLeWith (Atom.le ct) vs bs args = true
  | [], [], [], _, _, _ => by simp [argsLeWith]
  | v :: vs, t :: args, b :: bs, hl, ha, hb => by
    simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true, beq_iff_eq] at ha
    obtain ⟨⟨rfl, rfl⟩, ha⟩ := ha
    simp only [argsLeWith, List.headD_cons, List.tail_cons, Variance.leWith, Bool.and_eq_true,
      Ty.leWith_le]
    exact ⟨Ty.le_top hwf b, objectArgs_le hwf (by simpa using hl) ha (by simpa using hb)⟩
  | [], _ :: _, _, hl, _, _ => by simp at hl
  | [], [], _ :: _, _, _, hb => by simp at hb
  | _ :: _, [], _, hl, _, _ => by simp at hl
  | _ :: _, _ :: _, [], _, _, hb => by simp at hb

/-- A value's class and its arguments: the object's. -/
theorem typeOf_cls {s : Store} {v : Value} {cu : Nat} {asu : List Ty}
    (hu : s.typeOf v = some (.cls cu asu)) : ∃ l o, v = .obj l ∧ s.objs[l]? = some o ∧ o.cls = cu ∧ o.args = asu := by
  cases v with
  | obj l => obtain ⟨o, ho, _, h⟩ := typeOf_obj hu; cases h; exact ⟨l, o, rfl, ho, rfl, rfl⟩
  | _ => simp [Store.typeOf] at hu

/-- The run-time class test answers as `≤` on the value's atom does, for a
class test the checker allowed (`verifiable`): the arguments follow from
the static type. -/
theorem isA_class_test (hwf : WfClasses P.classes) {Λ : List Ty} {s : Store} (hw : WfStore P Λ s)
    {v : Value} {σ : List Ty} {t : Ty} {cu d : Nat} {asu args : List Ty}
    (hv : s.hasTy P v (t.subst σ)) (hu : s.typeOf v = some (.cls cu asu))
    (hver : ((Atom.cls d args).closed && (Atom.cls d args).wf P.classes &&
      verifiable P.classes t (.cls d args)) = true) :
    P.classes.subclass cu d = (Atom.cls cu asu).le P.classes (.cls d args) := by
  simp only [Bool.and_eq_true] at hver
  obtain ⟨⟨hclosed, hwfa⟩, hver⟩ := hver
  obtain ⟨l, o, rfl, ho, rfl, rfl⟩ := typeOf_cls hu
  obtain ⟨hcls, hoclosed, holen, _⟩ := hw.objs l o ho
  have hd : d < P.classes.length := by
    simp only [Atom.wf] at hwfa
    cases h : P.classes[d]? with
    | none => rw [h] at hwfa; cases hwfa
    | some _ => exact (List.getElem?_eq_some_iff.mp h).1
  have hdparams : args.length = (((P.classes[d]?).map (·.params)).getD []).length := by
    simp only [Atom.wf] at hwfa
    cases h : P.classes[d]? with
    | none => rw [h] at hwfa; cases hwfa
    | some k => rw [h] at hwfa; simp at hwfa; simp [h, hwfa]
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hsub
    rw [Atom.le_cls_iff hwf]
    rw [ClassTable.subclass_iff] at hsub
    obtain ⟨bs, hbs⟩ := ClassTable.ancestorArgs_of_mem hwf o.cls o.args d hsub
    cases hobj : objectArgs P.classes d args
    case true =>
      -- Arguments every instance has.
      right
      simp only [objectArgs, Bool.and_eq_true, beq_iff_eq] at hobj
      refine ⟨bs, hbs, objectArgs_le hwf hobj.1 hobj.2 ?_⟩
      exact ClassTable.ancestorArgs_length hwf o.cls o.args d bs hbs holen
    case false =>
      right
      rw [hasTy_iff] at hv
      obtain ⟨u', hu', b', hb', hab⟩ := hv
      rw [hu] at hu'; cases hu'
      obtain ⟨b, hb, hbb'⟩ := Ty.mem_subst.mp hb'
      cases b with
      | param i => exact (verifiable_no_param hver hobj hb).elim
      | cls e bs0 =>
        simp at hbb'; subst hbb'
        rw [Atom.le_cls_iff hwf] at hab
        obtain ⟨h1, h2⟩ := verifiable_sub hver hb
        rcases hab with ⟨rfl, hbs0⟩ | ⟨x, hx, hab⟩
        · -- `b` is `Object`: the test's class is below it, not allowed.
          have hbs' : bs0 = [] := by cases bs0 <;> simp_all [Ty.substArgs]
          subst hbs'
          by_cases hd0 : d = 0
          · subst hd0
            -- The root has no parameters: `args = []`, which every
            -- instance has.
            exfalso
            cases h0 : P.classes[0]? with
            | none => simp only [List.getElem?_eq_none_iff] at h0; omega
            | some k =>
              have hr := hwf.rootParams k h0
              have hw0 := hwfa
              simp only [Atom.wf, h0, hr, List.length_nil, beq_iff_eq] at hw0
              have := List.eq_nil_of_length_eq_zero hw0; subst this
              simp [objectArgs, ClassTable.variances, h0, hr] at hobj
          · have hs0 : P.classes.subclass 0 d = false := by
              rw [Bool.eq_false_iff, ne_eq, ClassTable.subclass_iff]
              intro hmem; rw [ClassTable.ancestors_zero hwf] at hmem; simp at hmem; exact hd0 hmem
            rcases h2 hs0 with this | this
            · rw [hobj] at this; cases this
            rw [Bool.eq_false_iff, ne_eq, ClassTable.subclass_iff] at this
            exact absurd (ClassTable.root_mem_ancestors hwf d hd) this
        · have he : e ∈ P.classes.ancestors o.cls := ClassTable.ancestorArgs_mem hwf _ _ _ _ hx
          cases hed : P.classes.subclass e d with
          | true =>
            -- The static atom's chain gives arguments below the tested
            -- ones; the object's are below the static atom's, and the
            -- chain keeps that up to `d`.
            obtain ⟨as', has', hle | hobj'⟩ := h1 hed
            · have h3 := ClassTable.ancestorArgs_subst P.classes σ has'
              have hclosed' : Ty.closedArgs args = true := by simpa [Atom.closed] using hclosed
              have hle' := argsLeWith_subst hwf σ hle
              rw [Ty.substArgs_closed_id σ args hclosed'] at hle'
              have hde : d ∈ P.classes.ancestors e := ClassTable.ancestorArgs_mem hwf _ _ _ _ h3
              obtain ⟨y, hy⟩ := ClassTable.ancestorArgs_of_mem hwf e x d hde
              exact ⟨y, ClassTable.ancestorArgs_trans hwf hx hy,
                argsLeWith_le_trans hwf (ClassTable.chain_mono hwf hy h3 hab) hle'⟩
            · rw [hobj] at hobj'; cases hobj'
          | false =>
            rcases h2 hed with h3 | h3
            · rw [hobj] at h3; cases h3
            rw [Bool.eq_false_iff, ne_eq, ClassTable.subclass_iff] at h3 hed
            rcases ClassTable.ancestors_total hwf o.cls e d he hsub with h | h
            · exact absurd h h3
            · exact absurd h hed
      | _ => simp at hbb'; subst hbb'; simp [Atom.le] at hab
  · intro hle
    rw [Atom.le_cls_iff hwf] at hle
    rcases hle with ⟨rfl, _⟩ | ⟨x, hx, _⟩
    · exact (ClassTable.subclass_iff _ _).mpr (ClassTable.root_mem_ancestors hwf _ hcls)
    · exact (ClassTable.subclass_iff _ _).mpr (ClassTable.ancestorArgs_mem hwf _ _ _ _ hx)

/-- `is_a?` true (through `σ`): the value is of an atom of `t` below the
class, or of the class itself (which `t` having an atom above it, one of
a related class, or a parameter keeps in). -/
theorem hasTy_isATrue_subst (hwf : WfClasses P.classes) {s : Store} {v : Value} {σ : List Ty}
    {t : Ty} {a u : Atom} (hclosed : a.closed = true)
    (hv : s.hasTy P v (t.subst σ)) (hu : s.typeOf v = some u) (hua : u.le P.classes a = true) :
    s.hasTy P v ((isATrue P.classes t a).subst σ) := by
  have ha : Atom.subst σ a = [a] := Atom.subst_closed_id σ a hclosed
  rw [hasTy_iff] at hv ⊢
  obtain ⟨u', hu', b', hb', hub⟩ := hv
  rw [hu] at hu'; cases hu'
  refine ⟨u, hu, ?_⟩
  obtain ⟨b, hb, hbb'⟩ := Ty.mem_subst.mp hb'
  -- `a` itself is in where `t` has an atom above it, of a related class,
  -- or a parameter.
  have hain : (∃ c ∈ t, (a.le P.classes c && a != c) || a.classRelated P.classes c || c.isParam) →
      a ∈ Ty.subst σ (isATrue P.classes t a) := fun ⟨c, hc, hac⟩ => by
    refine Ty.mem_subst.mpr ⟨a, List.mem_append_right _ ?_, by rw [ha]; simp⟩
    simp only [List.any_eq_true]
    rw [if_pos ⟨c, hc, hac⟩]; simp
  by_cases hba : b.le P.classes a = true
  · exact ⟨b', Ty.mem_subst.mpr ⟨b, List.mem_append_left _ (List.mem_filter.mpr ⟨hb, hba⟩), hbb'⟩, hub⟩
  refine ⟨a, hain ⟨b, hb, ?_⟩, hua⟩
  simp only [Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq]
  cases b with
  | param i => exact Or.inr (by simp [Atom.isParam])
  | cls e bs =>
    simp at hbb'; subst hbb'
    left
    cases a with
    | cls d args =>
      cases u
      all_goals try
        (simp only [Atom.le, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at hua
         obtain ⟨rfl, rfl⟩ := hua
         exact absurd (Atom.le_object hwf e bs) hba)
      rename_i cu asu
      rw [Atom.le_cls_iff hwf] at hub hua
      rcases hua with ⟨rfl, rfl⟩ | ⟨_, hua, _⟩
      · exact absurd (Atom.le_object hwf e bs) hba
      rcases hub with ⟨rfl, hbs⟩ | ⟨_, hub, _⟩
      · -- `b` is `Object`: `a` is below it, and not it.
        have hbs' : bs = [] := by cases bs <;> simp_all [Ty.substArgs]
        subst hbs'
        left
        refine ⟨Atom.le_object hwf d args, ?_⟩
        rintro h; cases h
        exact hba (Atom.le_refl hwf _)
      -- Both classes are above the object's: related.
      right
      have he := ClassTable.ancestorArgs_mem hwf _ _ _ _ hub
      have hd := ClassTable.ancestorArgs_mem hwf _ _ _ _ hua
      simp only [Atom.classRelated, Atom.classOf, Bool.or_eq_true, ClassTable.subclass_iff]
      rcases ClassTable.ancestors_total hwf cu e d he hd with h | h
      · exact Or.inl h
      · exact Or.inr h
    | _ =>
      -- A value atom: the value's atom is it, below a class only if that
      -- class is the root; `a` is below the root and not it.
      cases u <;> (try simp [Atom.le] at hua) <;>
        simp only [Atom.le, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at hub <;>
        (obtain ⟨rfl, hbs⟩ := hub
         have hbs' : bs = [] := by cases bs <;> simp_all [Ty.substArgs]
         subst hbs'
         exact Or.inl ⟨by simp [Atom.le], by simp⟩)
  | _ =>
    -- A value atom of `t`: the value is it, so it is below `a`.
    simp at hbb'; subst hbb'
    exfalso
    cases u <;> simp_all [Atom.le]

/-- `is_a?` false (through `σ`): of the atoms of `t` not below the class. -/
theorem hasTy_isAFalse_subst (hwf : WfClasses P.classes) {s : Store} {v : Value} {σ : List Ty} {t : Ty} {a u : Atom}
    (hclosed : a.closed = true)
    (hv : s.hasTy P v (t.subst σ)) (hu : s.typeOf v = some u) (hua : u.le P.classes a = false) :
    s.hasTy P v ((isAFalse P.classes t a).subst σ) := by
  rw [hasTy_iff] at hv ⊢
  obtain ⟨u', hu', b', hb', hub⟩ := hv
  rw [hu] at hu'; cases hu'
  obtain ⟨b, hb, hbb'⟩ := Ty.mem_subst.mp hb'
  refine ⟨u, hu, b', Ty.mem_subst.mpr ⟨b, List.mem_filter.mpr ⟨hb, ?_⟩, hbb'⟩, hub⟩
  cases hba : b.le P.classes a
  · rfl
  · -- `b ≤ a` carries to `b'` (`a` closed), so the value would be of `a`.
    exfalso
    have := Ty.le_iff.mp (Atom.subst_le hwf σ hba) b' hbb'
    obtain ⟨a', ha', hba'⟩ := this
    rw [Atom.subst_closed_id σ a hclosed] at ha'
    simp at ha'; subst ha'
    have := Atom.le_trans hwf hub hba'
    rw [hua] at this; cases this

/-- A value other than `nil`, of `u` (through `σ`): of `u` without `nil`. -/
theorem hasTy_remove_nil_subst {s : Store} {v : Value} {σ : List Ty} {u : Ty}
    (h : s.hasTy P v (u.subst σ)) (hne : v ≠ .nil) : s.hasTy P v ((u.remove .nil).subst σ) := by
  rw [hasTy_iff] at *
  obtain ⟨a, ha, b', hb', hab⟩ := h
  obtain ⟨b, hb, hbb'⟩ := Ty.mem_subst.mp hb'
  refine ⟨a, ha, b', Ty.mem_subst.mpr ⟨b, List.mem_filter.mpr ⟨hb, ?_⟩, hbb'⟩, hab⟩
  cases b <;> simp
  simp at hbb'; subst hbb'
  cases a <;> simp_all [Atom.le]
  cases v with
  | obj l => obtain ⟨_, _, _, h⟩ := typeOf_obj ha; cases h
  | _ => simp_all [Store.typeOf]

/-- A value other than `nil`: of its type without `nil`. -/
theorem hasTy_remove_nil {s : Store} {v : Value} {t : Ty} (hv : s.hasTy P v t) (hne : v ≠ .nil) :
    s.hasTy P v (t.remove .nil) := by
  rw [hasTy_iff] at *
  obtain ⟨a, ha, b, hb, hab⟩ := hv
  refine ⟨a, ha, b, List.mem_filter.mpr ⟨hb, ?_⟩, hab⟩
  cases b <;> simp
  cases a <;> simp_all [Atom.le]
  cases v with
  | obj l => obtain ⟨_, _, _, h⟩ := typeOf_obj ha; cases h
  | _ => simp_all [Store.typeOf]

/-- A type of final atoms (the value classes) is closed: it substitutes
to itself. -/
theorem Ty.closed_of_allFinal {t : Ty} (h : t.allFinal = true) : t.closed = true := by
  induction t with
  | nil => rfl
  | cons a t ih =>
    simp only [Ty.allFinal, List.all_cons, Bool.and_eq_true] at h
    simp only [Ty.closed, Bool.and_eq_true]
    refine ⟨?_, ih h.2⟩
    cases a <;> simp_all [Atom.final, Atom.closed]

theorem Ty.subst_of_allFinal (σ : List Ty) {t : Ty} (h : t.allFinal = true) : Ty.subst σ t = t :=
  Ty.subst_closed_id σ t (Ty.closed_of_allFinal h)

theorem Ty.allFinal_keep {t : Ty} (h : t.allFinal = true) (as : List Atom) : (t.keep as).allFinal = true := by
  simp only [Ty.allFinal, Ty.keep, List.all_eq_true] at h ⊢
  exact fun a ha => h a (List.mem_filter.mp ha).1

theorem Ty.allFinal_remove {t : Ty} (h : t.allFinal = true) (a : Atom) : (t.remove a).allFinal = true := by
  simp only [Ty.allFinal, Ty.remove, List.all_eq_true] at h ⊢
  exact fun b hb => h b (List.mem_filter.mp hb).1

/-- A value of a type of final atoms is no object. -/
theorem not_obj_of_final {s : Store} {v : Value} {t : Ty} (hv : s.hasTy P v t)
    (hfin : t.allFinal = true) : ∀ l, v ≠ .obj l := by
  rintro l rfl
  rw [hasTy_iff] at hv
  obtain ⟨a, ha, b, hb, hab⟩ := hv
  obtain ⟨o, _, _, rfl⟩ := typeOf_obj ha
  have := List.all_eq_true.mp hfin b hb
  cases b <;> simp_all [Atom.final, Atom.le]

/-- A value of final atoms equal to `w` (no object): of `w`'s atoms. -/
theorem hasTy_keep {s : Store} {v : Value} {t : Ty} {a : Atom} (hv : s.hasTy P v t)
    (hfin : t.allFinal = true) (ha : s.typeOf v = some a) : s.hasTy P v (t.keep [a]) := by
  rw [hasTy_iff] at *
  obtain ⟨a', ha', b, hb, hab⟩ := hv
  rw [ha] at ha'; cases ha'
  have hfb := List.all_eq_true.mp hfin b hb
  -- Below a final atom is only itself.
  have hba : b = a := by
    cases a <;> cases b <;> simp_all [Atom.final, Atom.le]
  subst hba
  exact ⟨_, ha, _, List.mem_filter.mpr ⟨hb, by simp [Ty.keep]⟩, hab⟩

end QuarzCore
