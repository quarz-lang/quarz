/-
What the tests (`nil?`, `is_a?`, `==` against nil, true, false) tell of
a value: its type narrowed as design §2.1's table says.
-/

import QuarzCore.Lemmas

set_option linter.deprecated false

namespace QuarzCore

open ClassTable

variable {P : Program}

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
    (hab : a.le ct [] b' = true) (hbp : b.isParam = false) : a.le ct [] b = true := by
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
  | proc i => obtain ⟨_, _, h⟩ := typeOf_proc ha; cases h
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
  have hcond : (u.any Atom.isParam || Ty.le P.classes [] [.nil] u) = true := by
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
        (argsLeWith (Atom.le ct []) (ct.variances d) as' args = true ∨ objectArgs ct d args = true)) ∧
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
    bs.length = vs.length → argsLeWith (Atom.le ct []) vs bs args = true
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

/-- The class `procClass` finds: of kind `proc`, with `n + 1` parameters. -/
theorem procClass_kind {n k : Nat} (h : P.procClass n = some k) :
    P.classes.kindOf k = .proc ∧ (P.classes[k]?).map (·.params.length) = some (n + 1) := by
  simp only [Program.procClass] at h
  obtain ⟨hk, hp, _⟩ := List.findIdx?_eq_some_iff_getElem.mp h
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  refine ⟨?_, ?_⟩
  · simp [ClassTable.kindOf, List.getElem?_eq_getElem hk, hp.1]
  · simp [List.getElem?_eq_getElem hk, hp.2]

/-- A procedures' class is right below `Object`. -/
theorem proc_ancestors (hwf : WfClasses P.classes) {k : Nat} (hk : P.classes.kindOf k = .proc) :
    P.classes.ancestors k = [k, 0] := by
  cases hck : P.classes[k]? with
  | none => simp [ClassTable.kindOf, hck] at hk
  | some cl =>
    have hkind : cl.kind = .proc := by simpa [ClassTable.kindOf, hck] using hk
    obtain ⟨hs, _⟩ := hwf.procShape k cl hck hkind
    rw [ClassTable.ancestors_eq hwf k]
    simp only [ClassTable.superOf, hck, Option.bind_some, hs]
    rw [ClassTable.ancestors_eq hwf 0]
    cases h0 : P.classes[0]? with
    | none => exact absurd (List.getElem?_eq_none_iff.mp h0) (by have := hwf.nonempty; omega)
    | some k0 => simp [ClassTable.superOf, h0, hwf.root k0 h0]

/-- A built-in generic class is right below `Object`. -/
theorem builtin_ancestors (hwf : WfClasses P.classes) {k : Nat} (hk : P.classes.kindOf k = .builtin) :
    P.classes.ancestors k = [k, 0] := by
  cases hck : P.classes[k]? with
  | none => simp [ClassTable.kindOf, hck] at hk
  | some cl =>
    have hkind : cl.kind = .builtin := by simpa [ClassTable.kindOf, hck] using hk
    obtain ⟨hs, _⟩ := hwf.builtinShape k cl hck hkind
    rw [ClassTable.ancestors_eq hwf k]
    simp only [ClassTable.superOf, hck, Option.bind_some, hs]
    rw [ClassTable.ancestors_eq hwf 0]
    cases h0 : P.classes[0]? with
    | none => exact absurd (List.getElem?_eq_none_iff.mp h0) (by have := hwf.nonempty; omega)
    | some k0 => simp [ClassTable.superOf, h0, hwf.root k0 h0]

/-- A built-in value's type: of a built-in generic class. -/
theorem typeOf_builtin_kind {Λ : List Ty} {s : Store} (hw : WfStore P Λ s) {i : Nat} {u : Atom}
    (hu : s.typeOf (.builtin i) = some u) : ∃ k as, u = .cls k as ∧ P.classes.kindOf k = .builtin := by
  simp only [Store.typeOf, Option.map_eq_some_iff] at hu
  obtain ⟨⟨k, as⟩, he, rfl⟩ := hu
  exact ⟨k, as, rfl, (hw.builts i k as he).2.1⟩

/-- A procedure's type: of a procedures' class. -/
theorem typeOf_proc_kind {Λ : List Ty} {s : Store} (hw : WfStore P Λ s) {i : Nat} {u : Atom}
    (hu : s.typeOf (.proc i) = some u) : ∃ k as, u = .cls k as ∧ P.classes.kindOf k = .proc := by
  simp only [Store.typeOf, Option.bind_eq_some_iff] at hu
  obtain ⟨p, hp, h⟩ := hu
  obtain ⟨c, Γ, ps, own, ret, body, vars, me, sa, k, ob, hc, rfl, _, _, hk, _⟩ := hw.procs i p hp
  simp only at h
  cases h
  rw [hc] at hk
  exact ⟨_, _, rfl, (procClass_kind hk).1⟩

/-- A value of a class atom: the class is one, its arguments closed and as
many as its parameters (an object's, or a procedure's: `ProcN`). -/
theorem typeOf_cls_wf {Λ : List Ty} {s : Store} (hw : WfStore P Λ s) {v : Value} {cu : Nat}
    {asu : List Ty} (hu : s.typeOf v = some (.cls cu asu)) :
    cu < P.classes.length ∧ Ty.closedArgs asu = true ∧
      asu.length = (((P.classes[cu]?).map (·.params)).getD []).length := by
  cases v with
  | obj l =>
    obtain ⟨o, ho, _, h⟩ := typeOf_obj hu
    cases h
    obtain ⟨hcls, hcl, hlen, _⟩ := hw.objs l o ho
    exact ⟨hcls, hcl, hlen⟩
  | proc i =>
    simp only [Store.typeOf, Option.bind_eq_some_iff] at hu
    obtain ⟨p, hp, h⟩ := hu
    obtain ⟨c, Γ, ps, own, ret, body, vars, me, sa, k, ob, hc, rfl, _, _, hk, hn, _, hcore, _⟩ :=
      hw.procs i p hp
    simp only at h
    cases h
    have hlt : cu < P.classes.length := by
      rw [hc] at hk
      simp only [Program.procClass] at hk
      exact (List.findIdx?_eq_some_iff_getElem.mp hk).1
    refine ⟨hlt, Ty.substArgs_closed _ hcore.closed _, ?_⟩
    rw [ClassTable.substArgs_length']
    cases hck : P.classes[cu]? with
    | none => rw [hck] at hn; cases hn
    | some cl => rw [hck] at hn; simp at hn ⊢; simp [hn]
  | builtin i =>
    simp only [Store.typeOf, Option.map_eq_some_iff] at hu
    obtain ⟨⟨k, as⟩, he, h⟩ := hu
    cases h
    obtain ⟨h1, _, h3, h4, _⟩ := hw.builts i _ _ he
    exact ⟨h1, h3, h4⟩
  | _ => simp [Store.typeOf] at hu

/-- The run-time class test answers as `≤` on the value's atom does, for a
class test the checker allowed (`verifiable`): the arguments follow from
the static type. -/
theorem isA_class_test (hwf : WfClasses P.classes) {Λ : List Ty} {s : Store} (hw : WfStore P Λ s)
    {v : Value} {σ : List Ty} {t : Ty} {cu d : Nat} {asu args : List Ty}
    (hv : s.hasTy P v (t.subst σ)) (hu : s.typeOf v = some (.cls cu asu))
    (hver : ((Atom.cls d args).closed && (Atom.cls d args).wf P.classes &&
      verifiable P.classes t (.cls d args)) = true) :
    P.classes.subclass cu d = (Atom.cls cu asu).le P.classes [] (.cls d args) := by
  simp only [Bool.and_eq_true] at hver
  obtain ⟨⟨hclosed, hwfa⟩, hver⟩ := hver
  obtain ⟨hcls, hoclosed, holen⟩ := typeOf_cls_wf hw hu
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
    obtain ⟨bs, hbs⟩ := ClassTable.ancestorArgs_of_mem hwf cu asu d hsub
    cases hobj : objectArgs P.classes d args
    case true =>
      -- Arguments every instance has.
      right
      simp only [objectArgs, Bool.and_eq_true, beq_iff_eq] at hobj
      refine ⟨bs, hbs, objectArgs_le hwf hobj.1 hobj.2 ?_⟩
      exact ClassTable.ancestorArgs_length hwf cu asu d bs hbs holen
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
        · have he : e ∈ P.classes.ancestors cu := ClassTable.ancestorArgs_mem hwf _ _ _ _ hx
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
            rcases ClassTable.ancestors_total hwf cu e d he hsub with h | h
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
theorem hasTy_isATrueOn_subst (hwf : WfClasses P.classes) {s : Store} {v : Value} {σ : List Ty}
    {t : Ty} {a u : Atom} (hclosed : a.closed = true)
    (hv : s.hasTy P v (t.subst σ)) (hu : s.typeOf v = some u) (hua : u.le P.classes [] a = true) :
    s.hasTy P v ((isATrueOn P.classes t a).subst σ) := by
  have ha : Atom.subst σ a = [a] := Atom.subst_closed_id σ a hclosed
  rw [hasTy_iff] at hv ⊢
  obtain ⟨u', hu', b', hb', hub⟩ := hv
  rw [hu] at hu'; cases hu'
  refine ⟨u, hu, ?_⟩
  obtain ⟨b, hb, hbb'⟩ := Ty.mem_subst.mp hb'
  -- `a` itself is in where `t` has an atom above it, of a related class,
  -- or a parameter.
  have hain : (∃ c ∈ t, (a.le P.classes [] c && a != c) ||
      (((a.classRelated P.classes c && !(c.closed && a.bare)) || c.isParam) &&
        !(c.le P.classes [] a))) →
      a ∈ Ty.subst σ (isATrueOn P.classes t a) := fun ⟨c, hc, hac⟩ => by
    refine Ty.mem_subst.mpr ⟨a, List.mem_append_right _ ?_, by rw [ha]; simp⟩
    simp only [List.any_eq_true]
    rw [if_pos ⟨c, hc, hac⟩]; simp
  by_cases hba : b.le P.classes [] a = true
  · exact ⟨b', Ty.mem_subst.mpr ⟨b, List.mem_append_left _ (List.mem_filter.mpr ⟨hb, hba⟩), hbb'⟩, hub⟩
  refine ⟨a, hain ⟨b, hb, ?_⟩, hua⟩
  simp only [Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq]
  cases b with
  | param i => exact Or.inr ⟨Or.inr (by simp [Atom.isParam]), by simpa using hba⟩
  | cls e bs =>
    simp at hbb'; subst hbb'
    -- The value's atom is no parameter.
    have hup : u.isParam = false := by cases u <;> simp_all [Atom.isParam]
    cases a with
    | cls d args =>
      cases u
      all_goals try (simp [Atom.isParam] at hup; done)
      all_goals try
        (simp only [Atom.le, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at hua
         obtain ⟨rfl, rfl⟩ := hua
         exact absurd (Atom.le_object hwf e bs) hba)
      rename_i cu asu
      rw [Atom.le_cls_iff hwf] at hub hua
      rcases hua with ⟨rfl, rfl⟩ | ⟨xa, hua, hxa⟩
      · exact absurd (Atom.le_object hwf e bs) hba
      rcases hub with ⟨rfl, hbs⟩ | ⟨yb, hub, hyb⟩
      · -- `b` is `Object`: `a` is below it, and not it.
        have hbs' : bs = [] := by cases bs <;> simp_all [Ty.substArgs]
        subst hbs'
        left
        refine ⟨Atom.le_object hwf d args, ?_⟩
        rintro h; cases h
        exact hba (Atom.le_refl hwf _)
      -- Both classes are above the object's: related.
      have he := ClassTable.ancestorArgs_mem hwf _ _ _ _ hub
      have hd := ClassTable.ancestorArgs_mem hwf _ _ _ _ hua
      have hrel : Atom.classRelated P.classes (.cls d args) (.cls e bs) = true := by
        simp only [Atom.classRelated, Atom.classOf, Bool.or_eq_true, ClassTable.subclass_iff]
        rcases ClassTable.ancestors_total hwf cu e d he hd with h | h
        · exact Or.inl h
        · exact Or.inr h
      by_cases hcb : ((Atom.cls e bs).closed && (Atom.cls d args).bare) = true
      · -- `b` closed and `a` without arguments: one is below the other.
        simp only [Bool.and_eq_true] at hcb
        obtain ⟨hcl, hbare⟩ := hcb
        have hargs : args = [] := by cases args <;> simp_all [Atom.bare]
        subst hargs
        have hsb : Ty.substArgs σ bs = bs := by
          have := Atom.subst_closed_id σ (.cls e bs) hcl
          simpa using this
        rw [hsb] at hyb
        have hxa' : xa = [] := by cases xa <;> simp_all [argsLeWith]
        subst hxa'
        rcases ClassTable.ancestors_total hwf cu e d he hd with h | h
        · -- `a`'s class below `b`'s: `a ≤ b`.
          have h1 := ClassTable.ancestorArgs_through hwf cu asu d [] e yb hua hub h
          left
          refine ⟨(Atom.le_cls_iff hwf d [] e bs).mpr (Or.inr ⟨yb, h1, hyb⟩), ?_⟩
          rintro hab; cases hab
          exact hba (Atom.le_refl hwf _)
        · -- `b`'s class below `a`'s: `b ≤ a`, which is not.
          have h1 := ClassTable.ancestorArgs_through hwf cu asu e yb d [] hub hua h
          exfalso; apply hba
          by_cases hed : e = d
          · subst hed
            rw [ClassTable.ancestorArgs_self hwf] at h1
            cases h1
            have : bs = [] := by cases bs <;> simp_all [argsLeWith]
            subst this
            exact Atom.le_refl hwf _
          · obtain ⟨z, hz, hzl⟩ := ClassTable.ancestorArgs_other P.classes bs h1 hed
            have : z = [] := List.eq_nil_of_length_eq_zero (by simpa using hzl)
            subst this
            exact (Atom.le_cls_iff hwf e bs d []).mpr (Or.inr ⟨[], hz, by simp [argsLeWith]⟩)
      · right
        refine ⟨Or.inl ⟨hrel, ?_⟩, by simpa using hba⟩
        cases h1 : (Atom.cls e bs).closed <;> cases h2 : (Atom.cls d args).bare <;> simp_all
    | _ =>
      -- A value atom: the value's atom is it, below a class only if that
      -- class is the root; `a` is below the root and not it.
      cases u <;> (try (simp [Atom.isParam] at hup; done)) <;> (try simp [Atom.le] at hua) <;>
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

/-- Only a `data` type or a variant itself is below it: nothing
subclasses it. -/
theorem ancestorArgs_data (hwf : WfClasses P.classes) {d : Nat}
    (hd : P.classes.kindOf d = .data ∨ P.classes.kindOf d = .variant) :
    ∀ (c : Nat) (as bs : List Ty), P.classes.ancestorArgs c as d = some bs → c = d := by
  intro c
  induction c using Nat.strongRecOn with
  | _ c ih =>
    intro as bs h
    rw [ClassTable.ancestorArgs_unfold hwf] at h
    by_cases hcd : (c == d) = true
    · simpa using hcd
    · rw [if_neg hcd] at h
      cases hk : P.classes[c]? with
      | none => simp [hk] at h
      | some k =>
        simp only [hk] at h
        cases hs : k.super with
        | none => simp [hs] at h
        | some p =>
          simp only [hs] at h
          have hpc : p < c := by
            have := ClassTable.superOf_lt hwf (show ClassTable.superOf P.classes c = some p by
              simp [ClassTable.superOf, hk, hs])
            exact this
          have := ih p hpc _ bs h
          subst this
          rcases hd with hd | hd
          · exact absurd hd (hwf.dataLeaf c k p hk hs)
          · exact absurd hd (hwf.variantLeaf c k p hk hs)

/-- One step of the chain: a class gives its superclass the arguments
substituted. -/
theorem ancestorArgs_super (hwf : WfClasses P.classes) {c p : Nat} {k : Class}
    (hk : P.classes[c]? = some k) (hs : k.super = some p) (as : List Ty) :
    P.classes.ancestorArgs c as p = some (Ty.substArgs as k.superArgs) := by
  rw [ClassTable.ancestorArgs_unfold hwf]
  have hpc : p < c := ClassTable.superOf_lt hwf (by simp [ClassTable.superOf, hk, hs])
  have : (c == p) = false := by simp; omega
  rw [if_neg (by simp [this])]
  simp only [hk, hs]
  exact ClassTable.ancestorArgs_self hwf p _

/-- A class strictly below `e` is below a class whose superclass is `e`. -/
theorem ancestorArgs_child (hwf : WfClasses P.classes) {e : Nat} :
    ∀ (c : Nat) (as bs : List Ty), P.classes.ancestorArgs c as e = some bs → c ≠ e →
      ∃ V k, P.classes[V]? = some k ∧ k.super = some e ∧ ∃ ys, P.classes.ancestorArgs c as V = some ys := by
  intro c
  induction c using Nat.strongRecOn with
  | _ c ih =>
    intro as bs h hce
    rw [ClassTable.ancestorArgs_unfold hwf] at h
    rw [if_neg (by simpa using hce)] at h
    cases hk : P.classes[c]? with
    | none => simp [hk] at h
    | some k =>
      simp only [hk] at h
      cases hs : k.super with
      | none => simp [hs] at h
      | some p =>
        simp only [hs] at h
        by_cases hpe : p = e
        · subst hpe
          exact ⟨c, k, hk, hs, as, ClassTable.ancestorArgs_self hwf c as⟩
        · have hpc : p < c := ClassTable.superOf_lt hwf (by simp [ClassTable.superOf, hk, hs])
          obtain ⟨V, kv, hkv, hsv, ys, hys⟩ := ih p hpc _ bs h hpe
          exact ⟨V, kv, hkv, hsv, ys, ClassTable.ancestorArgs_trans hwf (ancestorArgs_super hwf hk hs as) hys⟩

/-- A value below an `enum`: of one of its variants (no object is of the
`enum` itself, and its variants have no subclasses nor parameters). -/
theorem enum_variant (hwf : WfClasses P.classes) {Λ : List Ty} {s : Store} (hw : WfStore P Λ s)
    {v : Value} {u : Atom} (hu : s.typeOf v = some u) {E : Nat} (hE : P.classes.kindOf E = .enumC)
    (hle : u.le P.classes [] (.cls E []) = true) :
    ∃ V, V ∈ P.classes.variantsOf E ∧ u = .cls V [] := by
  have hE0 : E ≠ 0 := by
    rintro rfl
    cases h0 : P.classes[0]? with
    | none => simp [ClassTable.kindOf, h0] at hE
    | some k0 => simp [ClassTable.kindOf, h0, hwf.rootKind k0 h0] at hE
  cases v
  case obj l =>
    obtain ⟨o, ho, _, rfl⟩ := typeOf_obj hu
    rw [Atom.le_cls_iff hwf] at hle
    rcases hle with ⟨h0, _⟩ | ⟨x, hx, _⟩
    · exact absurd h0 hE0
    have hne : o.cls ≠ E := fun h => (hw.noEnum l o ho).1 (h ▸ hE)
    obtain ⟨V, kv, hkv, hsv, ys, hys⟩ := ancestorArgs_child hwf o.cls o.args x hx hne
    obtain ⟨hvar, hpar⟩ := hwf.enumChild V kv E hkv hsv hE
    have hkV : P.classes.kindOf V = .variant := by simp [ClassTable.kindOf, hkv, hvar]
    have hcV := ancestorArgs_data hwf (.inr hkV) _ _ _ hys
    obtain ⟨_, _, hlen, _⟩ := hw.objs l o ho
    rw [hcV] at hlen
    simp [hkv, hpar] at hlen
    refine ⟨V, ?_, by rw [hcV, hlen]⟩
    simp only [ClassTable.variantsOf, List.mem_filter, List.mem_range, beq_iff_eq]
    exact ⟨(List.getElem?_eq_some_iff.mp hkv).1, by simp [hkv, hsv]⟩
  case proc i =>
    -- A procedures' class is right below `Object`: not below an `enum`.
    obtain ⟨k, as, rfl, hkp⟩ := typeOf_proc_kind hw hu
    rw [Atom.le_cls_iff hwf] at hle
    rcases hle with ⟨h0, _⟩ | ⟨x, hx, _⟩
    · exact absurd h0 hE0
    have hmem := ClassTable.ancestorArgs_mem hwf _ _ _ _ hx
    rw [proc_ancestors hwf hkp] at hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl
    · rw [hkp] at hE; cases hE
    · exact absurd rfl hE0
  case builtin i =>
    obtain ⟨k, as, rfl, hkp⟩ := typeOf_builtin_kind hw hu
    rw [Atom.le_cls_iff hwf] at hle
    rcases hle with ⟨h0, _⟩ | ⟨x, hx, _⟩
    · exact absurd h0 hE0
    have hmem := ClassTable.ancestorArgs_mem hwf _ _ _ _ hx
    rw [builtin_ancestors hwf hkp] at hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl
    · rw [hkp] at hE; cases hE
    · exact absurd rfl hE0
  all_goals
    simp [Store.typeOf] at hu; subst hu
    simp [Atom.le, hE0] at hle

/-- A value of `t` is one of `t` with its enums expanded to their
variants (no object is of an `enum` itself). -/
theorem hasTy_expandEnums_subst (hwf : WfClasses P.classes) {Λ : List Ty} {s : Store}
    (hw : WfStore P Λ s) {v : Value} {σ : List Ty} {t : Ty} {u : Atom}
    (hv : s.hasTy P v (t.subst σ)) (hu : s.typeOf v = some u) :
    s.hasTy P v ((Ty.expandEnums P.classes t).subst σ) := by
  rw [hasTy_iff] at hv ⊢
  obtain ⟨u', hu', b', hb', hub⟩ := hv
  rw [hu] at hu'; cases hu'
  obtain ⟨b, hb, hbb'⟩ := Ty.mem_subst.mp hb'
  have hexp : ∃ b0 ∈ Ty.expandEnums P.classes t, ∃ b0' ∈ Atom.subst σ b0, u.le P.classes [] b0' = true := by
    cases b
    case cls E args =>
      cases args
      case nil =>
        by_cases hE : P.classes.kindOf E = .enumC
        · simp at hbb'; subst hbb'
          obtain ⟨V, hV, rfl⟩ := enum_variant hwf hw hu hE hub
          refine ⟨.cls V [], List.mem_flatMap.mpr ⟨_, hb, ?_⟩, .cls V [], by simp, Atom.le_refl hwf _⟩
          simp [hE]; exact hV
        · exact ⟨_, List.mem_flatMap.mpr ⟨_, hb, by simp [hE]⟩, b', hbb', hub⟩
      all_goals exact ⟨_, List.mem_flatMap.mpr ⟨_, hb, by simp⟩, b', hbb', hub⟩
    all_goals exact ⟨_, List.mem_flatMap.mpr ⟨_, hb, by simp⟩, b', hbb', hub⟩
  obtain ⟨b0, hb0, b0', hb0', hub0⟩ := hexp
  exact ⟨u, hu, b0', Ty.mem_subst.mpr ⟨b0, hb0, hb0'⟩, hub0⟩

theorem hasTy_isATrue_subst (hwf : WfClasses P.classes) {Λ : List Ty} {s : Store} (hw : WfStore P Λ s)
    {v : Value} {σ : List Ty} {t : Ty} {a u : Atom} (hclosed : a.closed = true)
    (hv : s.hasTy P v (t.subst σ)) (hu : s.typeOf v = some u) (hua : u.le P.classes [] a = true) :
    s.hasTy P v ((isATrue P.classes t a).subst σ) :=
  hasTy_isATrueOn_subst hwf hclosed (hasTy_expandEnums_subst hwf hw hv hu) hu hua

/-- `is_a?` false (through `σ`): of the atoms of `t` not below the class,
an `enum` as its variants. -/
theorem hasTy_isAFalse_subst (hwf : WfClasses P.classes) {Λ : List Ty} {s : Store} (hw : WfStore P Λ s)
    {v : Value} {σ : List Ty} {t : Ty} {a u : Atom}
    (hclosed : a.closed = true)
    (hv : s.hasTy P v (t.subst σ)) (hu : s.typeOf v = some u) (hua : u.le P.classes [] a = false) :
    s.hasTy P v ((isAFalse P.classes t a).subst σ) := by
  rw [hasTy_iff] at hv ⊢
  obtain ⟨u', hu', b', hb', hub⟩ := hv
  rw [hu] at hu'; cases hu'
  obtain ⟨b, hb, hbb'⟩ := Ty.mem_subst.mp hb'
  -- The atom standing for the value in `t` expanded: `b`, or the variant
  -- of the `enum` `b` the value is of.
  have hexp : ∃ b0 ∈ Ty.expandEnums P.classes t, ∃ b0' ∈ Atom.subst σ b0, u.le P.classes [] b0' = true := by
    cases b
    case cls E args =>
      cases args
      case nil =>
        by_cases hE : P.classes.kindOf E = .enumC
        · simp at hbb'; subst hbb'
          obtain ⟨V, hV, rfl⟩ := enum_variant hwf hw hu hE hub
          refine ⟨.cls V [], List.mem_flatMap.mpr ⟨_, hb, ?_⟩, .cls V [], by simp, Atom.le_refl hwf _⟩
          simp [hE]; exact hV
        · exact ⟨_, List.mem_flatMap.mpr ⟨_, hb, by simp [hE]⟩, b', hbb', hub⟩
      all_goals exact ⟨_, List.mem_flatMap.mpr ⟨_, hb, by simp⟩, b', hbb', hub⟩
    all_goals exact ⟨_, List.mem_flatMap.mpr ⟨_, hb, by simp⟩, b', hbb', hub⟩
  obtain ⟨b0, hb0, b0', hb0', hub0⟩ := hexp
  refine ⟨u, hu, b0', Ty.mem_subst.mpr ⟨b0, List.mem_filter.mpr ⟨hb0, ?_⟩, hb0'⟩, hub0⟩
  cases hba : b0.le P.classes [] a
  · rfl
  · -- `b0 ≤ a` carries to `b0'` (`a` closed), so the value would be of `a`.
    exfalso
    have := Ty.le_iff.mp (Atom.subst_le hwf σ hba) b0' hb0'
    obtain ⟨a', ha', hba'⟩ := this
    rw [Atom.subst_closed_id σ a hclosed] at ha'
    simp at ha'; subst ha'
    have := Atom.le_trans hwf hub0 hba'
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
  | proc i => obtain ⟨_, _, h⟩ := typeOf_proc ha; cases h
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
  | proc i => obtain ⟨_, _, h⟩ := typeOf_proc ha; cases h
  | _ => simp_all [Store.typeOf]

/-- A type of final atoms (the value classes, `data` types without
arguments) is closed: it substitutes to itself. -/
theorem Ty.closed_of_allFinalIn {t : Ty} (h : t.allFinalIn P = true) : t.closed = true := by
  induction t with
  | nil => rfl
  | cons a t ih =>
    simp only [Ty.allFinalIn, List.all_cons, Bool.and_eq_true] at h
    simp only [Ty.closed, Bool.and_eq_true]
    refine ⟨?_, ih h.2⟩
    have h1 := h.1
    cases a with
    | cls c args => cases args <;> simp_all [Atom.finalIn, Atom.final, Atom.closed, Ty.closedArgs]
    | _ => simp_all [Atom.finalIn, Atom.final, Atom.closed]

theorem Ty.subst_of_allFinalIn (σ : List Ty) {t : Ty} (h : t.allFinalIn P = true) : Ty.subst σ t = t :=
  Ty.subst_closed_id σ t (Ty.closed_of_allFinalIn h)

theorem Ty.allFinalIn_keep {t : Ty} (h : t.allFinalIn P = true) (as : List Atom) :
    (t.keep as).allFinalIn P = true := by
  simp only [Ty.allFinalIn, Ty.keep, List.all_eq_true] at h ⊢
  exact fun a ha => h a (List.mem_filter.mp ha).1

theorem Ty.allFinalIn_remove {t : Ty} (h : t.allFinalIn P = true) (a : Atom) :
    (t.remove a).allFinalIn P = true := by
  simp only [Ty.allFinalIn, Ty.remove, List.all_eq_true] at h ⊢
  exact fun b hb => h b (List.mem_filter.mp hb).1

/-- A value of a type of final atoms: no object, or one whose class
defines no `==` (a `data` type's). -/
theorem value_finalIn (hwf : WfClasses P.classes) {s : Store} {v : Value} {t : Ty} (hv : s.hasTy P v t)
    (hfin : t.allFinalIn P = true) :
    (∀ l, v ≠ .obj l) ∨ ∃ l o, v = .obj l ∧ s.objs[l]? = some o ∧ P.lookup o.cls "==" = none := by
  cases v
  case obj l =>
    right
    rw [hasTy_iff] at hv
    obtain ⟨a, ha, b, hb, hab⟩ := hv
    obtain ⟨o, ho, _, rfl⟩ := typeOf_obj ha
    have hfb := List.all_eq_true.mp hfin b hb
    cases b with
    | cls c args =>
      cases args with
      | cons => simp [Atom.finalIn, Atom.final] at hfb
      | nil =>
        simp only [Atom.finalIn, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
          Option.isNone_iff_eq_none] at hfb
        obtain ⟨hkd, hlk⟩ := hfb
        rw [Atom.le_cls_iff hwf] at hab
        rcases hab with ⟨rfl, _⟩ | ⟨x, hx, _⟩
        · -- The root is no `data` type nor variant.
          exfalso
          cases h0 : P.classes[0]? with
          | none => rcases hkd with hkd | hkd <;> simp [ClassTable.kindOf, h0] at hkd
          | some k0 => rcases hkd with hkd | hkd <;> simp [ClassTable.kindOf, h0, hwf.rootKind k0 h0] at hkd
        · have := ancestorArgs_data hwf hkd _ _ _ hx
          exact ⟨l, o, rfl, ho, by rw [this]; exact hlk⟩
    | _ => simp_all [Atom.finalIn, Atom.final, Atom.le]
  all_goals exact .inl fun l h => by cases h

/-- A value of final atoms whose atom is a value class's: of that atom
alone. -/
theorem hasTy_keep (hwf : WfClasses P.classes) {s : Store} {v : Value} {t : Ty} {a : Atom}
    (hv : s.hasTy P v t) (hfin : t.allFinalIn P = true) (ha : s.typeOf v = some a)
    (hfa : a.final = true) : s.hasTy P v (t.keep [a]) := by
  rw [hasTy_iff] at *
  obtain ⟨a', ha', b, hb, hab⟩ := hv
  rw [ha] at ha'; cases ha'
  have hfb := List.all_eq_true.mp hfin b hb
  -- Below a final atom, a value class's atom is only itself.
  have hba : b = a := by
    cases b with
    | cls c args =>
      cases args with
      | cons => simp [Atom.finalIn, Atom.final] at hfb
      | nil =>
        simp only [Atom.finalIn, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hfb
        exfalso
        cases a <;> simp [Atom.final] at hfa <;> simp only [Atom.le, Bool.and_eq_true, beq_iff_eq] at hab <;>
          (obtain ⟨rfl, _⟩ := hab
           cases h0 : P.classes[0]? with
           | none => rcases hfb.1 with h | h <;> simp [ClassTable.kindOf, h0] at h
           | some k0 => rcases hfb.1 with h | h <;> simp [ClassTable.kindOf, h0, hwf.rootKind k0 h0] at h)
    | _ => cases a <;> simp_all [Atom.finalIn, Atom.final, Atom.le]
  subst hba
  exact ⟨_, ha, _, List.mem_filter.mpr ⟨hb, by simp [Ty.keep]⟩, hab⟩

end QuarzCore
