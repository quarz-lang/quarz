/-
Inheritance: a subclass's fields begin with its superclass's (so a field
is at the same index in both), and the method a subclass runs for a call
is the one its superclass would, or one overriding it.
-/

import QuarzCore.Lemmas

set_option linter.deprecated false

namespace QuarzCore

open ClassTable

variable {ct : ClassTable}

theorem allFieldsDecl_prefix (hwf : WfClasses ct) {c d : Nat} (h : c ∈ ct.ancestors d) :
    ∃ rest, ct.allFieldsDecl d = ct.allFieldsDecl c ++ rest := by
  obtain ⟨pre, hpre, _⟩ := ancestors_suffix hwf d c h
  refine ⟨(pre.reverse.filterMap fun d => (ct[d]?).map (d, ·)).flatMap fun (d, k) =>
    k.fields.map (d, ·), ?_⟩
  simp [allFieldsDecl, hpre, List.reverse_append, List.filterMap_append, List.flatMap_append]

theorem allFields_prefix (hwf : WfClasses ct) {c d : Nat} (h : c ∈ ct.ancestors d) :
    ∃ rest, ct.allFields d = ct.allFields c ++ rest := by
  obtain ⟨rest, hr⟩ := allFieldsDecl_prefix hwf h
  exact ⟨rest.map (·.2), by simp [allFields, hr]⟩

theorem find?_idx {α} {p : α → Bool} : ∀ {l : List α} {a : α}, l.find? p = some a →
    ∃ i, l.findIdx? p = some i ∧ l[i]? = some a
  | [], _, h => by simp at h
  | x :: l, a, h => by
    by_cases hx : p x
    · simp [List.find?, hx] at h; subst h; exact ⟨0, by simp [List.findIdx?_cons, hx], rfl⟩
    · simp [List.find?, hx] at h
      obtain ⟨i, hi, hl⟩ := find?_idx h
      exact ⟨i + 1, by simp [List.findIdx?_cons, hx, hi], by simpa using hl⟩

theorem find?_append_of {α} {p : α → Bool} {l r : List α} {a : α} (h : l.find? p = some a) :
    (l ++ r).find? p = some a := by
  simp [List.find?_append, h]

theorem findIdx?_append_of {α} {p : α → Bool} {l r : List α} {i : Nat} (h : l.findIdx? p = some i) :
    (l ++ r).findIdx? p = some i := by
  simp [List.findIdx?_append, h]

/-- A field of class `c`, in an instance of a subclass `d`: found first
there, at the same index. -/
theorem field_in_subclass (hwf : WfClasses ct) {c d : Nat} (h : c ∈ ct.ancestors d) {f : String}
    {fd : Field} (hf : ct.field? c f = some fd) :
    ∃ i, fieldIndex ct d f = some i ∧ (ct.allFields d)[i]? = some fd := by
  obtain ⟨rest, hr⟩ := allFields_prefix hwf h
  obtain ⟨i, hi, hl⟩ := find?_idx hf
  refine ⟨i, ?_, ?_⟩
  · unfold fieldIndex; rw [hr]; exact findIdx?_append_of hi
  · rw [hr, List.getElem?_append_left (List.getElem?_eq_some_iff.mp hl).1]; exact hl

/-- `field_in_subclass`, the index also within the class's own layout. -/
theorem field_in_subclass' (hwf : WfClasses ct) {c d : Nat} (h : c ∈ ct.ancestors d) {f : String}
    {fd : Field} (hf : ct.field? c f = some fd) :
    ∃ i, fieldIndex ct d f = some i ∧ (ct.allFields d)[i]? = some fd ∧
      (ct.allFields c)[i]? = some fd := by
  obtain ⟨rest, hr⟩ := allFields_prefix hwf h
  obtain ⟨i, hi, hl⟩ := find?_idx hf
  refine ⟨i, ?_, ?_, hl⟩
  · unfold fieldIndex; rw [hr]; exact findIdx?_append_of hi
  · rw [hr, List.getElem?_append_left (List.getElem?_eq_some_iff.mp hl).1]; exact hl

/-- The fields seen from a class have the declared names. -/
theorem allFieldsAt_names (ct : ClassTable) (k : Nat) (as : List Ty) :
    (ct.allFieldsAt k as).map (·.name) = (ct.allFields k).map (·.name) := by
  simp [ClassTable.allFieldsAt, ClassTable.allFields, List.map_map, Function.comp_def]

/-- `findIdx?` by name sees only the names. -/
theorem findIdx?_name_eq {l l' : List Field} (h : l.map (·.name) = l'.map (·.name)) (f : String) :
    l.findIdx? (·.name == f) = l'.findIdx? (·.name == f) := by
  have : ∀ (l : List Field), l.findIdx? (·.name == f) = (l.map (·.name)).findIdx? (· == f) := by
    intro l; induction l with
    | nil => rfl
    | cons a l ih => simp [List.findIdx?_cons, ih]
  rw [this, this, h]

/-- A field as class `c` sees it, by name: its index, where a subclass `d`
has it too, and the field as declared there (same name and `var`). -/
theorem fieldAt_in_subclass (hwf : WfClasses ct) {c d : Nat} (h : c ∈ ct.ancestors d)
    {as : List Ty} {f : String} {fd : Field} (hf : ct.fieldAt? c as f = some fd) :
    ∃ i, fieldIndex ct d f = some i ∧ (ct.allFieldsAt c as)[i]? = some fd ∧
      ∃ fd0, (ct.allFields d)[i]? = some fd0 ∧ (ct.allFields c)[i]? = some fd0 ∧
        fd0.name = fd.name ∧ fd0.var = fd.var ∧ fd0.default = fd.default := by
  obtain ⟨rest, hr⟩ := allFields_prefix hwf h
  obtain ⟨i, hi, hl⟩ := find?_idx hf
  obtain ⟨d', fd0, _, hf0, hfd⟩ := ClassTable.allFieldsAt_some ct hl
  refine ⟨i, ?_, hl, fd0, ?_, hf0, by rw [hfd], by rw [hfd], by rw [hfd]⟩
  · unfold fieldIndex; rw [hr]
    have hi' : (ct.allFields c).findIdx? (·.name == f) = some i := by
      rw [← findIdx?_name_eq (allFieldsAt_names ct c as) f]; exact hi
    exact findIdx?_append_of hi'
  · rw [hr, List.getElem?_append_left (List.getElem?_eq_some_iff.mp hf0).1]; exact hf0

theorem ancestors_nodup (hwf : WfClasses ct) : ∀ c, (ct.ancestors c).Nodup := by
  intro c
  induction c using Nat.strongRecOn with
  | _ c ih =>
    rw [ancestors_eq hwf]
    cases hs : superOf ct c with
    | none => simp
    | some s =>
      simp only
      refine List.nodup_cons.mpr ⟨fun hm => ?_, ih s (superOf_lt hwf hs)⟩
      have := ancestors_le hwf s c hm
      have := superOf_lt hwf hs
      omega

/-- What `wfMethod` says of a method's overriding. -/
theorem Program.wfMethod_overrides {P : Program} {mt : Method} (h : P.wfMethod mt = true)
    (hi : mt.name ≠ "initialize") :
    ∀ d ∈ (P.classes.ancestors mt.owner).drop 1, ∀ sup,
      P.lookupAt d ((P.classes.ancestorArgs mt.owner (P.classes.selfArgs mt.owner) d).getD [])
        mt.name = some sup →
      P.overrides mt sup = true := by
  intro d hd sup hsup
  simp only [Program.wfMethod, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, List.all_eq_true] at h
  have := (h.1.2.resolve_left hi).2 d hd
  rw [hsup] at this
  exact this

theorem Program.wfMethod_pos {P : Program} {mt : Method} (h : P.wfMethod mt = true)
    (hi : mt.name ≠ "initialize") : P.methodPosOk mt = true := by
  simp only [Program.wfMethod, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  exact (h.1.2.resolve_left hi).1

theorem Program.lookup_spec {P : Program} {c : Nat} {m : String} {mt : Method}
    (h : P.lookup c m = some mt) :
    mt ∈ P.methods ∧ mt.owner ∈ P.classes.ancestors c ∧ mt.name = m := by
  unfold Program.lookup at h
  obtain ⟨d, hd, hf⟩ := List.exists_of_findSome?_eq_some h
  have hmem := List.mem_of_find?_eq_some hf
  have hp := List.find?_some hf
  simp at hp
  obtain ⟨rfl, rfl⟩ := hp
  exact ⟨hmem, hd, rfl⟩

/-- Substituting a block's signature twice is substituting with the
composition. -/
theorem BlockSig.subst_subst (sig : BlockSig) (as σ : List Ty) :
    (sig.subst as).subst σ = sig.subst (Ty.substArgs σ as) := by
  simp [BlockSig.subst, List.map_map, Function.comp_def, Ty.subst_comp]

/-- Instantiating twice is instantiating with the composition. -/
theorem Method.inst_inst (mt : Method) (as σ : List Ty) :
    (mt.inst as).inst σ = mt.inst (Ty.substArgs σ as) := by
  simp only [Method.inst, List.map_map, Function.comp_def, Ty.subst_comp]
  congr 1
  cases mt.block with
  | none => rfl
  | some sig => simp [BlockSig.subst_subst]

/-- The method a view `k[as]` finds, seen through a substitution of the
view's arguments. -/
theorem Program.lookupAt_subst {P : Program} {k : Nat} {as : List Ty} {m : String} {mt : Method}
    (σ : List Ty) (h : P.lookupAt k as m = some mt) :
    P.lookupAt k (Ty.substArgs σ as) m = some (mt.inst σ) := by
  simp only [Program.lookupAt, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h ⊢
  obtain ⟨mt0, h0, bs, hbs, rfl⟩ := h
  exact ⟨mt0, h0, _, ClassTable.ancestorArgs_subst P.classes σ hbs, (Method.inst_inst mt0 bs σ).symm⟩

/-- `lookupAt` is `lookup` instantiated. -/
theorem Program.lookupAt_spec {P : Program} {k : Nat} {as : List Ty} {m : String} {mt : Method}
    (h : P.lookupAt k as m = some mt) :
    ∃ mt0 bs, P.lookup k m = some mt0 ∧ P.classes.ancestorArgs k as mt0.owner = some bs ∧
      mt = mt0.inst bs := by
  simp only [Program.lookupAt, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨mt0, h0, bs, hbs, rfl⟩ := h
  exact ⟨mt0, bs, h0, hbs, rfl⟩

theorem Method.inst_owner (mt : Method) (as : List Ty) : (mt.inst as).owner = mt.owner := rfl
theorem Method.inst_name (mt : Method) (as : List Ty) : (mt.inst as).name = mt.name := rfl
theorem Method.inst_locals (mt : Method) (as : List Ty) : (mt.inst as).locals = mt.locals := rfl
theorem Method.inst_body (mt : Method) (as : List Ty) : (mt.inst as).body = mt.body := rfl
theorem Method.inst_params_fst (mt : Method) (as : List Ty) :
    (mt.inst as).params.map (·.1) = mt.params.map (·.1) := by
  simp [Method.inst, List.map_map, Function.comp_def]
theorem Method.inst_params_snd (mt : Method) (as : List Ty) :
    (mt.inst as).params.map (·.2) = (mt.params.map (·.2)).map (Ty.subst as) := by
  simp [Method.inst, List.map_map, Function.comp_def]
theorem Method.inst_params_length (mt : Method) (as : List Ty) :
    (mt.inst as).params.length = mt.params.length := by simp [Method.inst]
theorem Method.inst_ret (mt : Method) (as : List Ty) : (mt.inst as).ret = mt.ret.subst as := rfl
theorem Method.inst_block_none (mt : Method) (as : List Ty) :
    (mt.inst as).block = none ↔ mt.block = none := by
  simp [Method.inst]

/-- A view finds no method only where the class finds none (an owner is
always an ancestor, which the chain gives arguments). -/
theorem Program.lookupAt_none_iff {P : Program} (hwf : WfClasses P.classes) (k : Nat) (as : List Ty)
    (m : String) : P.lookupAt k as m = none ↔ P.lookup k m = none := by
  simp only [Program.lookupAt]
  cases h : P.lookup k m with
  | none => simp
  | some mt =>
    simp only [Option.bind_some, Option.map_eq_none_iff]
    obtain ⟨_, hown, _⟩ := Program.lookup_spec h
    obtain ⟨bs, hbs⟩ := ClassTable.ancestorArgs_of_mem hwf k as mt.owner hown
    simp [hbs]

/-- The method a subclass runs: the one found, or one overriding it (the
one found, with the arguments the overriding method's class gives its
owner, is what `wfMethod` compared). -/
theorem Program.lookup_sub {P : Program} (hwf : WfClasses P.classes)
    (hm : ∀ mt ∈ P.methods, P.wfMethod mt = true) {k rc : Nat} {m : String} {mt : Method}
    (h : P.lookup k m = some mt) (hk : k ∈ P.classes.ancestors rc) (hi : m ≠ "initialize") :
    ∃ mt', P.lookup rc m = some mt' ∧ (mt' = mt ∨
      (P.overrides mt' (mt.inst ((P.classes.ancestorArgs mt'.owner (P.classes.selfArgs mt'.owner)
        mt.owner).getD [])) = true ∧ mt.owner ∈ P.classes.ancestors mt'.owner)) := by
  obtain ⟨pre, hpre, _⟩ := ancestors_suffix hwf rc k hk
  have hnd := ancestors_nodup hwf rc
  have hspec := Program.lookup_spec h
  unfold Program.lookup at h ⊢
  rw [hpre, List.findSome?_append]
  cases hp : pre.findSome? (fun d => P.methods.find? fun mt => mt.owner == d && mt.name == m) with
  | none => exact ⟨mt, by simpa using h, .inl rfl⟩
  | some mt' =>
    refine ⟨mt', rfl, .inr ?_⟩
    obtain ⟨e, he, hf⟩ := List.exists_of_findSome?_eq_some hp
    have hmem := List.mem_of_find?_eq_some hf
    have hpr := List.find?_some hf
    simp at hpr
    obtain ⟨hown, hname⟩ := hpr
    -- `k` is above `e`, strictly: `e` comes before `k`'s chain.
    have heA : e ∈ P.classes.ancestors rc := by rw [hpre]; exact List.mem_append_left _ he
    have hkA : k ∈ P.classes.ancestors rc := hk
    have he_notk : e ∉ P.classes.ancestors k := by
      intro hek
      rw [hpre] at hnd
      exact (List.nodup_append.mp hnd).2.2 e he e hek rfl
    rcases ancestors_total hwf rc e k heA hkA with h1 | h1
    · exact absurd h1 he_notk
    · have hke : k ≠ e := fun hke => he_notk (hke ▸ mem_ancestors_self hwf k)
      have hdrop : k ∈ (P.classes.ancestors e).drop 1 := by
        rw [ancestors_eq hwf] at h1 ⊢
        rcases List.mem_cons.mp h1 with h2 | h2
        · exact absurd h2 hke
        · simpa using h2
      -- The arguments `e` gives `k`, and through `k`, `mt.owner`.
      obtain ⟨σk, hσk⟩ := ancestorArgs_of_mem hwf e (P.classes.selfArgs e) k h1
      obtain ⟨σo, hσo⟩ := ancestorArgs_of_mem hwf k σk mt.owner hspec.2.1
      have hcomp := ancestorArgs_trans hwf hσk hσo
      have := Program.wfMethod_overrides (hm mt' hmem) (by rw [hname]; exact hi) k
        (by rw [hown]; exact hdrop) (mt.inst σo)
        (by
          rw [hname, hown, hσk]
          simp only [Option.getD, Program.lookupAt]
          unfold Program.lookup
          rw [h]
          simp [hσo])
      refine ⟨by rw [hown, hcomp]; simpa using this, ?_⟩
      rw [hown]
      exact ancestors_trans hwf e k mt.owner h1 hspec.2.1

end QuarzCore
