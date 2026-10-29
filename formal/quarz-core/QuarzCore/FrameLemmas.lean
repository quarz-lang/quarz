/-
Lemmas for running a method's body in a new frame (its locals at fresh
locations, its parameters bound), and for which of an object's fields
hold a value before `initialize` (or `super`) runs: shared by `new`,
`super` (EvalCases.lean, ConstructCases.lean) and calls (StepCases.lean).
-/

import QuarzCore.SoundDefs
import QuarzCore.InheritLemmas

set_option linter.deprecated false

namespace QuarzCore

variable {P : Program}

/-! ### A new frame -/

/-- What binding values to names does: only their locations change. -/
theorem bindAll_same {vars : List (String × Nat)} :
    ∀ {xs : List String} {vs : List Value} {s s' : Store}, bindAll s vars xs vs = some s' →
      s'.objs = s.objs ∧ s'.locs.length = s.locs.length ∧
      ∀ l, (∀ x ∈ xs, lookupVar vars x ≠ some l) → s'.locs[l]? = s.locs[l]?
  | [], [], s, s', h => by simp [bindAll] at h; subst h; exact ⟨rfl, rfl, fun _ _ => rfl⟩
  | x :: xs, v :: vs, s, s', h => by
    simp only [bindAll, bind, Option.bind_eq_some_iff] at h
    obtain ⟨l, hl, h⟩ := h
    obtain ⟨h1, h2, h3⟩ := bindAll_same h
    refine ⟨h1, by rw [h2]; simp [Store.setLoc], fun l' hl' => ?_⟩
    rw [h3 l' fun y hy => hl' y (List.mem_cons_of_mem _ hy)]
    have : l' ≠ l := fun e => hl' x (List.mem_cons_self ..) (e ▸ hl)
    simp [Store.setLoc, List.getElem?_set_ne (Ne.symm this)]
  | [], _ :: _, _, _, h => by simp [bindAll] at h
  | _ :: _, [], _, _, h => by simp [bindAll] at h

/-- Binding leaves the procedures. -/
theorem bindAll_procs {vars : List (String × Nat)} :
    ∀ {xs : List String} {vs : List Value} {s s' : Store}, bindAll s vars xs vs = some s' →
      s'.procs = s.procs
  | [], [], s, s', h => by simp [bindAll] at h; subst h; rfl
  | x :: xs, v :: vs, s, s', h => by
    simp only [bindAll, bind, Option.bind_eq_some_iff] at h
    obtain ⟨l, _, h⟩ := h
    rw [bindAll_procs h]; rfl
  | [], _ :: _, _, _, h => by simp [bindAll] at h
  | _ :: _, [], _, _, h => by simp [bindAll] at h

/-- Bound to distinct names, at distinct locations: each holds its value. -/
theorem bindAll_val {vars : List (String × Nat)}
    (hinj : ∀ x y l, lookupVar vars x = some l → lookupVar vars y = some l → x = y) :
    ∀ {xs : List String} {vs : List Value} {s s' : Store}, bindAll s vars xs vs = some s' →
      xs.Nodup → (∀ x ∈ xs, ∀ l, lookupVar vars x = some l → l < s.locs.length) →
      ∀ x v, (x, v) ∈ xs.zip vs → ∃ l, lookupVar vars x = some l ∧ s'.locs[l]? = some v
  | [], [], _, _, _, _, _, _, _, hm => by simp at hm
  | x :: xs, w :: vs, s, s', h, hnd, hin, y, v, hm => by
    simp only [bindAll, bind, Option.bind_eq_some_iff] at h
    obtain ⟨l, hl, h⟩ := h
    have hnd' := List.nodup_cons.mp hnd
    rcases List.mem_cons.mp hm with he | hm
    · cases he
      refine ⟨l, hl, ?_⟩
      rw [(bindAll_same h).2.2 l fun z hz hzl => hnd'.1 (by rw [hinj z x l hzl hl] at hz; exact hz)]
      simp [Store.setLoc, hin x (List.mem_cons_self ..) l hl]
    · exact bindAll_val hinj h hnd'.2 (fun z hz l' hl' => by
        simpa [Store.setLoc] using hin z (List.mem_cons_of_mem _ hz) l' hl') y v hm
  | [], _ :: _, _, _, h, _, _, _, _, _ => by simp [bindAll] at h
  | _ :: _, [], _, _, h, _, _, _, _, _ => by simp [bindAll] at h

theorem bindAll_some {vars : List (String × Nat)} :
    ∀ {xs : List String} {vs : List Value} (s : Store), xs.length = vs.length →
      (∀ x ∈ xs, ∃ l, lookupVar vars x = some l) → ∃ s', bindAll s vars xs vs = some s'
  | [], [], s, _, _ => ⟨s, rfl⟩
  | x :: xs, v :: vs, s, hlen, hl => by
    obtain ⟨l, hx⟩ := hl x (List.mem_cons_self ..)
    obtain ⟨s', hs'⟩ := bindAll_some (s.setLoc l v) (by simpa using hlen)
      fun y hy => hl y (List.mem_cons_of_mem _ hy)
    exact ⟨s', by simp [bindAll, hx, hs']⟩
  | [], _ :: _, _, h, _ => by simp at h
  | _ :: _, [], _, h, _ => by simp at h

theorem lookupVar_cons (x y : String) (l : Nat) (rest : List (String × Nat)) :
    lookupVar ((x, l) :: rest) y = if x = y then some l else lookupVar rest y := by
  by_cases h : x = y
  · simp [lookupVar, List.find?, h]
  · have : (x == y) = false := by simpa using h
    simp [lookupVar, List.find?, this, h]

/-- A new frame's names, each at its fresh location. -/
theorem lookupVar_alloc : ∀ {names : List String} {base j : Nat} {x : String}, names.Nodup →
    names[j]? = some x → lookupVar (Store.allocVars base names) x = some (base + j)
  | [], _, _, _, _, h => by simp at h
  | y :: ys, base, j, x, hnd, h => by
    have hnd' := List.nodup_cons.mp hnd
    simp only [Store.allocVars, lookupVar_cons]
    cases j with
    | zero => simp at h; subst h; simp
    | succ j =>
      simp at h
      have hxy : y ≠ x := fun e => hnd'.1 (e ▸ List.mem_of_getElem? h)
      rw [if_neg hxy, lookupVar_alloc hnd'.2 h]
      congr 1; omega

theorem lookupVar_alloc_inv : ∀ {names : List String} {base l : Nat} {x : String},
    lookupVar (Store.allocVars base names) x = some l → ∃ j, names[j]? = some x ∧ l = base + j
  | [], _, _, _, h => by simp [Store.allocVars, lookupVar] at h
  | y :: ys, base, l, x, h => by
    simp only [Store.allocVars, lookupVar_cons] at h
    split at h
    · rename_i hyx; cases h; exact ⟨0, by simp [hyx], rfl⟩
    · obtain ⟨j, hj, rfl⟩ := lookupVar_alloc_inv h
      exact ⟨j + 1, by simpa using hj, by omega⟩

theorem mem_allocVars : ∀ {names : List String} {base l : Nat} {x : String},
    (x, l) ∈ Store.allocVars base names → base ≤ l ∧ l < base + names.length
  | [], _, _, _, h => by simp [Store.allocVars] at h
  | y :: ys, base, l, x, h => by
    simp only [Store.allocVars, List.mem_cons] at h
    rcases h with h | h
    · cases h; simp
    · have := mem_allocVars h; simp; omega

theorem Ext.restrict {W W' Wo : Nat → Prop} {Λ Λ' : List Ty} {s s' : Store} (h : Ext P W Wo Λ Λ' s s')
    (hw : ∀ l, l < s.locs.length → W l → W' l) : Ext P W' Wo Λ Λ' s s' where
  tys := h.tys
  procs := h.procs
  locs := fun l v hv => by
    obtain ⟨v', h1, h2⟩ := h.locs l v hv
    refine ⟨v', h1, ?_⟩
    rcases h2 with h2 | ⟨hwl, t, ht, hty⟩
    · exact .inl h2
    · exact .inr ⟨hw l (List.getElem?_eq_some_iff.mp hv).1 hwl, t, ht, hty⟩
  grow := h.grow
  imm := h.imm

theorem params_get : ∀ {ps : List (String × Ty)} {p : Path} {t : Ty},
    Env.get (ps.map fun (x, t) => ((.local x : Path), t)) p = some t → ∃ x, p = .local x ∧ (x, t) ∈ ps
  | [], _, _, h => by simp [Env.get] at h
  | (y, u) :: ps, p, t, h => by
    simp only [List.map_cons, Env.get_cons] at h
    split at h
    · rename_i hp; cases h; exact ⟨y, hp.symm, List.mem_cons_self ..⟩
    · obtain ⟨x, hx, hm⟩ := params_get h; exact ⟨x, hx, List.mem_cons_of_mem _ hm⟩

theorem find_nodup : ∀ {l : List (String × Ty)} {x : String} {t : Ty}, (l.map (·.1)).Nodup →
    (x, t) ∈ l → (l.find? (·.1 == x)).map (·.2) = some t
  | [], _, _, _, h => by cases h
  | (y, u) :: l, x, t, hnd, h => by
    have hnd' := List.nodup_cons.mp hnd
    by_cases hy : y = x
    · subst hy
      rcases List.mem_cons.mp h with he | hm
      · cases he; simp [List.find?]
      · exact absurd (List.mem_map.mpr ⟨_, hm, rfl⟩) hnd'.1
    · have hne : (y == x) = false := by simpa using hy
      rcases List.mem_cons.mp h with he | hm
      · cases he; exact absurd rfl hy
      · simp only [List.find?, hne]; exact find_nodup hnd'.2 hm

/-- A method's parameter: a local of its type (`wfMethod`). -/
theorem decl_param {mt : Method} (h : P.wfMethod mt = true) {x : String} {t : Ty}
    (hm : (x, t) ∈ mt.params) : (⟨P, mt, false, false⟩ : Ctx).decl x = some t := by
  simp only [Program.wfMethod, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨_, hlen⟩, hnd⟩, hpre⟩, _⟩, _⟩ := h
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hm
  have hpl := (List.getElem?_eq_some_iff.mp hi).1
  have hil : i < mt.locals.length := by omega
  have hz : (mt.params.zip mt.locals)[i]? = some ((x, t), mt.locals[i]) := by
    simp [List.zip, List.getElem?_zipWith, hi, hil]
  have heq := hpre _ (List.mem_iff_getElem?.mpr ⟨i, hz⟩)
  simp only at heq
  have hloc : (x, t) ∈ mt.locals := by rw [heq]; exact List.getElem_mem hil
  exact find_nodup hnd hloc

theorem zip_fst_snd : ∀ (ps : List (String × Ty)), (ps.map (·.1)).zip (ps.map (·.2)) = ps
  | [] => rfl
  | (x, t) :: ps => by simp [zip_fst_snd ps]

/-- `(x, t)` of the parameters and types: the value given for `x`, of `t`. -/
theorem zip_val {s : Store} :
    ∀ {ps : List String} {ts : List Ty} {vs : List Value}, AllTy P s vs ts →
      ∀ x t, (x, t) ∈ ps.zip ts → ∃ v, (x, v) ∈ ps.zip vs ∧ s.hasTy P v t
  | [], _, _, _, _, _, hm => by simp at hm
  | _ :: _, [], _, _, _, _, hm => by simp at hm
  | p :: ps, t' :: ts, [], h, _, _, _ => h.elim
  | p :: ps, t' :: ts, v :: vs, ⟨h1, h2⟩, x, t, hm => by
    rcases List.mem_cons.mp hm with he | hm
    · cases he; exact ⟨v, List.mem_cons_self .., h1⟩
    · obtain ⟨w, hw, hwt⟩ := zip_val h2 x t hm
      exact ⟨w, List.mem_cons_of_mem _ hw, hwt⟩

/-! ### Fields -/

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

/-! ### Which fields must be assigned -/

section
variable {ct : ClassTable}

/-- The fields with their declaring classes, without the classes. -/
theorem snd_decl (ct : ClassTable) : ∀ ds : List Nat,
    (((ds.filterMap fun d => (ct[d]?).map (d, ·)).flatMap fun (d, k) => k.fields.map (d, ·)).map (·.2))
      = (ds.filterMap (ct[·]?)).flatMap (·.fields)
  | [] => rfl
  | d :: ds => by
    cases hk : ct[d]? with
    | none => simp [List.filterMap_cons, hk, snd_decl ct ds]
    | some k => simp [List.filterMap_cons, hk, snd_decl ct ds, Function.comp_def]

theorem allFields_eq (ct : ClassTable) (k : Nat) :
    ct.allFields k = ((ct.ancestors k).reverse.filterMap (ct[·]?)).flatMap (·.fields) := by
  rw [ClassTable.allFields, ClassTable.allFieldsDecl, snd_decl]

/-- A class's fields: those of a class above it, then those of the
classes between. -/
theorem allFields_split (hwf : WfClasses ct) {e k : Nat} (h : e ∈ ct.ancestors k) :
    ∃ pre, ct.ancestors k = pre ++ ct.ancestors e ∧ e ∉ pre ∧
      ct.allFields k = ct.allFields e ++ (pre.reverse.filterMap (ct[·]?)).flatMap (·.fields) := by
  obtain ⟨pre, hpre, hn⟩ := ClassTable.ancestors_suffix hwf k e h
  refine ⟨pre, hpre, hn, ?_⟩
  simp [allFields_eq, hpre, List.reverse_append, List.filterMap_append, List.flatMap_append]

theorem mem_classes_fields {pre : List Nat} {f : Field}
    (h : f ∈ (pre.reverse.filterMap (ct[·]?)).flatMap (·.fields)) :
    ∃ d ∈ pre, ∃ cl, ct[d]? = some cl ∧ f ∈ cl.fields := by
  obtain ⟨cl, hcl, hf⟩ := List.mem_flatMap.mp h
  obtain ⟨d, hd, hcd⟩ := List.mem_filterMap.mp hcl
  exact ⟨d, List.mem_reverse.mp hd, cl, hcd, hf⟩

end

/-- A class that does not define `initialize` has no field to assign. -/
theorem own_not_required {d : Nat} (hi : P.wfInit d = true) (hno : P.ownInit d = false)
    {cl : Class} (hcl : P.classes[d]? = some cl) {f : Field} (hf : f ∈ cl.fields) :
    f.required P.classes = false := by
  simp only [Program.wfInit, hcl, Option.map_some, Option.getD_some, hno, Bool.or_false,
    Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false] at hi
  cases h : f.required P.classes
  · rfl
  · exact absurd h (hi f hf)

/-- The classes `lookup` passed over do not define the method. -/
theorem lookup_before {k : Nat} {m : String} {mt : Method} (hwf : WfClasses P.classes)
    (h : P.lookup k m = some mt) :
    ∃ pre, P.classes.ancestors k = pre ++ P.classes.ancestors mt.owner ∧
      ∀ d ∈ pre, P.methods.find? (fun mt => mt.owner == d && mt.name == m) = none := by
  obtain ⟨_, hown, _⟩ := Program.lookup_spec h
  obtain ⟨pre, hpre, hn⟩ := ClassTable.ancestors_suffix hwf k mt.owner hown
  refine ⟨pre, hpre, fun d hd => ?_⟩
  unfold Program.lookup at h
  rw [hpre, List.findSome?_append] at h
  cases hp : pre.findSome? (fun d => P.methods.find? fun mt => mt.owner == d && mt.name == m) with
  | none => exact List.findSome?_eq_none_iff.mp hp d hd
  | some x =>
    rw [hp] at h; simp at h; subst h
    obtain ⟨e, he, hf⟩ := List.exists_of_findSome?_eq_some hp
    have := List.find?_some hf
    simp at this
    exact absurd (this.1 ▸ he) hn

theorem ownInit_of_find {d : Nat} (h : P.methods.find? (fun mt => mt.owner == d && mt.name == "initialize") = none) :
    P.ownInit d = false := by
  unfold Program.ownInit
  rw [List.find?_eq_none] at h
  cases ha : P.methods.any fun mt => mt.owner == d && mt.name == "initialize"
  · rfl
  · obtain ⟨x, hx, hp⟩ := List.any_eq_true.mp ha
    exact absurd hp (h x hx)

/-- The fields of instances of `k` past those of its `initialize`'s
class: none to assign. -/
theorem init_beyond (hwf : WfClasses P.classes) (hi : ∀ d, d < P.classes.length → P.wfInit d = true)
    {k : Nat} {mi : Method} (h : P.lookup k "initialize" = some mi) :
    ∃ rest, P.classes.allFields k = P.classes.allFields mi.owner ++ rest ∧
      ∀ f ∈ rest, f.required P.classes = false := by
  obtain ⟨_, hown, _⟩ := Program.lookup_spec h
  obtain ⟨pre, hpre, hnone⟩ := lookup_before hwf h
  obtain ⟨pre', hpre', _, hsplit⟩ := allFields_split hwf hown
  rw [hpre] at hpre'
  have hpp : pre' = pre := (List.append_cancel_right hpre').symm
  subst hpp
  refine ⟨_, hsplit, fun f hf => ?_⟩
  obtain ⟨d, hd, cl, hcl, hfc⟩ := mem_classes_fields hf
  exact own_not_required (hi d (List.getElem?_eq_some_iff.mp hcl).1) (ownInit_of_find (hnone d hd)) hcl hfc

/-- No `initialize`: no field to assign. -/
theorem no_init_fields (hi : ∀ d, d < P.classes.length → P.wfInit d = true) {k : Nat}
    (h : P.lookup k "initialize" = none) : ∀ f ∈ P.classes.allFields k, f.required P.classes = false := by
  intro f hf
  rw [allFields_eq] at hf
  obtain ⟨d, hd, cl, hcl, hfc⟩ := mem_classes_fields (pre := (P.classes.ancestors k).reverse)
    (by simpa using hf)
  have hnone : P.methods.find? (fun mt => mt.owner == d && mt.name == "initialize") = none := by
    unfold Program.lookup at h
    exact List.findSome?_eq_none_iff.mp h d (List.mem_reverse.mp hd)
  exact own_not_required (hi d (List.getElem?_eq_some_iff.mp hcl).1) (ownInit_of_find hnone) hcl hfc

theorem Env.get_mem : ∀ {Γ : Env} {p : Path} {t : Ty}, Γ.get p = some t → (p, t) ∈ Γ
  | [], _, _, h => by simp [Env.get] at h
  | (q, u) :: Γ, p, t, h => by
    simp only [Env.get] at h
    split at h
    · cases h; subst_vars; exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (Env.get_mem h)

theorem mem_heldEnv {ct : ClassTable} {fs : List Field} {p : Path} {t : Ty}
    (h : (p, t) ∈ Program.heldEnv ct fs) :
    ∃ f ∈ fs, f.required ct = false ∧ p = .field f.name ∧ t = f.ty := by
  obtain ⟨f, hf, he⟩ := List.mem_filterMap.mp h
  cases hr : f.required ct
  · simp [hr] at he; exact ⟨f, hf, hr, he.1.symm, he.2.symm⟩
  · simp [hr] at he

/-- With distinct names, a field is found by its name. -/
theorem field?_at (hwf : WfClasses P.classes) {k : Nat} (hk : k < P.classes.length) {i : Nat}
    {f : Field} (hi : (P.classes.allFields k)[i]? = some f) : P.classes.field? k f.name = some f := by
  have hidx := fieldIndex_at hwf hk hi
  unfold ClassTable.field?
  obtain ⟨hil, rfl⟩ := List.getElem?_eq_some_iff.mp hi
  rw [List.find?_eq_some_iff_getElem]
  refine ⟨by simp, i, hil, rfl, fun j hj => ?_⟩
  obtain ⟨_, _, hmin⟩ := List.findIdx?_eq_some_iff_getElem.mp hidx
  simpa using hmin j hj

/-- With distinct names, a field seen from the class is found by its name. -/
theorem fieldAt?_at (hwf : WfClasses P.classes) {k : Nat} (hk : k < P.classes.length) (as : List Ty)
    {i : Nat} {f : Field} (hi : (P.classes.allFieldsAt k as)[i]? = some f) :
    P.classes.fieldAt? k as f.name = some f := by
  have hn : ((P.classes.allFieldsAt k as).map (·.name)).Nodup := by
    rw [allFieldsAt_names]; exact hwf.names k hk
  have hidx := findIdx?_name hn hi
  unfold ClassTable.fieldAt?
  obtain ⟨hil, rfl⟩ := List.getElem?_eq_some_iff.mp hi
  rw [List.find?_eq_some_iff_getElem]
  refine ⟨by simp, i, hil, rfl, fun j hj => ?_⟩
  obtain ⟨_, _, hmin⟩ := List.findIdx?_eq_some_iff_getElem.mp hidx
  simpa using hmin j hj

/-- A class's own parameters, given arguments, are those arguments. -/
theorem substArgs_selfArgs (ct : ClassTable) {k : Nat} {σ : List Ty}
    (hl : σ.length = (((ct[k]?).map (·.params)).getD []).length) :
    Ty.substArgs σ (ct.selfArgs k) = σ := by
  apply List.ext_getElem?
  intro i
  rw [Ty.substArgs_getElem?]
  simp only [ClassTable.selfArgs, List.getElem?_map, List.getElem?_range']
  by_cases hi : i < σ.length
  · have : i < (((ct[k]?).map (·.params)).getD []).length := hl ▸ hi
    simp [this, Ty.subst, Atom.subst, List.getElem?_eq_getElem hi]
  · have : ¬ i < (((ct[k]?).map (·.params)).getD []).length := hl ▸ hi
    simp [this, List.getElem?_eq_none_iff.mpr (by omega : σ.length ≤ i)]

/-- A field as the class `k` (an ancestor, given the arguments the object's
class gives it) sees it, then with those arguments substituted, is the
field as the object's class sees it. -/
theorem fieldAt_coherent (hwf : WfClasses P.classes) {rc : Nat} {as : List Ty}
    (hlen : as.length = (((P.classes[rc]?).map (·.params)).getD []).length)
    {k : Nat} {σ : List Ty} (hσ : P.classes.ancestorArgs rc as k = some σ) {i : Nat} {f : Field}
    (hf : (P.classes.allFieldsAt k (P.classes.selfArgs k))[i]? = some f) :
    (P.classes.allFieldsAt rc as)[i]? = some { f with ty := f.ty.subst σ } := by
  obtain ⟨d, f0, hd, _, rfl⟩ := ClassTable.allFieldsAt_some P.classes hf
  have hk : k ∈ P.classes.ancestors rc := ClassTable.ancestorArgs_mem hwf rc as k σ hσ
  obtain ⟨rest, hr⟩ := allFieldsDecl_prefix hwf hk
  have hd' : (P.classes.allFieldsDecl rc)[i]? = some (d, f0) := by
    rw [hr, List.getElem?_append_left (List.getElem?_eq_some_iff.mp hd).1]; exact hd
  rw [ClassTable.allFieldsAt_getElem?, hd']
  simp only [Option.map_some, Option.some.injEq]
  -- The declaring class `d` is above `k`: its arguments through `k`.
  have hdk : d ∈ P.classes.ancestors k := by
    have := List.mem_of_getElem? hd
    unfold ClassTable.allFieldsDecl at this
    obtain ⟨⟨d', cl⟩, hmem, hf'⟩ := List.mem_flatMap.mp this
    obtain ⟨e, he, hcd⟩ := List.mem_filterMap.mp hmem
    have := List.mem_map.mp hf'
    obtain ⟨_, _, heq⟩ := this
    cases hcd' : P.classes[e]? with
    | none => simp [hcd'] at hcd
    | some cl' =>
      simp [hcd'] at hcd
      obtain ⟨rfl, rfl⟩ := hcd
      cases heq; exact List.mem_reverse.mp he
  obtain ⟨τ, hτ⟩ := ClassTable.ancestorArgs_of_mem hwf k (P.classes.selfArgs k) d hdk
  have hσlen : σ.length = (((P.classes[k]?).map (·.params)).getD []).length :=
    ClassTable.ancestorArgs_length hwf rc as k σ hσ hlen
  have hτ' : P.classes.ancestorArgs k σ d = some (Ty.substArgs σ τ) := by
    have := ClassTable.ancestorArgs_subst P.classes σ hτ
    rwa [substArgs_selfArgs P.classes hσlen] at this
  have hcomp := ClassTable.ancestorArgs_trans hwf hσ hτ'
  simp only [hτ, hcomp, Option.getD_some]
  congr 1
  exact (Ty.subst_comp σ τ f0.ty).symm

/-- A field of a view with the view's own parameters, as an instance given
`targs` has it. -/
theorem fieldAt_of_static (hwf : WfClasses P.classes) {k : Nat} {targs : List Ty}
    (hlen : targs.length = (((P.classes[k]?).map (·.params)).getD []).length) {i : Nat} {f : Field}
    (hf : (P.classes.allFieldsAt k targs)[i]? = some f) :
    ∃ f', (P.classes.allFieldsAt k (P.classes.selfArgs k))[i]? = some f' ∧
      f = { f' with ty := f'.ty.subst targs } := by
  have hi := (List.getElem?_eq_some_iff.mp hf).1
  rw [ClassTable.allFieldsAt_length] at hi
  obtain ⟨f', hf'⟩ : ∃ f', (P.classes.allFieldsAt k (P.classes.selfArgs k))[i]? = some f' :=
    ⟨_, List.getElem?_eq_getElem (by rw [ClassTable.allFieldsAt_length]; exact hi)⟩
  have := fieldAt_coherent hwf hlen (ClassTable.ancestorArgs_self hwf k targs) hf'
  rw [hf] at this; cases this
  exact ⟨f', hf', rfl⟩

/-- A field as an instance has it and as a class above sees it: the same
but for the type. -/
theorem fieldAt_default (hwf : WfClasses P.classes) {rc : Nat} {as : List Ty}
    (hlen : as.length = (((P.classes[rc]?).map (·.params)).getD []).length)
    {k : Nat} (hk : k ∈ P.classes.ancestors rc) {i : Nat} {f fs : Field}
    (hf : (P.classes.allFieldsAt rc as)[i]? = some f)
    (hfs : (P.classes.allFieldsAt k (P.classes.selfArgs k))[i]? = some fs) :
    f.default = fs.default ∧ f.name = fs.name ∧ f.var = fs.var := by
  obtain ⟨σ, hσ⟩ := ClassTable.ancestorArgs_of_mem hwf rc as k hk
  have := fieldAt_coherent hwf hlen hσ hfs
  rw [hf] at this; cases this; exact ⟨rfl, rfl, rfl⟩

/-- A field not to assign stays so with its type's parameters substituted
(`nil` stays below it). -/
theorem required_subst {ct : ClassTable} (hwf : WfClasses ct) {f : Field} (σ : List Ty)
    (h : f.required ct = false) : ({ f with ty := f.ty.subst σ } : Field).required ct = false := by
  simp only [Field.required, Bool.and_eq_false_iff, Bool.not_eq_false'] at h ⊢
  rcases h with h | h
  · exact Or.inl h
  · right
    have := Ty.subst_le hwf σ h
    simpa using this

/-- The fields of `k` before `j` that hold a value, as an environment:
they hold it in the frame of `self`, an object of `k` or a subclass. -/
theorem sat_held (hwf : WfClasses P.classes) {c : Ctx} (hc : c.prog = P) {fr : Frame} {Λ : List Ty}
    {s : Store} (hw : WfStore P Λ s) {l : Nat} {o : Obj} (hl : fr.self = .obj l)
    (ho : s.objs[l]? = some o) (hsub : c.meth.owner ∈ P.classes.ancestors o.cls)
    (hsa : fr.selfArgs = s.argsFor P.classes l c.meth.owner) {j : Nat}
    (hset : ∀ i, i < j → ∀ f, c.fields[i]? = some f →
      f.required P.classes = false → o.set[i]? = some true) :
    Sat P c (Program.heldEnv P.classes (c.fields.take j)) fr s := by
  subst hc
  intro p t hp
  obtain ⟨f, hf, hr, rfl, rfl⟩ := mem_heldEnv (Env.get_mem hp)
  obtain ⟨i, hij, hfi⟩ := List.mem_take_iff_getElem.mp hf
  have hij' : i < j := by have := Nat.lt_min.mp hij; omega
  have hil : i < c.fields.length := by
    have := Nat.lt_min.mp hij; omega
  have hfi' : c.fields[i]? = some f := by rw [← hfi]; simp [hil]
  obtain ⟨hcls, hclosed, hlen, hflen, hslen, hty⟩ := hw.objs l o ho
  have hown : c.meth.owner < c.prog.classes.length :=
    Nat.lt_of_le_of_lt (ClassTable.ancestors_le hwf _ _ hsub) hcls
  obtain ⟨σ, hσ⟩ := ClassTable.ancestorArgs_of_mem hwf o.cls o.args c.meth.owner hsub
  have hsa' : fr.selfArgs = σ := by rw [hsa]; simp [Store.argsFor, ho, hσ]
  have hfo := fieldAt_coherent hwf hlen hσ hfi'
  obtain ⟨d, f0, _, hf0, hff⟩ := ClassTable.allFieldsAt_some c.prog.classes hfi'
  obtain ⟨rest, hr'⟩ := allFields_prefix hwf hsub
  have hfo0 : (c.prog.classes.allFields o.cls)[i]? = some f0 := by
    rw [hr', List.getElem?_append_left (List.getElem?_eq_some_iff.mp hf0).1]; exact hf0
  have hname : f.name = f0.name := by rw [hff]
  have hs := hset i hij' f hfi' hr
  have hfl : i < o.fields.length := by
    rw [hflen]; exact (List.getElem?_eq_some_iff.mp hfo0).1
  refine ⟨l, o, f, i, hl, ho, fieldAt?_at hwf hown _ hfi', by rw [hname]; exact fieldIndex_at hwf hcls hfo0,
    by rw [hsa']; exact hfo, hs, fun _ => ⟨o.fields[i], by simp [hfl], ?_⟩⟩
  rw [hsa']
  exact hty i _ _ hs (by simp [hfl]) hfo

theorem Env.get_append : ∀ (Γ Δ : Env) (p : Path),
    (Γ ++ Δ).get p = match Γ.get p with
      | some t => some t
      | none => Δ.get p
  | [], _, _ => rfl
  | (q, t) :: Γ, Δ, p => by
    simp only [List.cons_append, Env.get]
    split
    · rfl
    · exact Env.get_append Γ Δ p

/-- The object made: every field set, an instance of its class. -/
theorem made_of {s : Store} {l : Nat} {o : Obj} {Λ : List Ty} (hwf : WfClasses P.classes)
    (hw : WfStore P Λ s) (ho : s.objs[l]? = some o)
    (hall : ∀ (i : Nat) (f : Field), (P.classes.allFields o.cls)[i]? = some f → o.set[i]? = some true) :
    s.hasTy P (.obj l) [.cls o.cls o.args] := by
  obtain ⟨_, _, _, hflen, hslen, _⟩ := hw.objs l o ho
  have : o.set.all id = true := all_id_iff.mpr fun i hi =>
    hall i _ (by rw [List.getElem?_eq_getElem (by omega)])
  exact hasTy_iff.mpr ⟨_, typeOf_obj_of ho this, .cls o.cls o.args, List.mem_singleton.mpr rfl,
    Atom.le_refl hwf _⟩

end QuarzCore
