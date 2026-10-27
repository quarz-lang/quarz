/-
`C.new(args)` (design §4, docs/01 §3): the fields' defaults run in order,
then `initialize`; the object is made (every field set) when `new` gives
it, and only `initialize` (and the defaults) assign its immutable fields.
-/

import QuarzCore.StepCases

set_option linter.deprecated false

namespace QuarzCore

variable {P : Program} {orc : Oracle}

/-! ### Which fields must be assigned -/

section
variable {ct : ClassTable}

/-- A class's fields: those of a class above it, then those of the
classes between. -/
theorem allFields_split (hwf : WfClasses ct) {e k : Nat} (h : e ∈ ct.ancestors k) :
    ∃ pre, ct.ancestors k = pre ++ ct.ancestors e ∧ e ∉ pre ∧
      ct.allFields k = ct.allFields e ++ (pre.reverse.filterMap (ct[·]?)).flatMap (·.fields) := by
  obtain ⟨pre, hpre, hn⟩ := ClassTable.ancestors_suffix hwf k e h
  refine ⟨pre, hpre, hn, ?_⟩
  simp [ClassTable.allFields, hpre, List.reverse_append, List.filterMap_append, List.flatMap_append]

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
  · exact absurd h (hi.1 f hf)

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
  unfold ClassTable.allFields at hf
  obtain ⟨d, hd, cl, hcl, hfc⟩ := mem_classes_fields (pre := (P.classes.ancestors k).reverse)
    (by simpa using hf)
  have hnone : P.methods.find? (fun mt => mt.owner == d && mt.name == "initialize") = none := by
    unfold Program.lookup at h
    exact List.findSome?_eq_none_iff.mp h d (List.mem_reverse.mp hd)
  exact own_not_required (hi d (List.getElem?_eq_some_iff.mp hcl).1) (ownInit_of_find hnone) hcl hfc

/-! ### The fields held before `initialize` -/

theorem zipIdx_drop_cons {α} {l : List α} {j : Nat} (h : j < l.length) :
    l.zipIdx.drop j = (l[j], j) :: l.zipIdx.drop (j + 1) := by
  rw [List.drop_eq_getElem_cons (by simpa using h), List.getElem_zipIdx]; simp

theorem zipIdx_drop_nil {α} {l : List α} {j : Nat} (h : l.length ≤ j) : l.zipIdx.drop j = [] :=
  List.drop_eq_nil_of_le (by simpa using h)

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

/-- The fields of `k` before `j` that hold a value, as an environment:
they hold it in the frame of `self`, an object of `k` or a subclass. -/
theorem sat_held (hwf : WfClasses P.classes) {c : Ctx} (hc : c.prog = P) {fr : Frame} {Λ : List Ty}
    {s : Store} (hw : WfStore P Λ s) {l : Nat} {o : Obj} (hl : fr.self = .obj l)
    (ho : s.objs[l]? = some o) (hsub : c.meth.owner ∈ P.classes.ancestors o.cls) {j : Nat}
    (hset : ∀ i, i < j → ∀ f, (P.classes.allFields c.meth.owner)[i]? = some f →
      f.required P.classes = false → o.set[i]? = some true) :
    Sat P c (Program.heldEnv P.classes ((P.classes.allFields c.meth.owner).take j)) fr s := by
  subst hc
  intro p t hp
  obtain ⟨f, hf, hr, rfl, rfl⟩ := mem_heldEnv (Env.get_mem hp)
  obtain ⟨i, hij, hfi⟩ := List.mem_take_iff_getElem.mp hf
  have hij' : i < j := by have := Nat.lt_min.mp hij; omega
  have hil : i < (c.prog.classes.allFields c.meth.owner).length := by
    have := Nat.lt_min.mp hij; omega
  have hfi' : (c.prog.classes.allFields c.meth.owner)[i]? = some f := by rw [← hfi]; simp [hil]
  obtain ⟨hcls, hflen, hslen, hty⟩ := hw.objs l o ho
  have hown : c.meth.owner < c.prog.classes.length :=
    Nat.lt_of_le_of_lt (ClassTable.ancestors_le hwf _ _ hsub) hcls
  obtain ⟨rest, hr'⟩ := allFields_prefix hwf hsub
  have hfo : (c.prog.classes.allFields o.cls)[i]? = some f := by
    rw [hr', List.getElem?_append_left hil]; exact hfi'
  have hs := hset i hij' f hfi' hr
  have hfl : i < o.fields.length := by rw [hflen]; exact (List.getElem?_eq_some_iff.mp hfo).1
  exact ⟨l, o, f, i, hl, ho, field?_at hwf hown hfi', fieldIndex_at hwf hcls hfo, hfo, hs,
    fun _ => ⟨o.fields[i], by simp [hfl], hty i _ f hs (by simp [hfl]) hfo⟩⟩

/-! ### The defaults -/

/-- The frame a field default of class `k` runs in: no locals, `self`
the object being made. -/
theorem frame_default (hwf : WfClasses P.classes) {k : Nat} {t : Ty} {Λ : List Ty} {s : Store}
    {l : Nat} {o : Obj} (hw : WfStore P Λ s) (ho : s.objs[l]? = some o) (hk : o.cls = k) :
    FrameOK P (P.defaultCtx k t) Λ ⟨[], .obj l, none⟩ s [] where
  core := {
    decls := fun x d hd => by simp [Ctx.decl, Program.defaultCtx] at hd
    inj := fun x y l h => by simp [lookupVar] at h
    inStore := fun x l h => by simp at h
    self := fun h => by simp [Ctx.inInit, Program.defaultCtx] at h
    selfInit := fun _ => ⟨l, o, rfl, ho, by
        show k ∈ P.classes.ancestors o.cls
        rw [hk]; exact ClassTable.mem_ancestors_self hwf k, fun i h1 h2 => by
        obtain ⟨_, hflen, hslen, _⟩ := hw.objs l o ho
        have : (P.classes.allFields k).length ≤ i := h1
        rw [← hk] at this; omega⟩
    selfObj := ⟨l, rfl⟩ }
  chain := by simp [ChainAt, Program.defaultCtx]
  above := fun _ _ _ h => by simp [chainLocs] at h
  chainIn := fun _ h => by simp [chainLocs] at h
  initBlk := fun _ h => by simp [Program.defaultCtx] at h

variable (P) in
/-- What running the defaults gives: never stuck; every field of `k` not
to be assigned in `initialize` set; no location written, and no immutable
field but the object's. -/
def DefaultsPost (l k : Nat) (Λ : List Ty) (s : Store) : Result → Prop
  | .ok _ s' => ∃ Λ', WfStore P Λ' s' ∧ Ext P (fun _ => False) (· = l) Λ Λ' s s' ∧
      ∃ o', s'.objs[l]? = some o' ∧ ∀ (i : Nat) (f : Field), (P.classes.allFields k)[i]? = some f →
        f.required P.classes = false → o'.set[i]? = some true
  | .stuck | .returned _ _ => False
  | _ => True

theorem defaults_good (hP : WfProg P) {N : Nat} (ihs : ∀ m, m ≤ N → Good P orc m) {k l : Nat}
    (hk : k < P.classes.length) :
    ∀ (n : Nat), n ≤ N → ∀ (j : Nat) (s : Store) (Λ : List Ty) (o : Obj), WfStore P Λ s →
      s.objs[l]? = some o → o.cls = k →
      (∀ i f, (P.classes.allFields k)[i]? = some f → f.required P.classes = false →
        (i < j ∨ f.default = none) → o.set[i]? = some true) →
      DefaultsPost P l k Λ s (runDefaults P orc n s l ((P.classes.allFields k).zipIdx.drop j)) := by
  have hwf := hP.classes
  intro n
  induction n with
  | zero =>
    intro _ j s Λ o hw ho hc hinv
    by_cases hj : j < (P.classes.allFields k).length
    · rw [zipIdx_drop_cons hj]; simp only [runDefaults]; exact trivial
    · rw [zipIdx_drop_nil (by omega)]
      simp only [runDefaults]
      exact ⟨Λ, hw, Ext.refl _ _ Λ s, o, ho, fun i f hf hr =>
        hinv i f hf hr (.inl (by have := (List.getElem?_eq_some_iff.mp hf).1; omega))⟩
  | succ n ih =>
    intro hn j s Λ o hw ho hc hinv
    by_cases hj : j < (P.classes.allFields k).length
    · rw [zipIdx_drop_cons hj]
      have hfj : (P.classes.allFields k)[j]? = some (P.classes.allFields k)[j] := by simp [hj]
      generalize (P.classes.allFields k)[j] = f at hfj
      simp only [runDefaults]
      cases hd : f.default with
      | none =>
        dsimp only
        refine ih (by omega) (j + 1) s Λ o hw ho hc fun i g hg hr hor => hinv i g hg hr ?_
        rcases hor with h | h
        · by_cases hij : i = j
          · subst hij; rw [hfj] at hg; cases hg; exact .inr hd
          · exact .inl (by omega)
        · exact .inr h
      | some d =>
        dsimp only
        obtain ⟨e, oT, he, hty, hle⟩ := hP.defaults k hk j f d hfj hd
        rw [he]; dsimp only
        have hf0 := frame_default (t := f.ty) hwf hw ho hc
        have hs0 : Sat P (P.defaultCtx k f.ty)
            (Program.heldEnv P.classes ((P.classes.allFields k).take j)) ⟨[], .obj l, none⟩ s :=
          sat_held hwf rfl hw rfl ho (by rw [hc]; exact ClassTable.mem_ancestors_self hwf k)
            fun i hi g hg hr => hinv i g hg hr (.inl hi)
        have := (ihs n (by omega)).eval _ _ e oT ⟨[], .obj l, none⟩ s Λ [] rfl hty hw hf0 hs0
        revert this
        generalize eval P orc n ⟨[], .obj l, none⟩ s e = r
        intro this
        cases r with
        | ok v s1 =>
          obtain ⟨Λ1, hw1, he1, _, hv1, _⟩ := this
          simp only [Result.bind]
          obtain ⟨o1, ho1, hc1, hl1, hs1⟩ := he1.grow l o ho
          have hfi : (P.classes.allFields o1.cls)[j]? = some f := by rw [hc1, hc]; exact hfj
          have hvf : s1.hasTy P v f.ty := hasTy_le hwf hv1 hle
          have he2 : Ext P (fun _ => False) (· = l) Λ1 Λ1 s1 (s1.setField l j v) :=
            Ext.setField ho1 hfi fun _ => rfl
          have ho2 : (s1.setField l j v).objs[l]? =
              some { o1 with fields := o1.fields.set j v, set := o1.set.set j true } := by
            rw [Store.setField_objs, if_pos rfl, ho1]; rfl
          have hjs : j < o1.set.length := by
            obtain ⟨_, hflen, hslen, _⟩ := hw1.objs l o1 ho1
            rw [hc1, hc] at hflen; omega
          have hrest := ih (by omega) (j + 1) (s1.setField l j v) Λ1 _ (hw1.setField ho1 hfi hvf) ho2
            (by simp [hc1, hc]) fun i g hg hr hor => by
              by_cases hij : i = j
              · subst hij; simp [hjs]
              · show (o1.set.set j true)[i]? = some true
                rw [List.getElem?_set_ne (Ne.symm hij)]
                refine hs1 i (hinv i g hg hr ?_)
                rcases hor with h | h
                · exact .inl (by omega)
                · exact .inr h
          revert hrest
          generalize runDefaults P orc n (s1.setField l j v) l _ = r2
          intro hrest
          cases r2 with
          | ok w s3 =>
            obtain ⟨Λ3, hw3, he3, rest⟩ := hrest
            -- The default writes no location (it has none), nor any immutable field.
            have he1' : Ext P (fun _ => False) (· = l) Λ Λ1 s s1 := he1.mono
              (fun _ h => by rcases h with ⟨_, _, h⟩ | h <;> simp [lookupVar, blkW] at h)
              (fun _ ⟨_, hb, _⟩ => by simp [Program.defaultCtx] at hb)
            exact ⟨Λ3, hw3, ((he1'.transW he2 hw).transW he3 hw).mono (fun _ h => by simp_all)
              (fun _ h => h), rest⟩
          | stuck => exact (hrest : False).elim
          | returned => exact (hrest : False).elim
          | raised => exact trivial
          | timeout => exact trivial
        | returned v s1 =>
          obtain ⟨_, _, _, _, _, hib, _⟩ := this
          simp [Program.defaultCtx] at hib
        | stuck => exact (this : False).elim
        | raised => exact trivial
        | timeout => exact trivial
    · rw [zipIdx_drop_nil (by omega)]
      simp only [runDefaults]
      exact ⟨Λ, hw, Ext.refl _ _ Λ s, o, ho, fun i f hf hr =>
        hinv i f hf hr (.inl (by have := (List.getElem?_eq_some_iff.mp hf).1; omega))⟩

/-! ### `new` -/

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
    s.hasTy P (.obj l) [.cls o.cls] := by
  obtain ⟨_, hflen, hslen, _⟩ := hw.objs l o ho
  have : o.set.all id = true := all_id_iff.mpr fun i hi =>
    hall i _ (by rw [List.getElem?_eq_getElem (by omega)])
  exact hasTy_iff.mpr ⟨_, typeOf_obj_of ho this, .cls o.cls, List.mem_singleton.mpr rfl,
    Atom.le_refl hwf _⟩

theorem construct_succ (hP : WfProg P) {n : Nat} (ihs : ∀ m, m ≤ n → Good P orc m) :
    ConstructGood P orc (n + 1) := by
  intro s Λ k vs hw hk hinit hnone
  have hwf := hP.classes
  simp only [construct]
  -- The new object: a field that admits `nil` and has no default holds it.
  generalize hfs : P.classes.allFields k = fs
  let o0 : Obj := ⟨k, fs.map fun _ => .nil, fs.map fun f => f.default.isNone && Ty.le P.classes [.nil] f.ty⟩
  let l := s.objs.length
  have ho1 : ({ s with objs := s.objs ++ [o0] } : Store).objs[l]? = some o0 := by simp [l]
  have hw1 : WfStore P Λ { s with objs := s.objs ++ [o0] } := ⟨hw.len, fun l' o ho => by
    by_cases hl : l' < s.objs.length
    · rw [show ({ s with objs := s.objs ++ [o0] } : Store).objs = s.objs ++ [o0] from rfl,
        List.getElem?_append_left hl] at ho
      obtain ⟨a, b, b2, d⟩ := hw.objs l' o ho
      exact ⟨a, b, b2, fun i v f h0 h1 h2 => hasTy_mono (objs_append_mono _) (d i v f h0 h1 h2)⟩
    · have hl' : l' = s.objs.length := by
        have := (List.getElem?_eq_some_iff.mp ho).1
        simp at this; omega
      subst hl'
      simp at ho; subst ho
      refine ⟨hk, by simp [o0, hfs], by simp [o0], fun i v f h0 h1 h2 => ?_⟩
      simp only [o0, List.getElem?_map, Option.map_eq_some_iff] at h0 h1
      obtain ⟨f', hf', hv⟩ := h1
      obtain ⟨f'', hf'', hset⟩ := h0
      rw [hf'] at hf''; cases hf''
      have h2' : fs[i]? = some f := by rw [← hfs]; exact h2
      rw [hf'] at h2'; cases h2'; subst hv
      simp only [Bool.and_eq_true] at hset
      obtain ⟨b, hb, hnb⟩ := Ty.le_iff.mp hset.2 .nil (List.mem_singleton.mpr rfl)
      exact hasTy_iff.mpr ⟨.nil, rfl, b, hb, hnb⟩⟩
  have he1 : Ext P (fun _ => False) (fun _ => False) Λ Λ s { s with objs := s.objs ++ [o0] } :=
    Ext.newObj _
  have hd := defaults_good (orc := orc) (k := k) hP ihs hk n (Nat.le_refl n) 0 _ Λ o0 hw1 ho1 rfl
    fun i f hf hr hor => by
      rcases hor with h | h
      · omega
      · simp only [o0, ← hfs, List.getElem?_map, hf, Option.map_some, h, Option.isNone_none,
          Bool.true_and]
        simp only [Field.required, h, Option.isNone_none, Bool.true_and, Bool.not_eq_false'] at hr
        rw [hr]
  rw [List.drop_zero, hfs] at hd
  revert hd
  generalize runDefaults P orc n _ l fs.zipIdx = r
  intro hd
  cases r with
  | ok _ s2 =>
    obtain ⟨Λ2, hw2, he2, o2, ho2, hset2⟩ := hd
    obtain ⟨o2', ho2', hc2, _, _⟩ := he2.grow l o0 ho1
    rw [ho2] at ho2'; cases ho2'
    have hc2 : o2.cls = k := hc2
    have hset2 : ∀ (i : Nat) (f : Field), (P.classes.allFields k)[i]? = some f →
        f.required P.classes = false → o2.set[i]? = some true := hset2
    have he12 : Ext P (fun _ => False) (· = l) Λ Λ2 s s2 :=
      (he1.trans he2 hw).mono (fun _ h => h.elim False.elim False.elim) (fun _ h => h.elim False.elim id)
    -- No location of `s` written, only the new object's fields.
    have hfresh : ∀ {W : Nat → Prop} {Λ' : List Ty} {s' : Store}, Ext P W (· = l) Λ Λ' s s' →
        (∀ l', l' < s.locs.length → W l' → False) → Ext P (fun _ => False) (fun _ => False) Λ Λ' s s' :=
      fun h hr => (h.restrict hr).fresh fun _ h => by rw [h]; exact Nat.le_refl _
    cases hl : P.lookup k "initialize" with
    | none =>
      dsimp only
      rw [hnone hl]
      simp only [List.isEmpty_nil, if_true]
      refine ⟨Λ2, hw2, hfresh he12 (fun _ _ h => h), ?_⟩
      have := made_of hwf hw2 ho2 fun i f hf => hset2 i f (by rw [hc2] at hf; exact hf)
        (no_init_fields hP.inits hl f (by rw [hc2] at hf; exact List.mem_of_getElem? hf))
      rwa [hc2] at this
    | some mi =>
      dsimp only
      obtain ⟨hblk, hvs⟩ := hinit mi hl
      have hvs2 : AllTy P s2 vs (mi.params.map (·.2)) := hvs.mono he12.grow
      obtain ⟨hmem', howner, hname'⟩ := Program.lookup_spec hl
      obtain ⟨hwfm, oB, hty, hout, hallset⟩ := hP.methods mi hmem'
      have hni : (mi.name == "initialize") = true := by simp [hname']
      have hinInit : (⟨P, mi, false⟩ : Ctx).inInit = true := hni
      rw [hni] at hty
      simp only [if_true] at hty
      have hlen' : vs.length = mi.params.length := by rw [hvs.length]; simp
      rw [if_neg (by simp [hlen'])]
      simp only [Store.alloc]
      -- The frame: `initialize`'s locals at fresh locations (as `send_succ`).
      have hwfm' := hwfm
      simp only [Program.wfMethod, Bool.and_eq_true, decide_eq_true_eq] at hwfm'
      obtain ⟨⟨⟨⟨⟨_, hplen⟩, hnd⟩, hpre⟩, _⟩, _⟩ := hwfm'
      have hcl : ∀ x d, (⟨P, mi, false⟩ : Ctx).decl x = some d →
          ∃ j, mi.locals[j]? = some (x, d) := fun x d hd => by
        simp only [Ctx.decl, Option.map_eq_some_iff] at hd
        obtain ⟨⟨y, d'⟩, hf, hd'⟩ := hd
        simp at hd'; subst hd'
        have hp := List.find?_some hf
        simp at hp; subst hp
        exact List.mem_iff_getElem?.mp (List.mem_of_find?_eq_some hf)
      have hlookj : ∀ j x d, mi.locals[j]? = some (x, d) →
          lookupVar (Store.allocVars s2.locs.length (mi.locals.map (·.1))) x = some (s2.locs.length + j) :=
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
          ∃ l, lookupVar (Store.allocVars s2.locs.length (mi.locals.map (·.1))) x = some l := by
        intro x hx
        obtain ⟨⟨y, t⟩, hm, rfl⟩ := List.mem_map.mp hx
        obtain ⟨j, hj⟩ := hcl y t (decl_param hwfm hm)
        exact ⟨_, hlookj j y t hj⟩
      obtain ⟨s3, hb⟩ := bindAll_some (vars := Store.allocVars s2.locs.length (mi.locals.map (·.1)))
        ⟨s2.locs ++ (mi.locals.map (·.1)).map fun _ => .nil, s2.objs⟩ (by rw [List.length_map, hlen'])
        hexists
      simp only [hb]
      obtain ⟨hobjs, hlen3, hsame⟩ := bindAll_same hb
      simp only [List.length_append, List.length_map] at hlen3
      have hge : ∀ x l', lookupVar (Store.allocVars s2.locs.length (mi.locals.map (·.1))) x = some l' →
          s2.locs.length ≤ l' ∧ l' < s2.locs.length + mi.locals.length := fun x l' h => by
        have := mem_allocVars (lookupVar_mem h); simpa using this
      have mono : ∀ {v : Value} {t : Ty}, s2.hasTy P v t → s3.hasTy P v t := fun h => by
        unfold Store.hasTy Store.hasType Store.typeOf at *; rw [hobjs]; exact h
      have he23 : Ext P (fun _ => False) (fun _ => False) Λ2 (Λ2 ++ mi.locals.map (·.2)) s2 s3 := by
        refine ⟨List.prefix_append _ _, fun l' v hv => ⟨v, ?_, .inl rfl⟩, fun l' o' ho' =>
          ⟨o', by rw [hobjs]; exact ho', rfl, rfl, fun _ h => h⟩,
          fun _ o1 o2 h1 h2 _ _ _ _ _ => by rw [hobjs, h1] at h2; cases h2; rfl⟩
        have hl' := (List.getElem?_eq_some_iff.mp hv).1
        rw [hsame l' fun x _ hx => by have := (hge x l' hx).1; omega]
        simp [List.getElem?_append_left hl', hv]
      have hw3 : WfStore P (Λ2 ++ mi.locals.map (·.2)) s3 :=
        ⟨by simp [hw2.len, hlen3], fun l' o' ho' => by
          rw [hobjs] at ho'
          obtain ⟨a, b, b2, d⟩ := hw2.objs l' o' ho'
          exact ⟨a, b, b2, fun i v f h0 h1 h2 => mono (d i v f h0 h1 h2)⟩⟩
      have ho3 : s3.objs[l]? = some o2 := by rw [hobjs]; exact ho2
      have hsub : mi.owner ∈ P.classes.ancestors o2.cls := by rw [hc2]; exact howner
      obtain ⟨rest, hrest, hrestnr⟩ := init_beyond hwf hP.inits hl
      have hcore : FrameCore P ⟨P, mi, false⟩ (Λ2 ++ mi.locals.map (·.2))
          (Store.allocVars s2.locs.length (mi.locals.map (·.1))) (.obj l) s3 := by
        refine ⟨fun x d hd => ?_, fun x y l' hx hy => ?_, fun x l' hm => ?_,
          fun h => (by rw [hinInit] at h; cases h), fun _ => ⟨l, o2, rfl, ho3, hsub, fun i h1 h2 => ?_⟩,
          ⟨l, rfl⟩⟩
        · obtain ⟨j, hj⟩ := hcl x d hd
          refine ⟨_, hlookj j x d hj, ?_⟩
          have hjl := (List.getElem?_eq_some_iff.mp hj).1
          rw [List.getElem?_append_right (by rw [hw2.len]; omega)]
          simp [hw2.len, hj]
        · obtain ⟨jx, hjx, rfl⟩ := lookupVar_alloc_inv hx
          obtain ⟨jy, hjy, hjj⟩ := lookupVar_alloc_inv hy
          have : jx = jy := by omega
          subst this; rw [hjx] at hjy; cases hjy; rfl
        · have := mem_allocVars hm; simp [hlen3] at this ⊢; omega
        · -- A field past `initialize`'s class: not to be assigned, so set.
          obtain ⟨_, hflen, hslen, _⟩ := hw2.objs l o2 ho2
          rw [hc2] at hflen
          have hi : i < (P.classes.allFields k).length := by omega
          have hfi : (P.classes.allFields k)[i]? = some (P.classes.allFields k)[i] := by simp [hi]
          refine hset2 i _ hfi (hrestnr _ ?_)
          have : (P.classes.allFields k)[i]? = rest[i - (P.classes.allFields mi.owner).length]? := by
            rw [hrest, List.getElem?_append_right h1]
          rw [hfi] at this
          exact List.mem_of_getElem? this.symm
      have hf3 : FrameOK P ⟨P, mi, false⟩ (Λ2 ++ mi.locals.map (·.2))
          ⟨Store.allocVars s2.locs.length (mi.locals.map (·.1)), .obj l, none⟩ s3 [] :=
        ⟨hcore, by simp [ChainAt, hblk], fun _ _ _ h => by simp [chainLocs] at h,
          fun _ h => by simp [chainLocs] at h, fun _ _ => rfl⟩
      have hs3 : Sat P ⟨P, mi, false⟩ (mi.params.map (fun (x, t) => (.local x, t)) ++
          Program.heldEnv P.classes (P.classes.allFields mi.owner))
          ⟨Store.allocVars s2.locs.length (mi.locals.map (·.1)), .obj l, none⟩ s3 := by
        intro p t hp
        rw [Env.get_append] at hp
        split at hp
        · cases hp
          rename_i hp
          obtain ⟨x, rfl, hm⟩ := params_get hp
          have hd := decl_param hwfm hm
          obtain ⟨v, hvm, hvt⟩ := zip_val hvs2 x t (by rw [zip_fst_snd]; exact hm)
          obtain ⟨lx, hlx, hv⟩ := bindAll_val hcore.inj hb hpnd
            (fun y _ l' hl' => by have := hge y l' hl'; simp; omega) x v hvm
          exact ⟨lx, v, t, hlx, hv, hd, mono hvt, mono hvt⟩
        · have := sat_held (c := ⟨P, mi, false⟩) (j := (P.classes.allFields mi.owner).length) hwf rfl
            hw3 (fr := ⟨Store.allocVars s2.locs.length (mi.locals.map (·.1)), .obj l, none⟩) rfl ho3 hsub
            (fun i hi f hf hr => hset2 i f (by
              rw [hrest, List.getElem?_append_left hi]; exact hf) hr)
          rw [List.take_length] at this
          exact this p t hp
      have := (ihs n (Nat.le_refl n)).eval ⟨P, mi, false⟩ _ mi.body oB _ s3 _ [] rfl hty hw3 hf3 hs3
      revert this
      generalize eval P orc n _ s3 mi.body = r
      intro this
      have hrestrict : ∀ l', l' < s.locs.length →
          (((False ∨ False) ∨ evalW ⟨Store.allocVars s2.locs.length (mi.locals.map (·.1)), .obj l, none⟩
            mi.body l')) → False := by
        rintro l' hl' ((h | h) | ⟨x, _, hx⟩ | h)
        · exact h
        · exact h
        · have := (hge x l' hx).1
          have := he12.len hl'
          omega
        · simp [blkW] at h
      have hWo : ∀ l', initW ⟨P, mi, false⟩
          ⟨Store.allocVars s2.locs.length (mi.locals.map (·.1)), .obj l, none⟩ l' → l' = l :=
        fun _ ⟨_, _, h⟩ => by cases h; rfl
      -- What `new` gives: the object, made.
      have hfin : ∀ {Λ4 : List Ty} {s4 : Store}, WfStore P Λ4 s4 →
          Ext P (evalW ⟨Store.allocVars s2.locs.length (mi.locals.map (·.1)), .obj l, none⟩ mi.body)
            (initW ⟨P, mi, false⟩ ⟨Store.allocVars s2.locs.length (mi.locals.map (·.1)), .obj l, none⟩)
            (Λ2 ++ mi.locals.map (·.2)) Λ4 s3 s4 →
          (s4.typeOf (.obj l)).isSome = true → ConstructPost P k Λ s (.ok (.obj l) s4) := by
        intro Λ4 s4 hw4 he4 hmade
        refine ⟨Λ4, hw4, hfresh (((he12.trans he23 hw).trans he4 (by exact hw)).mono (fun _ h => h)
          (fun l' h => by
            rcases h with (h | h) | h
            · exact h
            · exact h.elim
            · exact hWo l' h)) hrestrict, ?_⟩
        obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hmade
        obtain ⟨o4, ho4, _, rfl⟩ := typeOf_obj ha
        obtain ⟨o4', ho4', hc4, _, _⟩ := ((he23.trans he4 hw2)).grow l o2 ho2
        rw [ho4] at ho4'; cases ho4'
        refine hasTy_iff.mpr ⟨_, ha, .cls k, List.mem_singleton.mpr rfl, ?_⟩
        rw [hc4, hc2]; exact Atom.le_refl hwf _
      cases r with
      | ok v s4 =>
        obtain ⟨Λ4, hw4, he4, hf4, _, ⟨Γ4, hΓ4, hs4⟩, _⟩ := this
        refine hfin hw4 he4 ?_
        have hset := hallset hname'
        rw [hΓ4] at hset
        have := self_typed hwf rfl hf4 hw4 hs4 (by simpa [hinInit] using hset)
        obtain ⟨_, ha, _⟩ := hasTy_iff.mp this
        simp [ha]
      | returned v s4 =>
        obtain ⟨Λ4, hw4, he4, _, _, _, hmade⟩ := this
        exact hfin hw4 he4 (hmade hinInit)
      | stuck => exact (this : False).elim
      | raised => exact trivial
      | timeout => exact trivial
  | stuck => exact (hd : False).elim
  | returned => exact (hd : False).elim
  | raised => exact trivial
  | timeout => exact trivial

end QuarzCore
