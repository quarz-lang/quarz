/-
`C.new(args)` (design §4, docs/01 §3): the fields' defaults run in order,
then `initialize`; the object is made (every field set) when `new` gives
it, and only `initialize` (and the defaults) assign its immutable fields.
-/

import QuarzCore.StepCases

set_option linter.deprecated false

namespace QuarzCore

variable {P : Program} {orc : Oracle}

/-! ### The fields held before `initialize` -/

theorem zipIdx_drop_cons {α} {l : List α} {j : Nat} (h : j < l.length) :
    l.zipIdx.drop j = (l[j], j) :: l.zipIdx.drop (j + 1) := by
  rw [List.drop_eq_getElem_cons (by simpa using h), List.getElem_zipIdx]; simp

theorem zipIdx_drop_nil {α} {l : List α} {j : Nat} (h : l.length ≤ j) : l.zipIdx.drop j = [] :=
  List.drop_eq_nil_of_le (by simpa using h)

/-! ### The defaults -/

/-- The frame a field default of class `k` runs in: no locals, `self`
the object being made, its arguments the frame's. -/
theorem frame_default (hwf : WfClasses P.classes) {k : Nat} {t : Ty} {Λ : List Ty} {s : Store}
    {l : Nat} {o : Obj} (hw : WfStore P Λ s) (ho : s.objs[l]? = some o) (hk : o.cls = k)
    (hheld : ∀ (i : Nat) (f : Field), (P.classes.allFieldsAt o.cls o.args)[i]? = some f →
      f.default = none → f.required P.classes = false → o.set[i]? = some true) :
    FrameOK P (P.defaultCtx k t) Λ ⟨[], .obj l, o.args, none⟩ s [] where
  core := {
    decls := fun x d hd => by simp [Ctx.decl, Program.defaultCtx] at hd
    inj := fun x y l h => by simp [lookupVar] at h
    inStore := fun x l h => by simp at h
    pins := fun x l h => by simp [lookupVar] at h
    pinsIn := fun x l h => by simp [lookupVar] at h
    self := fun h => by simp [Ctx.inInit, Program.defaultCtx] at h
    selfInit := fun _ => ⟨l, o, rfl, ho, by
        show k ∈ P.classes.ancestors o.cls
        rw [hk]; exact ClassTable.mem_ancestors_self hwf k, fun i h1 h2 => by
        obtain ⟨_, _, _, hflen, hslen, _⟩ := hw.objs l o ho
        have : (P.classes.allFields k).length ≤ i := h1
        rw [← hk] at this; omega, hheld⟩
    selfObj := ⟨l, rfl, by
      show o.args = s.argsFor P.classes l k
      rw [← hk]; simp [Store.argsFor, ho, ClassTable.ancestorArgs_self hwf]⟩
    closed := (hw.objs l o ho).2.1
    bounded := by
      show ArgsIn P.classes (P.classes.boundsOf k) o.args
      rw [← hk]; exact hw.bounds l o ho }
  chain := by simp [ChainAt, Program.defaultCtx]
  above := fun _ _ _ h => by simp [chainLocs] at h
  chainIn := fun _ h => by simp [chainLocs] at h
  initBlk := fun _ h => by simp [Program.defaultCtx] at h

variable (P) in
/-- What running the defaults gives: never stuck; every field of `k`
given `targs` not to be assigned in `initialize` set; no location
written, and no immutable field but the object's. -/
def DefaultsPost (l k : Nat) (targs : List Ty) (Λ : List Ty) (s : Store) : Result → Prop
  | .ok _ s' => ∃ Λ', WfStore P Λ' s' ∧ Ext P (fun _ => False) (· = l) Λ Λ' s s' ∧
      ∃ o', s'.objs[l]? = some o' ∧
        ∀ (i : Nat) (f : Field), (P.classes.allFieldsAt k targs)[i]? = some f →
          f.required P.classes = false → o'.set[i]? = some true
  | .raised v s' => ∃ Λ', WfStore P Λ' s' ∧ Ext P (fun _ => False) (· = l) Λ Λ' s s' ∧
      s'.hasTy P v [.cls P.exn []]
  | .stuck | .returned _ _ => False
  | _ => True

theorem defaults_good (hP : WfProg P) {N : Nat} (ihs : ∀ m, m ≤ N → Good P orc m) {k l : Nat}
    {targs : List Ty} (hk : k < P.classes.length) :
    ∀ (n : Nat), n ≤ N → ∀ (j : Nat) (s : Store) (Λ : List Ty) (o : Obj), WfStore P Λ s →
      s.objs[l]? = some o → o.cls = k → o.args = targs →
      (∀ i f, (P.classes.allFieldsAt k targs)[i]? = some f → f.required P.classes = false →
        (i < j ∨ f.default = none) → o.set[i]? = some true) →
      DefaultsPost P l k targs Λ s
        (runDefaults P orc n s l ((P.classes.allFieldsAt k targs).zipIdx.drop j)) := by
  have hwf := hP.classes
  intro n
  induction n with
  | zero =>
    intro _ j s Λ o hw ho hc ha hinv
    by_cases hj : j < (P.classes.allFieldsAt k targs).length
    · rw [zipIdx_drop_cons hj]; simp only [runDefaults]; exact trivial
    · rw [zipIdx_drop_nil (by omega)]
      simp only [runDefaults]
      exact ⟨Λ, hw, Ext.refl _ _ Λ s, o, ho, fun i f hf hr =>
        hinv i f hf hr (.inl (by have := (List.getElem?_eq_some_iff.mp hf).1; omega))⟩
  | succ n ih =>
    intro hn j s Λ o hw ho hc ha hinv
    by_cases hj : j < (P.classes.allFieldsAt k targs).length
    · rw [zipIdx_drop_cons hj]
      have hfj : (P.classes.allFieldsAt k targs)[j]? = some (P.classes.allFieldsAt k targs)[j] := by
        simp [hj]
      generalize (P.classes.allFieldsAt k targs)[j] = f at hfj
      simp only [runDefaults]
      cases hd : f.default with
      | none =>
        dsimp only
        refine ih (by omega) (j + 1) s Λ o hw ho hc ha fun i g hg hr hor => hinv i g hg hr ?_
        rcases hor with h | h
        · by_cases hij : i = j
          · subst hij; rw [hfj] at hg; cases hg; exact .inr hd
          · exact .inl (by omega)
        · exact .inr h
      | some d =>
        dsimp only
        obtain ⟨_, _, hlen, hflen, hslen, _⟩ := hw.objs l o ho
        rw [hc, ha] at hlen
        -- The field as the class sees it, whose default was checked.
        obtain ⟨f', hf', rfl⟩ := fieldAt_of_static hwf hlen hfj
        obtain ⟨e, oT, he, hty, hle⟩ := hP.defaults k hk j f' d hf' hd
        rw [he]; dsimp only
        have hfr : s.argsFor P.classes l (((s.objs[l]?).map (·.cls)).getD 0) = o.args := by
          simp [ho, hc, Store.argsFor, ClassTable.ancestorArgs_self hwf]
        rw [hfr]
        have hf0 := frame_default (t := f'.ty) hwf hw ho hc fun i g hg hgd hr =>
          hinv i g (by rw [hc, ha] at hg; exact hg) hr (.inr hgd)
        have hs0 : Sat P (P.defaultCtx k f'.ty)
            (Program.heldEnv P.classes ((P.classes.allFieldsAt k (P.classes.selfArgs k)).take j))
            ⟨[], .obj l, o.args, none⟩ s :=
          sat_held hwf rfl hw rfl ho (by rw [hc]; exact ClassTable.mem_ancestors_self hwf k)
            (by show o.args = s.argsFor P.classes l k
                simp [ho, hc, Store.argsFor, ClassTable.ancestorArgs_self hwf])
            fun i hi g hg hr =>
              hinv i _ (fieldAt_coherent hwf hlen (ClassTable.ancestorArgs_self hwf k targs) hg)
                (required_subst hwf targs hr) (.inl hi)
        have := (ihs n (by omega)).eval _ _ e oT ⟨[], .obj l, o.args, none⟩ s Λ [] rfl hty hw hf0 hs0
        revert this
        generalize eval P orc n ⟨[], .obj l, o.args, none⟩ s e = r
        intro this
        cases r with
        | ok v s1 =>
          obtain ⟨Λ1, hw1, he1, _, hv1, _⟩ := this
          simp only [Result.bind]
          obtain ⟨o1, ho1, hc1, ha1, hl1, hs1⟩ := he1.grow l o ho
          obtain ⟨_, f0, _, hf0, _⟩ := ClassTable.allFieldsAt_some P.classes hfj
          have hfi : (P.classes.allFields o1.cls)[j]? = some f0 := by rw [hc1, hc]; exact hf0
          have hfi' : (P.classes.allFieldsAt o1.cls o1.args)[j]? =
              some { f' with ty := f'.ty.subst targs } := by rw [hc1, ha1, hc, ha]; exact hfj
          have hvf : s1.hasTy P v (f'.ty.subst targs) := by
            have hin : ArgsIn P.classes (P.classes.boundsOf k) targs := by
              rw [← hc, ← ha]; exact hw.bounds l o ho
            rw [ha] at hv1; exact hasTy_le hwf hv1 (Ty.subst_leK hwf targs hin hle)
          have he2 : Ext P (fun _ => False) (· = l) Λ1 Λ1 s1 (s1.setField l j v) :=
            Ext.setField ho1 hfi fun _ => rfl
          have ho2 : (s1.setField l j v).objs[l]? =
              some { o1 with fields := o1.fields.set j v, set := o1.set.set j true } := by
            rw [Store.setField_objs, if_pos rfl, ho1]; rfl
          have hjs : j < o1.set.length := by
            obtain ⟨_, _, _, hflen, hslen, _⟩ := hw1.objs l o1 ho1
            rw [hc1, hc] at hflen
            rw [ClassTable.allFieldsAt_length] at hj; omega
          have hrest := ih (by omega) (j + 1) (s1.setField l j v) Λ1 _ (hw1.setField ho1 hfi' hvf) ho2
            (by simp [hc1, hc]) (by simp [ha1, ha]) fun i g hg hr hor => by
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
          | raised w s3 =>
            obtain ⟨Λ3, hw3, he3, hv3⟩ := hrest
            have he1' : Ext P (fun _ => False) (· = l) Λ Λ1 s s1 := he1.mono
              (fun _ h => by rcases h with ⟨_, _, h⟩ | h <;> simp [lookupVar, blkW] at h)
              (fun _ ⟨_, hb, _⟩ => by simp [Program.defaultCtx] at hb)
            exact ⟨Λ3, hw3, ((he1'.transW he2 hw).transW he3 hw).mono (fun _ h => by simp_all)
              (fun _ h => h), hv3⟩
          | timeout => exact trivial
        | returned v s1 =>
          obtain ⟨_, _, _, _, _, hib, _⟩ := this
          simp [Program.defaultCtx] at hib
        | stuck => exact (this : False).elim
        | raised v s1 =>
          obtain ⟨Λ1, hw1, he1, _, hv1⟩ := this
          exact ⟨Λ1, hw1, he1.mono
              (fun _ h => by rcases h with ⟨_, _, h⟩ | h <;> simp [lookupVar, blkW] at h)
              (fun _ ⟨_, hb, _⟩ => by simp [Program.defaultCtx] at hb), hv1⟩
        | timeout => exact trivial
    · rw [zipIdx_drop_nil (by omega)]
      simp only [runDefaults]
      exact ⟨Λ, hw, Ext.refl _ _ Λ s, o, ho, fun i f hf hr =>
        hinv i f hf hr (.inl (by have := (List.getElem?_eq_some_iff.mp hf).1; omega))⟩

/-! ### `new` -/

theorem construct_succ (hP : WfProg P) {n : Nat} (ihs : ∀ m, m ≤ n → Good P orc m) :
    ConstructGood P orc (n + 1) := by
  intro s Λ k targs vs hw hk hclosed hlen hin hne hinit hnone
  have hwf := hP.classes
  simp only [construct]
  -- The new object: a field that admits `nil` and has no default holds it.
  generalize hfs : P.classes.allFieldsAt k targs = fs
  let o0 : Obj := ⟨k, targs, fs.map fun _ => .nil,
    fs.map fun f => f.default.isNone && Ty.le P.classes [] [.nil] f.ty⟩
  let l := s.objs.length
  have ho1 : ({ s with objs := s.objs ++ [o0] } : Store).objs[l]? = some o0 := by simp [l]
  have hfslen : fs.length = (P.classes.allFields k).length := by
    rw [← hfs, ClassTable.allFieldsAt_length]
  have hw1 : WfStore P Λ { s with objs := s.objs ++ [o0] } := ⟨hw.len, hw.pinsLen, fun l' o ho => by
    by_cases hl : l' < s.objs.length
    · rw [show ({ s with objs := s.objs ++ [o0] } : Store).objs = s.objs ++ [o0] from rfl,
        List.getElem?_append_left hl] at ho
      obtain ⟨a, a1, a2, b, b2, d⟩ := hw.objs l' o ho
      exact ⟨a, a1, a2, b, b2, fun i v f h0 h1 h2 => hasTy_mono (objs_append_mono _) (List.prefix_refl _) (d i v f h0 h1 h2)⟩
    · have hl' : l' = s.objs.length := by
        have := (List.getElem?_eq_some_iff.mp ho).1
        simp at this; omega
      subst hl'
      simp at ho; subst ho
      refine ⟨hk, hclosed, hlen, by simp [o0, hfslen], by simp [o0], fun i v f h0 h1 h2 => ?_⟩
      simp only [o0, List.getElem?_map, Option.map_eq_some_iff] at h0 h1
      obtain ⟨f', hf', hv⟩ := h1
      obtain ⟨f'', hf'', hset⟩ := h0
      rw [hf'] at hf''; cases hf''
      have h2' : fs[i]? = some f := by rw [← hfs]; exact h2
      rw [hf'] at h2'; cases h2'; subst hv
      simp only [Bool.and_eq_true] at hset
      obtain ⟨b, hb, hnb⟩ := Ty.le_iff.mp hset.2 .nil (List.mem_singleton.mpr rfl)
      exact hasTy_iff.mpr ⟨.nil, rfl, b, hb, hnb⟩,
    fun l' o ho => by
      by_cases hl : l' < s.objs.length
      · rw [show ({ s with objs := s.objs ++ [o0] } : Store).objs = s.objs ++ [o0] from rfl,
          List.getElem?_append_left hl] at ho
        exact hw.noEnum l' o ho
      · have hl' : l' = s.objs.length := by
          have := (List.getElem?_eq_some_iff.mp ho).1
          simp at this; omega
        subst hl'
        simp at ho; subst ho
        exact hne,
    fun l' o ho => by
      by_cases hl : l' < s.objs.length
      · rw [show ({ s with objs := s.objs ++ [o0] } : Store).objs = s.objs ++ [o0] from rfl,
          List.getElem?_append_left hl] at ho
        exact hw.bounds l' o ho
      · have hl' : l' = s.objs.length := by
          have := (List.getElem?_eq_some_iff.mp ho).1
          simp at this; omega
        subst hl'
        simp at ho; subst ho
        exact hin,
    fun i p hp => (hw.procs i p hp).stable (Ext.newObj (W := fun _ => False) (Wo := fun _ => False) o0)⟩
  have he1 : Ext P (fun _ => False) (fun _ => False) Λ Λ s { s with objs := s.objs ++ [o0] } :=
    Ext.newObj _
  have hd := defaults_good (orc := orc) (k := k) (targs := targs) hP ihs hk n (Nat.le_refl n) 0 _ Λ o0
    hw1 ho1 rfl rfl fun i f hf hr hor => by
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
    obtain ⟨o2', ho2', hc2, ha2, _, _⟩ := he2.grow l o0 ho1
    rw [ho2] at ho2'; cases ho2'
    have hc2 : o2.cls = k := hc2
    have ha2 : o2.args = targs := ha2
    have hset2 : ∀ (i : Nat) (f : Field), (P.classes.allFieldsAt k targs)[i]? = some f →
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
      rw [hnone ((Program.lookupAt_none_iff hwf k targs "initialize").mpr hl)]
      simp only [List.isEmpty_nil, if_true]
      refine ⟨Λ2, hw2, hfresh he12 (fun _ _ h => h), ?_⟩
      -- No `initialize`: every field is non-required as declared, so as
      -- the instance has it.
      have := made_of hwf hw2 ho2 fun i f hf => by
        rw [hc2] at hf
        have hi : i < (P.classes.allFieldsAt k targs).length := by
          rw [ClassTable.allFieldsAt_length]; exact (List.getElem?_eq_some_iff.mp hf).1
        have hg : (P.classes.allFieldsAt k targs)[i]? = some (P.classes.allFieldsAt k targs)[i] :=
          List.getElem?_eq_getElem hi
        obtain ⟨d, f0, _, hf0, hff⟩ := ClassTable.allFieldsAt_some P.classes hg
        rw [hf] at hf0; cases hf0
        refine hset2 i _ hg ?_
        rw [hff]
        exact required_subst hwf _ (no_init_fields hP.inits hl f (List.mem_of_getElem? hf))
      rwa [hc2, ha2] at this
    | some mi =>
      dsimp only
      obtain ⟨hmem', howner, hname'⟩ := Program.lookup_spec hl
      -- The `initialize` found, as the view `k[targs]` sees it.
      obtain ⟨σ, hσ⟩ := ClassTable.ancestorArgs_of_mem hwf k targs mi.owner howner
      have hlat : P.lookupAt k targs "initialize" = some (mi.inst σ) := by
        simp [Program.lookupAt, hl, hσ]
      obtain ⟨hblk, hvs⟩ := hinit _ hlat
      have hblk0 : mi.block = none := (Method.inst_block_none mi σ).mp hblk
      rw [Method.inst_params_snd] at hvs
      obtain ⟨rest, hrest, hrestnr⟩ := init_beyond hwf hP.inits hl
      have hsa2 : s2.argsFor P.classes l mi.owner = σ := by
        simp [Store.argsFor, ho2, hc2, ha2, hσ]
      -- Every field set but those `initialize` assigns (past its class: none).
      obtain ⟨hlen', s3, hb, hargs3, hpost⟩ := init_run hP (ihs n (Nat.le_refl n)).eval hw2 hmem'
        hname' hblk0 (by rw [hsa2]; exact hvs.mono he12.grow he12.procs) ho2 (by rw [hc2]; exact howner)
        fun i f hf hor => by
          rw [hc2, ha2] at hf
          refine hset2 i f hf ?_
          rcases hor with h | h
          · obtain ⟨d, f0, _, hf0, hff⟩ := ClassTable.allFieldsAt_some P.classes hf
            rw [hrest, List.getElem?_append_right h] at hf0
            rw [hff]
            exact required_subst hwf _ (hrestnr f0 (List.mem_of_getElem? hf0))
          · exact h
      rw [if_neg (by simp [hlen'])]
      simp only [Store.alloc, hb]
      rw [hargs3]
      revert hpost
      generalize eval P orc n _ s3 mi.body = r
      intro hpost
      -- What `new` gives: the object, made.
      have hfin : ∀ {Λ4 : List Ty} {s4 : Store}, WfStore P Λ4 s4 →
          Ext P (fun _ => False) (· = l) Λ2 Λ4 s2 s4 →
          (s4.typeOf (.obj l)).isSome = true → ConstructPost P k targs Λ s (.ok (.obj l) s4) := by
        intro Λ4 s4 hw4 he4 hmade
        refine ⟨Λ4, hw4, hfresh (he12.transW he4 hw) (fun _ _ h => h.elim id id), ?_⟩
        obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hmade
        obtain ⟨o4, ho4, _, rfl⟩ := typeOf_obj ha
        obtain ⟨o4', ho4', hc4, ha4, _, _⟩ := he4.grow l o2 ho2
        rw [ho4] at ho4'; cases ho4'
        refine hasTy_iff.mpr ⟨_, ha, .cls k targs, List.mem_singleton.mpr rfl, ?_⟩
        rw [hc4, hc2, ha4, ha2]; exact Atom.le_refl hwf _
      cases r with
      | ok v s4 => obtain ⟨Λ4, hw4, he4, hmade⟩ := hpost; exact hfin hw4 he4 hmade
      | returned v s4 => obtain ⟨Λ4, hw4, he4, hmade⟩ := hpost; exact hfin hw4 he4 hmade
      | stuck => exact (hpost : False).elim
      | raised v s4 =>
        obtain ⟨Λ4, hw4, he4, hv⟩ := hpost
        exact ⟨Λ4, hw4, hfresh (he12.transW he4 hw) (fun _ _ h => h.elim id id), hv⟩
      | timeout => exact trivial
  | stuck => exact (hd : False).elim
  | returned => exact (hd : False).elim
  | raised v s2 =>
    obtain ⟨Λ2, hw2, he2, hv⟩ := hd
    have he12 : Ext P (fun _ => False) (· = l) Λ Λ2 s s2 :=
      (he1.trans he2 hw).mono (fun _ h => h.elim False.elim False.elim) (fun _ h => h.elim False.elim id)
    exact ⟨Λ2, hw2, (he12.restrict (fun _ _ h => h)).fresh fun _ h => by rw [h]; exact Nat.le_refl _, hv⟩
  | timeout => exact trivial

end QuarzCore
