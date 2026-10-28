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
      obtain ⟨hmem', howner, hname'⟩ := Program.lookup_spec hl
      obtain ⟨rest, hrest, hrestnr⟩ := init_beyond hwf hP.inits hl
      -- Every field set but those `initialize` assigns (past its class: none).
      obtain ⟨hlen', s3, hb, hpost⟩ := init_run hP (ihs n (Nat.le_refl n)).eval hw2 hmem' hname' hblk
        (hvs.mono he12.grow) ho2 (by rw [hc2]; exact howner) fun i f hf hor => by
          rw [hc2] at hf
          refine hset2 i f hf ?_
          rcases hor with h | h
          · rw [hrest, List.getElem?_append_right h] at hf
            exact hrestnr f (List.mem_of_getElem? hf)
          · exact h
      rw [if_neg (by simp [hlen'])]
      simp only [Store.alloc, hb]
      revert hpost
      generalize eval P orc n _ s3 mi.body = r
      intro hpost
      -- What `new` gives: the object, made.
      have hfin : ∀ {Λ4 : List Ty} {s4 : Store}, WfStore P Λ4 s4 →
          Ext P (fun _ => False) (· = l) Λ2 Λ4 s2 s4 →
          (s4.typeOf (.obj l)).isSome = true → ConstructPost P k Λ s (.ok (.obj l) s4) := by
        intro Λ4 s4 hw4 he4 hmade
        refine ⟨Λ4, hw4, hfresh (he12.transW he4 hw) (fun _ _ h => h.elim id id), ?_⟩
        obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hmade
        obtain ⟨o4, ho4, _, rfl⟩ := typeOf_obj ha
        obtain ⟨o4', ho4', hc4, _, _⟩ := he4.grow l o2 ho2
        rw [ho4] at ho4'; cases ho4'
        refine hasTy_iff.mpr ⟨_, ha, .cls k, List.mem_singleton.mpr rfl, ?_⟩
        rw [hc4, hc2]; exact Atom.le_refl hwf _
      cases r with
      | ok v s4 => obtain ⟨Λ4, hw4, he4, hmade⟩ := hpost; exact hfin hw4 he4 hmade
      | returned v s4 => obtain ⟨Λ4, hw4, he4, hmade⟩ := hpost; exact hfin hw4 he4 hmade
      | stuck => exact (hpost : False).elim
      | raised => exact trivial
      | timeout => exact trivial
  | stuck => exact (hd : False).elim
  | returned => exact (hd : False).elim
  | raised => exact trivial
  | timeout => exact trivial

end QuarzCore
