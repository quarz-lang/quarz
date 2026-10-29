/-
`Ext`: a preorder on stores, and what each store operation keeps.
-/

import QuarzCore.Lemmas

set_option linter.deprecated false

namespace QuarzCore

variable {P : Program}

theorem ObjsGrow.refl (s : Store) : ObjsGrow s s :=
  fun _ o h => ⟨o, h, rfl, rfl, rfl, fun _ h => h⟩

theorem ObjsGrow.trans {s1 s2 s3 : Store} (h1 : ObjsGrow s1 s2) (h2 : ObjsGrow s2 s3) :
    ObjsGrow s1 s3 := fun l o ho => by
  obtain ⟨o2, ho2, hc2, ha2, hl2, hs2⟩ := h1 l o ho
  obtain ⟨o3, ho3, hc3, ha3, hl3, hs3⟩ := h2 l o2 ho2
  exact ⟨o3, ho3, hc3.trans hc2, ha3.trans ha2, hl3.trans hl2, fun i h => hs3 i (hs2 i h)⟩

theorem Ext.refl (W Wo : Nat → Prop) (Λ : List Ty) (s : Store) : Ext P W Wo Λ Λ s s where
  tys := List.prefix_refl Λ
  procs := List.prefix_refl _
  locs := fun _ v h => ⟨v, h, .inl rfl⟩
  grow := ObjsGrow.refl s
  imm := fun _ o o' h h' _ _ _ _ _ => by rw [h] at h'; cases h'; rfl

theorem Ext.mono {W W' Wo Wo' : Nat → Prop} {Λ Λ' : List Ty} {s s' : Store}
    (h : Ext P W Wo Λ Λ' s s') (hw : ∀ l, W l → W' l) (ho : ∀ l, Wo l → Wo' l) :
    Ext P W' Wo' Λ Λ' s s' where
  tys := h.tys
  procs := h.procs
  locs := fun l v hv => by
    obtain ⟨v', h1, h2⟩ := h.locs l v hv
    refine ⟨v', h1, ?_⟩
    rcases h2 with h2 | ⟨hw', t, ht, hty⟩
    · exact .inl h2
    · exact .inr ⟨hw l hw', t, ht, hty⟩
  grow := h.grow
  imm := fun l o o' h1 h2 hn => h.imm l o o' h1 h2 (fun hw => hn (ho l hw))

theorem Ext.monoW {W W' Wo : Nat → Prop} {Λ Λ' : List Ty} {s s' : Store}
    (h : Ext P W Wo Λ Λ' s s') (hw : ∀ l, W l → W' l) : Ext P W' Wo Λ Λ' s s' :=
  h.mono hw fun _ h => h

theorem prefix_getElem? {Λ Λ' : List Ty} (h : Λ <+: Λ') {l : Nat} {t : Ty} (ht : Λ[l]? = some t) :
    Λ'[l]? = some t := by
  obtain ⟨r, rfl⟩ := h
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp ht).1]; exact ht

theorem Ext.trans {W1 W2 Wo1 Wo2 : Nat → Prop} {Λ1 Λ2 Λ3 : List Ty} {s1 s2 s3 : Store}
    (h1 : Ext P W1 Wo1 Λ1 Λ2 s1 s2) (h2 : Ext P W2 Wo2 Λ2 Λ3 s2 s3) (hw : WfStore P Λ1 s1) :
    Ext P (fun l => W1 l ∨ W2 l) (fun l => Wo1 l ∨ Wo2 l) Λ1 Λ3 s1 s3 where
  tys := h1.tys.trans h2.tys
  procs := h1.procs.trans h2.procs
  locs := fun l v hv => by
    obtain ⟨v2, hv2, hc2⟩ := h1.locs l v hv
    obtain ⟨v3, hv3, hc3⟩ := h2.locs l v2 hv2
    refine ⟨v3, hv3, ?_⟩
    -- The location's declared type, the same in every `Λ`.
    have hl : l < Λ1.length := by
      rw [hw.len]; exact (List.getElem?_eq_some_iff.mp hv).1
    obtain ⟨t, ht⟩ : ∃ t, Λ1[l]? = some t := ⟨Λ1[l], by simp [hl]⟩
    rcases hc2 with rfl | ⟨hw1, t1, ht1, hty1⟩
    · rcases hc3 with rfl | ⟨hw2, t2, ht2, hty2⟩
      · exact .inl rfl
      · rw [prefix_getElem? h1.tys ht] at ht2; cases ht2
        exact .inr ⟨.inr hw2, t, ht, hty2⟩
    · rw [ht] at ht1; cases ht1
      rcases hc3 with rfl | ⟨_, t2, ht2, hty2⟩
      · exact .inr ⟨.inl hw1, _, ht, h2.hasTy hty1⟩
      · rw [prefix_getElem? h1.tys ht] at ht2; cases ht2
        exact .inr ⟨.inl hw1, _, ht, hty2⟩
  grow := h1.grow.trans h2.grow
  imm := fun l o o3 ho ho3 hn i f hf hv => by
    obtain ⟨o2, ho2, hc2, _, _⟩ := h1.grow l o ho
    rw [h2.imm l o2 o3 ho2 ho3 (fun h => hn (.inr h)) i f (by rw [hc2]; exact hf) hv,
      h1.imm l o o2 ho ho2 (fun h => hn (.inl h)) i f hf hv]

/-- Two steps of a frame, each assigning only what `Wo` allows. -/
theorem Ext.transW {W1 W2 Wo : Nat → Prop} {Λ1 Λ2 Λ3 : List Ty} {s1 s2 s3 : Store}
    (h1 : Ext P W1 Wo Λ1 Λ2 s1 s2) (h2 : Ext P W2 Wo Λ2 Λ3 s2 s3) (hw : WfStore P Λ1 s1) :
    Ext P (fun l => W1 l ∨ W2 l) Wo Λ1 Λ3 s1 s3 :=
  (h1.trans h2 hw).mono (fun _ h => h) fun _ h => h.elim id id

/-- A step of a frame, then one assigning no immutable field. -/
theorem Ext.transF {W1 W2 Wo : Nat → Prop} {Λ1 Λ2 Λ3 : List Ty} {s1 s2 s3 : Store}
    (h1 : Ext P W1 Wo Λ1 Λ2 s1 s2) (h2 : Ext P W2 (fun _ => False) Λ2 Λ3 s2 s3) (hw : WfStore P Λ1 s1) :
    Ext P (fun l => W1 l ∨ W2 l) Wo Λ1 Λ3 s1 s3 :=
  (h1.trans h2 hw).mono (fun _ h => h) fun _ h => h.elim id False.elim

/-- What an object not there before may have done is no one's concern. -/
theorem Ext.fresh {W Wo : Nat → Prop} {Λ Λ' : List Ty} {s s' : Store}
    (h : Ext P W Wo Λ Λ' s s') (hf : ∀ l, Wo l → s.objs.length ≤ l) :
    Ext P W (fun _ => False) Λ Λ' s s' where
  tys := h.tys
  procs := h.procs
  locs := h.locs
  grow := h.grow
  imm := fun l o o' h1 h2 _ => h.imm l o o' h1 h2 fun hw =>
    absurd (List.getElem?_eq_some_iff.mp h1).1 (Nat.not_lt.mpr (hf l hw))

/-! ### Store operations -/

theorem getElem?_set_ne' {α} {xs : List α} {i j : Nat} {v : α} (h : j ≠ i) :
    (xs.set i v)[j]? = xs[j]? := List.getElem?_set_ne (fun e => h e.symm)

/-- Writing a value of its declared type into a location `W` allows. -/
theorem Ext.setLoc {W Wo : Nat → Prop} {Λ : List Ty} {s : Store} {l : Nat} {v : Value} {t : Ty}
    (hl : l < s.locs.length) (ht : Λ[l]? = some t) (hv : s.hasTy P v t) (hw : W l) :
    Ext P W Wo Λ Λ s (s.setLoc l v) where
  tys := List.prefix_refl Λ
  procs := List.prefix_refl _
  locs := fun l' v' h => by
    by_cases he : l' = l
    · subst he
      refine ⟨v, by simp [Store.setLoc, hl], .inr ⟨hw, t, ht, ?_⟩⟩
      exact hv
    · exact ⟨v', by simpa [Store.setLoc, getElem?_set_ne' he] using h, .inl rfl⟩
  grow := fun _ o h => ⟨o, h, rfl, rfl, rfl, fun _ h => h⟩
  imm := fun _ o o' h h' _ _ _ _ _ => by simp [Store.setLoc] at h'; rw [h] at h'; cases h'; rfl

/-- A new procedure at the end. -/
theorem Ext.newProc {W Wo : Nat → Prop} {Λ : List Ty} {s : Store} (p : ProcV) :
    Ext P W Wo Λ Λ s { s with procs := s.procs ++ [p] } where
  tys := List.prefix_refl Λ
  procs := List.prefix_append _ _
  locs := fun _ v h => ⟨v, h, .inl rfl⟩
  grow := fun _ o h => ⟨o, h, rfl, rfl, rfl, fun _ h => h⟩
  imm := fun _ o o' h h' _ _ _ _ _ => by simp at h'; rw [h] at h'; cases h'; rfl

/-- A new object at the end. -/
theorem Ext.newObj {W Wo : Nat → Prop} {Λ : List Ty} {s : Store} (o : Obj) :
    Ext P W Wo Λ Λ s { s with objs := s.objs ++ [o] } where
  tys := List.prefix_refl Λ
  procs := List.prefix_refl _
  locs := fun _ v h => ⟨v, h, .inl rfl⟩
  grow := fun l o' h => ⟨o', by
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]; exact h,
    rfl, rfl, rfl, fun _ h => h⟩
  imm := fun l o1 o2 h h' _ _ _ _ _ => by
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1, h] at h'; cases h'; rfl

/-- Fresh locations, for the locals `names` of a new frame. -/
theorem Ext.alloc {W Wo : Nat → Prop} {Λ : List Ty} {s : Store} (names : List String) (tys : List Ty) :
    Ext P W Wo Λ (Λ ++ tys) s (s.alloc names).1 where
  tys := List.prefix_append Λ tys
  procs := List.prefix_refl _
  locs := fun l v h => ⟨v, by
      simp only [Store.alloc]
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]; exact h, .inl rfl⟩
  grow := fun _ o h => ⟨o, h, rfl, rfl, rfl, fun _ h => h⟩
  imm := fun _ o o' h h' _ _ _ _ _ => by simp [Store.alloc] at h'; rw [h] at h'; cases h'; rfl

end QuarzCore
