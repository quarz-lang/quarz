/-
`Ext`: a preorder on stores, and what each store operation keeps.
-/

import QuarzCore.Lemmas

set_option linter.deprecated false

namespace QuarzCore

variable {P : Program}

theorem Ext.refl (W : Nat → Prop) (Λ : List Ty) (s : Store) : Ext P W Λ Λ s s where
  tys := List.prefix_refl Λ
  locs := fun _ v h => ⟨v, h, .inl rfl⟩
  objs := fun _ o h => ⟨o, h, rfl, fun _ _ _ _ => rfl⟩

theorem Ext.mono {W W' : Nat → Prop} {Λ Λ' : List Ty} {s s' : Store} (h : Ext P W Λ Λ' s s')
    (hw : ∀ l, W l → W' l) : Ext P W' Λ Λ' s s' where
  tys := h.tys
  locs := fun l v hv => by
    obtain ⟨v', h1, h2⟩ := h.locs l v hv
    refine ⟨v', h1, ?_⟩
    rcases h2 with h2 | ⟨hw', t, ht, hty⟩
    · exact .inl h2
    · exact .inr ⟨hw l hw', t, ht, hty⟩
  objs := h.objs

theorem prefix_getElem? {Λ Λ' : List Ty} (h : Λ <+: Λ') {l : Nat} {t : Ty} (ht : Λ[l]? = some t) :
    Λ'[l]? = some t := by
  obtain ⟨r, rfl⟩ := h
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp ht).1]; exact ht

theorem Ext.trans {W1 W2 : Nat → Prop} {Λ1 Λ2 Λ3 : List Ty} {s1 s2 s3 : Store}
    (h1 : Ext P W1 Λ1 Λ2 s1 s2) (h2 : Ext P W2 Λ2 Λ3 s2 s3) (hw : WfStore P Λ1 s1) :
    Ext P (fun l => W1 l ∨ W2 l) Λ1 Λ3 s1 s3 where
  tys := h1.tys.trans h2.tys
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
  objs := fun l o ho => by
    obtain ⟨o2, ho2, hc2, hf2⟩ := h1.objs l o ho
    obtain ⟨o3, ho3, hc3, hf3⟩ := h2.objs l o2 ho2
    refine ⟨o3, ho3, hc3.trans hc2, fun i f hf hv => ?_⟩
    rw [hf3 i f (by rw [hc2]; exact hf) hv, hf2 i f hf hv]

/-! ### Store operations -/

theorem getElem?_set_ne' {α} {xs : List α} {i j : Nat} {v : α} (h : j ≠ i) :
    (xs.set i v)[j]? = xs[j]? := List.getElem?_set_ne (fun e => h e.symm)

/-- Writing a value of its declared type into a location `W` allows. -/
theorem Ext.setLoc {W : Nat → Prop} {Λ : List Ty} {s : Store} {l : Nat} {v : Value} {t : Ty}
    (hl : l < s.locs.length) (ht : Λ[l]? = some t) (hv : s.hasTy P v t) (hw : W l) :
    Ext P W Λ Λ s (s.setLoc l v) where
  tys := List.prefix_refl Λ
  locs := fun l' v' h => by
    by_cases he : l' = l
    · subst he
      refine ⟨v, by simp [Store.setLoc, hl], .inr ⟨hw, t, ht, ?_⟩⟩
      exact hv
    · exact ⟨v', by simpa [Store.setLoc, getElem?_set_ne' he] using h, .inl rfl⟩
  objs := fun _ o h => ⟨o, h, rfl, fun _ _ _ _ => rfl⟩

theorem WfStore.setLoc {Λ : List Ty} {s : Store} (h : WfStore P Λ s) (l : Nat) (v : Value) :
    WfStore P Λ (s.setLoc l v) where
  len := by simp [Store.setLoc, h.len]
  objs := fun l o ho => by
    obtain ⟨h1, h2, h3⟩ := h.objs l o ho
    exact ⟨h1, h2, fun i w f hw hf => h3 i w f hw hf⟩

/-- A new object at the end. -/
theorem Ext.newObj {W : Nat → Prop} {Λ : List Ty} {s : Store} (o : Obj) :
    Ext P W Λ Λ s { s with objs := s.objs ++ [o] } where
  tys := List.prefix_refl Λ
  locs := fun _ v h => ⟨v, h, .inl rfl⟩
  objs := fun l o' h => ⟨o', by
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]; exact h,
    rfl, fun _ _ _ _ => rfl⟩

/-- Fresh locations, for the locals `names` of a new frame. -/
theorem Ext.alloc {W : Nat → Prop} {Λ : List Ty} {s : Store} (names : List String) (tys : List Ty) :
    Ext P W Λ (Λ ++ tys) s (s.alloc names).1 where
  tys := List.prefix_append Λ tys
  locs := fun l v h => ⟨v, by
      simp only [Store.alloc]
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]; exact h, .inl rfl⟩
  objs := fun _ o h => ⟨o, h, rfl, fun _ _ _ _ => rfl⟩

end QuarzCore
