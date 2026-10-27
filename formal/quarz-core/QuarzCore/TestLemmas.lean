/-
What the tests (`nil?`, `is_a?`, `==` against nil, true, false) tell of
a value: its type narrowed as design §2.1's table says.
-/

import QuarzCore.Lemmas

set_option linter.deprecated false

namespace QuarzCore

open ClassTable

variable {P : Program}

/-- Two atoms above one are ordered (single inheritance). -/
theorem Atom.le_total_above (hwf : WfClasses P.classes) {u a b : Atom}
    (ha : u.le P.classes a = true) (hb : u.le P.classes b = true) :
    a.le P.classes b = true ∨ b.le P.classes a = true := by
  cases u <;> cases a <;> cases b <;> simp_all [Atom.le, subclass_iff, ancestors_zero hwf] <;>
    first
    | exact (ancestors_total hwf _ _ _ ha hb).symm
    | (subst_vars; simp [mem_ancestors_self hwf])

/-- `is_a?` true: of the atoms below the class, or of the class itself
when it is below one of them (design §2.1, 270e62e). -/
theorem hasTy_isATrue (hwf : WfClasses P.classes) {s : Store} {v : Value} {t : Ty} {a u : Atom}
    (hv : s.hasTy P v t) (hu : s.typeOf v = some u) (hua : u.le P.classes a = true) :
    s.hasTy P v (isATrue P.classes t a) := by
  rw [hasTy_iff] at hv ⊢
  obtain ⟨u', hu', b, hb, hub⟩ := hv
  rw [hu] at hu'; cases hu'
  refine ⟨u, hu, ?_⟩
  by_cases hba : b.le P.classes a = true
  · exact ⟨b, List.mem_append_left _ (List.mem_filter.mpr ⟨hb, hba⟩), hub⟩
  · have hab : a.le P.classes b = true := by
      rcases Atom.le_total_above hwf hua hub with h | h
      · exact h
      · exact absurd h hba
    have hne : a ≠ b := by rintro rfl; exact hba (Atom.le_refl hwf _)
    refine ⟨a, List.mem_append_right _ ?_, hua⟩
    have : t.any (fun b => a.le P.classes b && a != b) = true :=
      List.any_eq_true.mpr ⟨b, hb, by simp [hab, hne]⟩
    simp [this]

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

/-- `nil`, of a type: of the type's `nil`. -/
theorem hasTy_nilTy {s : Store} {t : Ty} (hv : s.hasTy P .nil t) : s.hasTy P .nil (nilTy P.classes t) := by
  refine hasTy_iff.mpr ⟨.nil, rfl, .nil, ?_, by simp [Atom.le]⟩
  rw [hasTy_iff] at hv
  obtain ⟨a, ha, b, hb, hab⟩ := hv
  simp [Store.typeOf] at ha; subst ha
  simp [nilTy, Ty.le]; exact ⟨b, hb, hab⟩

/-- A value other than `nil`: of its type without `nil`. -/
theorem hasTy_remove_nil {s : Store} {v : Value} {t : Ty} (hv : s.hasTy P v t) (hne : v ≠ .nil) :
    s.hasTy P v (t.remove .nil) := by
  rw [hasTy_iff] at *
  obtain ⟨a, ha, b, hb, hab⟩ := hv
  refine ⟨a, ha, b, List.mem_filter.mpr ⟨hb, ?_⟩, hab⟩
  cases b <;> simp
  cases a <;> simp_all [Atom.le]
  cases v <;> simp_all [Store.typeOf]

/-- A value of a type of final atoms is no object. -/
theorem not_obj_of_final {s : Store} {v : Value} {t : Ty} (hv : s.hasTy P v t)
    (hfin : t.allFinal = true) : ∀ l, v ≠ .obj l := by
  rintro l rfl
  rw [hasTy_iff] at hv
  obtain ⟨a, ha, b, hb, hab⟩ := hv
  simp [Store.typeOf] at ha
  obtain ⟨o, _, rfl⟩ := ha
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
