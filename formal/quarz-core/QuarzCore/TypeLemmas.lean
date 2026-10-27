/-
The order of atoms and types, under a well-formed class table: class 0
the root, every other class's superclass before it (`WfClasses`). Then
the superclass chains end at the root, `≤` is a preorder, and two
classes above one are ordered (single inheritance), which the `is_a?`
rule relies on.
-/

import QuarzCore.Program

namespace QuarzCore

structure WfClasses (ct : ClassTable) : Prop where
  nonempty : 0 < ct.length
  root : ∀ k, ct[0]? = some k → k.super = none
  super : ∀ i k, 0 < i → ct[i]? = some k → ∃ d, k.super = some d ∧ d < i

theorem Program.wfClasses_sound {P : Program} (h : P.wfClasses = true) : WfClasses P.classes := by
  simp only [Program.wfClasses, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨hne, hall⟩ := h
  refine ⟨hne, fun k hk => ?_, fun i k hi hk => ?_⟩
  · have := hall 0 hne
    simp [hk] at this
    exact this
  · have hlt : i < P.classes.length := by
      rcases List.getElem?_eq_some_iff.mp hk with ⟨h, _⟩; exact h
    have := hall i hlt
    simp only [hk] at this
    have hi0 : (i == 0) = false := by simp; omega
    simp only [hi0] at this
    revert this
    cases hs : k.super with
    | none => simp
    | some d => intro this; exact ⟨d, rfl, by simpa using this⟩

namespace ClassTable

theorem ancestorsAux_head (ct : ClassTable) (n c : Nat) :
    ancestorsAux ct (n + 1) c = c :: (match (ct[c]?).bind (·.super) with
      | some d => ancestorsAux ct n d
      | none => []) := rfl

/-- With enough fuel, the chain is the class and its superclass's. -/
theorem ancestorsAux_enough (ct : ClassTable) (hwf : WfClasses ct) :
    ∀ c n m, c < n → c < m → ancestorsAux ct n c = ancestorsAux ct m c := by
  intro c
  induction c using Nat.strongRecOn with
  | _ c ih =>
    intro n m hn hm
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    simp only [ancestorsAux_head]
    congr 1
    cases hk : ct[c]? with
    | none => simp
    | some k =>
      cases hs : k.super with
      | none => simp [hs]
      | some d =>
        have hd : d < c := by
          rcases Nat.eq_zero_or_pos c with h0 | hpos
          · subst h0; have := hwf.root k hk; simp_all
          · obtain ⟨d', hd', hlt⟩ := hwf.super c k hpos hk
            rw [hs] at hd'; cases hd'; exact hlt
        simp only [Option.bind_some, hs]
        exact ih d hd n m (Nat.lt_of_lt_of_le hd (Nat.le_of_lt_succ hn))
          (Nat.lt_of_lt_of_le hd (Nat.le_of_lt_succ hm))

variable {ct : ClassTable}

/-- The superclass of a class (none for the root and for an id out of
the table). -/
def superOf (ct : ClassTable) (c : Nat) : Option Nat := (ct[c]?).bind (·.super)

theorem superOf_lt (hwf : WfClasses ct) {c d : Nat} (h : superOf ct c = some d) : d < c := by
  unfold superOf at h
  cases hk : ct[c]? with
  | none => simp [hk] at h
  | some k =>
    simp [hk] at h
    rcases Nat.eq_zero_or_pos c with h0 | hpos
    · subst h0; have := hwf.root k hk; simp_all
    · obtain ⟨d', hd', hlt⟩ := hwf.super c k hpos hk
      rw [h] at hd'; cases hd'; exact hlt

theorem ancestors_eq (hwf : WfClasses ct) (c : Nat) :
    ct.ancestors c = c :: (match superOf ct c with
      | some d => ct.ancestors d
      | none => []) := by
  have hn := hwf.nonempty
  unfold ancestors
  obtain ⟨n, hn'⟩ : ∃ n, ct.length = n + 1 := ⟨ct.length - 1, by omega⟩
  rw [hn', ancestorsAux_head]
  congr 1
  cases hs : superOf ct c with
  | none =>
    simp only [superOf] at hs
    simp only [hs]
  | some d =>
    have hlt := superOf_lt hwf hs
    have hcl : c < ct.length := by
      unfold superOf at hs
      cases hk : ct[c]? with
      | none => simp [hk] at hs
      | some k => exact (List.getElem?_eq_some_iff.mp hk).1
    simp only [superOf] at hs
    simp only [hs]
    rw [← hn']
    exact ancestorsAux_enough ct hwf d n ct.length (by omega) (by omega)

/-- What is above `c` is not after it in the table. -/
theorem ancestors_le (hwf : WfClasses ct) : ∀ c d, d ∈ ct.ancestors c → d ≤ c := by
  intro c
  induction c using Nat.strongRecOn with
  | _ c ih =>
    intro d hd
    rw [ancestors_eq hwf] at hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact Nat.le_refl _
    · cases hs : superOf ct c with
      | none => simp [hs] at hd
      | some s =>
        simp only [hs] at hd
        have := ih s (superOf_lt hwf hs) d hd
        have := superOf_lt hwf hs
        omega

theorem mem_ancestors_self (hwf : WfClasses ct) (c : Nat) : c ∈ ct.ancestors c := by
  rw [ancestors_eq hwf]; simp

/-- What is above something above `c` is above `c`. -/
theorem ancestors_trans (hwf : WfClasses ct) :
    ∀ c d e, d ∈ ct.ancestors c → e ∈ ct.ancestors d → e ∈ ct.ancestors c := by
  intro c
  induction c using Nat.strongRecOn with
  | _ c ih =>
    intro d e hd he
    rw [ancestors_eq hwf] at hd ⊢
    rcases List.mem_cons.mp hd with rfl | hd
    · rw [ancestors_eq hwf] at he; exact he
    · cases hs : superOf ct c with
      | none => simp [hs] at hd
      | some s =>
        simp only [hs] at hd ⊢
        exact List.mem_cons_of_mem _ (ih s (superOf_lt hwf hs) d e hd he)

/-- Two classes above `c` are ordered (single inheritance). -/
theorem ancestors_total (hwf : WfClasses ct) :
    ∀ c d e, d ∈ ct.ancestors c → e ∈ ct.ancestors c →
      d ∈ ct.ancestors e ∨ e ∈ ct.ancestors d := by
  intro c
  induction c using Nat.strongRecOn with
  | _ c ih =>
    intro d e hd he
    rw [ancestors_eq hwf] at hd he
    rcases List.mem_cons.mp hd with rfl | hd
    · right
      rcases List.mem_cons.mp he with rfl | he
      · exact mem_ancestors_self hwf _
      · rw [ancestors_eq hwf]; exact List.mem_cons_of_mem _ he
    · rcases List.mem_cons.mp he with rfl | he
      · left; rw [ancestors_eq hwf]; exact List.mem_cons_of_mem _ hd
      · cases hs : superOf ct c with
        | none => simp [hs] at hd
        | some s =>
          simp only [hs] at hd he
          exact ih s (superOf_lt hwf hs) d e hd he

/-- Every class of the table is under the root. -/
theorem root_mem_ancestors (hwf : WfClasses ct) :
    ∀ c, c < ct.length → 0 ∈ ct.ancestors c := by
  intro c
  induction c using Nat.strongRecOn with
  | _ c ih =>
    intro hc
    rw [ancestors_eq hwf]
    cases hs : superOf ct c with
    | none =>
      -- Only the root has no superclass.
      rcases Nat.eq_zero_or_pos c with h0 | hpos
      · simp [h0]
      · obtain ⟨k, hk⟩ : ∃ k, ct[c]? = some k := ⟨ct[c], by simp [hc]⟩
        obtain ⟨d, hd, _⟩ := hwf.super c k hpos hk
        simp [superOf, hk, hd] at hs
    | some d =>
      have hlt := superOf_lt hwf hs
      simp only [hs]
      exact List.mem_cons_of_mem _ (ih d hlt (by omega))

theorem superOf_zero (hwf : WfClasses ct) : superOf ct 0 = none := by
  unfold superOf
  cases hk : ct[0]? with
  | none => rfl
  | some k => simp [hwf.root k hk]

theorem ancestors_zero (hwf : WfClasses ct) : ct.ancestors 0 = [0] := by
  rw [ancestors_eq hwf, superOf_zero hwf]

/-- A class's chain ends with the chain of each class above it. -/
theorem ancestors_suffix (hwf : WfClasses ct) :
    ∀ c d, d ∈ ct.ancestors c → ∃ pre, ct.ancestors c = pre ++ ct.ancestors d ∧ d ∉ pre := by
  intro c
  induction c using Nat.strongRecOn with
  | _ c ih =>
    intro d hd
    rw [ancestors_eq hwf] at hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact ⟨[], by simp, by simp⟩
    · cases hs : superOf ct c with
      | none => simp [hs] at hd
      | some s =>
        simp only [hs] at hd
        obtain ⟨pre, hpre, hnot⟩ := ih s (superOf_lt hwf hs) d hd
        have hle := ancestors_le hwf s d hd
        have hlt := superOf_lt hwf hs
        refine ⟨c :: pre, by simp only [ancestors_eq hwf c, hs, hpre, List.cons_append], ?_⟩
        intro hm
        rcases List.mem_cons.mp hm with h | h
        · -- `d` above `s` above `c`: not `c` (a chain descends).
          omega
        · exact hnot h

theorem subclass_iff (c d : Nat) : ct.subclass c d = true ↔ d ∈ ct.ancestors c := by
  simp [subclass]

end ClassTable

namespace Atom

open ClassTable

variable {ct : ClassTable}

theorem le_refl (hwf : WfClasses ct) (a : Atom) : a.le ct a = true := by
  cases a <;> simp [Atom.le, subclass_iff, mem_ancestors_self hwf]

theorem le_trans (hwf : WfClasses ct) {a b c : Atom} (hab : a.le ct b = true)
    (hbc : b.le ct c = true) : a.le ct c = true := by
  cases a <;> cases b <;> cases c <;>
    simp_all [Atom.le, subclass_iff, ancestors_zero hwf] <;>
    exact ancestors_trans hwf _ _ _ hab hbc

end Atom

end QuarzCore
