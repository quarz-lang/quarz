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

end ClassTable

end QuarzCore
