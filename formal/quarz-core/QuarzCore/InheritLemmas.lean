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

theorem allFields_prefix (hwf : WfClasses ct) {c d : Nat} (h : c ∈ ct.ancestors d) :
    ∃ rest, ct.allFields d = ct.allFields c ++ rest := by
  obtain ⟨pre, hpre, _⟩ := ancestors_suffix hwf d c h
  refine ⟨(pre.reverse.filterMap (ct[·]?)).flatMap (·.fields), ?_⟩
  simp [allFields, hpre, List.reverse_append, List.filterMap_append, List.flatMap_append]

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
theorem Program.wfMethod_overrides {P : Program} {mt : Method} (h : P.wfMethod mt = true) :
    ∀ d ∈ (P.classes.ancestors mt.owner).drop 1, ∀ sup, P.lookup d mt.name = some sup →
      P.overrides mt sup = true := by
  intro d hd sup hsup
  simp only [Program.wfMethod, Bool.and_eq_true, List.all_eq_true] at h
  have := h.1.2 d hd
  rw [hsup] at this
  exact this

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

/-- The method a subclass runs: the one found, or one overriding it. -/
theorem Program.lookup_sub {P : Program} (hwf : WfClasses P.classes)
    (hm : ∀ mt ∈ P.methods, P.wfMethod mt = true) {k rc : Nat} {m : String} {mt : Method}
    (h : P.lookup k m = some mt) (hk : k ∈ P.classes.ancestors rc) :
    ∃ mt', P.lookup rc m = some mt' ∧ (mt' = mt ∨ P.overrides mt' mt = true) := by
  obtain ⟨pre, hpre, _⟩ := ancestors_suffix hwf rc k hk
  have hnd := ancestors_nodup hwf rc
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
      have := Program.wfMethod_overrides (hm mt' hmem) k (by rw [hown]; exact hdrop) mt
        (by rw [hname]; unfold Program.lookup; exact h)
      exact this

end QuarzCore
