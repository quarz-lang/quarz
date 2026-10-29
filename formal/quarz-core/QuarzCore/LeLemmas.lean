/-
The order of atoms and types (G1b: variance). `Atom.le` is `leF` with as
much fuel as the two atoms are deep; under `WfClasses` (a superclass's
arguments take no arguments) that is enough, so `le` is `leF` with any
fuel (`le_iff_leF`) and unfolds as `le_cls_iff` says. The rest of the
proof uses `le_cls_iff`, never the fuel.
-/

import QuarzCore.TypeLemmas

set_option linter.deprecated false

namespace QuarzCore

variable {ct : ClassTable}

/-! ### Depth -/

theorem Atom.depth_pos (a : Atom) : 1 ≤ a.depth := by cases a <;> simp [Atom.depth]

theorem Ty.depth_mem {a : Atom} : ∀ {t : Ty}, a ∈ t → a.depth ≤ t.depth
  | b :: t, h => by
    simp only [Ty.depth]
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (Ty.depth_mem h) (Nat.le_max_right _ _)

theorem Ty.argsDepth_mem {t : Ty} : ∀ {ts : List Ty}, t ∈ ts → t.depth ≤ Ty.argsDepth ts
  | u :: ts, h => by
    simp only [Ty.argsDepth]
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (Ty.argsDepth_mem h) (Nat.le_max_right _ _)

theorem Ty.depth_le {n : Nat} : ∀ {t : Ty}, (∀ a ∈ t, a.depth ≤ n) → t.depth ≤ n
  | [], _ => Nat.zero_le _
  | a :: t, h => by
    simp only [Ty.depth]
    exact Nat.max_le.mpr ⟨h a (List.mem_cons_self ..), Ty.depth_le fun b hb => h b (List.mem_cons_of_mem _ hb)⟩

theorem Ty.argsDepth_le {n : Nat} : ∀ {ts : List Ty}, (∀ t ∈ ts, t.depth ≤ n) → Ty.argsDepth ts ≤ n
  | [], _ => Nat.zero_le _
  | t :: ts, h => by
    simp only [Ty.argsDepth]
    exact Nat.max_le.mpr ⟨h t (List.mem_cons_self ..), Ty.argsDepth_le fun u hu => h u (List.mem_cons_of_mem _ hu)⟩

/-- An atom of an argument list: no deeper than the list. -/
theorem Ty.argsDepth_flatten {x : Atom} {ts : List Ty} (h : x ∈ ts.flatten) :
    x.depth ≤ Ty.argsDepth ts := by
  obtain ⟨t, ht, hx⟩ := List.mem_flatten.mp h
  exact Nat.le_trans (Ty.depth_mem hx) (Ty.argsDepth_mem ht)

theorem Ty.depth_zero {t : Ty} (h : t.depth = 0) : t = [] := by
  cases t with
  | nil => rfl
  | cons a t =>
    have := Ty.depth_mem (List.mem_cons_self (a := a) (l := t))
    have := Atom.depth_pos a
    omega

theorem Ty.mem_subst {σ : List Ty} : ∀ {s : Ty} {a' : Atom},
    a' ∈ Ty.subst σ s ↔ ∃ a ∈ s, a' ∈ a.subst σ := by
  intro s a'
  induction s with
  | nil => simp [Ty.subst]
  | cons a s ih =>
    simp only [Ty.subst, List.mem_append, ih, List.mem_cons]
    constructor
    · rintro (h | ⟨b, hb, h⟩)
      · exact ⟨a, Or.inl rfl, h⟩
      · exact ⟨b, Or.inr hb, h⟩
    · rintro ⟨b, rfl | hb, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨b, hb, h⟩

/-- A type whose atoms take no arguments (a superclass's argument),
substituted: no deeper than the arguments, or 1. -/
theorem Ty.subst_depth (σ : List Ty) {t : Ty} (ht : t.depth ≤ 1) :
    (Ty.subst σ t).depth ≤ max (Ty.argsDepth σ) 1 := by
  apply Ty.depth_le
  intro a' ha'
  obtain ⟨a, ha, ha'⟩ := Ty.mem_subst.mp ha'
  have hda := Nat.le_trans (Ty.depth_mem ha) ht
  cases a with
  | param i =>
    simp only [Atom.subst] at ha'
    cases hi : σ[i]? with
    | none => rw [hi] at ha'; simp at ha'; subst ha'; simp only [Atom.depth, Ty.argsDepth]; omega
    | some u =>
      rw [hi] at ha'; simp only [Option.getD_some] at ha'
      exact Nat.le_trans (Ty.depth_mem ha')
        (Nat.le_trans (Ty.argsDepth_mem (List.mem_of_getElem? hi)) (Nat.le_max_left _ _))
  | cls c args =>
    simp only [Atom.subst, List.mem_singleton] at ha'; subst ha'
    simp only [Atom.depth] at hda ⊢
    have h0 : Ty.argsDepth args = 0 := by omega
    have : Ty.argsDepth (Ty.substArgs σ args) = 0 := by
      apply Nat.le_zero.mp
      apply Ty.argsDepth_le
      intro u hu
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hu
      rw [Ty.substArgs_getElem?] at hi
      cases hj : args[i]? with
      | none => rw [hj] at hi; cases hi
      | some w =>
        rw [hj] at hi; simp at hi; subst hi
        have : Ty.depth w = 0 := Nat.le_zero.mp (h0 ▸ Ty.argsDepth_mem (List.mem_of_getElem? hj))
        rw [Ty.depth_zero this]; simp [Ty.subst, Ty.depth]
    omega
  | _ => simp only [Atom.subst, List.mem_singleton] at ha'; subst ha'; simp only [Atom.depth]; omega

namespace ClassTable

/-- The chain gives an ancestor arguments no deeper than its own, or 1. -/
theorem ancestorArgsAux_depth (hwf : WfClasses ct) : ∀ n c as d bs,
    ancestorArgsAux ct n c as d = some bs → Ty.argsDepth bs ≤ max (Ty.argsDepth as) 1 := by
  intro n
  induction n with
  | zero => intro c as d bs h; simp [ancestorArgsAux] at h
  | succ n ih =>
    intro c as d bs h
    rw [ancestorArgsAux_succ] at h
    by_cases hcd : (c == d) = true
    · rw [if_pos hcd] at h; simp at h; subst h; exact Nat.le_max_left _ _
    · rw [if_neg hcd] at h
      cases hk : ct[c]? with
      | none => simp [hk] at h
      | some k =>
        simp only [hk] at h
        cases hs : k.super with
        | none => simp [hs] at h
        | some p =>
          simp only [hs] at h
          refine Nat.le_trans (ih p _ d bs h) (Nat.max_le.mpr ⟨?_, Nat.le_max_right _ _⟩)
          apply Ty.argsDepth_le
          intro u hu
          obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hu
          rw [Ty.substArgs_getElem?] at hi
          cases hj : k.superArgs[i]? with
          | none => rw [hj] at hi; cases hi
          | some w =>
            rw [hj] at hi; simp at hi; subst hi
            exact Ty.subst_depth as (hwf.superDepth c k hk w (List.mem_of_getElem? hj))

theorem ancestorArgs_depth (hwf : WfClasses ct) {c : Nat} {as : List Ty} {d : Nat} {bs : List Ty}
    (h : ct.ancestorArgs c as d = some bs) : Ty.argsDepth bs ≤ max (Ty.argsDepth as) 1 :=
  ancestorArgsAux_depth hwf _ c as d bs h

theorem variances_of {d : Nat} {k : Class} (h : ct[d]? = some k) : ct.variances d = k.params := by
  simp [variances, h]

end ClassTable

/-! ### Comparators -/

theorem Ty.leWith_mono {f g : Atom → Atom → Bool} {s t : Ty}
    (h : ∀ a ∈ s, ∀ b ∈ t, f a b = true → g a b = true) (hf : Ty.leWith f s t = true) :
    Ty.leWith g s t = true := by
  simp only [Ty.leWith, List.all_eq_true, List.any_eq_true] at hf ⊢
  intro a ha
  obtain ⟨b, hb, hab⟩ := hf a ha
  exact ⟨b, hb, h a ha b hb hab⟩

theorem Variance.leWith_mono {f g : Atom → Atom → Bool} (v : Variance) {s t : Ty}
    (h : ∀ a b, ((a ∈ s ∧ b ∈ t) ∨ (a ∈ t ∧ b ∈ s)) → f a b = true → g a b = true)
    (hf : v.leWith f s t = true) : v.leWith g s t = true := by
  cases v <;> simp only [Variance.leWith, Bool.and_eq_true] at hf ⊢
  · exact Ty.leWith_mono (fun a ha b hb => h a b (.inl ⟨ha, hb⟩)) hf
  · exact Ty.leWith_mono (fun a ha b hb => h a b (.inr ⟨ha, hb⟩)) hf
  · exact ⟨Ty.leWith_mono (fun a ha b hb => h a b (.inl ⟨ha, hb⟩)) hf.1,
      Ty.leWith_mono (fun a ha b hb => h a b (.inr ⟨ha, hb⟩)) hf.2⟩

theorem argsLeWith_mono {f g : Atom → Atom → Bool} : ∀ (vs : List Variance) (xs ys : List Ty),
    (∀ a b, ((a ∈ xs.flatten ∧ b ∈ ys.flatten) ∨ (a ∈ ys.flatten ∧ b ∈ xs.flatten)) →
      f a b = true → g a b = true) →
    argsLeWith f vs xs ys = true → argsLeWith g vs xs ys = true
  | _, [], [], _, _ => by simp [argsLeWith]
  | vs, x :: xs, y :: ys, h, hf => by
    simp only [argsLeWith, Bool.and_eq_true] at hf ⊢
    refine ⟨Variance.leWith_mono _ (fun a b hab => h a b ?_) hf.1,
      argsLeWith_mono vs.tail xs ys (fun a b hab => h a b ?_) hf.2⟩
    · simp only [List.flatten_cons, List.mem_append]
      rcases hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact .inl ⟨.inl ha, .inl hb⟩
      · exact .inr ⟨.inl ha, .inl hb⟩
    · simp only [List.flatten_cons, List.mem_append]
      rcases hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact .inl ⟨.inr ha, .inr hb⟩
      · exact .inr ⟨.inr ha, .inr hb⟩
  | _, [], _ :: _, _, hf => by simp [argsLeWith] at hf
  | _, _ :: _, [], _, hf => by simp [argsLeWith] at hf

theorem argsLeWith_length {f : Atom → Atom → Bool} : ∀ {vs : List Variance} {xs ys : List Ty},
    argsLeWith f vs xs ys = true → xs.length = ys.length
  | _, [], [], _ => rfl
  | _, _ :: _, _ :: _, h => by
    simp only [argsLeWith, Bool.and_eq_true] at h
    simp [argsLeWith_length h.2]
  | _, [], _ :: _, h => by simp [argsLeWith] at h
  | _, _ :: _, [], h => by simp [argsLeWith] at h

/-! ### Fuel -/

namespace Atom

theorem leF_succ : ∀ (n : Nat) (a b : Atom), leF ct n a b = true → leF ct (n + 1) a b = true
  | 0, a, b, h => by simp [leF] at h
  | n + 1, a, b, h => by
    cases a <;> cases b
    case cls.cls c as d bs =>
      simp only [leF, Bool.or_eq_true] at h ⊢
      rcases h with h | h
      · exact .inl h
      · right
        cases hca : ct.ancestorArgs c as d with
        | none => rw [hca] at h; cases h
        | some as' =>
          rw [hca] at h
          exact argsLeWith_mono _ _ _ (fun a b _ hab => leF_succ n a b hab) h
    all_goals simpa [leF] using h

theorem leF_mono {n m : Nat} (hnm : n ≤ m) {a b : Atom} (h : leF ct n a b = true) :
    leF ct m a b = true := by
  induction hnm with
  | refl => exact h
  | step _ ih => exact leF_succ _ a b ih

theorem depth_sum (a b : Atom) : ∃ k, a.depth + b.depth = k + 1 :=
  ⟨a.depth + b.depth - 1, by have := depth_pos a; omega⟩

/-- `le` is `leF` with the depths' fuel, for any atoms. -/
theorem le_eq_leF (a b : Atom) : a.le ct b = leF ct (a.depth + b.depth) a b := by
  obtain ⟨k, hk⟩ := depth_sum a b
  cases a <;> cases b
  case cls.cls => rfl
  all_goals rw [hk]; simp [leF, Atom.le]

/-- The depth bound the fuel rests on: an atom the chain gives an
ancestor and one of the other side's arguments are, together, less deep
than the two classes. -/
theorem pair_depth (hwf : WfClasses ct) {c : Nat} {as : List Ty} {d : Nat} {bs as' : List Ty}
    (h : ct.ancestorArgs c as d = some as') {x y : Atom}
    (hxy : (x ∈ as'.flatten ∧ y ∈ bs.flatten) ∨ (x ∈ bs.flatten ∧ y ∈ as'.flatten)) :
    x.depth + y.depth + 1 ≤ (Atom.cls c as).depth + (Atom.cls d bs).depth := by
  have hd := ClassTable.ancestorArgs_depth hwf h
  simp only [Atom.depth]
  rcases hxy with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · have := Ty.argsDepth_flatten hx; have := Ty.argsDepth_flatten hy
    have : max (Ty.argsDepth as) 1 ≤ Ty.argsDepth as + 1 := Nat.max_le.mpr ⟨by omega, by omega⟩
    omega
  · have := Ty.argsDepth_flatten hx; have := Ty.argsDepth_flatten hy
    have : max (Ty.argsDepth as) 1 ≤ Ty.argsDepth as + 1 := Nat.max_le.mpr ⟨by omega, by omega⟩
    omega

/-- Fuel beyond the depths' changes nothing. -/
theorem leF_enough (hwf : WfClasses ct) : ∀ (n : Nat) (a b : Atom), leF ct n a b = true → a.le ct b = true
  | 0, a, b, h => by simp [leF] at h
  | n + 1, a, b, h => by
    rw [le_eq_leF]
    obtain ⟨k, hk⟩ := depth_sum a b
    rw [hk]
    cases a <;> cases b
    case cls.cls c as d bs =>
      simp only [leF, Bool.or_eq_true] at h ⊢
      rcases h with h | h
      · exact .inl h
      · right
        cases hca : ct.ancestorArgs c as d with
        | none => rw [hca] at h; cases h
        | some as' =>
          rw [hca] at h
          refine argsLeWith_mono _ _ _ (fun x y hxy hf => ?_) h
          have h1 := leF_enough hwf n x y hf
          rw [le_eq_leF] at h1
          exact leF_mono (by have := pair_depth hwf hca hxy; omega) h1
    all_goals simpa [leF] using h

theorem le_iff_leF (hwf : WfClasses ct) {a b : Atom} : a.le ct b = true ↔ ∃ n, leF ct n a b = true :=
  ⟨fun h => ⟨_, (le_eq_leF a b) ▸ h⟩, fun ⟨n, h⟩ => leF_enough hwf n a b h⟩

/-- A class is below another: the other is `Object`, or the chain gives
it arguments below its own, as its parameters' variances say. -/
theorem le_cls_iff (hwf : WfClasses ct) (c : Nat) (as : List Ty) (d : Nat) (bs : List Ty) :
    (Atom.cls c as).le ct (.cls d bs) = true ↔
      (d = 0 ∧ bs = []) ∨ ∃ as', ct.ancestorArgs c as d = some as' ∧
        argsLeWith (Atom.le ct) (ct.variances d) as' bs = true := by
  rw [le_eq_leF]
  obtain ⟨k, hk⟩ := depth_sum (.cls c as) (.cls d bs)
  rw [hk]
  simp only [leF, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff]
  constructor
  · rintro (h | h)
    · exact .inl h
    · right
      cases hca : ct.ancestorArgs c as d with
      | none => rw [hca] at h; cases h
      | some as' =>
        rw [hca] at h
        exact ⟨as', rfl, argsLeWith_mono _ _ _ (fun x y _ hf => leF_enough hwf k x y hf) h⟩
  · rintro (h | ⟨as', hca, h⟩)
    · exact .inl h
    · right
      rw [hca]
      refine argsLeWith_mono _ _ _ (fun x y hxy hf => ?_) h
      rw [le_eq_leF] at hf
      exact leF_mono (by have := pair_depth hwf hca hxy; omega) hf

end Atom

/-! ### Reflexivity -/

theorem Ty.leWith_refl_of {f : Atom → Atom → Bool} {t : Ty} (h : ∀ a ∈ t, f a a = true) :
    Ty.leWith f t t = true := by
  simp only [Ty.leWith, List.all_eq_true, List.any_eq_true]
  exact fun a ha => ⟨a, ha, h a ha⟩

theorem Variance.leWith_refl_of {f : Atom → Atom → Bool} (v : Variance) {t : Ty}
    (h : ∀ a ∈ t, f a a = true) : v.leWith f t t = true := by
  cases v <;> simp [Variance.leWith, Ty.leWith_refl_of h]

theorem argsLeWith_refl_of {f : Atom → Atom → Bool} : ∀ (vs : List Variance) (ts : List Ty),
    (∀ a ∈ ts.flatten, f a a = true) → argsLeWith f vs ts ts = true
  | _, [], _ => by simp [argsLeWith]
  | vs, t :: ts, h => by
    simp only [argsLeWith, Bool.and_eq_true]
    exact ⟨Variance.leWith_refl_of _ fun a ha => h a (by simp [ha]),
      argsLeWith_refl_of vs.tail ts fun a ha => h a (by simp only [List.flatten_cons, List.mem_append]; exact .inr ha)⟩

mutual
theorem Atom.leF_refl (hwf : WfClasses ct) : ∀ a : Atom, Atom.leF ct a.depth a a = true
  | .nil | .bool | .int | .str | .float => by simp [Atom.depth, Atom.leF]
  | .param i => by simp [Atom.depth, Atom.leF]
  | .cls c as => by
    simp only [Atom.depth, Atom.leF, ClassTable.ancestorArgs_self hwf, Bool.or_eq_true]
    exact .inr (argsLeWith_refl_of _ as fun a ha => by
      obtain ⟨t, ht, hat⟩ := List.mem_flatten.mp ha
      exact Ty.argsAtoms_refl hwf as t ht a hat)
theorem Ty.atoms_refl (hwf : WfClasses ct) : ∀ (t : Ty) (a : Atom), a ∈ t → Atom.leF ct t.depth a a = true
  | [], _, h => by cases h
  | b :: t, a, h => by
    rcases List.mem_cons.mp h with h | h
    · rw [h]; exact Atom.leF_mono (Nat.le_max_left _ _) (Atom.leF_refl hwf b)
    · exact Atom.leF_mono (Nat.le_max_right _ _) (Ty.atoms_refl hwf t a h)
theorem Ty.argsAtoms_refl (hwf : WfClasses ct) : ∀ (ts : List Ty) (t : Ty), t ∈ ts → ∀ a ∈ t,
    Atom.leF ct (Ty.argsDepth ts) a a = true
  | [], _, h, _, _ => by cases h
  | u :: ts, t, h, a, ha => by
    rcases List.mem_cons.mp h with h | h
    · exact Atom.leF_mono (Nat.le_max_left _ _) (Ty.atoms_refl hwf u a (h ▸ ha))
    · exact Atom.leF_mono (Nat.le_max_right _ _) (Ty.argsAtoms_refl hwf ts t h a ha)
end

namespace Atom

theorem le_refl (hwf : WfClasses ct) (a : Atom) : a.le ct a = true :=
  (le_iff_leF hwf).mpr ⟨_, leF_refl hwf a⟩

theorem le_object (hwf : WfClasses ct) (c : Nat) (as : List Ty) :
    (Atom.cls c as).le ct (.cls 0 []) = true :=
  (le_cls_iff hwf c as 0 []).mpr (.inl ⟨rfl, rfl⟩)

/-- Every atom is below `Object`. -/
theorem le_top (hwf : WfClasses ct) (a : Atom) : a.le ct (.cls 0 []) = true := by
  cases a
  case cls c as => exact le_object hwf c as
  all_goals simp [Atom.le]

end Atom

/-! ### Types -/

theorem Ty.leWith_le {s t : Ty} : Ty.leWith (Atom.le ct) s t = Ty.le ct s t := rfl

theorem Ty.le_iff {s t : Ty} :
    s.le ct t = true ↔ ∀ a ∈ s, ∃ b ∈ t, a.le ct b = true := by
  simp [Ty.le]

theorem Ty.le_refl (hwf : WfClasses ct) (t : Ty) : t.le ct t = true :=
  Ty.le_iff.mpr fun a ha => ⟨a, ha, Atom.le_refl hwf a⟩

theorem Ty.le_of_subset (hwf : WfClasses ct) {s t : Ty}
    (h : ∀ a ∈ s, a ∈ t) : s.le ct t = true :=
  Ty.le_iff.mpr fun a ha => ⟨a, h a ha, Atom.le_refl hwf a⟩

theorem Ty.le_append_left (hwf : WfClasses ct) (s t : Ty) :
    s.le ct (s ++ t) = true := Ty.le_of_subset hwf fun a ha => List.mem_append_left _ ha

theorem Ty.le_append_right (hwf : WfClasses ct) (s t : Ty) :
    t.le ct (s ++ t) = true := Ty.le_of_subset hwf fun a ha => List.mem_append_right _ ha

theorem Ty.append_le {s t u : Ty} (h1 : s.le ct u = true)
    (h2 : t.le ct u = true) : (s ++ t).le ct u = true := by
  rw [Ty.le_iff] at *
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · exact h1 a ha
  · exact h2 a ha

theorem Ty.le_append_mono {s s' t t' : Ty} (h1 : s.le ct s' = true) (h2 : t.le ct t' = true) :
    (s ++ t).le ct (s' ++ t') = true := by
  rw [Ty.le_iff] at *
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · obtain ⟨b, hb, h⟩ := h1 a ha; exact ⟨b, List.mem_append_left _ hb, h⟩
  · obtain ⟨b, hb, h⟩ := h2 a ha; exact ⟨b, List.mem_append_right _ hb, h⟩

theorem Ty.le_top (hwf : WfClasses ct) (t : Ty) : t.le ct [.cls 0 []] = true :=
  Ty.le_iff.mpr fun a _ => ⟨_, List.mem_singleton.mpr rfl, Atom.le_top hwf a⟩

theorem Ty.le_singleton {a b : Atom} : Ty.le ct [a] [b] = a.le ct b := by simp [Ty.le]

theorem Ty.substArgs_eq_map (σ : List Ty) : ∀ ts : List Ty, Ty.substArgs σ ts = ts.map (Ty.subst σ)
  | [] => rfl
  | t :: ts => by simp [Ty.substArgs, Ty.substArgs_eq_map σ ts]

/-! ### Argument lists, position by position -/

theorem argsLeWith_getElem {f : Atom → Atom → Bool} : ∀ {vs : List Variance} {xs ys : List Ty},
    argsLeWith f vs xs ys = true → ∀ {i : Nat} {x y : Ty}, xs[i]? = some x → ys[i]? = some y →
      ((vs[i]?).getD .inv).leWith f x y = true
  | vs, x' :: xs, y' :: ys, h, i, x, y, hx, hy => by
    simp only [argsLeWith, Bool.and_eq_true] at h
    cases i with
    | zero =>
      simp at hx hy; subst hx; subst hy
      cases vs <;> simpa using h.1
    | succ i =>
      simp at hx hy
      have := argsLeWith_getElem h.2 hx hy
      cases vs <;> simpa using this
  | _, [], _, _, i, x, y, hx, _ => by simp at hx
  | _, _ :: _, [], _, i, x, y, _, hy => by simp at hy

theorem Ty.leWith_trans {f : Atom → Atom → Bool} {s t u : Ty}
    (h : ∀ a ∈ s, ∀ b ∈ t, ∀ c ∈ u, f a b = true → f b c = true → f a c = true)
    (h1 : Ty.leWith f s t = true) (h2 : Ty.leWith f t u = true) : Ty.leWith f s u = true := by
  simp only [Ty.leWith, List.all_eq_true, List.any_eq_true] at h1 h2 ⊢
  intro a ha
  obtain ⟨b, hb, hab⟩ := h1 a ha
  obtain ⟨c, hc, hbc⟩ := h2 b hb
  exact ⟨c, hc, h a ha b hb c hc hab hbc⟩

theorem Variance.leWith_trans {f : Atom → Atom → Bool} (v : Variance) {s t u : Ty}
    (h : ∀ a ∈ s, ∀ b ∈ t, ∀ c ∈ u, (f a b = true → f b c = true → f a c = true) ∧
      (f c b = true → f b a = true → f c a = true))
    (h1 : v.leWith f s t = true) (h2 : v.leWith f t u = true) : v.leWith f s u = true := by
  cases v <;> simp only [Variance.leWith, Bool.and_eq_true] at h1 h2 ⊢
  · exact Ty.leWith_trans (fun a ha b hb c hc => (h a ha b hb c hc).1) h1 h2
  · exact Ty.leWith_trans (fun c hc b hb a ha => (h a ha b hb c hc).2) h2 h1
  · exact ⟨Ty.leWith_trans (fun a ha b hb c hc => (h a ha b hb c hc).1) h1.1 h2.1,
      Ty.leWith_trans (fun c hc b hb a ha => (h a ha b hb c hc).2) h2.2 h1.2⟩

theorem argsLeWith_trans {f : Atom → Atom → Bool} : ∀ (vs : List Variance) (xs ys zs : List Ty),
    (∀ x ∈ xs.flatten, ∀ y ∈ ys.flatten, ∀ z ∈ zs.flatten, (f x y = true → f y z = true → f x z = true) ∧
      (f z y = true → f y x = true → f z x = true)) →
    argsLeWith f vs xs ys = true → argsLeWith f vs ys zs = true → argsLeWith f vs xs zs = true
  | _, [], [], [], _, _, _ => by simp [argsLeWith]
  | vs, x :: xs, y :: ys, z :: zs, h, h1, h2 => by
    simp only [argsLeWith, Bool.and_eq_true] at h1 h2 ⊢
    refine ⟨Variance.leWith_trans _ (fun a ha b hb c hc => h a (by simp [ha]) b (by simp [hb]) c (by simp [hc]))
      h1.1 h2.1, argsLeWith_trans vs.tail xs ys zs (fun a ha b hb c hc => h a ?_ b ?_ c ?_) h1.2 h2.2⟩
    all_goals simp only [List.flatten_cons, List.mem_append]; exact .inr ‹_›
  | _, [], [], _ :: _, _, _, h2 => by simp [argsLeWith] at h2
  | _, [], _ :: _, _, _, h1, _ => by simp [argsLeWith] at h1
  | _, _ :: _, [], _, _, h1, _ => by simp [argsLeWith] at h1
  | _, _ :: _, _ :: _, [], _, _, h2 => by simp [argsLeWith] at h2

theorem argsLeWith_map {f g : Atom → Atom → Bool} {F : Ty → Ty} : ∀ (vs : List Variance) (xs ys : List Ty),
    (∀ s ∈ xs, ∀ t ∈ ys, (Ty.leWith f s t = true → Ty.leWith g (F s) (F t) = true) ∧
      (Ty.leWith f t s = true → Ty.leWith g (F t) (F s) = true)) →
    argsLeWith f vs xs ys = true → argsLeWith g vs (xs.map F) (ys.map F) = true
  | _, [], [], _, _ => by simp [argsLeWith]
  | vs, x :: xs, y :: ys, h, hf => by
    simp only [argsLeWith, Bool.and_eq_true, List.map_cons] at hf ⊢
    have hxy := h x (List.mem_cons_self) y (List.mem_cons_self)
    refine ⟨?_, argsLeWith_map vs.tail xs ys (fun s hs t ht => h s (List.mem_cons_of_mem _ hs) t
      (List.mem_cons_of_mem _ ht)) hf.2⟩
    have := hf.1
    cases hv : vs.headD .inv <;> rw [hv] at this <;> simp only [Variance.leWith, Bool.and_eq_true] at this ⊢
    · exact hxy.1 this
    · exact hxy.2 this
    · exact ⟨hxy.1 this.1, hxy.2 this.2⟩
  | _, [], _ :: _, _, hf => by simp [argsLeWith] at hf
  | _, _ :: _, [], _, hf => by simp [argsLeWith] at hf

/-! ### Substitution through arguments compared by variance

Where a type names the parameters as their variances allow (`posOk`),
substituting arguments `xs` below `ys` (as the variances say) gives a
type below (in a positive position) or above (in a negative one). -/

theorem if_not_pos {α} (pos : Bool) (x y : α) : (if (!pos) = true then x else y) = (if pos = true then y else x) := by
  cases pos <;> rfl

mutual
theorem Atom.subst_var (hwf : WfClasses ct) {vs : List Variance} {xs ys : List Ty}
    (hxy : argsLeWith (Atom.le ct) vs xs ys = true) :
    ∀ (a : Atom) (pos : Bool), a.posOk ct vs pos = true →
      Ty.le ct (a.subst (if pos then xs else ys)) (a.subst (if pos then ys else xs)) = true
  | .param i, pos, h => by
    have hlen := argsLeWith_length hxy
    simp only [Atom.subst]
    cases hx : xs[i]? with
    | none =>
      have hy : ys[i]? = none := by
        simp only [List.getElem?_eq_none_iff] at hx ⊢; omega
      cases pos <;> simp [hx, hy, Ty.le_refl hwf]
    | some x =>
      obtain ⟨y, hy⟩ : ∃ y, ys[i]? = some y :=
        ⟨_, List.getElem?_eq_getElem (by have := (List.getElem?_eq_some_iff.mp hx).1; omega)⟩
      have hc := argsLeWith_getElem hxy hx hy
      simp only [Atom.posOk] at h
      cases hv : vs[i]? with
      | none =>
        rw [hv] at hc; simp only [Option.getD_none, Variance.leWith, Bool.and_eq_true] at hc
        cases pos <;> simp only [hx, hy, Bool.false_eq_true, if_false, if_true, Option.getD_some]
        · exact hc.2
        · exact hc.1
      | some v =>
        rw [hv] at hc h; simp only [Option.getD_some] at hc
        cases v <;> simp only [Variance.leWith, Bool.and_eq_true] at hc h
        · subst h; simpa [hx, hy, Ty.leWith_le] using hc
        · cases pos
          · simpa [hx, hy, Ty.leWith_le] using hc
          · simp at h
        · cases pos <;> simp only [hx, hy, Bool.false_eq_true, if_false, if_true, Option.getD_some]
          · exact hc.2
          · exact hc.1
  | .cls d args, pos, h => by
    simp only [Atom.posOk] at h
    simp only [Atom.subst, Ty.le_singleton]
    exact (Atom.le_cls_iff hwf d _ d _).mpr (.inr ⟨_, ClassTable.ancestorArgs_self hwf d _,
      Ty.substArgs_var hwf hxy args pos _ h⟩)
  | .nil, _, _ | .bool, _, _ | .int, _, _ | .str, _, _ | .float, _, _ => by
    simp [Atom.subst, Ty.le_singleton, Atom.le]
theorem Ty.subst_var (hwf : WfClasses ct) {vs : List Variance} {xs ys : List Ty}
    (hxy : argsLeWith (Atom.le ct) vs xs ys = true) :
    ∀ (t : Ty) (pos : Bool), t.posOk ct vs pos = true →
      Ty.le ct (t.subst (if pos then xs else ys)) (t.subst (if pos then ys else xs)) = true
  | [], _, _ => by simp [Ty.subst, Ty.le]
  | a :: t, pos, h => by
    simp only [Ty.posOk, Bool.and_eq_true] at h
    simp only [Ty.subst]
    exact Ty.le_append_mono (Atom.subst_var hwf hxy a pos h.1) (Ty.subst_var hwf hxy t pos h.2)
theorem Ty.substArgs_var (hwf : WfClasses ct) {vs : List Variance} {xs ys : List Ty}
    (hxy : argsLeWith (Atom.le ct) vs xs ys = true) :
    ∀ (ts : List Ty) (pos : Bool) (ws : List Variance), Ty.argsPosOk ct vs pos ws ts = true →
      argsLeWith (Atom.le ct) ws (Ty.substArgs (if pos then xs else ys) ts)
        (Ty.substArgs (if pos then ys else xs) ts) = true
  | [], _, _, _ => by simp [Ty.substArgs, argsLeWith]
  | t :: ts, pos, ws, h => by
    simp only [Ty.argsPosOk, Bool.and_eq_true] at h
    simp only [Ty.substArgs, argsLeWith, Bool.and_eq_true]
    refine ⟨?_, Ty.substArgs_var hwf hxy ts pos ws.tail h.2⟩
    have h1 := h.1
    cases hw : ws.headD .inv <;> rw [hw] at h1 <;>
      simp only [Variance.leWith, Bool.and_eq_true, Ty.leWith_le] at h1 ⊢
    · exact Ty.subst_var hwf hxy t pos h1
    · have := Ty.subst_var hwf hxy t (!pos) h1
      rwa [if_not_pos, if_not_pos] at this
    · refine ⟨Ty.subst_var hwf hxy t pos h1.1, ?_⟩
      have := Ty.subst_var hwf hxy t (!pos) h1.2
      rwa [if_not_pos, if_not_pos] at this
end

/-! ### Along the chain -/

namespace ClassTable

/-- Arguments below others (as a class's variances say) give its
ancestors arguments below the others' (the superclass's arguments stand
in positive positions). -/
theorem chain_monoAux (hwf : WfClasses ct) : ∀ n d xs ys e xs' ys',
    ancestorArgsAux ct n d xs e = some xs' → ancestorArgsAux ct n d ys e = some ys' →
    argsLeWith (Atom.le ct) (ct.variances d) xs ys = true →
    argsLeWith (Atom.le ct) (ct.variances e) xs' ys' = true := by
  intro n
  induction n with
  | zero => intro d xs ys e xs' ys' h; simp [ancestorArgsAux] at h
  | succ n ih =>
    intro d xs ys e xs' ys' h1 h2 hxy
    rw [ancestorArgsAux_succ] at h1 h2
    by_cases hde : (d == e) = true
    · rw [if_pos hde] at h1 h2; simp at h1 h2 hde; subst h1; subst h2; subst hde; exact hxy
    · rw [if_neg hde] at h1 h2
      cases hk : ct[d]? with
      | none => simp [hk] at h1
      | some k =>
        simp only [hk] at h1 h2
        cases hs : k.super with
        | none => simp [hs] at h1
        | some p =>
          simp only [hs] at h1 h2
          rw [variances_of hk] at hxy
          have := Ty.substArgs_var hwf hxy k.superArgs true _ (hwf.superPos d k p hk hs)
          simp only [if_true] at this
          exact ih p _ _ e xs' ys' h1 h2 this

theorem chain_mono (hwf : WfClasses ct) {d : Nat} {xs ys : List Ty} {e : Nat} {xs' ys' : List Ty}
    (h1 : ct.ancestorArgs d xs e = some xs') (h2 : ct.ancestorArgs d ys e = some ys')
    (hxy : argsLeWith (Atom.le ct) (ct.variances d) xs ys = true) :
    argsLeWith (Atom.le ct) (ct.variances e) xs' ys' = true :=
  chain_monoAux hwf _ d xs ys e xs' ys' h1 h2 hxy

end ClassTable

/-! ### Transitivity, by the atoms' depths -/

namespace Atom

theorem le_trans_aux (hwf : WfClasses ct) : ∀ (n : Nat) (a b c : Atom),
    a.depth + b.depth + c.depth ≤ n → a.le ct b = true → b.le ct c = true → a.le ct c = true
  | 0, a, _, _, hn, _, _ => absurd hn (by have := depth_pos a; omega)
  | n + 1, a, b, c, hn, hab, hbc => by
    cases c
    case cls e cs =>
      cases b
      case cls d bs =>
        cases a
        case cls c1 as1 =>
          rw [le_cls_iff hwf] at hab hbc ⊢
          rcases hbc with ⟨rfl, rfl⟩ | ⟨bs', hbs', hbc⟩
          · exact .inl ⟨rfl, rfl⟩
          rcases hab with ⟨rfl, rfl⟩ | ⟨as', has', hab⟩
          · obtain ⟨rfl, rfl⟩ := ClassTable.ancestorArgs_root hwf e bs' hbs'
            have := argsLeWith_length hbc
            cases cs with
            | nil => exact .inl ⟨rfl, rfl⟩
            | cons => simp at this
          right
          have he : e ∈ ct.ancestors d := ClassTable.ancestorArgs_mem hwf d bs e bs' hbs'
          obtain ⟨as'', has''⟩ := ClassTable.ancestorArgs_of_mem hwf d as' e he
          refine ⟨as'', ClassTable.ancestorArgs_trans hwf has' has'', ?_⟩
          have hm := ClassTable.chain_mono hwf has'' hbs' hab
          have d1 := ClassTable.ancestorArgs_depth hwf has'
          have d2 := ClassTable.ancestorArgs_depth hwf has''
          have d3 := ClassTable.ancestorArgs_depth hwf hbs'
          simp only [Atom.depth] at hn
          refine argsLeWith_trans _ _ _ _ (fun x hx y hy z hz => ?_) hm hbc
          have hx' := Ty.argsDepth_flatten hx
          have hy' := Ty.argsDepth_flatten hy
          have hz' := Ty.argsDepth_flatten hz
          have : x.depth + y.depth + z.depth ≤ n := by
            have : max (Ty.argsDepth as1) 1 ≤ Ty.argsDepth as1 + 1 := Nat.max_le.mpr ⟨by omega, by omega⟩
            have : max (Ty.argsDepth as') 1 ≤ Ty.argsDepth as1 + 1 := Nat.max_le.mpr ⟨by omega, by omega⟩
            have : max (Ty.argsDepth bs) 1 ≤ Ty.argsDepth bs + 1 := Nat.max_le.mpr ⟨by omega, by omega⟩
            omega
          exact ⟨fun h1 h2 => le_trans_aux hwf n x y z this h1 h2,
            fun h1 h2 => le_trans_aux hwf n z y x (by omega) h1 h2⟩
        all_goals
          simp only [Atom.le, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at hab
          obtain ⟨rfl, rfl⟩ := hab
          rcases (le_cls_iff hwf 0 [] e cs).mp hbc with ⟨rfl, rfl⟩ | ⟨bs', hbs', hbc⟩
          · simp [Atom.le]
          · obtain ⟨rfl, rfl⟩ := ClassTable.ancestorArgs_root hwf e bs' hbs'
            have := argsLeWith_length hbc
            cases cs with
            | nil => simp [Atom.le]
            | cons => simp at this
      all_goals cases a <;> simp_all [Atom.le]
    all_goals cases b <;> cases a <;> simp_all [Atom.le]

theorem le_trans (hwf : WfClasses ct) {a b c : Atom} (hab : a.le ct b = true)
    (hbc : b.le ct c = true) : a.le ct c = true :=
  le_trans_aux hwf _ a b c (Nat.le_refl _) hab hbc

/-- A class is below an ancestor given exactly the arguments the chain
gives it. -/
theorem le_of_ancestorArgs (hwf : WfClasses ct) {c : Nat} {as : List Ty} {d : Nat} {bs : List Ty}
    (h : ct.ancestorArgs c as d = some bs) : (Atom.cls c as).le ct (.cls d bs) = true :=
  (le_cls_iff hwf c as d bs).mpr (.inr ⟨bs, h, argsLeWith_refl_of _ _ fun a _ => le_refl hwf a⟩)

end Atom

theorem Ty.le_trans (hwf : WfClasses ct) {s t u : Ty}
    (h1 : s.le ct t = true) (h2 : t.le ct u = true) : s.le ct u = true := by
  rw [Ty.le_iff] at *
  intro a ha
  obtain ⟨b, hb, hab⟩ := h1 a ha
  obtain ⟨c, hc, hbc⟩ := h2 b hb
  exact ⟨c, hc, Atom.le_trans hwf hab hbc⟩

/-! ### Substitution keeps the order -/

theorem Ty.subst_le_of {σ : List Ty} {s t : Ty}
    (h : ∀ a ∈ s, ∀ b ∈ t, a.le ct b = true → Ty.le ct (a.subst σ) (b.subst σ) = true)
    (hst : s.le ct t = true) : Ty.le ct (s.subst σ) (t.subst σ) = true := by
  rw [Ty.le_iff] at hst ⊢
  intro a' ha'
  obtain ⟨a, ha, ha'⟩ := Ty.mem_subst.mp ha'
  obtain ⟨b, hb, hab⟩ := hst a ha
  obtain ⟨b', hb', h'⟩ := Ty.le_iff.mp (h a ha b hb hab) a' ha'
  exact ⟨b', Ty.mem_subst.mpr ⟨b, hb, hb'⟩, h'⟩

theorem Atom.subst_le_aux (hwf : WfClasses ct) (σ : List Ty) : ∀ (n : Nat) (a b : Atom),
    a.depth + b.depth ≤ n → a.le ct b = true → Ty.le ct (a.subst σ) (b.subst σ) = true
  | 0, a, _, hn, _ => absurd hn (by have := depth_pos a; omega)
  | n + 1, a, b, hn, h => by
    cases b
    case cls d bs =>
      cases a
      case cls c as =>
        rw [Atom.le_cls_iff hwf] at h
        rcases h with ⟨rfl, rfl⟩ | ⟨as', has', h⟩
        · simp only [Atom.subst, Ty.substArgs]; exact Ty.le_top hwf _
        · simp only [Atom.subst, Ty.le_singleton]
          refine (Atom.le_cls_iff hwf c _ d _).mpr (.inr ⟨_, ClassTable.ancestorArgs_subst ct σ has', ?_⟩)
          rw [Ty.substArgs_eq_map, Ty.substArgs_eq_map]
          have d1 := ClassTable.ancestorArgs_depth hwf has'
          simp only [Atom.depth] at hn
          refine argsLeWith_map _ _ _ (fun s hs t ht => ⟨fun hst => ?_, fun hts => ?_⟩) h
          · rw [Ty.leWith_le] at hst ⊢
            refine Ty.subst_le_of (fun x hx y hy hxy => Atom.subst_le_aux hwf σ n x y ?_ hxy) hst
            have := Nat.le_trans (Ty.depth_mem hx) (Ty.argsDepth_mem hs)
            have := Nat.le_trans (Ty.depth_mem hy) (Ty.argsDepth_mem ht)
            have : max (Ty.argsDepth as) 1 ≤ Ty.argsDepth as + 1 := Nat.max_le.mpr ⟨by omega, by omega⟩
            omega
          · rw [Ty.leWith_le] at hts ⊢
            refine Ty.subst_le_of (fun x hx y hy hxy => Atom.subst_le_aux hwf σ n x y ?_ hxy) hts
            have := Nat.le_trans (Ty.depth_mem hx) (Ty.argsDepth_mem ht)
            have := Nat.le_trans (Ty.depth_mem hy) (Ty.argsDepth_mem hs)
            have : max (Ty.argsDepth as) 1 ≤ Ty.argsDepth as + 1 := Nat.max_le.mpr ⟨by omega, by omega⟩
            omega
      all_goals
        simp only [Atom.le, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [Atom.subst, Ty.substArgs]; exact Ty.le_top hwf _
    case param j =>
      cases a
      case param i =>
        simp only [Atom.le, beq_iff_eq] at h
        subst h
        exact Ty.le_refl hwf _
      all_goals simp_all [Atom.le]
    all_goals cases a <;> simp_all [Atom.le] <;> simp [Atom.subst, Ty.le, Atom.le]

theorem Atom.subst_le (hwf : WfClasses ct) (σ : List Ty) {a b : Atom}
    (h : a.le ct b = true) : Ty.le ct (a.subst σ) (b.subst σ) = true :=
  Atom.subst_le_aux hwf σ _ a b (Nat.le_refl _) h

theorem Ty.subst_le (hwf : WfClasses ct) (σ : List Ty) {s t : Ty}
    (h : s.le ct t = true) : Ty.le ct (s.subst σ) (t.subst σ) = true :=
  Ty.subst_le_of (fun _ _ _ _ hab => Atom.subst_le hwf σ hab) h

/-- Argument lists compared by variance, substituted. -/
theorem argsLeWith_subst (hwf : WfClasses ct) (σ : List Ty) {vs : List Variance} {xs ys : List Ty}
    (h : argsLeWith (Atom.le ct) vs xs ys = true) :
    argsLeWith (Atom.le ct) vs (Ty.substArgs σ xs) (Ty.substArgs σ ys) = true := by
  rw [Ty.substArgs_eq_map, Ty.substArgs_eq_map]
  exact argsLeWith_map _ _ _ (fun s _ t _ => ⟨fun h => by rw [Ty.leWith_le] at h ⊢; exact Ty.subst_le hwf σ h,
    fun h => by rw [Ty.leWith_le] at h ⊢; exact Ty.subst_le hwf σ h⟩) h

theorem argsLeWith_le_trans (hwf : WfClasses ct) {vs : List Variance} {xs ys zs : List Ty}
    (h1 : argsLeWith (Atom.le ct) vs xs ys = true) (h2 : argsLeWith (Atom.le ct) vs ys zs = true) :
    argsLeWith (Atom.le ct) vs xs zs = true :=
  argsLeWith_trans _ _ _ _ (fun _ _ _ _ _ _ => ⟨fun a b => Atom.le_trans hwf a b,
    fun a b => Atom.le_trans hwf a b⟩) h1 h2

end QuarzCore
