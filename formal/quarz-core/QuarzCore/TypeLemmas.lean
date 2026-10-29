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
  /-- The root has no parameters. -/
  rootParams : ∀ (k : Class), ct[0]? = some k → k.params = []
  super : ∀ i k, 0 < i → ct[i]? = some k → ∃ d, k.super = some d ∧ d < i
  /-- A superclass gets as many arguments as it has parameters. -/
  superArgs : ∀ (i : Nat) (k : Class) (d : Nat), ct[i]? = some k → k.super = some d →
    k.superArgs.length = (((ct[d]?).map Class.params).getD []).length
  names : ∀ i, i < ct.length → ((ct.allFields i).map (·.name)).Nodup
  /-- A superclass's arguments take no arguments themselves (their atoms
  are parameters or take none). -/
  superFlat : ∀ (i : Nat) (k : Class), ct[i]? = some k → ∀ t ∈ k.superArgs, ∀ a ∈ t,
    a.isParam = true ∨ a.depth ≤ 1
  /-- A superclass's arguments name the class's parameters as their
  variances allow, in a positive position. -/
  superPos : ∀ (i : Nat) (k : Class) (d : Nat), ct[i]? = some k → k.super = some d →
    Ty.argsPosOk ct k.params true (ct.variances d) k.superArgs = true
  /-- A superclass's arguments are within its parameters' bounds (with
  the class's own parameters at theirs). -/
  superBounds : ∀ (i : Nat) (k : Class) (d : Nat), ct[i]? = some k → k.super = some d →
    ∀ (j : Nat) (t : Ty), k.superArgs[j]? = some t → t.le ct k.bounds (Ty.boundOf (ct.boundsOf d) j) = true
  /-- No more bounds than parameters. -/
  boundsLen : ∀ (i : Nat) (k : Class), ct[i]? = some k → k.bounds.length ≤ k.params.length
  /-- A `data` type has no subclasses, nor has a variant; an `enum`'s are
  its variants. -/
  dataLeaf : ∀ (i : Nat) (k : Class) (d : Nat), ct[i]? = some k → k.super = some d →
    ct.kindOf d ≠ .data
  variantLeaf : ∀ (i : Nat) (k : Class) (d : Nat), ct[i]? = some k → k.super = some d →
    ct.kindOf d ≠ .variant
  enumChild : ∀ (i : Nat) (k : Class) (d : Nat), ct[i]? = some k → k.super = some d →
    ct.kindOf d = .enumC → k.kind = .variant ∧ k.params = []
  /-- The root is a class. -/
  rootKind : ∀ (k : Class), ct[0]? = some k → k.kind = .cls

/-- What `wfClasses` says of a class other than the root. -/
theorem Program.wfClasses_class {P : Program} (h : P.wfClasses = true) {i : Nat} {k : Class}
    (hk : P.classes[i]? = some k) (hi : i ≠ 0) :
    ∃ d, k.super = some d ∧ d < i ∧
      k.superArgs.length = (((P.classes[d]?).map Class.params).getD []).length ∧
      (k.superArgs.all fun t => t.all fun a => a.isParam || decide (a.depth ≤ 1)) = true ∧
      Ty.argsPosOk P.classes k.params true (P.classes.variances d) k.superArgs = true ∧
      (k.superArgs.zipIdx.all fun (t, j) =>
        t.le P.classes k.bounds (Ty.boundOf (P.classes.boundsOf d) j)) = true := by
  simp only [Program.wfClasses, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  have := h.1.1.1.2 i (List.getElem?_eq_some_iff.mp hk).1
  have hi' : (i == 0) = false := by simp [hi]
  simp only [hk, hi', Bool.false_eq_true, if_false] at this
  revert this
  cases hs : k.super with
  | none => simp
  | some d =>
    intro this
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, _⟩, h4⟩, h5⟩, h6⟩ := this
    exact ⟨d, rfl, h1, h2, h4, h5, h6⟩

theorem Program.wfClasses_sound {P : Program} (h : P.wfClasses = true) : WfClasses P.classes := by
  have h' := h
  simp only [Program.wfClasses, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h'
  obtain ⟨⟨⟨⟨hne, hall⟩, hnames⟩, hblen⟩, hkind⟩ := h'
  have root : ∀ k, P.classes[0]? = some k → k.super = none ∧ k.params = [] ∧ k.superArgs = [] := by
    intro k hk
    have := hall 0 hne
    simp [hk] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  have hnz : ∀ i k, P.classes[i]? = some k → k.super.isSome → i ≠ 0 := by
    rintro i k hk hs rfl
    rw [(root k hk).1] at hs; cases hs
  refine ⟨hne, fun k hk => (root k hk).1, fun k hk => (root k hk).2.1, fun i k hi hk => ?_,
    fun i k d hk hs => ?_, hnames, fun i k hk t ht a ha => ?_, fun i k d hk hs => ?_,
    fun i k d hk hs j t hj => ?_, fun i k hk => ?_, fun i k d hk hs => ?_, fun i k d hk hs => ?_,
    fun i k d hk hs hd => ?_, fun k hk => ?_⟩
  · obtain ⟨d, hd, h1, _⟩ := Program.wfClasses_class h hk (by omega)
    exact ⟨d, hd, h1⟩
  · obtain ⟨d', hd', _, h2, _⟩ := Program.wfClasses_class h hk (hnz i k hk (by simp [hs]))
    rw [hs] at hd'; cases hd'; exact h2
  · by_cases hi : i = 0
    · subst hi; rw [(root k hk).2.2] at ht; cases ht
    · obtain ⟨_, _, _, _, h4, _⟩ := Program.wfClasses_class h hk hi
      simp only [List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h4
      exact h4 t ht a ha
  · obtain ⟨d', hd', _, _, _, h5, _⟩ := Program.wfClasses_class h hk (hnz i k hk (by simp [hs]))
    rw [hs] at hd'; cases hd'; exact h5
  · obtain ⟨d', hd', _, _, _, _, h6⟩ := Program.wfClasses_class h hk (hnz i k hk (by simp [hs]))
    rw [hs] at hd'; cases hd'
    exact List.all_eq_true.mp h6 (t, j) (List.mem_zipIdx_iff_getElem?.mpr hj)
  · have := hblen i (List.getElem?_eq_some_iff.mp hk).1
    simp only [hk, decide_eq_true_eq] at this
    exact this
  · have := hkind i (List.getElem?_eq_some_iff.mp hk).1
    simp only [hk, hs, Bool.and_eq_true, bne_iff_ne, ne_eq] at this
    exact this.1.1.1
  · have := hkind i (List.getElem?_eq_some_iff.mp hk).1
    simp only [hk, hs, Bool.and_eq_true, bne_iff_ne, ne_eq] at this
    exact this.1.1.2
  · have := hkind i (List.getElem?_eq_some_iff.mp hk).1
    simp only [hk, hs, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_true, beq_iff_eq,
      List.isEmpty_iff] at this
    exact this.1.2.resolve_left (by simpa using hd)
  · have := hkind 0 hne
    simp [hk] at this
    exact this.2

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

/-! ### Closed types -/

theorem Ty.closed_append : ∀ s t : Ty, Ty.closed (s ++ t) = (Ty.closed s && Ty.closed t)
  | [], t => by simp [Ty.closed]
  | a :: s, t => by simp [Ty.closed, Ty.closed_append s t, Bool.and_assoc]

theorem Ty.closedArgs_mem (σ : List Ty) (hσ : Ty.closedArgs σ = true) : ∀ t ∈ σ, Ty.closed t = true := by
  induction σ with
  | nil => intro t h; cases h
  | cons u σ ih =>
    intro t ht
    simp only [Ty.closedArgs, Bool.and_eq_true] at hσ
    rcases List.mem_cons.mp ht with rfl | ht
    · exact hσ.1
    · exact ih hσ.2 t ht

-- Substituting closed arguments gives closed types.
mutual
theorem Atom.subst_closed (σ : List Ty) (hσ : Ty.closedArgs σ = true) : ∀ a : Atom,
    Ty.closed (Atom.subst σ a) = true
  | .nil | .bool | .int | .str | .float => rfl
  | .param i => by
    simp only [Atom.subst]
    cases h : σ[i]? with
    | none => rfl
    | some t =>
      simp only [Option.getD]
      exact Ty.closedArgs_mem σ hσ t (List.mem_of_getElem? h)
  | .cls c args => by
    simp only [Atom.subst, Ty.closed, Atom.closed, Bool.and_true]
    exact Ty.substArgs_closed σ hσ args
theorem Ty.subst_closed (σ : List Ty) (hσ : Ty.closedArgs σ = true) : ∀ t : Ty,
    Ty.closed (Ty.subst σ t) = true
  | [] => rfl
  | a :: t => by
    simp only [Ty.subst]
    rw [Ty.closed_append, Bool.and_eq_true]
    exact ⟨Atom.subst_closed σ hσ a, Ty.subst_closed σ hσ t⟩
theorem Ty.substArgs_closed (σ : List Ty) (hσ : Ty.closedArgs σ = true) : ∀ ts : List Ty,
    Ty.closedArgs (Ty.substArgs σ ts) = true
  | [] => rfl
  | t :: ts => by
    simp only [Ty.substArgs, Ty.closedArgs, Bool.and_eq_true]
    exact ⟨Ty.subst_closed σ hσ t, Ty.substArgs_closed σ hσ ts⟩
end


/-- An atom that is closed or names a parameter the arguments give is closed
once substituted with closed arguments. -/
theorem Atom.subst_closed_of_wf (σ : List Ty) (hσ : Ty.closedArgs σ = true) {a : Atom}
    (h : (a.closed || (a.isParam && a.paramIdx < σ.length)) = true) :
    Ty.closed (a.subst σ) = true := Atom.subst_closed σ hσ a

theorem Ty.subst_closed_of_wf (σ : List Ty) (hσ : Ty.closedArgs σ = true) (t : Ty) :
    Ty.closed (t.subst σ) = true := Ty.subst_closed σ hσ t

theorem Ty.substArgs_closed_of_wf (σ : List Ty) (hσ : Ty.closedArgs σ = true) (ts : List Ty) :
    Ty.closedArgs (Ty.substArgs σ ts) = true := Ty.substArgs_closed σ hσ ts

-- A closed type substitutes to itself.
mutual
theorem Atom.subst_closed_id (σ : List Ty) : ∀ a : Atom, a.closed = true → Atom.subst σ a = [a]
  | .nil, _ | .bool, _ | .int, _ | .str, _ | .float, _ => rfl
  | .param i, h => by simp [Atom.closed] at h
  | .cls c args, h => by
    simp only [Atom.closed] at h
    simp [Atom.subst, Ty.substArgs_closed_id σ args h]
theorem Ty.subst_closed_id (σ : List Ty) : ∀ t : Ty, t.closed = true → Ty.subst σ t = t
  | [], _ => rfl
  | a :: t, h => by
    simp only [Ty.closed, Bool.and_eq_true] at h
    simp [Ty.subst, Atom.subst_closed_id σ a h.1, Ty.subst_closed_id σ t h.2]
theorem Ty.substArgs_closed_id (σ : List Ty) : ∀ ts : List Ty, Ty.closedArgs ts = true →
    Ty.substArgs σ ts = ts
  | [], _ => rfl
  | t :: ts, h => by
    simp only [Ty.closedArgs, Bool.and_eq_true] at h
    simp [Ty.substArgs, Ty.subst_closed_id σ t h.1, Ty.substArgs_closed_id σ ts h.2]
end

namespace ClassTable

/-! ### Fields seen from a class -/

theorem allFieldsAt_getElem? (ct : ClassTable) (c : Nat) (as : List Ty) (i : Nat) :
    (ct.allFieldsAt c as)[i]? = ((ct.allFieldsDecl c)[i]?).map fun (d, f) =>
      { f with ty := Ty.subst ((ct.ancestorArgs c as d).getD []) f.ty } := by
  simp [allFieldsAt]

theorem allFields_getElem? (ct : ClassTable) (c : Nat) (i : Nat) :
    (ct.allFields c)[i]? = ((ct.allFieldsDecl c)[i]?).map (·.2) := by
  simp [allFields]

theorem allFieldsAt_length (ct : ClassTable) (c : Nat) (as : List Ty) :
    (ct.allFieldsAt c as).length = (ct.allFields c).length := by
  simp [allFieldsAt, allFields]

/-- A field seen from the class is the declared one with its type
substituted: same name, `var` and default. -/
theorem allFieldsAt_some (ct : ClassTable) {c : Nat} {as : List Ty} {i : Nat} {f : Field}
    (h : (ct.allFieldsAt c as)[i]? = some f) :
    ∃ d f0, (ct.allFieldsDecl c)[i]? = some (d, f0) ∧ (ct.allFields c)[i]? = some f0 ∧
      f = { f0 with ty := Ty.subst ((ct.ancestorArgs c as d).getD []) f0.ty } := by
  rw [allFieldsAt_getElem?] at h
  cases hd : (ct.allFieldsDecl c)[i]? with
  | none => simp [hd] at h
  | some df =>
    obtain ⟨d, f0⟩ := df
    simp [hd] at h
    exact ⟨d, f0, rfl, by simp [allFields_getElem?, hd], h.symm⟩

theorem allFields_some (ct : ClassTable) {c : Nat} (as : List Ty) {i : Nat} {f0 : Field}
    (h : (ct.allFields c)[i]? = some f0) :
    ∃ d, (ct.allFieldsDecl c)[i]? = some (d, f0) ∧
      (ct.allFieldsAt c as)[i]? = some { f0 with ty := Ty.subst ((ct.ancestorArgs c as d).getD []) f0.ty } := by
  rw [allFields_getElem?] at h
  cases hd : (ct.allFieldsDecl c)[i]? with
  | none => simp [hd] at h
  | some df =>
    obtain ⟨d, f1⟩ := df
    simp [hd] at h; subst h
    exact ⟨d, rfl, by simp [allFieldsAt_getElem?, hd]⟩

/-! ### Ancestors' arguments -/

theorem ancestorArgsAux_succ (ct : ClassTable) (n c : Nat) (as : List Ty) (d : Nat) :
    ancestorArgsAux ct (n + 1) c as d =
      (if c == d then some as else
        match ct[c]? with
        | some k => match k.super with
          | some p => ancestorArgsAux ct n p (Ty.substArgs as k.superArgs) d
          | none => none
        | none => none) := rfl

/-- Found with some fuel, found with more. -/
theorem ancestorArgsAux_mono (ct : ClassTable) :
    ∀ n m c as d bs, n ≤ m → ancestorArgsAux ct n c as d = some bs →
      ancestorArgsAux ct m c as d = some bs := by
  intro n
  induction n with
  | zero => intro m c as d bs _ h; simp [ancestorArgsAux] at h
  | succ n ih =>
    intro m c as d bs hle h
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [ancestorArgsAux_succ] at h ⊢
    by_cases hcd : (c == d) = true
    · rw [if_pos hcd] at h ⊢; exact h
    · rw [if_neg hcd] at h ⊢
      cases hk : ct[c]? with
      | none => simp [hk] at h
      | some k =>
        simp only [hk] at h ⊢
        cases hs : k.super with
        | none => simp [hs] at h
        | some p => simp only [hs] at h ⊢; exact ih m p _ d bs (by omega) h

/-- The classes a chain visits with fuel `n` from `c`: the fuel bounds the
chain, and under `wf` each step goes to a smaller index. -/
theorem ancestorArgsAux_step (ct : ClassTable) (hwf : WfClasses ct) :
    ∀ n c as d bs, ancestorArgsAux ct n c as d = some bs → d ≤ c := by
  intro n
  induction n with
  | zero => intro c as d bs h; simp [ancestorArgsAux] at h
  | succ n ih =>
    intro c as d bs h
    rw [ancestorArgsAux_succ] at h
    by_cases hcd : (c == d) = true
    · simp at hcd; omega
    · rw [if_neg hcd] at h
      cases hk : ct[c]? with
      | none => simp [hk] at h
      | some k =>
        simp only [hk] at h
        cases hs : k.super with
        | none => simp [hs] at h
        | some p =>
          simp only [hs] at h
          have hp : p < c := by
            rcases Nat.eq_zero_or_pos c with rfl | hpos
            · have := hwf.root k hk; simp [this] at hs
            · obtain ⟨d', hd', hlt⟩ := hwf.super c k hpos hk
              rw [hs] at hd'; cases hd'; exact hlt
          have := ih p _ d bs h
          omega

/-- The chain from `c` to `d`, then from `d` to `e`, is the chain from
`c` to `e`. -/
theorem ancestorArgsAux_trans (ct : ClassTable) (hwf : WfClasses ct) :
    ∀ n m c as d bs e cs, ancestorArgsAux ct n c as d = some bs →
      ancestorArgsAux ct m d bs e = some cs → ancestorArgsAux ct (n + m) c as e = some cs := by
  intro n
  induction n with
  | zero => intro m c as d bs e cs h; simp [ancestorArgsAux] at h
  | succ n ih =>
    intro m c as d bs e cs h1 h2
    rw [ancestorArgsAux_succ] at h1
    by_cases hcd : (c == d) = true
    · rw [if_pos hcd] at h1
      simp at h1 hcd; subst h1; subst hcd
      exact ancestorArgsAux_mono ct m (n + 1 + m) c as e cs (by omega) h2
    · rw [if_neg hcd] at h1
      cases hk : ct[c]? with
      | none => simp [hk] at h1
      | some k =>
        simp only [hk] at h1
        cases hs : k.super with
        | none => simp [hs] at h1
        | some p =>
          simp only [hs] at h1
          have step := ih m p _ d bs e cs h1 h2
          have : n + 1 + m = (n + m) + 1 := by omega
          rw [this, ancestorArgsAux_succ]
          -- `e` is at or below `d`, which is below `c`: `c ≠ e`.
          have hdc := ancestorArgsAux_step ct hwf (n) p _ d bs h1
          have hed := ancestorArgsAux_step ct hwf m d bs e cs h2
          have hp : p < c := by
            rcases Nat.eq_zero_or_pos c with rfl | hpos
            · have := hwf.root k hk; simp [this] at hs
            · obtain ⟨d', hd', hlt⟩ := hwf.super c k hpos hk
              rw [hs] at hd'; cases hd'; exact hlt
          have hce : ¬ (c == e) = true := by simp; omega
          rw [if_neg hce]; simp only [hk, hs]; exact step

/-- With enough fuel (more than the class's index: superclasses come
before their subclasses), the fuel does not matter. -/
theorem ancestorArgsAux_enough (ct : ClassTable) (hwf : WfClasses ct) :
    ∀ c n m as d, c < n → c < m → ancestorArgsAux ct n c as d = ancestorArgsAux ct m c as d := by
  intro c
  induction c using Nat.strongRecOn with
  | _ c ih =>
    intro n m as d hn hm
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [ancestorArgsAux_succ, ancestorArgsAux_succ]
    by_cases hcd : (c == d) = true
    · rw [if_pos hcd, if_pos hcd]
    · rw [if_neg hcd, if_neg hcd]
      cases hk : ct[c]? with
      | none => rfl
      | some k =>
        simp only
        cases hs : k.super with
        | none => rfl
        | some p =>
          simp only
          have hp : p < c := by
            rcases Nat.eq_zero_or_pos c with rfl | hpos
            · have := hwf.root k hk; simp [this] at hs
            · obtain ⟨d', hd', hlt⟩ := hwf.super c k hpos hk
              rw [hs] at hd'; cases hd'; exact hlt
          exact ih p hp n m _ d (by omega) (by omega)

/-- One step of the chain, with the table's fuel. -/
theorem ancestorArgs_unfold (hwf : WfClasses ct) (c : Nat) (as : List Ty) (d : Nat) :
    ct.ancestorArgs c as d = (if (c == d) = true then some as else
      match ct[c]? with
      | some k => match k.super with
        | some p => ct.ancestorArgs p (Ty.substArgs as k.superArgs) d
        | none => none
      | none => none) := by
  have hlen := hwf.nonempty
  unfold ancestorArgs
  by_cases hc : c < ct.length
  · rw [ancestorArgsAux_enough ct hwf c ct.length (c + 1) as d hc (by omega), ancestorArgsAux_succ]
    split
    · rfl
    · cases hk : ct[c]? with
      | none => rfl
      | some k =>
        simp only
        cases hs : k.super with
        | none => rfl
        | some p =>
          simp only
          have hp : p < c := by
            rcases Nat.eq_zero_or_pos c with rfl | hpos
            · have := hwf.root k hk; simp [this] at hs
            · obtain ⟨d', hd', hlt⟩ := hwf.super c k hpos hk
              rw [hs] at hd'; cases hd'; exact hlt
          exact ancestorArgsAux_enough ct hwf p c ct.length _ d hp (by omega)
  · obtain ⟨n, hn⟩ : ∃ n', ct.length = n' + 1 := ⟨ct.length - 1, by omega⟩
    rw [hn, ancestorArgsAux_succ]
    have hk : ct[c]? = none := by simp; omega
    simp [hk]

/-- The classes the chain gives arguments to are the ancestors. -/
theorem ancestorArgs_mem (hwf : WfClasses ct) :
    ∀ c as d bs, ct.ancestorArgs c as d = some bs → d ∈ ct.ancestors c := by
  intro c
  induction c using Nat.strongRecOn with
  | _ c ih =>
    intro as d bs h
    rw [ancestorArgs_unfold hwf] at h
    rw [ancestors_eq hwf]
    by_cases hcd : (c == d) = true
    · simp at hcd; subst hcd; simp
    · rw [if_neg hcd] at h
      cases hk : ct[c]? with
      | none => simp [hk] at h
      | some k =>
        simp only [hk] at h
        cases hs : k.super with
        | none => simp [hs] at h
        | some p =>
          simp only [hs] at h
          have hp : p < c := by
            rcases Nat.eq_zero_or_pos c with rfl | hpos
            · have := hwf.root k hk; simp [this] at hs
            · obtain ⟨d', hd', hlt⟩ := hwf.super c k hpos hk
              rw [hs] at hd'; cases hd'; exact hlt
          have hsup : superOf ct c = some p := by simp [superOf, hk, hs]
          simp only [hsup]
          exact List.mem_cons_of_mem _ (ih p hp _ d bs h)

/-- Two ancestors of `c` on its chain: the lower one's chain gives the
upper one the same arguments. -/
theorem ancestorArgs_through (hwf : WfClasses ct) :
    ∀ c as d bs e cs, ct.ancestorArgs c as d = some bs → ct.ancestorArgs c as e = some cs →
      e ∈ ct.ancestors d → ct.ancestorArgs d bs e = some cs := by
  intro c
  induction c using Nat.strongRecOn with
  | _ c ih =>
    intro as d bs e cs h1 h2 hed
    rw [ancestorArgs_unfold hwf] at h1
    by_cases hcd : (c == d) = true
    · rw [if_pos hcd] at h1; simp at hcd h1; subst hcd; subst h1; exact h2
    · rw [if_neg hcd] at h1
      cases hk : ct[c]? with
      | none => simp [hk] at h1
      | some k =>
        simp only [hk] at h1
        cases hs : k.super with
        | none => simp [hs] at h1
        | some p =>
          simp only [hs] at h1
          have hp : p < c := by
            rcases Nat.eq_zero_or_pos c with rfl | hpos
            · have := hwf.root k hk; simp [this] at hs
            · obtain ⟨d', hd', hlt⟩ := hwf.super c k hpos hk
              rw [hs] at hd'; cases hd'; exact hlt
          -- `e ≠ c`: `e` is above `d`, which is strictly above `c`.
          have hdc : d ∈ ct.ancestors p := ancestorArgs_mem hwf p _ d bs h1
          have hed' : e ∈ ct.ancestors p := ancestors_trans hwf p d e hdc hed
          have hec : ¬ (c == e) = true := by
            intro hce; simp at hce; subst hce
            have := ancestors_le hwf p c hed'; omega
          rw [ancestorArgs_unfold hwf, if_neg hec] at h2
          simp only [hk, hs] at h2
          exact ih p hp _ d bs e cs h1 h2 hed

/-- Every ancestor gets arguments from the chain. -/
theorem ancestorArgs_of_mem (hwf : WfClasses ct) :
    ∀ c as d, d ∈ ct.ancestors c → ∃ bs, ct.ancestorArgs c as d = some bs := by
  intro c
  induction c using Nat.strongRecOn with
  | _ c ih =>
    intro as d hd
    rw [ancestorArgs_unfold hwf]
    by_cases hcd : (c == d) = true
    · rw [if_pos hcd]; exact ⟨as, rfl⟩
    · rw [if_neg hcd]
      rw [ancestors_eq hwf] at hd
      rcases List.mem_cons.mp hd with h | h
      · simp at hcd; exact absurd h.symm hcd
      · revert h
        cases hk : ct[c]? with
        | none => simp [superOf, hk]
        | some k =>
          cases hs : k.super with
          | none => simp [superOf, hk, hs]
          | some p =>
            intro h
            have hsup : superOf ct c = some p := by simp [superOf, hk, hs]
            simp only [hsup] at h
            simp only [hk, hs]
            exact ih p (superOf_lt hwf hsup) _ d h

theorem substArgs_length' (σ : List Ty) : ∀ as : List Ty, (Ty.substArgs σ as).length = as.length
  | [] => rfl
  | a :: as => by simp [Ty.substArgs, substArgs_length' σ as]

/-- The chain keeps the arguments' number right. -/
theorem ancestorArgs_length (hwf : WfClasses ct) :
    ∀ c as d bs, ct.ancestorArgs c as d = some bs →
      as.length = (((ct[c]?).map (·.params)).getD []).length →
      bs.length = (((ct[d]?).map (·.params)).getD []).length := by
  intro c
  induction c using Nat.strongRecOn with
  | _ c ih =>
    intro as d bs h hl
    rw [ancestorArgs_unfold hwf] at h
    by_cases hcd : (c == d) = true
    · rw [if_pos hcd] at h; simp at hcd h; subst hcd; subst h; exact hl
    · rw [if_neg hcd] at h
      cases hk : ct[c]? with
      | none => simp [hk] at h
      | some k =>
        simp only [hk] at h
        cases hs : k.super with
        | none => simp [hs] at h
        | some p =>
          simp only [hs] at h
          have hsup : superOf ct c = some p := by simp [superOf, hk, hs]
          exact ih p (superOf_lt hwf hsup) _ d bs h
            (by rw [substArgs_length']; exact hwf.superArgs c k p hk hs)


/-- The chain keeps the arguments closed. -/
theorem ancestorArgsAux_closed (ct : ClassTable) : ∀ n c as d bs,
    ancestorArgsAux ct n c as d = some bs → Ty.closedArgs as = true → Ty.closedArgs bs = true := by
  intro n
  induction n with
  | zero => intro c as d bs h; simp [ancestorArgsAux] at h
  | succ n ih =>
    intro c as d bs h hc
    rw [ancestorArgsAux_succ] at h
    by_cases hcd : (c == d) = true
    · rw [if_pos hcd] at h; simp at h; subst h; exact hc
    · rw [if_neg hcd] at h
      cases hk : ct[c]? with
      | none => simp [hk] at h
      | some k =>
        simp only [hk] at h
        cases hs : k.super with
        | none => simp [hs] at h
        | some p =>
          simp only [hs] at h
          exact ih p _ d bs h (Ty.substArgs_closed as hc _)

theorem ancestorArgs_closed (ct : ClassTable) {c : Nat} {as : List Ty} {d : Nat} {bs : List Ty}
    (h : ct.ancestorArgs c as d = some bs) (hc : Ty.closedArgs as = true) : Ty.closedArgs bs = true :=
  ancestorArgsAux_closed ct _ c as d bs h hc

theorem ancestorArgs_self (hwf : WfClasses ct) (c : Nat) (as : List Ty) :
    ct.ancestorArgs c as c = some as := by
  have := hwf.nonempty
  unfold ancestorArgs
  obtain ⟨n, hn⟩ : ∃ n', ct.length = n' + 1 := ⟨ct.length - 1, by omega⟩
  rw [hn, ancestorArgsAux_succ]; simp

theorem ancestorArgs_trans (hwf : WfClasses ct) {c : Nat} {as : List Ty} {d : Nat} {bs : List Ty}
    {e : Nat} {cs : List Ty} (h1 : ct.ancestorArgs c as d = some bs)
    (h2 : ct.ancestorArgs d bs e = some cs) : ct.ancestorArgs c as e = some cs := by
  unfold ancestorArgs at *
  have h := ancestorArgsAux_trans ct hwf _ _ c as d bs e cs h1 h2
  by_cases hc : c < ct.length
  · rw [ancestorArgsAux_enough ct hwf c _ _ as e (by omega) hc] at h; exact h
  · -- `c` is no class: its chain is `c` alone, so `c = d` and `as = bs`.
    have hlen := hwf.nonempty
    obtain ⟨n, hn⟩ : ∃ n', ct.length = n' + 1 := ⟨ct.length - 1, by omega⟩
    rw [hn, ancestorArgsAux_succ] at h1
    have hk : ct[c]? = none := by simp; omega
    by_cases hcd : (c == d) = true
    · rw [if_pos hcd] at h1
      simp at h1 hcd; subst h1; subst hcd
      exact h2
    · rw [if_neg hcd] at h1; simp [hk] at h1

/-- Nothing is above the root but itself. -/
theorem ancestorArgs_root (hwf : WfClasses ct) (e : Nat) (cs : List Ty)
    (h : ct.ancestorArgs 0 [] e = some cs) : e = 0 ∧ cs = [] := by
  have hlen := hwf.nonempty
  unfold ancestorArgs at h
  obtain ⟨n, hn⟩ : ∃ n', ct.length = n' + 1 := ⟨ct.length - 1, by omega⟩
  rw [hn, ancestorArgsAux_succ] at h
  by_cases h0 : (0 == e) = true
  · rw [if_pos h0] at h; simp at h0 h; exact ⟨by omega, by simp_all⟩
  · rw [if_neg h0] at h
    cases hk : ct[0]? with
    | none => simp [hk] at h
    | some k => have := hwf.root k hk; simp [hk, this] at h

end ClassTable


/-! ### Substitution -/

namespace Ty

@[simp] theorem substArgs_nil (σ : List Ty) : Ty.substArgs σ [] = [] := rfl
@[simp] theorem substArgs_cons (σ : List Ty) (t : Ty) (ts : List Ty) :
    Ty.substArgs σ (t :: ts) = Ty.subst σ t :: Ty.substArgs σ ts := rfl
@[simp] theorem subst_nil (σ : List Ty) : Ty.subst σ [] = [] := rfl
@[simp] theorem subst_cons (σ : List Ty) (a : Atom) (t : Ty) :
    Ty.subst σ (a :: t) = a.subst σ ++ Ty.subst σ t := rfl

theorem substArgs_getElem? (σ : List Ty) : ∀ (as : List Ty) (i : Nat),
    (Ty.substArgs σ as)[i]? = (as[i]?).map (Ty.subst σ)
  | [], i => by simp [Ty.substArgs]
  | a :: as, 0 => by simp [Ty.substArgs]
  | a :: as, i + 1 => by simp [Ty.substArgs, substArgs_getElem? σ as i]

theorem substArgs_length (σ : List Ty) : ∀ as : List Ty, (Ty.substArgs σ as).length = as.length
  | [] => rfl
  | a :: as => by simp [Ty.substArgs, substArgs_length σ as]

theorem subst_append (σ : List Ty) : ∀ s t : Ty, Ty.subst σ (s ++ t) = Ty.subst σ s ++ Ty.subst σ t
  | [], t => rfl
  | a :: s, t => by simp [Ty.subst, subst_append σ s t]

-- Substituting twice is substituting the composition.
mutual
theorem Atom.subst_comp (σ as : List Ty) : ∀ a : Atom,
    Ty.subst σ (Atom.subst as a) = Atom.subst (Ty.substArgs σ as) a
  | .nil | .bool | .int | .str | .float => rfl
  | .param i => by
    simp only [Atom.subst, substArgs_getElem?]
    cases as[i]? <;> simp [Ty.subst, Atom.subst, Ty.substArgs]
  | .cls c args => by simp [Atom.subst, Ty.subst, substArgs_comp σ as args]
theorem subst_comp (σ as : List Ty) : ∀ t : Ty, Ty.subst σ (Ty.subst as t) = Ty.subst (Ty.substArgs σ as) t
  | [] => rfl
  | a :: t => by simp [Ty.subst, subst_append, Atom.subst_comp σ as a, subst_comp σ as t]
theorem substArgs_comp (σ as : List Ty) : ∀ ts : List Ty,
    Ty.substArgs σ (Ty.substArgs as ts) = Ty.substArgs (Ty.substArgs σ as) ts
  | [] => rfl
  | t :: ts => by simp [Ty.substArgs, subst_comp σ as t, substArgs_comp σ as ts]
end


/-- `subst σ ∘ subst as` on a list of types. -/
theorem substArgs_comp_fun (σ as : List Ty) (ts : List Ty) :
    (ts.map (Ty.subst as)).map (Ty.subst σ) = ts.map (Ty.subst (Ty.substArgs σ as)) := by
  simp [List.map_map, Function.comp_def, Ty.subst_comp]

end Ty

namespace Atom
@[simp] theorem subst_nil (σ : List Ty) : Atom.subst σ .nil = [.nil] := rfl
@[simp] theorem subst_bool (σ : List Ty) : Atom.subst σ .bool = [.bool] := rfl
@[simp] theorem subst_int (σ : List Ty) : Atom.subst σ .int = [.int] := rfl
@[simp] theorem subst_str (σ : List Ty) : Atom.subst σ .str = [.str] := rfl
@[simp] theorem subst_float (σ : List Ty) : Atom.subst σ .float = [.float] := rfl
@[simp] theorem subst_cls (σ : List Ty) (c : Nat) (args : List Ty) :
    Atom.subst σ (.cls c args) = [.cls c (Ty.substArgs σ args)] := rfl
@[simp] theorem subst_param (σ : List Ty) (i : Nat) :
    Atom.subst σ (.param i) = (σ[i]?).getD [.cls 0 []] := rfl
end Atom

namespace ClassTable

/-- The chain's arguments substituted are the chain of the substituted
arguments. -/
theorem ancestorArgsAux_subst (ct : ClassTable) (σ : List Ty) :
    ∀ n c as d bs, ancestorArgsAux ct n c as d = some bs →
      ancestorArgsAux ct n c (Ty.substArgs σ as) d = some (Ty.substArgs σ bs) := by
  intro n
  induction n with
  | zero => intro c as d bs h; simp [ancestorArgsAux] at h
  | succ n ih =>
    intro c as d bs h
    rw [ancestorArgsAux_succ] at h ⊢
    by_cases hcd : (c == d) = true
    · rw [if_pos hcd] at h ⊢; simp at h; subst h; rfl
    · rw [if_neg hcd] at h ⊢
      cases hk : ct[c]? with
      | none => simp [hk] at h
      | some k =>
        simp only [hk] at h ⊢
        cases hs : k.super with
        | none => simp [hs] at h
        | some p =>
          simp only [hs] at h ⊢
          have := ih p _ d bs h
          rwa [Ty.substArgs_comp] at this

theorem ancestorArgs_subst (ct : ClassTable) (σ : List Ty) {c : Nat} {as : List Ty} {d : Nat}
    {bs : List Ty} (h : ct.ancestorArgs c as d = some bs) :
    ct.ancestorArgs c (Ty.substArgs σ as) d = some (Ty.substArgs σ bs) :=
  ancestorArgsAux_subst ct σ _ c as d bs h

end ClassTable


end QuarzCore
