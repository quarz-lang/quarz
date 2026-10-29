/-
What holds of a frame, or of a block and the frames below it, still holds
after writes that miss their locations.
-/

import QuarzCore.ExtLemmas

set_option linter.deprecated false

namespace QuarzCore

variable {P : Program}

theorem lookupVar_mem {vars : List (String × Nat)} {x : String} {l : Nat}
    (h : lookupVar vars x = some l) : (x, l) ∈ vars := by
  unfold lookupVar at h
  cases hf : vars.find? (·.1 == x) with
  | none => simp [hf] at h
  | some e =>
    simp [hf] at h
    have := List.mem_of_find?_eq_some hf
    have hp := List.find?_some hf
    obtain ⟨y, k⟩ := e
    simp at hp h
    subst hp h
    exact this

theorem Ext.loc_same {W Wo : Nat → Prop} {Λ Λ' : List Ty} {s s' : Store} (he : Ext P W Wo Λ Λ' s s')
    {l : Nat} {v : Value} (hv : s.locs[l]? = some v) (hw : ¬ W l) : s'.locs[l]? = some v := by
  obtain ⟨v', h1, h2⟩ := he.locs l v hv
  rcases h2 with rfl | ⟨hw', _⟩
  · exact h1
  · exact absurd hw' hw

theorem Ext.len {W Wo : Nat → Prop} {Λ Λ' : List Ty} {s s' : Store} (he : Ext P W Wo Λ Λ' s s')
    {l : Nat} (hl : l < s.locs.length) : l < s'.locs.length := by
  obtain ⟨v', h1, _⟩ := he.locs l s.locs[l] (by simp [hl])
  exact (List.getElem?_eq_some_iff.mp h1).1

theorem InitSelf.stable {k : Nat} {me : Value} {s s' : Store} (hg : ObjsGrow s s')
    (h : InitSelf P k me s) : InitSelf P k me s' := by
  obtain ⟨l, o, rfl, ho, hk, hs, hheld⟩ := h
  obtain ⟨o', ho', hc, ha, hl, hs'⟩ := hg l o ho
  refine ⟨l, o', rfl, ho', by rw [hc]; exact hk, fun i h1 h2 => hs' i (hs i h1 (hl ▸ h2)),
    fun i f hf hd hr => ?_⟩
  rw [hc, ha] at hf
  exact hs' i (hheld i f hf hd hr)

/-- Objects keeping their classes and arguments, the arguments a method's
owner gets from an object stay. -/
theorem argsFor_stable {s s' : Store} (hg : ObjsGrow s s') {l : Nat} {o : Obj}
    (ho : s.objs[l]? = some o) (d : Nat) : s'.argsFor P.classes l d = s.argsFor P.classes l d := by
  obtain ⟨o', ho', hc, ha, _, _⟩ := hg l o ho
  simp [Store.argsFor, ho, ho', hc, ha]

/-- A path of a frame holds after writes that miss its locals and leave
its `self`'s immutable fields alone. -/
theorem PathHolds.stable {c : Ctx} {fr : Frame} {s s' : Store} {W Wo : Nat → Prop} {Λ Λ' : List Ty}
    (he : Ext P W Wo Λ Λ' s s') (hw : ∀ l, frameLocs fr.vars l → ¬ W l)
    (hwo : ∀ l, fr.self = .obj l → ¬ Wo l) :
    ∀ {p t}, PathHolds P c fr s p t → PathHolds P c fr s' p t
  | .local x, t, ⟨l, v, d, h1, h2, h3, h4, h5⟩ =>
    ⟨l, v, d, h1, he.loc_same h2 (hw l ⟨x, lookupVar_mem h1⟩), h3, he.hasTy h4, he.hasTy h5⟩
  | .field f, t, ⟨l, o, fd, i, h1, h2, h3, h4, h5, h6, h7⟩ => by
    obtain ⟨o', ho', hc, ha, _, hs⟩ := he.grow l o h2
    refine ⟨l, o', fd, i, h1, ho', h3, by rw [hc]; exact h4, by rw [hc, ha]; exact h5, hs i h6,
      fun hv => ?_⟩
    obtain ⟨v, h8, h9⟩ := h7 hv
    -- The declared field at `i` is immutable too.
    obtain ⟨d, f0, _, hf0, hf⟩ := ClassTable.allFieldsAt_some P.classes h5
    have hv0 : f0.var = false := by have := congrArg Field.var hf; simpa [hv] using this.symm
    exact ⟨v, by rw [he.imm l o o' h2 ho' (hwo l h1) i f0 hf0 hv0]; exact h8, he.hasTy h9⟩

theorem Sat.stable {c : Ctx} {Γ : Env} {fr : Frame} {s s' : Store} {W Wo : Nat → Prop}
    {Λ Λ' : List Ty} (h : Sat P c Γ fr s) (he : Ext P W Wo Λ Λ' s s')
    (hw : ∀ l, frameLocs fr.vars l → ¬ W l) (hwo : ∀ l, fr.self = .obj l → ¬ Wo l) :
    Sat P c Γ fr s' :=
  fun p t hp => (h p t hp).stable he hw hwo

theorem FrameCore.stable {c : Ctx} {Λ Λ' : List Ty} {vars : List (String × Nat)} {me : Value}
    {sa : List Ty} {s s' : Store} {W Wo : Nat → Prop} (h : FrameCore P c Λ vars me sa s)
    (he : Ext P W Wo Λ Λ' s s') : FrameCore P c Λ' vars me sa s' where
  decls := fun x d hd => by
    obtain ⟨l, h1, h2⟩ := h.decls x d hd
    exact ⟨l, h1, prefix_getElem? he.tys h2⟩
  inj := h.inj
  inStore := fun x l hm => he.len (h.inStore x l hm)
  self := fun hi => he.hasTy (h.self hi)
  selfInit := fun hi => (h.selfInit hi).stable he.grow
  selfObj := by
    obtain ⟨l, hl, hsa⟩ := h.selfObj
    refine ⟨l, hl, ?_⟩
    -- The object is in the store (`self` is typed, or being made).
    have : ∃ o, s.objs[l]? = some o := by
      by_cases hi : c.inInit = true
      · obtain ⟨l', o, hl', ho, _⟩ := h.selfInit hi; rw [hl] at hl'; cases hl'; exact ⟨o, ho⟩
      · have ht := h.self (by simpa using hi)
        rw [hl] at ht
        unfold Store.hasTy Store.hasType at ht
        cases hty : s.typeOf (.obj l) with
        | none => simp [hty] at ht
        | some a => obtain ⟨o, ho, _, _⟩ := typeOf_obj hty; exact ⟨o, ho⟩
    obtain ⟨o, ho⟩ := this
    rw [argsFor_stable he.grow ho]; exact hsa
  closed := h.closed
  bounded := h.bounded

/-- A block chain stays as checked under writes that miss its frames'
locals (and assign no immutable field, when there is a block). -/
theorem ChainAt.stable {Λ Λ' : List Ty} {s s' : Store} {W Wo : Nat → Prop}
    (he : Ext P W Wo Λ Λ' s s') :
    ∀ (ws : List (Ctx × Env × Out)) (blk : Option Closure) (sig : Option BlockSig),
      (∀ l, chainLocs blk l → ¬ W l) → (∀ l, Wo l → blk = none) →
      ChainAt P Λ s ws blk sig → ChainAt P Λ' s' ws blk sig
  | [], none, none, _, _, _ => trivial
  | (c, Δ, ob) :: ws, some (.mk vars me sa outer ps body), some sig, hw, hwo, h => by
    simp only [ChainAt] at h ⊢
    simp only [chainLocs] at hw
    obtain ⟨hc, hcore, hch, habove, hsig, hR⟩ := h
    have hwf : ∀ l, frameLocs vars l → ¬ W l := fun l hl => hw l (Or.inl hl)
    have hwo' : ∀ l, ¬ Wo l := fun l h => by cases hwo l h
    exact ⟨hc, hcore.stable he, ChainAt.stable he ws outer _ (fun l hl => hw l (Or.inr hl))
        (fun l h => absurd h (hwo' l)) hch,
      habove, hsig, hR.stable he hwf (fun l _ => hwo' l)⟩
  | [], some _, _, _, _, h => by simp [ChainAt] at h
  | [], none, some _, _, _, h => by simp [ChainAt] at h
  | _ :: _, none, _, _, _, h => by simp [ChainAt] at h
  | _ :: _, some (.mk _ _ _ _ _ _), none, _, _, h => by simp [ChainAt] at h

theorem BlockSig.le_refl {ct : ClassTable} (hwf : WfClasses ct) (sig : BlockSig) :
    BlockSig.le ct sig sig :=
  ⟨rfl, fun _ t t' h h' => by rw [h] at h'; cases h'; exact Ty.le_refl hwf t, Ty.le_refl hwf _⟩

theorem BlockSig.le_trans {ct : ClassTable} (hwf : WfClasses ct) {a b c : BlockSig}
    (h1 : BlockSig.le ct a b) (h2 : BlockSig.le ct b c) : BlockSig.le ct a c := by
  obtain ⟨l1, p1, r1⟩ := h1
  obtain ⟨l2, p2, r2⟩ := h2
  refine ⟨l1.trans l2, fun i t t' ht ht' => ?_, Ty.le_trans hwf r2 r1⟩
  obtain ⟨u, hu⟩ : ∃ u, b.params[i]? = some u :=
    ⟨_, List.getElem?_eq_getElem (by have := (List.getElem?_eq_some_iff.mp ht).1; omega)⟩
  exact Ty.le_trans hwf (p1 i t u ht hu) (p2 i u t' hu ht')

/-- A chain checked for a signature is one for any the method may run the
block with below it. -/
theorem ChainAt.weaken (hwf : WfClasses P.classes) {Λ : List Ty} {s : Store}
    (ws : List (Ctx × Env × Out)) (blk : Option Closure) {sig sig' : Option BlockSig}
    (h : ChainAt P Λ s ws blk sig') (hle : BlockSig.optLe P.classes sig sig') :
    ChainAt P Λ s ws blk sig := by
  rcases sig with _ | a <;> rcases sig' with _ | b
  · exact h
  · exact (hle : False).elim
  · exact (hle : False).elim
  · cases ws with
    | nil => cases blk <;> simp [ChainAt] at h
    | cons w ws =>
      obtain ⟨c, Δ, ob⟩ := w
      cases blk with
      | none => simp [ChainAt] at h
      | some clo =>
        obtain ⟨vars, me, sa, outer, ps, body⟩ := clo
        simp only [ChainAt] at h ⊢
        obtain ⟨hc, hcore, hch, habove, ⟨sig0, hrel, hrest⟩, hR⟩ := h
        have hct : c.ct = P.classes := by simp [Ctx.ct, hc]
        have hwf' : WfClasses c.ct := hct ▸ hwf
        have hle' : BlockSig.le c.ct a b := hct ▸ hle
        exact ⟨hc, hcore, hch, habove, ⟨sig0, BlockSig.le_trans hwf' hle' hrel, hrest⟩, hR⟩

/-- The chain after a run with a signature `sig'`, given it was checked
for `sig` before: the same for `sig` (the signature's part is static). -/
theorem ChainAt.restore {Λ Λ' : List Ty} {s s' : Store}
    (ws : List (Ctx × Env × Out)) (blk : Option Closure) {sig sig' : Option BlockSig}
    (h' : ChainAt P Λ' s' ws blk sig') (h : ChainAt P Λ s ws blk sig)
    (hle : BlockSig.optLe P.classes sig' sig) : ChainAt P Λ' s' ws blk sig := by
  rcases sig with _ | a <;> rcases sig' with _ | b
  · exact h'
  · exact (hle : False).elim
  · exact (hle : False).elim
  · cases ws with
    | nil => cases blk <;> simp [ChainAt] at h
    | cons w ws =>
      obtain ⟨c, Δ, ob⟩ := w
      cases blk with
      | none => simp [ChainAt] at h
      | some clo =>
        obtain ⟨vars, me, sa, outer, ps, body⟩ := clo
        simp only [ChainAt] at h h' ⊢
        obtain ⟨_, _, _, _, hsig, _⟩ := h
        obtain ⟨hc, hcore, hch, habove, _, hR⟩ := h'
        exact ⟨hc, hcore, hch, habove, hsig, hR⟩

theorem FrameOK.stable {c : Ctx} {Λ Λ' : List Ty} {fr : Frame} {s s' : Store} {W Wo : Nat → Prop}
    {ws : List (Ctx × Env × Out)} (h : FrameOK P c Λ fr s ws) (he : Ext P W Wo Λ Λ' s s')
    (hw : ∀ l, chainLocs fr.blk l → ¬ W l) (hwo : ∀ l, Wo l → fr.blk = none) :
    FrameOK P c Λ' fr s' ws where
  core := h.core.stable he
  chain := ChainAt.stable he ws fr.blk _ hw hwo h.chain
  above := h.above
  chainIn := fun l hl => he.len (h.chainIn l hl)
  initBlk := h.initBlk

/-- What `declEnv` has: locals `Γ` has, each as declared. -/
theorem Ctx.get_declEnv {c : Ctx} {p : Path} {t : Ty} :
    ∀ {Γ : Env}, (c.declEnv Γ).get p = some t →
      ∃ x, p = .local x ∧ c.decl x = some t ∧ ∃ u, Γ.get p = some u
  | [], h => by simp [Ctx.declEnv, Env.get] at h
  | (q, u) :: Γ, h => by
    have ih := @Ctx.get_declEnv c p t Γ
    simp only [Ctx.declEnv, List.filterMap_cons] at h ih
    have later : ∀ x, p = .local x → c.decl x = some t → (∃ u', Env.get Γ p = some u') →
        ∃ x, p = .local x ∧ c.decl x = some t ∧ ∃ u', Env.get ((q, u) :: Γ) p = some u' := by
      rintro x rfl hd ⟨u', hu'⟩
      refine ⟨x, rfl, hd, ?_⟩
      by_cases hq : q = .local x
      · exact ⟨u, by simp [Env.get, hq]⟩
      · exact ⟨u', by simp [Env.get, hq, hu']⟩
    cases q with
    | field f =>
      obtain ⟨x, hx, hd, hu⟩ := ih h
      exact later x hx hd hu
    | «local» y =>
      cases hd : c.decl y with
      | none =>
        simp only [hd, Option.map_none] at h
        obtain ⟨x, hx, hd', hu⟩ := ih h
        exact later x hx hd' hu
      | some d =>
        simp only [hd, Option.map_some, Env.get] at h
        by_cases hq : Path.local y = p
        · rw [if_pos hq] at h; cases h
          exact ⟨y, hq.symm, hd, u, by simp [Env.get, hq]⟩
        · rw [if_neg hq] at h
          obtain ⟨x, hx, hd', hu⟩ := ih h
          exact later x hx hd' hu

/-- Where `Γ` held, its locals hold values of their declared types. -/
theorem Sat.toDecl {c : Ctx} {Γ : Env} {fr : Frame} {s : Store} (hs : Sat P c Γ fr s) :
    Sat P c (c.declEnv Γ) fr s := by
  intro p t hp
  obtain ⟨x, rfl, hd, u, hu⟩ := Ctx.get_declEnv hp
  obtain ⟨l, v, d, h1, h2, h3, _, h5⟩ := hs _ _ hu
  rw [hd] at h3; cases h3
  exact ⟨l, v, t, h1, h2, hd, h5, h5⟩

/-- Locals as declared stay so: a write gives a local a value of its
declared type. -/
theorem Sat.declStable {c : Ctx} {Γ : Env} {fr : Frame} {Λ Λ' : List Ty} {s s' : Store}
    {W Wo : Nat → Prop} (hs : Sat P c (c.declEnv Γ) fr s)
    (hcore : FrameCore P c Λ fr.vars fr.self fr.selfArgs s) (he : Ext P W Wo Λ Λ' s s') :
    Sat P c (c.declEnv Γ) fr s' := by
  intro p t hp
  obtain ⟨x, rfl, hd, _⟩ := Ctx.get_declEnv hp
  obtain ⟨l, v, d, h1, h2, h3, _, h5⟩ := hs _ _ hp
  rw [hd] at h3; cases h3
  obtain ⟨v', hv', hch⟩ := he.locs l v h2
  rcases hch with rfl | ⟨_, t', ht', hty⟩
  · exact ⟨l, _, t, h1, hv', hd, he.hasTy h5, he.hasTy h5⟩
  · obtain ⟨l', hl', hΛ⟩ := hcore.decls x t hd
    rw [h1] at hl'; cases hl'
    rw [hΛ] at ht'; cases ht'
    exact ⟨l, v', t, h1, hv', hd, hty, hty⟩

/-- A procedure stays as made. -/
theorem ProcOK.stable {Λ Λ' : List Ty} {s s' : Store} {W Wo : Nat → Prop} {p : ProcV}
    (h : ProcOK P Λ s p) (he : Ext P W Wo Λ Λ' s s') : ProcOK P Λ' s' p := by
  obtain ⟨c, Γ, ps, own, ret, body, vars, me, sa, k, ob, hc, hp, hi, hd, hk, hn, hok, hcore, hs, hty, hret⟩ := h
  exact ⟨c, Γ, ps, own, ret, body, vars, me, sa, k, ob, hc, hp, hi, hd, hk, hn, hok, hcore.stable he,
    hs.declStable hcore he, hty, hret⟩

theorem WfStore.setLoc {Λ : List Ty} {s : Store} (h : WfStore P Λ s) {l : Nat} {v : Value} {t : Ty}
    (hl : l < s.locs.length) (ht : Λ[l]? = some t) (hv : s.hasTy P v t) :
    WfStore P Λ (s.setLoc l v) where
  len := by simp [Store.setLoc, h.len]
  objs := fun l o ho => by
    obtain ⟨h1, h1a, h1b, h2, h3, h4⟩ := h.objs l o ho
    exact ⟨h1, h1a, h1b, h2, h3, fun i w f hs hw hf => h4 i w f hs hw hf⟩
  bounds := fun l o ho => h.bounds l o ho
  noEnum := fun l o ho => h.noEnum l o ho
  procs := fun i p hp => (h.procs i p hp).stable (Ext.setLoc (W := fun _ => True) (Wo := fun _ => False) hl ht hv trivial)

/-- A new procedure, as checked. -/
theorem WfStore.newProc {Λ : List Ty} {s : Store} (hw : WfStore P Λ s) {p : ProcV}
    (hp : ProcOK P Λ s p) : WfStore P Λ { s with procs := s.procs ++ [p] } where
  len := hw.len
  objs := fun l o ho => by
    obtain ⟨h1, h1a, h1b, h2, h3, h4⟩ := hw.objs l o ho
    exact ⟨h1, h1a, h1b, h2, h3, fun i w f hs hw' hf => (Ext.newProc (W := fun _ => False)
      (Wo := fun _ => False) (Λ := Λ) p).hasTy (h4 i w f hs hw' hf)⟩
  noEnum := fun l o ho => hw.noEnum l o ho
  bounds := fun l o ho => hw.bounds l o ho
  procs := fun i q hq => by
    have he := Ext.newProc (P := P) (W := fun _ => False) (Wo := fun _ => False) (Λ := Λ) (s := s) p
    by_cases hi : i < s.procs.length
    · rw [List.getElem?_append_left hi] at hq
      exact (hw.procs i q hq).stable he
    · have : i = s.procs.length := by
        have := (List.getElem?_eq_some_iff.mp hq).1; simp at this; omega
      subst this
      simp at hq; subst hq
      exact hp.stable he

end QuarzCore
