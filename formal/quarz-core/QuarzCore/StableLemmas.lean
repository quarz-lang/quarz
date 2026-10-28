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
    obtain ⟨hc, hcore, hch, habove, hsig, hR, hJ⟩ := h
    have hwf : ∀ l, frameLocs vars l → ¬ W l := fun l hl => hw l (Or.inl hl)
    have hwo' : ∀ l, ¬ Wo l := fun l h => by cases hwo l h
    exact ⟨hc, hcore.stable he, ChainAt.stable he ws outer _ (fun l hl => hw l (Or.inr hl))
        (fun l h => absurd h (hwo' l)) hch,
      habove, hsig, hR.stable he hwf (fun l _ => hwo' l), hJ.stable he hwf (fun l _ => hwo' l)⟩
  | [], some _, _, _, _, h => by simp [ChainAt] at h
  | [], none, some _, _, _, h => by simp [ChainAt] at h
  | _ :: _, none, _, _, _, h => by simp [ChainAt] at h
  | _ :: _, some (.mk _ _ _ _ _ _), none, _, _, h => by simp [ChainAt] at h

theorem FrameOK.stable {c : Ctx} {Λ Λ' : List Ty} {fr : Frame} {s s' : Store} {W Wo : Nat → Prop}
    {ws : List (Ctx × Env × Out)} (h : FrameOK P c Λ fr s ws) (he : Ext P W Wo Λ Λ' s s')
    (hw : ∀ l, chainLocs fr.blk l → ¬ W l) (hwo : ∀ l, Wo l → fr.blk = none) :
    FrameOK P c Λ' fr s' ws where
  core := h.core.stable he
  chain := ChainAt.stable he ws fr.blk _ hw hwo h.chain
  above := h.above
  chainIn := fun l hl => he.len (h.chainIn l hl)
  initBlk := h.initBlk

end QuarzCore
