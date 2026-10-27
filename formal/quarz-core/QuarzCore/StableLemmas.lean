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

theorem Ext.loc_same {W : Nat → Prop} {Λ Λ' : List Ty} {s s' : Store} (he : Ext P W Λ Λ' s s')
    {l : Nat} {v : Value} (hv : s.locs[l]? = some v) (hw : ¬ W l) : s'.locs[l]? = some v := by
  obtain ⟨v', h1, h2⟩ := he.locs l v hv
  rcases h2 with rfl | ⟨hw', _⟩
  · exact h1
  · exact absurd hw' hw

theorem Ext.len {W : Nat → Prop} {Λ Λ' : List Ty} {s s' : Store} (he : Ext P W Λ Λ' s s')
    {l : Nat} (hl : l < s.locs.length) : l < s'.locs.length := by
  obtain ⟨v', h1, _⟩ := he.locs l s.locs[l] (by simp [hl])
  exact (List.getElem?_eq_some_iff.mp h1).1

theorem PathHolds.stable {c : Ctx} {fr : Frame} {s s' : Store} {W : Nat → Prop} {Λ Λ' : List Ty}
    (he : Ext P W Λ Λ' s s') (hw : ∀ l, frameLocs fr.vars l → ¬ W l) :
    ∀ {p t}, PathHolds P c fr s p t → PathHolds P c fr s' p t
  | .local x, t, ⟨l, v, d, h1, h2, h3, h4, h5⟩ =>
    ⟨l, v, d, h1, he.loc_same h2 (hw l ⟨x, lookupVar_mem h1⟩), h3, he.hasTy h4, he.hasTy h5⟩
  | .field f, t, ⟨l, o, fd, i, v, h1, h2, h3, h4, h5, h6, h7, h8⟩ => by
    obtain ⟨o', ho', hc, hf⟩ := he.objs l o h2
    refine ⟨l, o', fd, i, v, h1, ho', h3, h4, by rw [hc]; exact h5, by rw [hc]; exact h6, ?_,
      he.hasTy h8⟩
    rw [hf i fd h6 h4]; exact h7

theorem Sat.stable {c : Ctx} {Γ : Env} {fr : Frame} {s s' : Store} {W : Nat → Prop}
    {Λ Λ' : List Ty} (h : Sat P c Γ fr s) (he : Ext P W Λ Λ' s s')
    (hw : ∀ l, frameLocs fr.vars l → ¬ W l) : Sat P c Γ fr s' :=
  fun p t hp => (h p t hp).stable he hw

theorem FrameCore.stable {c : Ctx} {Λ Λ' : List Ty} {vars : List (String × Nat)} {me : Value}
    {s s' : Store} {W : Nat → Prop} (h : FrameCore P c Λ vars me s) (he : Ext P W Λ Λ' s s') :
    FrameCore P c Λ' vars me s' where
  decls := fun x d hd => by
    obtain ⟨l, h1, h2⟩ := h.decls x d hd
    exact ⟨l, h1, prefix_getElem? he.tys h2⟩
  inj := h.inj
  inStore := fun x l hm => he.len (h.inStore x l hm)
  self := he.hasTy h.self
  selfObj := h.selfObj

theorem ChainAt.stable {Λ Λ' : List Ty} {s s' : Store} {W : Nat → Prop}
    (he : Ext P W Λ Λ' s s') :
    ∀ (ws : List (Ctx × Env × Out)) (blk : Option Closure) (sig : Option BlockSig),
      (∀ l, chainLocs blk l → ¬ W l) → ChainAt P Λ s ws blk sig → ChainAt P Λ' s' ws blk sig
  | [], none, none, _, _ => trivial
  | (c, Δ, ob) :: ws, some (.mk vars me outer ps body), some sig, hw, h => by
    simp only [ChainAt] at h ⊢
    simp only [chainLocs] at hw
    obtain ⟨hc, hcore, hch, habove, hps, hty, hret, hR, hJ⟩ := h
    have hwf : ∀ l, frameLocs vars l → ¬ W l := fun l hl => hw l (Or.inl hl)
    exact ⟨hc, hcore.stable he, ChainAt.stable he ws outer _ (fun l hl => hw l (Or.inr hl)) hch,
      habove, hps, hty, hret, hR.stable he hwf, hJ.stable he hwf⟩
  | [], some _, _, _, h => by simp [ChainAt] at h
  | [], none, some _, _, h => by simp [ChainAt] at h
  | _ :: _, none, _, _, h => by simp [ChainAt] at h
  | _ :: _, some (.mk _ _ _ _ _), none, _, h => by simp [ChainAt] at h

theorem FrameOK.stable {c : Ctx} {Λ Λ' : List Ty} {fr : Frame} {s s' : Store} {W : Nat → Prop}
    {ws : List (Ctx × Env × Out)} (h : FrameOK P c Λ fr s ws) (he : Ext P W Λ Λ' s s')
    (hw : ∀ l, chainLocs fr.blk l → ¬ W l) : FrameOK P c Λ' fr s' ws where
  core := h.core.stable he
  chain := ChainAt.stable he ws fr.blk _ hw h.chain
  above := h.above
  chainIn := fun l hl => he.len (h.chainIn l hl)

end QuarzCore
