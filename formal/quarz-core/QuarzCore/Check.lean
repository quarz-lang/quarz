/-
What `check` accepts, `Typed` derives, with the same `Out` (the direction
soundness needs): the function is the relation's rules run.
-/

import QuarzCore.Typed

namespace QuarzCore

theorem guard_eq {p : Prop} [Decidable p] : (guard p : Option Unit) = if p then some () else none := rfl

attribute [local simp] Option.bind_eq_some_iff guard_eq

mutual

theorem check_typed : ∀ {c : Ctx} {Γ : Env} {e : Expr} {o : Out}, check c Γ e = some o →
    Typed c Γ e o
  | c, Γ, .nil, o, h => by simp [check] at h; subst h; exact .nil
  | c, Γ, .tru, o, h => by simp [check] at h; subst h; exact .tru
  | c, Γ, .fls, o, h => by simp [check] at h; subst h; exact .fls
  | c, Γ, .int _, o, h => by simp [check] at h; subst h; exact .int
  | c, Γ, .str _, o, h => by simp [check] at h; subst h; exact .str
  | c, Γ, .flt _, o, h => by simp [check] at h; subst h; exact .flt
  | c, Γ, .self, o, h => by simp [check] at h; subst h; exact .self
  | c, Γ, .raise, o, h => by simp [check] at h; subst h; exact .raise
  | c, Γ, .var x t, o, h => by
    simp [check] at h
    obtain ⟨u, hu, hle, rfl⟩ := h
    exact .var hu hle
  | c, Γ, .field f t, o, h => by
    simp [check] at h
    obtain ⟨fd, hfd, h⟩ := h
    split at h
    · rename_i hv; simp at h; obtain ⟨hle, rfl⟩ := h; exact .fieldVar hfd hv hle
    · rename_i hv; simp at h; obtain ⟨hle, rfl⟩ := h
      exact .fieldImm hfd (by simpa using hv) rfl hle
  | c, Γ, .assign x e, o, h => by
    simp [check] at h
    obtain ⟨oe, he, d, hd, hle, h⟩ := h
    split at h
    · simp at h; subst h; exact .assignDead (check_typed he) hd hle (by assumption)
    · simp at h; subst h; exact .assign (check_typed he) hd hle (by assumption)
  | c, Γ, .setField f e, o, h => by
    simp [check] at h
    obtain ⟨fd, hfd, hv, oe, he, hle, h⟩ := h
    split at h
    · simp at h; subst h; exact .setFieldDead hfd hv (check_typed he) hle (by assumption)
    · simp at h; subst h; exact .setField hfd hv (check_typed he) hle (by assumption)
  | c, Γ, .new k args, o, h => by
    simp [check] at h
    obtain ⟨hk, h⟩ := h
    split at h
    · simp at h
    · simp at h; subst h; exact .newDead hk (checkArgs_typed (by assumption))
    · simp at h; obtain ⟨⟨hl, hall⟩, rfl⟩ := h
      exact .new hk (checkArgs_typed (by assumption)) hl (by simpa using hall)
  | c, Γ, .call r m args, o, h => by
    simp [check] at h
    obtain ⟨orr, hr, h⟩ := h
    split at h
    · simp at h; subst h; exact .callDeadRecv (check_typed hr) (by assumption)
    · split at h
      · simp at h
      · simp at h; subst h
        exact .callDeadArgs (check_typed hr) (by assumption) (checkArgs_typed (by assumption))
      · simp at h; obtain ⟨ms, hms, hall, rfl⟩ := h
        exact .call (check_typed hr) (by assumption) (checkArgs_typed (by assumption)) hms
          (by simpa using hall)
  | c, Γ, .callBlk r m args ps body, o, h => by
    simp [check] at h
    obtain ⟨orr, hr, h⟩ := h
    split at h
    · simp at h; subst h; exact .callBlkDeadRecv (check_typed hr) (by assumption)
    · split at h
      · simp at h
      · simp at h; subst h
        exact .callBlkDeadArgs (check_typed hr) (by assumption) (checkArgs_typed (by assumption))
      · simp at h
        obtain ⟨ms, hms, m0, hm0, sig, hsig, hall, hps, ob, hb, hret, rfl⟩ := h
        exact .callBlk (check_typed hr) (by assumption) (checkArgs_typed (by assumption)) hms
          (by simpa using hm0) hsig (by simpa using hall) hps (check_typed hb) hret
  | c, Γ, .yield args, o, h => by
    simp [check] at h
    obtain ⟨sig, hsig, h⟩ := h
    split at h
    · simp at h
    · simp at h; subst h; exact .yieldDead hsig (checkArgs_typed (by assumption))
    · simp at h; obtain ⟨⟨hl, hall⟩, rfl⟩ := h
      exact .yield hsig (checkArgs_typed (by assumption)) hl (by simpa using hall)
  | c, Γ, .prim f args params ret, o, h => by
    simp [check] at h
    split at h
    · simp at h
    · simp at h; subst h; exact .primDead (checkArgs_typed (by assumption))
    · simp at h; obtain ⟨⟨hl, hall⟩, rfl⟩ := h
      exact .prim (checkArgs_typed (by assumption)) hl (by simpa using hall)
  | c, Γ, .seq a b, o, h => by
    simp [check] at h
    obtain ⟨oa, ha, h⟩ := h
    split at h
    · simp at h; subst h; exact .seqDead (check_typed ha) (by assumption)
    · exact .seq (check_typed ha) (by assumption) (check_typed h)
  | c, Γ, .ite cnd t e, o, h => by
    simp [check] at h
    obtain ⟨oc, hc, ot, hot, oe, hoe, rfl⟩ := h
    exact .ite (check_typed hc) (checkBranch_typed hot) (checkBranch_typed hoe)
  | c, Γ, .while cnd b, o, h => by
    simp [check] at h
    obtain ⟨oc, hc, h⟩ := h
    split at h
    · simp at h; subst h; exact .whileNever rfl (check_typed hc) (by assumption)
    · simp at h; obtain ⟨ob, hb, hall, rfl⟩ := h
      exact .while rfl (check_typed hc) (by assumption) (check_typed hb)
        (by cases hob : ob.out <;> simp_all)
  | c, Γ, .ret e, o, h => by
    simp [check] at h
    obtain ⟨hib, oe, he, hle, rfl⟩ := h
    exact .ret (by simpa using hib) (check_typed he) hle
  | c, Γ, .isNil e, o, h => by
    simp [check] at h
    obtain ⟨oe, he, h⟩ := h
    split at h
    · simp at h; subst h; exact .testDead (check_typed he) (by assumption) (by simp)
    · simp at h; subst h; exact .isNil (check_typed he) (by assumption)
  | c, Γ, .isA e a, o, h => by
    simp [check] at h
    obtain ⟨oe, he, h⟩ := h
    split at h
    · simp at h; subst h; exact .testDead (check_typed he) (by assumption) (by simp)
    · simp at h; subst h; exact .isA (check_typed he) (by assumption)
  | c, Γ, .eqNil e, o, h => by
    simp [check] at h
    obtain ⟨oe, he, h⟩ := h
    split at h
    · simp at h; subst h; exact .testDead (check_typed he) (by assumption) (by simp)
    · simp at h; subst h; exact .eqNil (check_typed he) (by assumption)
  | c, Γ, .neNil e, o, h => by
    simp [check] at h
    obtain ⟨oe, he, h⟩ := h
    split at h
    · simp at h; subst h; exact .testDead (check_typed he) (by assumption) (by simp)
    · simp at h; subst h; exact .neNil (check_typed he) (by assumption)
  | c, Γ, .eqTrue e, o, h => by
    simp [check] at h
    obtain ⟨oe, he, h⟩ := h
    split at h
    · simp at h; subst h; exact .testDead (check_typed he) (by assumption) (by simp)
    · simp at h; subst h; exact .eqTrue (check_typed he) (by assumption)
  | c, Γ, .eqFalse e, o, h => by
    simp [check] at h
    obtain ⟨oe, he, h⟩ := h
    split at h
    · simp at h; subst h; exact .testDead (check_typed he) (by assumption) (by simp)
    · simp at h; subst h; exact .eqFalse (check_typed he) (by assumption)
  | c, Γ, .and a b, o, h => by
    simp [check] at h
    obtain ⟨oa, ha, ob, hob, rfl⟩ := h
    exact .and (check_typed ha) (checkBranch_typed hob)
  | c, Γ, .or a b, o, h => by
    simp [check] at h
    obtain ⟨oa, ha, ob, hob, rfl⟩ := h
    exact .or (check_typed ha) (checkBranch_typed hob)
  | c, Γ, .not a, o, h => by
    simp [check] at h
    obtain ⟨oa, ha, rfl⟩ := h
    exact .not (check_typed ha)

theorem checkBranch_typed : ∀ {c : Ctx} {g : Option Env} {e : Expr} {o : Out},
    checkBranch c g e = some o → TypedBranch c g e o
  | c, some Γ, e, o, h => .live (check_typed (by simpa [checkBranch] using h))
  | c, none, e, o, h => by simp [checkBranch] at h; subst h; exact .dead

theorem checkArgs_typed : ∀ {c : Ctx} {Γ : Env} {es : List Expr} {ao : ArgsOut},
    checkArgs c Γ es = some ao → TypedArgs c Γ es ao
  | c, Γ, [], ao, h => by simp [checkArgs] at h; subst h; exact .nil
  | c, Γ, e :: es, ao, h => by
    simp [checkArgs] at h
    obtain ⟨o, he, h⟩ := h
    split at h
    · simp at h; subst h; exact .consDead (check_typed he) (by assumption)
    · split at h
      · simp at h
      · simp at h; subst h
        exact .restDead (check_typed he) (by assumption) (checkArgs_typed (by assumption))
      · simp at h; subst h
        exact .cons (check_typed he) (by assumption) (checkArgs_typed (by assumption))

end

end QuarzCore
