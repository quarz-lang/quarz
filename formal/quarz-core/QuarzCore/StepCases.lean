/-
evalArgs, send, runBlock and equal with fuel `n + 1`, from the five
functions with fuel `n` (Good).
-/

import QuarzCore.EvalCases

set_option linter.deprecated false

namespace QuarzCore

variable {P : Program} {orc : Oracle}

theorem ArgsPost.extend_other {c : Ctx} {ao ao' : ArgsOut} {fr : Frame}
    {ws : List (Ctx × Env × Out)} {Λ Λ1 : List Ty} {s s1 : Store} {W1 W2 W : Nat → Prop}
    {r : Result} (h : ArgsPost P c ao fr ws Λ1 s1 W2 (.other r)) (he : Ext P W1 Λ Λ1 s s1)
    (hw : WfStore P Λ s) (h1 : ∀ l, W1 l → W l) (h2 : ∀ l, W2 l → W l) :
    ArgsPost P c ao' fr ws Λ s W (.other r) := by
  cases r with
  | ok => exact absurd h id
  | stuck => exact h
  | returned v s' =>
    obtain ⟨Λ', a, e, f, g, i⟩ := h
    exact ⟨Λ', a, (he.trans e hw).mono fun l hl => hl.elim (h1 l) (h2 l), f, g, i⟩
  | raised => trivial
  | timeout => trivial

theorem evalWs_cons_left {fr : Frame} {e : Expr} {es : List Expr} :
    ∀ l, evalW fr e l → evalWs fr (e :: es) l := by
  rintro l (⟨x, hx, hl⟩ | h)
  · exact .inl ⟨e, List.mem_cons_self .., x, hx, hl⟩
  · exact .inr h

theorem evalWs_cons_right {fr : Frame} {e : Expr} {es : List Expr} :
    ∀ l, evalWs fr es l → evalWs fr (e :: es) l := by
  rintro l (⟨e', he', h⟩ | h)
  · exact .inl ⟨e', List.mem_cons_of_mem _ he', h⟩
  · exact .inr h

/-- What `wfMethod` says of an `==`. -/
theorem Program.wfMethod_eq {mt : Method} (h : P.wfMethod mt = true) (hn : mt.name = "==") :
    mt.ret.le P.classes [.bool] = true ∧ mt.block = none ∧
      ∃ x t, mt.params = [(x, t)] ∧ Ty.le P.classes [.nil, .bool] t = true := by
  simp only [Program.wfMethod, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, hn,
    not_true_eq_false, false_or] at h
  obtain ⟨_, ⟨⟨hret, hblk⟩, hp⟩⟩ := h
  refine ⟨hret, by simpa using hblk, ?_⟩
  revert hp
  match mt.params with
  | [(x, t)] => exact fun hp => ⟨x, t, rfl, hp⟩
  | [] => simp
  | _ :: _ :: _ => simp

theorem SendPost.weaken {ret ret' : Ty} {sig : Option BlockSig} {blk : Option Closure}
    {ws : List (Ctx × Env × Out)} {Λ : List Ty} {s : Store} {r : Result}
    (hwf : WfClasses P.classes) (h : SendPost P ret sig blk ws Λ s r)
    (hle : ret.le P.classes ret' = true) : SendPost P ret' sig blk ws Λ s r := by
  cases r with
  | ok v s' =>
    obtain ⟨Λ', a, b, d, e⟩ := h
    exact ⟨Λ', a, b, hasTy_le hwf d hle, e⟩
  | stuck => exact h
  | returned => exact h
  | raised => trivial
  | timeout => trivial

/-- What binding values to names does: only their locations change. -/
theorem bindAll_same {vars : List (String × Nat)} :
    ∀ {xs : List String} {vs : List Value} {s s' : Store}, bindAll s vars xs vs = some s' →
      s'.objs = s.objs ∧ s'.locs.length = s.locs.length ∧
      ∀ l, (∀ x ∈ xs, lookupVar vars x ≠ some l) → s'.locs[l]? = s.locs[l]?
  | [], [], s, s', h => by simp [bindAll] at h; subst h; exact ⟨rfl, rfl, fun _ _ => rfl⟩
  | x :: xs, v :: vs, s, s', h => by
    simp only [bindAll, bind, Option.bind_eq_some_iff] at h
    obtain ⟨l, hl, h⟩ := h
    obtain ⟨h1, h2, h3⟩ := bindAll_same h
    refine ⟨h1, by rw [h2]; simp [Store.setLoc], fun l' hl' => ?_⟩
    rw [h3 l' fun y hy => hl' y (List.mem_cons_of_mem _ hy)]
    have : l' ≠ l := fun e => hl' x (List.mem_cons_self ..) (e ▸ hl)
    simp [Store.setLoc, List.getElem?_set_ne (Ne.symm this)]
  | [], _ :: _, _, _, h => by simp [bindAll] at h
  | _ :: _, [], _, _, h => by simp [bindAll] at h

/-- Bound to distinct names, at distinct locations: each holds its value. -/
theorem bindAll_val {vars : List (String × Nat)}
    (hinj : ∀ x y l, lookupVar vars x = some l → lookupVar vars y = some l → x = y) :
    ∀ {xs : List String} {vs : List Value} {s s' : Store}, bindAll s vars xs vs = some s' →
      xs.Nodup → (∀ x ∈ xs, ∀ l, lookupVar vars x = some l → l < s.locs.length) →
      ∀ x v, (x, v) ∈ xs.zip vs → ∃ l, lookupVar vars x = some l ∧ s'.locs[l]? = some v
  | [], [], _, _, _, _, _, _, _, hm => by simp at hm
  | x :: xs, w :: vs, s, s', h, hnd, hin, y, v, hm => by
    simp only [bindAll, bind, Option.bind_eq_some_iff] at h
    obtain ⟨l, hl, h⟩ := h
    have hnd' := List.nodup_cons.mp hnd
    rcases List.mem_cons.mp hm with he | hm
    · cases he
      refine ⟨l, hl, ?_⟩
      rw [(bindAll_same h).2.2 l fun z hz hzl => hnd'.1 (by rw [hinj z x l hzl hl] at hz; exact hz)]
      simp [Store.setLoc, hin x (List.mem_cons_self ..) l hl]
    · exact bindAll_val hinj h hnd'.2 (fun z hz l' hl' => by
        simpa [Store.setLoc] using hin z (List.mem_cons_of_mem _ hz) l' hl') y v hm
  | [], _ :: _, _, _, h, _, _, _, _, _ => by simp [bindAll] at h
  | _ :: _, [], _, _, h, _, _, _, _, _ => by simp [bindAll] at h

theorem bindAll_some {vars : List (String × Nat)} :
    ∀ {xs : List String} {vs : List Value} (s : Store), xs.length = vs.length →
      (∀ x ∈ xs, ∃ l, lookupVar vars x = some l) → ∃ s', bindAll s vars xs vs = some s'
  | [], [], s, _, _ => ⟨s, rfl⟩
  | x :: xs, v :: vs, s, hlen, hl => by
    obtain ⟨l, hx⟩ := hl x (List.mem_cons_self ..)
    obtain ⟨s', hs'⟩ := bindAll_some (s.setLoc l v) (by simpa using hlen)
      fun y hy => hl y (List.mem_cons_of_mem _ hy)
    exact ⟨s', by simp [bindAll, hx, hs']⟩
  | [], _ :: _, _, h, _ => by simp at h
  | _ :: _, [], _, h, _ => by simp at h

/-- The un-narrowed environment of what `xs` names holds after writes of
values of their declared types to those locals only. -/
theorem Sat.reset_typed {c : Ctx} {Δ : Env} {xs : List String} {fr : Frame} {Λ Λ' : List Ty}
    {s s' : Store} {W : Nat → Prop} (hs : Sat P c (c.reset Δ xs) fr s)
    (hcore : FrameCore P c Λ fr.vars fr.self s) (he : Ext P W Λ Λ' s s')
    (hW : ∀ l, W l → frameLocs fr.vars l → frameW fr.vars xs l) : Sat P c (c.reset Δ xs) fr s' := by
  intro p t hp
  cases p with
  | field f =>
    obtain ⟨l, o, fd, i, v, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hs _ _ hp
    obtain ⟨o', ho', hc, hf⟩ := he.objs l o h2
    exact ⟨l, o', fd, i, v, h1, ho', h3, h4, by rw [hc]; exact h5, by rw [hc]; exact h6,
      by rw [hf i fd h6 h4]; exact h7, he.hasTy h8⟩
  | «local» x =>
    obtain ⟨l, v, d, h1, h2, h3, h4, h5⟩ := hs _ _ hp
    obtain ⟨v', hv', hch⟩ := he.locs l v h2
    rcases hch with rfl | ⟨hwl, t', ht', hty⟩
    · exact ⟨l, _, d, h1, hv', h3, he.hasTy h4, he.hasTy h5⟩
    · obtain ⟨y, hy, hyl⟩ := hW l hwl ⟨x, lookupVar_mem h1⟩
      have hyx := hcore.inj y x l hyl h1
      subst hyx
      obtain ⟨u, _, hif⟩ := Ctx.reset_get_local hp
      rw [if_pos hy, h3] at hif
      cases hif
      obtain ⟨l', hl', hΛ⟩ := hcore.decls y _ h3
      rw [h1] at hl'; cases hl'
      rw [hΛ] at ht'; cases ht'
      exact ⟨l, v', _, h1, hv', h3, hty, hty⟩

/-- Setting paths one after another, each holding its type. -/
theorem Sat.foldl_set {c : Ctx} {fr : Frame} {s : Store} :
    ∀ (ps : List (String × Ty)) {Γ : Env}, Sat P c Γ fr s →
      (∀ x t, (x, t) ∈ ps → PathHolds P c fr s (.local x) t) →
      Sat P c (ps.foldl (fun g (x, t) => g.set (.local x) t) Γ) fr s
  | [], _, h, _ => h
  | (x, t) :: ps, Γ, h, hp => by
    simp only [List.foldl_cons]
    exact Sat.foldl_set ps (h.set (hp x t (List.mem_cons_self ..)))
      fun y u hy => hp y u (List.mem_cons_of_mem _ hy)

variable (hP : WfProg P) (horc : OracleOK P orc) {n : Nat} (ih : Good P orc n)
include hP horc ih

theorem args_succ : ArgsGood P orc (n + 1) := by
  intro c Γ es ao fr s Λ ws hc ht hw hf hs
  subst hc
  cases ht with
  | nil => exact ⟨[], Γ, rfl, Λ, hw, Ext.refl _ Λ s, hf, hs, trivial⟩
  | cons he hout hes =>
    simp only [evalArgs]
    have := ih.eval _ _ _ _ fr s Λ ws rfl he hw hf hs
    revert this
    generalize eval c.prog orc n fr s _ = r
    intro this
    cases r with
    | ok v s1 =>
      dsimp only
      obtain ⟨Λ1, hw1, he1, hf1, hv1, ho1, _, _⟩ := this
      obtain ⟨Δ1, hΔ, hs1⟩ := ho1
      rw [hout] at hΔ; cases hΔ
      have := ih.args _ _ _ _ fr s1 Λ1 ws rfl hes hw1 hf1 hs1
      revert this
      generalize evalArgs c.prog orc n fr s1 _ = ar
      intro this
      cases ar with
      | ok vs s2 =>
        obtain ⟨tys', Δ2, hao, Λ2, hw2, he2, hf2, hs2, hvs⟩ := this
        cases hao
        exact ⟨_, _, rfl, Λ2, hw2, (he1.trans he2 hw).mono fun l hl =>
          hl.elim (evalWs_cons_left l) (evalWs_cons_right l), hf2, hs2, he2.hasTy hv1, hvs⟩
      | other r => exact this.extend_other he1 hw evalWs_cons_left evalWs_cons_right
    | returned v s1 =>
      obtain ⟨Λ1, a, e, f, g, i⟩ := this
      exact ⟨Λ1, a, e.mono evalWs_cons_left, f, g, i⟩
    | raised => trivial
    | timeout => trivial
    | stuck => exact this
  | consDead he hout =>
    simp only [evalArgs]
    have := ih.eval _ _ _ _ fr s Λ ws rfl he hw hf hs
    revert this
    generalize eval c.prog orc n fr s _ = r
    intro this
    cases r with
    | ok v s1 =>
      obtain ⟨_, _, _, _, _, ho1, _, _⟩ := this
      obtain ⟨_, hΔ, _⟩ := ho1
      rw [hout] at hΔ; cases hΔ
    | returned v s1 =>
      obtain ⟨Λ1, a, e, f, g, i⟩ := this
      exact ⟨Λ1, a, e.mono evalWs_cons_left, f, g, i⟩
    | raised => trivial
    | timeout => trivial
    | stuck => exact this
  | restDead he hout hes =>
    simp only [evalArgs]
    have := ih.eval _ _ _ _ fr s Λ ws rfl he hw hf hs
    revert this
    generalize eval c.prog orc n fr s _ = r
    intro this
    cases r with
    | ok v s1 =>
      dsimp only
      obtain ⟨Λ1, hw1, he1, hf1, hv1, ho1, _, _⟩ := this
      obtain ⟨Δ1, hΔ, hs1⟩ := ho1
      rw [hout] at hΔ; cases hΔ
      have := ih.args _ _ _ _ fr s1 Λ1 ws rfl hes hw1 hf1 hs1
      revert this
      generalize evalArgs c.prog orc n fr s1 _ = ar
      intro this
      cases ar with
      | ok vs s2 => obtain ⟨_, _, hao, _⟩ := this; cases hao
      | other r => exact this.extend_other he1 hw evalWs_cons_left evalWs_cons_right
    | returned v s1 =>
      obtain ⟨Λ1, a, e, f, g, i⟩ := this
      exact ⟨Λ1, a, e.mono evalWs_cons_left, f, g, i⟩
    | raised => trivial
    | timeout => trivial
    | stuck => exact this

end QuarzCore

namespace QuarzCore

variable {P : Program} {orc : Oracle}
variable (hP : WfProg P) (horc : OracleOK P orc) {n : Nat} (ih : Good P orc n)
include hP horc ih

theorem equal_succ : EqualGood P orc (n + 1) := by
  intro s Λ v w t hw hv hw'
  have hwf := hP.classes
  have hnone : BlkGiven P Λ s [] none none := ⟨trivial, fun l h => by simp [chainLocs] at h⟩
  have plain : ∀ b : Bool, SendPost P [.bool] none none [] Λ s (.ok (.bool b) s) :=
    fun b => ⟨Λ, hw, Ext.refl _ Λ s, hasTy_lit_bool, hnone⟩
  cases v with
  | obj l =>
    simp only [equal]
    cases ho : s.objs[l]? with
    | none => exact plain false
    | some o =>
      simp only [Option.bind_some]
      cases hl : P.lookup o.cls "==" with
      | none => exact plain false
      | some mt =>
        dsimp only
        obtain ⟨hmem, _, hname⟩ := Program.lookup_spec hl
        obtain ⟨hret, hblk, x, pt, hps, hpt⟩ :=
          Program.wfMethod_eq (hP.methods mt hmem).1 hname
        have hargs : AllTy P s [w] (mt.params.map (·.2)) := by
          rw [hps]
          refine ⟨?_, trivial⟩
          rcases hw' with rfl | rfl | rfl
          · exact hasTy_le hwf hasTy_lit_nil (Ty.le_trans hwf (Ty.le_append_left hwf [.nil] [.bool]) hpt)
          · exact hasTy_le hwf hasTy_lit_bool (Ty.le_trans hwf (Ty.le_append_right hwf [.nil] [.bool]) hpt)
          · exact hasTy_le hwf hasTy_lit_bool (Ty.le_trans hwf (Ty.le_append_right hwf [.nil] [.bool]) hpt)
        have := ih.send s Λ (.obj l) o.cls "==" mt [w] none [] hw
          ⟨l, o, rfl, ho, ClassTable.mem_ancestors_self hwf _⟩ hl hargs (by rw [hblk]; exact hnone)
        rw [hblk] at this
        exact this.weaken hwf hret
  | _ => exact plain _

end QuarzCore
