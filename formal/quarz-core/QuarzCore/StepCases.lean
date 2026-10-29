/-
evalArgs, send, runBlock and equal with fuel `n + 1`, from the six
functions with fuel `n` (Good).
-/

import QuarzCore.EvalCases

set_option linter.deprecated false

namespace QuarzCore

variable {P : Program} {orc : Oracle}

theorem ArgsPost.extend_other {c : Ctx} {ao ao' : ArgsOut} {fr : Frame}
    {ws : List (Ctx × Env × Out)} {Λ Λ1 : List Ty} {s s1 : Store} {W1 W2 W : Nat → Prop}
    {r : Result} (h : ArgsPost P c ao fr ws Λ1 s1 W2 (.other r)) (he : Ext P W1 (initW c fr) Λ Λ1 s s1)
    (hw : WfStore P Λ s) (h1 : ∀ l, W1 l → W l) (h2 : ∀ l, W2 l → W l) :
    ArgsPost P c ao' fr ws Λ s W (.other r) := by
  cases r with
  | ok => exact absurd h id
  | stuck => exact h
  | returned v s' =>
    obtain ⟨Λ', a, e, f, g, i⟩ := h
    exact ⟨Λ', a, (he.transW e hw).monoW fun l hl => hl.elim (h1 l) (h2 l), f, g, i⟩
  | raised v s' =>
    obtain ⟨Λ', a, e, f, g⟩ := h
    exact ⟨Λ', a, (he.transW e hw).monoW fun l hl => hl.elim (h1 l) (h2 l), f, g⟩
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
    mt.ret.le P.classes (P.classes.boundsOf mt.owner) [.bool] = true ∧ mt.block = none ∧
      ∃ x t, mt.params = [(x, t)] ∧ Ty.le P.classes (P.classes.boundsOf mt.owner) [.nil, .bool] t = true := by
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
    (hle : ret.le P.classes [] ret' = true) : SendPost P ret' sig blk ws Λ s r := by
  cases r with
  | ok v s' =>
    obtain ⟨Λ', a, b, d, e⟩ := h
    exact ⟨Λ', a, b, hasTy_le hwf d hle, e⟩
  | stuck => exact h
  | returned => exact h
  | raised => trivial
  | timeout => trivial

/-- Arguments for a method, for one overriding it. -/
theorem AllTy.over (hwf : WfClasses P.classes) {s : Store} :
    ∀ {vs : List Value} {sup sub : List (String × Ty)}, AllTy P s vs (sup.map (·.2)) →
      sup.length = sub.length → ((sup.zip sub).all fun ((_, t), (_, u)) => t.le P.classes [] u) = true →
      AllTy P s vs (sub.map (·.2))
  | [], [], [], _, _, _ => trivial
  | _ :: _, _ :: _, _ :: _, ⟨h1, h2⟩, hl, ha => by
    simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at ha
    exact ⟨hasTy_le hwf h1 ha.1, AllTy.over hwf h2 (by simpa using hl) ha.2⟩
  | [], [], _ :: _, _, hl, _ => by simp at hl
  | [], _ :: _, _, h, _, _ => h.elim
  | _ :: _, [], _, h, _, _ => h.elim
  | _ :: _, _ :: _, [], _, hl, _ => by simp at hl

/-- Arguments for a method, for one overriding it, both seen through `σ`. -/
theorem AllTy.over_subst (hwf : WfClasses P.classes) {s : Store} (σ : List Ty) {κ : List Ty}
    (hσ : ArgsIn P.classes κ σ) :
    ∀ {vs : List Value} {sup sub : List (String × Ty)},
      AllTy P s vs ((sup.map (·.2)).map (Ty.subst σ)) →
      sup.length = sub.length → ((sup.zip sub).all fun ((_, t), (_, u)) => t.le P.classes κ u) = true →
      AllTy P s vs ((sub.map (·.2)).map (Ty.subst σ))
  | [], [], [], _, _, _ => trivial
  | _ :: _, _ :: _, _ :: _, ⟨h1, h2⟩, hl, ha => by
    simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at ha
    exact ⟨hasTy_le hwf h1 (Ty.subst_leK hwf σ hσ ha.1), AllTy.over_subst hwf σ hσ h2 (by simpa using hl) ha.2⟩
  | [], [], _ :: _, _, hl, _ => by simp at hl
  | [], _ :: _, _, h, _, _ => h.elim
  | _ :: _, [], _, h, _, _ => h.elim
  | _ :: _, _ :: _, [], _, hl, _ => by simp at hl

/-- What the method run for a call takes and gives, against the one the
receiver's view found (`mt0` with `bs`, the arguments the receiver's
class gives `mt0`'s owner): the same method, or an override of it, whose
own view of `mt0` (through `σ`, the arguments the class gives the
override's owner) is the receiver's. -/
theorem over_facts_exact (hwf : WfClasses P.classes) {mt0 mt' : Method} {c : Nat} {as bs σ : List Ty}
    {s : Store} {vs : List Value}
    (h : mt' = mt0 ∨ (P.overrides mt' (mt0.inst ((P.classes.ancestorArgs mt'.owner
        (P.classes.selfArgs mt'.owner) mt0.owner).getD [])) = true ∧
      mt0.owner ∈ P.classes.ancestors mt'.owner))
    (hbs : P.classes.ancestorArgs c as mt0.owner = some bs)
    (hσ : P.classes.ancestorArgs c as mt'.owner = some σ)
    (hσlen : σ.length = (((P.classes[mt'.owner]?).map (·.params)).getD []).length)
    (hσin : ArgsIn P.classes (P.classes.boundsOf mt'.owner) σ)
    (hvs : AllTy P s vs ((mt0.inst bs).params.map (·.2))) :
    vs.length = mt'.params.length ∧ AllTy P s vs ((mt'.params.map (·.2)).map (Ty.subst σ)) ∧
      Ty.le P.classes [] (mt'.ret.subst σ) (mt0.inst bs).ret = true ∧
      mt'.block.map (BlockSig.subst σ) = (mt0.inst bs).block := by
  rw [Method.inst_params_snd] at hvs
  rcases h with rfl | ⟨h, hown⟩
  · rw [hbs] at hσ; cases hσ
    exact ⟨by rw [hvs.length]; simp, hvs, Ty.le_refl hwf _, rfl⟩
  · obtain ⟨τ, hτ⟩ :=
      ClassTable.ancestorArgs_of_mem hwf mt'.owner (P.classes.selfArgs mt'.owner) mt0.owner hown
    -- `mt'`'s view of `mt0`, through `σ`, is the receiver's.
    have hτσ : Ty.substArgs σ τ = bs := by
      have h1 := ClassTable.ancestorArgs_subst P.classes σ hτ
      rw [substArgs_selfArgs P.classes hσlen] at h1
      have h2 := ClassTable.ancestorArgs_through hwf _ _ _ _ _ _ hσ hbs hown
      rw [h1] at h2; cases h2; rfl
    rw [hτ, Option.getD_some] at h
    simp only [Program.overrides, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨hl, hall⟩, hret⟩, hblk⟩ := h
    have hvs' : AllTy P s vs (((mt0.inst τ).params.map (·.2)).map (Ty.subst σ)) := by
      rw [Method.inst_params_snd, Ty.substArgs_comp_fun, hτσ]; exact hvs
    refine ⟨by rw [hvs.length, hl]; simp [Method.inst_params_length],
      AllTy.over_subst hwf σ hσin hvs' hl.symm hall, ?_, ?_⟩
    · rw [Method.inst_ret] at hret ⊢
      have := Ty.subst_leK hwf σ hσin hret
      rwa [Ty.subst_comp, hτσ] at this
    · rw [hblk]
      simp only [Method.inst, Option.map_map]
      congr 1
      funext sig
      simp [Function.comp, BlockSig.subst_subst, hτσ]

/-- Values of types below others, mapped. -/
theorem AllTy.map_le (hwf : WfClasses P.classes) {s : Store} {f g : Ty → Ty} :
    ∀ {vs : List Value} {ts : List Ty}, AllTy P s vs (ts.map f) →
      (∀ t ∈ ts, Ty.le P.classes [] (f t) (g t) = true) → AllTy P s vs (ts.map g)
  | [], [], _, _ => trivial
  | _ :: _, t :: ts, ⟨h1, h2⟩, h => ⟨hasTy_le hwf h1 (h t (List.mem_cons_self)),
      AllTy.map_le hwf h2 fun u hu => h u (List.mem_cons_of_mem _ hu)⟩
  | [], _ :: _, h, _ => h.elim
  | _ :: _, [], h, _ => h.elim

/-- What the method run for a call takes and gives, against the one the
receiver's view found (`mt0` with `bs`): through the object's own
arguments for `mt0`'s owner (`bs0`, below `bs` as the owner's variances
say), where the variance check of `mt0`'s signature makes the
parameters take at least and the result and block give at most; then as
`over_facts_exact` says for an override. -/
theorem over_facts (hwf : WfClasses P.classes) {mt0 mt' : Method} {c : Nat} {as bs bs0 σ : List Ty}
    {s : Store} {vs : List Value}
    (h : mt' = mt0 ∨ (P.overrides mt' (mt0.inst ((P.classes.ancestorArgs mt'.owner
        (P.classes.selfArgs mt'.owner) mt0.owner).getD [])) = true ∧
      mt0.owner ∈ P.classes.ancestors mt'.owner))
    (hpos : P.methodPosOk mt0 = true)
    (hbs0 : P.classes.ancestorArgs c as mt0.owner = some bs0)
    (hrel : argsLeWith (Atom.le P.classes []) (P.classes.variances mt0.owner) bs0 bs = true)
    (hσ : P.classes.ancestorArgs c as mt'.owner = some σ)
    (hσlen : σ.length = (((P.classes[mt'.owner]?).map (·.params)).getD []).length)
    (hσin : ArgsIn P.classes (P.classes.boundsOf mt'.owner) σ)
    (hvs : AllTy P s vs ((mt0.inst bs).params.map (·.2))) :
    vs.length = mt'.params.length ∧ AllTy P s vs ((mt'.params.map (·.2)).map (Ty.subst σ)) ∧
      Ty.le P.classes [] (mt'.ret.subst σ) (mt0.inst bs).ret = true ∧
      BlockSig.optLe P.classes (mt'.block.map (BlockSig.subst σ)) (mt0.inst bs).block := by
  simp only [Program.methodPosOk, Bool.and_eq_true, List.all_eq_true] at hpos
  obtain ⟨⟨hpp, hpr⟩, hpb⟩ := hpos
  have hneg : ∀ t : Ty, t.posOk P.classes (P.classes.variances mt0.owner) false = true →
      Ty.le P.classes [] (t.subst bs) (t.subst bs0) = true := fun t ht => by
    simpa using Ty.subst_var hwf hrel t false ht
  have hposi : ∀ t : Ty, t.posOk P.classes (P.classes.variances mt0.owner) true = true →
      Ty.le P.classes [] (t.subst bs0) (t.subst bs) = true := fun t ht => by
    simpa using Ty.subst_var hwf hrel t true ht
  have hvs0 : AllTy P s vs ((mt0.inst bs0).params.map (·.2)) := by
    rw [Method.inst_params_snd] at hvs ⊢
    refine AllTy.map_le hwf hvs fun t ht => hneg t ?_
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ht
    exact hpp p hp
  obtain ⟨hl, hvsσ, hretσ, hblkσ⟩ := over_facts_exact hwf h hbs0 hσ hσlen hσin hvs0
  refine ⟨hl, hvsσ, ?_, ?_⟩
  · rw [Method.inst_ret] at hretσ ⊢
    exact Ty.le_trans hwf hretσ (hposi _ hpr)
  · rw [hblkσ]
    simp only [Method.inst]
    cases hb : mt0.block with
    | none => trivial
    | some sig =>
      rw [hb] at hpb
      simp only [Bool.and_eq_true, List.all_eq_true] at hpb
      simp only [Option.map_some, BlockSig.optLe, BlockSig.le, BlockSig.subst, List.length_map]
      refine ⟨trivial, fun i t t' ht ht' => ?_, hneg _ hpb.2⟩
      simp only [List.getElem?_map] at ht ht'
      obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp ht
      rw [hp] at ht'; simp at ht'; subst ht'
      exact hposi p (hpb.1 p (List.mem_of_getElem? hp))

variable (hP : WfProg P) (horc : OracleOK P orc) {n : Nat} (ih : Good P orc n)
include hP horc ih

theorem args_succ : ArgsGood P orc (n + 1) := by
  intro c Γ es ao fr s Λ ws hc ht hw hf hs
  subst hc
  cases ht with
  | nil => exact ⟨[], Γ, rfl, Λ, hw, Ext.refl _ _ Λ s, hf, hs, trivial⟩
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
        exact ⟨_, _, rfl, Λ2, hw2, (he1.transW he2 hw).monoW fun l hl =>
          hl.elim (evalWs_cons_left l) (evalWs_cons_right l), hf2, hs2, he2.hasTy hv1, hvs⟩
      | other r => exact this.extend_other he1 hw evalWs_cons_left evalWs_cons_right
    | returned v s1 =>
      obtain ⟨Λ1, a, e, f, g, i⟩ := this
      exact ⟨Λ1, a, e.monoW evalWs_cons_left, f, g, i⟩
    | raised v s1 =>
      obtain ⟨Λ1, a, e, f, g⟩ := this
      exact ⟨Λ1, a, e.monoW evalWs_cons_left, f, g⟩
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
      exact ⟨Λ1, a, e.monoW evalWs_cons_left, f, g, i⟩
    | raised v s1 =>
      obtain ⟨Λ1, a, e, f, g⟩ := this
      exact ⟨Λ1, a, e.monoW evalWs_cons_left, f, g⟩
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
      exact ⟨Λ1, a, e.monoW evalWs_cons_left, f, g, i⟩
    | raised v s1 =>
      obtain ⟨Λ1, a, e, f, g⟩ := this
      exact ⟨Λ1, a, e.monoW evalWs_cons_left, f, g⟩
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
    fun b => ⟨Λ, hw, Ext.refl _ _ Λ s, hasTy_lit_bool, hnone⟩
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
        obtain ⟨hmem, hown, hname⟩ := Program.lookup_spec hl
        obtain ⟨hret, hblk, x, pt, hps, hpt⟩ :=
          Program.wfMethod_eq (hP.methods mt hmem).1 hname
        -- The method as the receiver's own view (its class, its arguments) finds it.
        obtain ⟨σ, hσ⟩ := ClassTable.ancestorArgs_of_mem hwf o.cls o.args mt.owner hown
        have hσin := ClassTable.ancestorArgs_in hwf hσ (hw.objs l o ho).2.2.1 (hw.bounds l o ho)
        have hlat : P.lookupAt o.cls o.args "==" = some (mt.inst σ) := by
          simp [Program.lookupAt, hl, hσ]
        have hargs : AllTy P s [w] ((mt.inst σ).params.map (·.2)) := by
          rw [Method.inst_params_snd, hps]
          have hpt' : Ty.le P.classes [] [.nil, .bool] (pt.subst σ) = true := by
            have := Ty.subst_leK hwf σ hσin hpt
            rwa [Ty.subst_closed_id σ [.nil, .bool] rfl] at this
          refine ⟨?_, trivial⟩
          rcases hw' with rfl | rfl | rfl
          · exact hasTy_le hwf hasTy_lit_nil (Ty.le_trans hwf (Ty.le_append_left hwf [.nil] [.bool]) hpt')
          · exact hasTy_le hwf hasTy_lit_bool (Ty.le_trans hwf (Ty.le_append_right hwf [.nil] [.bool]) hpt')
          · exact hasTy_le hwf hasTy_lit_bool (Ty.le_trans hwf (Ty.le_append_right hwf [.nil] [.bool]) hpt')
        -- The receiver is of a type, so made.
        have hmade : s.hasTy P (.obj l) [.cls o.cls o.args] := by
          obtain ⟨a, ha, _⟩ := hasTy_iff.mp hv
          obtain ⟨o', ho', _, rfl⟩ := typeOf_obj ha
          rw [ho] at ho'; cases ho'
          exact hasTy_iff.mpr ⟨_, ha, .cls o.cls o.args, List.mem_singleton.mpr rfl, Atom.le_refl hwf _⟩
        have hblk' : (mt.inst σ).block = none := (Method.inst_block_none mt σ).mpr hblk
        have := ih.send s Λ (.obj l) o.cls o.args "==" (mt.inst σ) [w] none [] hw
          ⟨l, o, rfl, ho, ClassTable.mem_ancestors_self hwf _⟩ hmade (by decide) hlat hargs
          (by rw [hblk']; exact hnone)
        rw [hblk'] at this
        refine this.weaken hwf ?_
        rw [Method.inst_ret]
        have := Ty.subst_leK hwf σ hσin hret
        rwa [Ty.subst_closed_id σ [.bool] rfl] at this
  | _ => exact plain _

omit hP horc ih in
/-- A frame of a method is one of its blocks' too. -/
theorem FrameCore.inBlock {c : Ctx} {Λ : List Ty} {vars : List (String × Nat)} {me : Value}
    {sa : List Ty} {s : Store} (h : FrameCore P c Λ vars me sa s) (b : Bool) :
    FrameCore P { c with inBlock := b } Λ vars me sa s :=
  ⟨h.decls, h.inj, h.inStore, h.self, h.selfInit, h.selfObj, h.closed, h.bounded, h.pins, h.pinsIn⟩

omit hP horc ih in
theorem FrameCore.ofBlock {c : Ctx} {Λ : List Ty} {vars : List (String × Nat)} {me : Value}
    {sa : List Ty} {s : Store} {b : Bool} (h : FrameCore P { c with inBlock := b } Λ vars me sa s) :
    FrameCore P c Λ vars me sa s :=
  ⟨h.decls, h.inj, h.inStore, h.self, h.selfInit, h.selfObj, h.closed, h.bounded, h.pins, h.pinsIn⟩

theorem block_succ : BlockGood P orc (n + 1) := by
  intro s Λ clo sig vs ws hw hgiven hvs
  obtain ⟨hch, hin⟩ := hgiven
  have hwf := hP.classes
  obtain ⟨vars, me, sa, outer, ps, body⟩ := clo
  cases ws with
  | nil => simp [ChainAt] at hch
  | cons w ws' =>
  obtain ⟨c, Δ, ob⟩ := w
  simp only [ChainAt] at hch
  obtain ⟨hc, hcore, hch', habove, ⟨sig0, hrel, hps, hty, hret⟩, hR⟩ := hch
  subst hc
  -- The values the method gives: of the block's parameters' types.
  have hvs : AllTy c.prog s vs (sig0.subst sa).params := by
    obtain ⟨hl, hp, _⟩ := hrel
    revert hvs hl hp
    generalize sig.params = xs
    generalize (sig0.subst sa).params = ys
    intro hvs hl hp
    induction xs generalizing vs ys with
    | nil => cases ys with
      | nil => exact hvs
      | cons => simp at hl
    | cons x xs ihx =>
      cases ys with
      | nil => simp at hl
      | cons y ys =>
        cases vs with
        | nil => exact hvs.elim
        | cons v vs =>
          exact ⟨hasTy_le hP.classes hvs.1 (hp 0 x y rfl rfl),
            ihx vs ys hvs.2 (by simpa using hl) fun i t t' h1 h2 => hp (i + 1) t t' h1 h2⟩
  simp only [blockParamsOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at hps
  obtain ⟨⟨hlen, hnd⟩, hpd⟩ := hps
  -- The values: of the signature's types as the block's writer named
  -- them, through its frame's arguments.
  have hzip : ∀ x t, (x, t) ∈ ps.zip sig0.params →
      ∃ v, (x, v) ∈ ps.zip vs ∧ s.hasTy c.prog v (t.subst sa) := fun x t hm =>
    zip_val hvs x (t.subst sa) (by
      simp only [BlockSig.subst, List.zip_map_right]
      exact List.mem_map.mpr ⟨(x, t), hm, rfl⟩)
  -- Each parameter: a local, declared at least as wide as its type.
  have hdecl : ∀ x t, (x, t) ∈ ps.zip sig0.params → ∃ d, c.decl x = some d ∧ t.le c.ct c.bounds d = true :=
    fun x t hm => by
      have := hpd (x, t) hm
      simp only at this
      split at this
      · rename_i d hd; exact ⟨d, hd, this⟩
      · cases this
  have hlook : ∀ x ∈ ps, ∃ l, lookupVar vars x = some l := fun x hx => by
    obtain ⟨t, ht⟩ : ∃ t, (x, t) ∈ ps.zip sig0.params := by
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hx
      have hil : i < sig0.params.length := by rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hi).1
      exact ⟨sig0.params[i], List.mem_iff_getElem?.mpr ⟨i, by simp [List.zip, List.getElem?_zipWith, hi, hil]⟩⟩
    obtain ⟨d, hd, _⟩ := hdecl x t ht
    obtain ⟨l, hl, _⟩ := hcore.decls x d hd
    exact ⟨l, hl⟩
  obtain ⟨s1, hb⟩ := bindAll_some (vars := vars) s (by rw [hlen, hvs.length]; simp [BlockSig.subst]) hlook
  simp only [runBlock, hb]
  obtain ⟨hobjs, hlen1, hsame⟩ := bindAll_same hb
  have hprocs := bindAll_procs hb
  have hpins1 := bindAll_pins hb
  have hbts := bindAll_builts hb
  have hval := bindAll_val hcore.inj hb hnd (fun x _ l hl => hcore.inStore x l (lookupVar_mem hl))
  have mono : ∀ {v : Value} {t : Ty}, s.hasTy c.prog v t → s1.hasTy c.prog v t := fun h => by
    unfold Store.hasTy Store.hasType Store.typeOf at *; rw [hobjs, hprocs, hbts]; exact h
  -- Binding: each parameter's location gets a value of its declared type.
  have he1 : Ext c.prog (frameW vars ps) (fun _ => False) Λ Λ s s1 := by
    refine ⟨List.prefix_refl Λ, fun l v hv => ?_, fun l o ho => ⟨o, by rw [hobjs]; exact ho, rfl,
      rfl, rfl, fun _ h => h⟩, fun l o o' ho ho' _ _ _ _ _ => by rw [hobjs, ho] at ho'; cases ho'; rfl,
      by rw [hprocs]; exact List.prefix_refl _, by rw [hpins1]; exact List.prefix_refl _, by rw [hbts]; exact List.prefix_refl _⟩
    by_cases hl : ∃ x ∈ ps, lookupVar vars x = some l
    · obtain ⟨x, hx, hxl⟩ := hl
      obtain ⟨t, ht⟩ : ∃ t, (x, t) ∈ ps.zip sig0.params := by
        obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hx
        have hil : i < sig0.params.length := by rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hi).1
        exact ⟨sig0.params[i], List.mem_iff_getElem?.mpr ⟨i, by simp [List.zip, List.getElem?_zipWith, hi, hil]⟩⟩
      obtain ⟨w, hwm, hwt⟩ := hzip x t ht
      obtain ⟨l', hl', hw'⟩ := hval x w hwm
      rw [hxl] at hl'; cases hl'
      obtain ⟨d, hd, htd⟩ := hdecl x t ht
      obtain ⟨l'', hl'', hΛ⟩ := hcore.decls x d hd
      rw [hxl] at hl''; cases hl''
      exact ⟨w, hw', .inr ⟨.inl ⟨x, hx, hxl⟩, d.subst sa, hΛ, mono (hasTy_le hwf hwt (Ty.subst_leK hwf sa hcore.bounded htd))⟩⟩
    · exact ⟨v, by rw [hsame l fun x hx hxl => hl ⟨x, hx, hxl⟩]; exact hv, .inl rfl⟩
  have hw1 : WfStore c.prog Λ s1 := ⟨by rw [hlen1]; exact hw.len, by rw [hpins1, hlen1]; exact hw.pinsLen,
    fun l o ho => by
    rw [hobjs] at ho
    obtain ⟨a, a1, a2, b, b2, d⟩ := hw.objs l o ho
    exact ⟨a, a1, a2, b, b2, fun i v f h0 h1 h2 => mono (d i v f h0 h1 h2)⟩,
    fun l o ho => by rw [hobjs] at ho; exact hw.noEnum l o ho,
    fun l o ho => by rw [hobjs] at ho; exact hw.bounds l o ho,
    fun i p hp => by rw [hprocs] at hp; exact (hw.procs i p hp).stable he1,
      fun i k as h' => by rw [hbts] at h'; exact hw.builts i k as h'⟩
  have hframe : ∀ l, frameW vars ps l → ¬ chainLocs outer l := fun l ⟨x, _, hxl⟩ hc =>
    Nat.lt_irrefl _ (habove l l ⟨x, lookupVar_mem hxl⟩ hc)
  have hf1 : FrameOK c.prog { c with inBlock := true } Λ ⟨vars, me, sa, outer⟩ s1 ws' :=
    ⟨(hcore.stable he1).inBlock true, hch'.stable he1 _ _ _ (fun l hl hw => hframe l hw hl)
        (fun _ h => h.elim), habove,
      fun l hl => by rw [hlen1]; exact hin l (by simp only [chainLocs]; exact Or.inr hl),
      fun _ h => by simp at h⟩
  have hs1 : Sat c.prog c (blockEnv c Δ ps sig0 body) ⟨vars, me, sa, outer⟩ s1 := by
    refine Sat.foldl_set _ (hR.reset_typed hcore he1 (fun l h _ => ?_) (fun _ h => List.mem_append_right _ h))
      fun x t hm => ?_
    · obtain ⟨x, hx, hxl⟩ := h; exact ⟨x, List.mem_append_left _ (List.mem_append_left _ hx), hxl⟩
    · obtain ⟨w, hwm, hwt⟩ := hzip x t hm
      obtain ⟨l, hl, hw'⟩ := hval x w hwm
      obtain ⟨d, hd, htd⟩ := hdecl x t hm
      exact ⟨l, w, d, hl, hw', hd, mono hwt, mono (hasTy_le hwf hwt (Ty.subst_leK hwf sa hcore.bounded htd))⟩
  have := ih.eval { c with inBlock := true } _ body ob ⟨vars, me, sa, outer⟩ s1 Λ ws' rfl hty hw1 hf1 hs1
  revert this
  generalize eval c.prog orc n ⟨vars, me, sa, outer⟩ s1 body = r
  intro this
  cases r with
  | ok v s2 =>
    obtain ⟨Λ2, hw2, he2, hf2, hv2, ho2, _, _⟩ := this
    have he12 : Ext c.prog _ (fun _ => False) _ _ _ _ := (he1.trans he2 hw).mono (fun _ h => h)
      (fun _ h => h.elim False.elim fun ⟨_, hb, _⟩ => by simp at hb)
    have hblkW : ∀ l, (frameW vars ps l ∨ evalW ⟨vars, me, sa, outer⟩ body l) →
        blkW (some (.mk vars me sa outer ps body)) l := by
      rintro l (⟨x, hx, hl⟩ | ⟨x, hx, hl⟩ | h) <;> simp only [blkW]
      · exact Or.inl ⟨x, List.mem_append_left _ hx, hl⟩
      · exact Or.inl ⟨x, List.mem_append_right _ hx, hl⟩
      · exact Or.inr h
    refine ⟨Λ2, hw2, he12.monoW hblkW, hasTy_le hwf (hasTy_le hwf hv2 (Ty.subst_leK hwf sa hcore.bounded hret)) hrel.2.2, ?_,
      fun l hl => ?_⟩
    · simp only [ChainAt]
      refine ⟨trivial, hf2.core.ofBlock, hf2.chain, habove, ⟨sig0, hrel, ?_, hty, hret⟩,
        hR.reset_typed hcore he12 (fun l h hfl => ?_) (fun _ h => List.mem_append_right _ h)⟩
      · simp only [blockParamsOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true]
        exact ⟨⟨hlen, hnd⟩, hpd⟩
      · rcases h with ⟨x, hx, hl⟩ | ⟨x, hx, hl⟩ | h
        · exact ⟨x, List.mem_append_left _ (List.mem_append_left _ hx), hl⟩
        · exact ⟨x, List.mem_append_left _ (List.mem_append_right _ hx), hl⟩
        · obtain ⟨y, hy⟩ := hfl
          exact absurd (habove l l ⟨y, hy⟩ (blkW_chain h)) (Nat.lt_irrefl _)
    · simp only [chainLocs] at hl
      rcases hl with ⟨x, hx⟩ | hl
      · exact hf2.core.inStore x l hx
      · exact hf2.chainIn l hl
  | returned v s2 =>
    obtain ⟨_, _, _, _, _, hib, _⟩ := this
    cases hib
  | raised v s2 =>
    obtain ⟨Λ2, hw2, he2, hf2, hv2⟩ := this
    have he12 : Ext c.prog _ (fun _ => False) _ _ _ _ := (he1.trans he2 hw).mono (fun _ h => h)
      (fun _ h => h.elim False.elim fun ⟨_, hb, _⟩ => by simp at hb)
    have hblkW : ∀ l, (frameW vars ps l ∨ evalW ⟨vars, me, sa, outer⟩ body l) →
        blkW (some (.mk vars me sa outer ps body)) l := by
      rintro l (⟨x, hx, hl⟩ | ⟨x, hx, hl⟩ | h) <;> simp only [blkW]
      · exact Or.inl ⟨x, List.mem_append_left _ hx, hl⟩
      · exact Or.inl ⟨x, List.mem_append_right _ hx, hl⟩
      · exact Or.inr h
    refine ⟨Λ2, hw2, he12.monoW hblkW, hv2, ?_, fun l hl => ?_⟩
    · simp only [ChainAt]
      refine ⟨trivial, hf2.core.ofBlock, hf2.chain, habove, ⟨sig0, hrel, ?_, hty, hret⟩,
        hR.reset_typed hcore he12 (fun l h hfl => ?_) (fun _ h => List.mem_append_right _ h)⟩
      · simp only [blockParamsOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true]
        exact ⟨⟨hlen, hnd⟩, hpd⟩
      · rcases h with ⟨x, hx, hl⟩ | ⟨x, hx, hl⟩ | h
        · exact ⟨x, List.mem_append_left _ (List.mem_append_left _ hx), hl⟩
        · exact ⟨x, List.mem_append_left _ (List.mem_append_right _ hx), hl⟩
        · obtain ⟨y, hy⟩ := hfl
          exact absurd (habove l l ⟨y, hy⟩ (blkW_chain h)) (Nat.lt_irrefl _)
    · simp only [chainLocs] at hl
      rcases hl with ⟨x, hx⟩ | hl
      · exact hf2.core.inStore x l hx
      · exact hf2.chainIn l hl
  | timeout => trivial
  | stuck => exact this

theorem send_succ : SendGood P orc (n + 1) := by
  intro s Λ recv k as m mt vs blk ws hw hobj hrecv hni hl hvs hblk
  have hwf := hP.classes
  obtain ⟨l, o, rfl, ho, hk⟩ := hobj
  obtain ⟨hcls, hclosed, halen, _, _, _⟩ := hw.objs l o ho
  -- The receiver is of a type: made.
  have hmade : s.typeOf (.obj l) = some (.cls o.cls o.args) := by
    obtain ⟨a, ha, _⟩ := hasTy_iff.mp hrecv
    obtain ⟨o', ho', hall, rfl⟩ := typeOf_obj ha
    rw [ho] at ho'; cases ho'; exact ha
  -- Its view `k[as]`: the arguments its class gives `k` are below `as`,
  -- as `k`'s variances say.
  have hkas : ∃ as0, P.classes.ancestorArgs o.cls o.args k = some as0 ∧
      argsLeWith (Atom.le P.classes []) (P.classes.variances k) as0 as = true := by
    obtain ⟨a, ha, b, hb, hab⟩ := hasTy_iff.mp hrecv
    rw [hmade] at ha; cases ha
    rw [List.mem_singleton] at hb; subst hb
    rcases (Atom.le_cls_iff hwf ..).mp hab with ⟨rfl, rfl⟩ | h
    · obtain ⟨bs, hbs⟩ := ClassTable.ancestorArgs_of_mem hwf o.cls o.args 0 hk
      have hlen := ClassTable.ancestorArgs_length hwf _ _ _ _ hbs halen
      have hb0 : bs = [] := by
        cases h0 : P.classes[0]? with
        | none => simp only [List.getElem?_eq_none_iff] at h0; have := hwf.nonempty; omega
        | some r => have hr := hwf.rootParams r h0; simpa [h0, hr] using hlen
      rw [hb0] at hbs; exact ⟨[], hbs, by simp [argsLeWith]⟩
    · exact h
  obtain ⟨as0, hkas, hasle⟩ := hkas
  -- The method found, as declared (`mt0`), and the one the receiver's
  -- class runs (`mt'`), with the arguments the class gives each owner.
  obtain ⟨mt0, bs, hl0, hbs, rfl⟩ := Program.lookupAt_spec hl
  obtain ⟨mt', hl', hsub⟩ := Program.lookup_sub hwf (fun mt h => (hP.methods mt h).1) hl0 hk hni
  obtain ⟨hmem', howner, hname'⟩ := Program.lookup_spec hl'
  obtain ⟨σ, hσ⟩ := ClassTable.ancestorArgs_of_mem hwf o.cls o.args mt'.owner howner
  -- The object's own arguments for `mt0`'s owner, below the view's.
  obtain ⟨bs0, hbs0k⟩ := ClassTable.ancestorArgs_of_mem hwf k as0 mt0.owner
    (ClassTable.ancestorArgs_mem hwf _ _ _ _ hbs)
  have hbs' : P.classes.ancestorArgs o.cls o.args mt0.owner = some bs0 :=
    ClassTable.ancestorArgs_trans hwf hkas hbs0k
  have hrel := ClassTable.chain_mono hwf hbs0k hbs hasle
  have hpos : P.methodPosOk mt0 = true := by
    obtain ⟨hmem0, _, hname0⟩ := Program.lookup_spec hl0
    exact Program.wfMethod_pos (hP.methods mt0 hmem0).1 (by rw [hname0]; exact hni)
  have hσclosed := ClassTable.ancestorArgs_closed P.classes hσ hclosed
  have hσlen := ClassTable.ancestorArgs_length hwf _ _ _ _ hσ halen
  have hσin := ClassTable.ancestorArgs_in hwf hσ halen (hw.bounds l o ho)
  obtain ⟨hlen', hvs', hret', hblk'⟩ := over_facts hwf hsub hpos hbs' hrel hσ hσlen hσin hvs
  obtain ⟨hwfm, o', hty, hout, _⟩ := hP.methods mt' hmem'
  -- Not `initialize` (`Program.resolve`): its own parameters only.
  have hni' : (mt'.name == "initialize") = false := by simp [hname', hni]
  have hnotInit : (⟨P, mt', false, false⟩ : Ctx).inInit = false := hni'
  rw [hni'] at hty
  simp only [Bool.false_eq_true, if_false, List.append_nil] at hty
  simp only [send, ho, Option.bind_some, hl']
  rw [if_neg (by simp [hlen'])]
  simp only [Store.alloc]
  -- The new frame: the method's locals at fresh locations.
  have hwfm' := hwfm
  simp only [Program.wfMethod, Bool.and_eq_true, decide_eq_true_eq] at hwfm'
  obtain ⟨⟨⟨⟨⟨_, hplen⟩, hnd⟩, hpre⟩, _⟩, _⟩ := hwfm'
  have hcl : ∀ x d, (⟨P, mt', false, false⟩ : Ctx).decl x = some d →
      ∃ j, mt'.locals[j]? = some (x, d) := fun x d hd => by
    simp only [Ctx.decl, Option.map_eq_some_iff] at hd
    obtain ⟨⟨y, d'⟩, hf, hd'⟩ := hd
    simp at hd'; subst hd'
    have hp := List.find?_some hf
    simp at hp; subst hp
    exact List.mem_iff_getElem?.mp (List.mem_of_find?_eq_some hf)
  have hlookj : ∀ j x d, mt'.locals[j]? = some (x, d) →
      lookupVar (Store.allocVars s.locs.length (mt'.locals.map (·.1))) x = some (s.locs.length + j) :=
    fun j x d hj => lookupVar_alloc hnd (by simp [hj])
  -- The parameters are the first locals.
  have hptake : mt'.params = mt'.locals.take mt'.params.length := by
    apply List.ext_getElem (by simp; omega)
    intro i h1 h2
    have hil : i < mt'.locals.length := by omega
    have hz : (mt'.params.zip mt'.locals)[i]? = some (mt'.params[i], mt'.locals[i]) := by
      simp [List.zip, List.getElem?_zipWith, h1, hil]
    have := List.all_eq_true.mp hpre _ (List.mem_iff_getElem?.mpr ⟨i, hz⟩)
    simp at this; simp [this]
  have hpnd : (mt'.params.map (·.1)).Nodup := by
    rw [hptake, List.map_take]; exact hnd.sublist (List.take_sublist _ _)
  have hexists : ∀ x ∈ mt'.params.map (·.1),
      ∃ l, lookupVar (Store.allocVars s.locs.length (mt'.locals.map (·.1))) x = some l := by
    intro x hx
    obtain ⟨⟨y, t⟩, hm, rfl⟩ := List.mem_map.mp hx
    obtain ⟨j, hj⟩ := hcl y t (decl_param hwfm hm)
    exact ⟨_, hlookj j y t hj⟩
  obtain ⟨s2, hb⟩ := bindAll_some (vars := Store.allocVars s.locs.length (mt'.locals.map (·.1)))
    ⟨s.locs ++ (mt'.locals.map (·.1)).map (fun _ => .nil), s.objs, s.procs,
      s.pins ++ (mt'.locals.map (·.1)).map (fun x => decide (x ∈ mt'.body.procAssigned)), s.builts⟩
    (by rw [List.length_map, hlen']) hexists
  obtain ⟨hobjs, hlen2, hsame⟩ := bindAll_same hb
  have hprocs := bindAll_procs hb
  have hpins := bindAll_pins hb
  have hbts := bindAll_builts hb
  simp only at hpins
  have hsa2 : s2.argsFor P.classes l mt'.owner = σ := by simp [Store.argsFor, hobjs, ho, hσ]
  simp only [hb, hsa2]
  simp only [List.length_append, List.length_map] at hlen2
  have hge : ∀ x l', lookupVar (Store.allocVars s.locs.length (mt'.locals.map (·.1))) x = some l' →
      s.locs.length ≤ l' ∧ l' < s.locs.length + mt'.locals.length := fun x l' h => by
    have := mem_allocVars (lookupVar_mem h); simpa using this
  have mono : ∀ {v : Value} {t : Ty}, s.hasTy P v t → s2.hasTy P v t := fun h => by
    unfold Store.hasTy Store.hasType Store.typeOf at *; rw [hobjs, hprocs, hbts]; exact h
  have he12 : Ext P (fun _ => False) (fun _ => False) Λ (Λ ++ (mt'.locals.map (·.2)).map (Ty.subst σ)) s s2 := by
    refine ⟨List.prefix_append _ _, fun l' v hv => ⟨v, ?_, .inl rfl⟩, fun l' o' ho' =>
      ⟨o', by rw [hobjs]; exact ho', rfl, rfl, rfl, fun _ h => h⟩,
      fun _ o1 o2 h1 h2 _ _ _ _ _ => by rw [hobjs, h1] at h2; cases h2; rfl,
      by rw [hprocs]; exact List.prefix_refl _, by rw [hpins]; exact List.prefix_append _ _, by rw [hbts]; exact List.prefix_refl _⟩
    have hl' := (List.getElem?_eq_some_iff.mp hv).1
    rw [hsame l' fun x _ hx => by have := (hge x l' hx).1; omega]
    simp [List.getElem?_append_left hl', hv]
  have hw2 : WfStore P (Λ ++ (mt'.locals.map (·.2)).map (Ty.subst σ)) s2 :=
    ⟨by simp [hw.len, hlen2], by rw [hpins, hlen2]; simp [hw.pinsLen], fun l' o' ho' => by
      rw [hobjs] at ho'
      obtain ⟨a, a1, a2, b, b2, d⟩ := hw.objs l' o' ho'
      exact ⟨a, a1, a2, b, b2, fun i v f h0 h1 h2 => mono (d i v f h0 h1 h2)⟩,
      fun l' o' ho' => by rw [hobjs] at ho'; exact hw.noEnum l' o' ho',
      fun l' o' ho' => by rw [hobjs] at ho'; exact hw.bounds l' o' ho',
      fun i p hp => by rw [hprocs] at hp; exact (hw.procs i p hp).stable he12,
      fun i k as h' => by rw [hbts] at h'; exact hw.builts i k as h'⟩
  have hcore : FrameCore P ⟨P, mt', false, false⟩ (Λ ++ (mt'.locals.map (·.2)).map (Ty.subst σ))
      (Store.allocVars s.locs.length (mt'.locals.map (·.1))) (.obj l) σ s2 := by
    refine ⟨fun x d hd => ?_, fun x y l' hx hy => ?_, fun x l' hm => ?_, fun _ => ?_,
      fun h => absurd h (by rw [hnotInit]; simp), ⟨l, rfl, hsa2.symm⟩, hσclosed, hσin,
      fun x l' hl' => (fresh_pins hw.pinsLen hpins hl').1, fun x l' hl' => (fresh_pins hw.pinsLen hpins hl').2⟩
    · obtain ⟨j, hj⟩ := hcl x d hd
      refine ⟨_, hlookj j x d hj, ?_⟩
      have hjl := (List.getElem?_eq_some_iff.mp hj).1
      rw [List.getElem?_append_right (by rw [hw.len]; omega)]
      simp [hw.len, hj]
    · obtain ⟨jx, hjx, rfl⟩ := lookupVar_alloc_inv hx
      obtain ⟨jy, hjy, hjj⟩ := lookupVar_alloc_inv hy
      have : jx = jy := by omega
      subst this; rw [hjx] at hjy; cases hjy; rfl
    · have := mem_allocVars hm; simp [hlen2] at this ⊢; omega
    · refine hasTy_iff.mpr ⟨.cls o.cls o.args, ?_, .cls mt'.owner σ, List.mem_singleton.mpr rfl, ?_⟩
      · exact typeOf_mono (fun l' o' h => ⟨o', by rw [hobjs]; exact h, rfl, rfl, rfl, fun _ h => h⟩)
          (by rw [hprocs]; exact List.prefix_refl _) (by rw [hbts]; exact List.prefix_refl _) hmade
      · exact Atom.le_of_ancestorArgs hwf hσ
  obtain ⟨hch0, hin⟩ := hblk
  have hch := ChainAt.weaken hwf ws blk hch0 hblk'
  have hf2 : FrameOK P ⟨P, mt', false, false⟩ (Λ ++ (mt'.locals.map (·.2)).map (Ty.subst σ))
      ⟨Store.allocVars s.locs.length (mt'.locals.map (·.1)), .obj l, σ, blk⟩ s2 ws :=
    ⟨hcore, hch.stable he12 _ _ _ (fun _ _ h => h) (fun _ h => h.elim), fun l1 l2 ⟨x, hx⟩ hc => by
      have := (mem_allocVars hx).1; have := hin l2 hc; omega,
      fun l1 hc => by have := hin l1 hc; omega, fun h => absurd h (by rw [hnotInit]; simp)⟩
  have hs2 : Sat P ⟨P, mt', false, false⟩ (mt'.params.map fun (x, t) => (.local x, t))
      ⟨Store.allocVars s.locs.length (mt'.locals.map (·.1)), .obj l, σ, blk⟩ s2 := by
    intro p t hp
    obtain ⟨x, rfl, hm⟩ := params_get hp
    have hd := decl_param hwfm hm
    obtain ⟨v, hvm, hvt⟩ := zip_val_subst hvs' x t (by rw [zip_fst_snd]; exact hm)
    obtain ⟨lx, hlx, hv⟩ := bindAll_val hcore.inj hb hpnd
      (fun y _ l' hl' => by have := hge y l' hl'; simp; omega) x v hvm
    exact ⟨lx, v, t, hlx, hv, hd, mono hvt, mono hvt⟩
  have := ih.eval ⟨P, mt', false, false⟩ _ mt'.body o' _ s2 _ ws rfl hty hw2 hf2 hs2
  revert this
  generalize eval P orc n _ s2 mt'.body = r
  intro this
  have hrestrict : ∀ l', l' < s.locs.length →
      (False ∨ evalW ⟨Store.allocVars s.locs.length (mt'.locals.map (·.1)), .obj l, σ, blk⟩ mt'.body l') →
      blkW blk l' := by
    rintro l' hl' (h | ⟨x, _, hx⟩ | h)
    · exact h.elim
    · have := (hge x l' hx).1; omega
    · exact h
  -- The method assigns no immutable field.
  have hnoW : ∀ {fr : Frame} l, initW ⟨P, mt', false, false⟩ fr l → False :=
    fun _ ⟨hi, _⟩ => by rw [hnotInit] at hi; cases hi
  cases r with
  | ok v s3 =>
    obtain ⟨Λ3, hw3, he3, hf3, hv3, ho3, _, _⟩ := this
    have he3 := he3.mono (Wo' := fun _ => False) (fun _ h => h) (fun l h => (hnoW l h).elim)
    have hret3 : s3.hasTy P v (mt0.inst bs).ret := by
      rcases hout (by rw [hname']; exact hni) with h | h
      · obtain ⟨_, h', _⟩ := ho3; rw [h] at h'; cases h'
      · exact hasTy_le hwf (hasTy_le hwf hv3 (Ty.subst_leK hwf σ hσin h)) hret'
    refine ⟨Λ3, hw3, ((he12.trans he3 hw).mono (fun _ h => h) (fun _ h => h.elim id id)).restrict hrestrict, hret3, ?_, hf3.chainIn⟩
    exact ChainAt.restore ws blk hf3.chain hch0 hblk'
  | returned v s3 =>
    obtain ⟨Λ3, hw3, he3, hf3, hv3, _⟩ := this
    have he3 := he3.mono (Wo' := fun _ => False) (fun _ h => h) (fun l h => (hnoW l h).elim)
    refine ⟨Λ3, hw3, ((he12.trans he3 hw).mono (fun _ h => h) (fun _ h => h.elim id id)).restrict hrestrict,
      hasTy_le hwf (hasTy_le hwf hv3 (Ty.subst_le hwf σ ?_)) hret', ?_, hf3.chainIn⟩
    · exact Ty.le_refl hwf _
    exact ChainAt.restore ws blk hf3.chain hch0 hblk'
  | raised v s3 =>
    obtain ⟨Λ3, hw3, he3, hf3, hv3⟩ := this
    have he3 := he3.mono (Wo' := fun _ => False) (fun _ h => h) (fun l h => (hnoW l h).elim)
    refine ⟨Λ3, hw3, ((he12.trans he3 hw).mono (fun _ h => h) (fun _ h => h.elim id id)).restrict hrestrict,
      hv3, ?_, hf3.chainIn⟩
    exact ChainAt.restore ws blk hf3.chain hch0 hblk'
  | timeout => trivial
  | stuck => exact this

end QuarzCore
