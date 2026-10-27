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
    (hcore : FrameCore P c Λ fr.vars fr.self s) (he : Ext P W (fun _ => False) Λ Λ' s s')
    (hW : ∀ l, W l → frameLocs fr.vars l → frameW fr.vars xs l) : Sat P c (c.reset Δ xs) fr s' := by
  intro p t hp
  cases p with
  | field f =>
    obtain ⟨l, o, fd, i, h1, h2, h3, h4, h5, h6, h7⟩ := hs _ _ hp
    obtain ⟨o', ho', hc, _, hs'⟩ := he.grow l o h2
    refine ⟨l, o', fd, i, h1, ho', h3, by rw [hc]; exact h4, by rw [hc]; exact h5, hs' i h6, fun hv => ?_⟩
    obtain ⟨v, h8, h9⟩ := h7 hv
    exact ⟨v, by rw [he.imm l o o' h2 ho' id i fd h5 hv]; exact h8, he.hasTy h9⟩
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

theorem lookupVar_cons (x y : String) (l : Nat) (rest : List (String × Nat)) :
    lookupVar ((x, l) :: rest) y = if x = y then some l else lookupVar rest y := by
  by_cases h : x = y
  · simp [lookupVar, List.find?, h]
  · have : (x == y) = false := by simpa using h
    simp [lookupVar, List.find?, this, h]

/-- A new frame's names, each at its fresh location. -/
theorem lookupVar_alloc : ∀ {names : List String} {base j : Nat} {x : String}, names.Nodup →
    names[j]? = some x → lookupVar (Store.allocVars base names) x = some (base + j)
  | [], _, _, _, _, h => by simp at h
  | y :: ys, base, j, x, hnd, h => by
    have hnd' := List.nodup_cons.mp hnd
    simp only [Store.allocVars, lookupVar_cons]
    cases j with
    | zero => simp at h; subst h; simp
    | succ j =>
      simp at h
      have hxy : y ≠ x := fun e => hnd'.1 (e ▸ List.mem_of_getElem? h)
      rw [if_neg hxy, lookupVar_alloc hnd'.2 h]
      congr 1; omega

theorem lookupVar_alloc_inv : ∀ {names : List String} {base l : Nat} {x : String},
    lookupVar (Store.allocVars base names) x = some l → ∃ j, names[j]? = some x ∧ l = base + j
  | [], _, _, _, h => by simp [Store.allocVars, lookupVar] at h
  | y :: ys, base, l, x, h => by
    simp only [Store.allocVars, lookupVar_cons] at h
    split at h
    · rename_i hyx; cases h; exact ⟨0, by simp [hyx], rfl⟩
    · obtain ⟨j, hj, rfl⟩ := lookupVar_alloc_inv h
      exact ⟨j + 1, by simpa using hj, by omega⟩

theorem mem_allocVars : ∀ {names : List String} {base l : Nat} {x : String},
    (x, l) ∈ Store.allocVars base names → base ≤ l ∧ l < base + names.length
  | [], _, _, _, h => by simp [Store.allocVars] at h
  | y :: ys, base, l, x, h => by
    simp only [Store.allocVars, List.mem_cons] at h
    rcases h with h | h
    · cases h; simp
    · have := mem_allocVars h; simp; omega

theorem Ext.restrict {W W' Wo : Nat → Prop} {Λ Λ' : List Ty} {s s' : Store} (h : Ext P W Wo Λ Λ' s s')
    (hw : ∀ l, l < s.locs.length → W l → W' l) : Ext P W' Wo Λ Λ' s s' where
  tys := h.tys
  locs := fun l v hv => by
    obtain ⟨v', h1, h2⟩ := h.locs l v hv
    refine ⟨v', h1, ?_⟩
    rcases h2 with h2 | ⟨hwl, t, ht, hty⟩
    · exact .inl h2
    · exact .inr ⟨hw l (List.getElem?_eq_some_iff.mp hv).1 hwl, t, ht, hty⟩
  grow := h.grow
  imm := h.imm

theorem params_get : ∀ {ps : List (String × Ty)} {p : Path} {t : Ty},
    Env.get (ps.map fun (x, t) => ((.local x : Path), t)) p = some t → ∃ x, p = .local x ∧ (x, t) ∈ ps
  | [], _, _, h => by simp [Env.get] at h
  | (y, u) :: ps, p, t, h => by
    simp only [List.map_cons, Env.get_cons] at h
    split at h
    · rename_i hp; cases h; exact ⟨y, hp.symm, List.mem_cons_self ..⟩
    · obtain ⟨x, hx, hm⟩ := params_get h; exact ⟨x, hx, List.mem_cons_of_mem _ hm⟩

theorem find_nodup : ∀ {l : List (String × Ty)} {x : String} {t : Ty}, (l.map (·.1)).Nodup →
    (x, t) ∈ l → (l.find? (·.1 == x)).map (·.2) = some t
  | [], _, _, _, h => by cases h
  | (y, u) :: l, x, t, hnd, h => by
    have hnd' := List.nodup_cons.mp hnd
    by_cases hy : y = x
    · subst hy
      rcases List.mem_cons.mp h with he | hm
      · cases he; simp [List.find?]
      · exact absurd (List.mem_map.mpr ⟨_, hm, rfl⟩) hnd'.1
    · have hne : (y == x) = false := by simpa using hy
      rcases List.mem_cons.mp h with he | hm
      · cases he; exact absurd rfl hy
      · simp only [List.find?, hne]; exact find_nodup hnd'.2 hm

/-- A method's parameter: a local of its type (`wfMethod`). -/
theorem decl_param {mt : Method} (h : P.wfMethod mt = true) {x : String} {t : Ty}
    (hm : (x, t) ∈ mt.params) : (⟨P, mt, false, false⟩ : Ctx).decl x = some t := by
  simp only [Program.wfMethod, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨_, hlen⟩, hnd⟩, hpre⟩, _⟩, _⟩ := h
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hm
  have hpl := (List.getElem?_eq_some_iff.mp hi).1
  have hil : i < mt.locals.length := by omega
  have hz : (mt.params.zip mt.locals)[i]? = some ((x, t), mt.locals[i]) := by
    simp [List.zip, List.getElem?_zipWith, hi, hil]
  have heq := hpre _ (List.mem_iff_getElem?.mpr ⟨i, hz⟩)
  simp only at heq
  have hloc : (x, t) ∈ mt.locals := by rw [heq]; exact List.getElem_mem hil
  exact find_nodup hnd hloc

/-- Arguments for a method, for one overriding it. -/
theorem AllTy.over (hwf : WfClasses P.classes) {s : Store} :
    ∀ {vs : List Value} {sup sub : List (String × Ty)}, AllTy P s vs (sup.map (·.2)) →
      sup.length = sub.length → ((sup.zip sub).all fun ((_, t), (_, u)) => t.le P.classes u) = true →
      AllTy P s vs (sub.map (·.2))
  | [], [], [], _, _, _ => trivial
  | _ :: _, _ :: _, _ :: _, ⟨h1, h2⟩, hl, ha => by
    simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at ha
    exact ⟨hasTy_le hwf h1 ha.1, AllTy.over hwf h2 (by simpa using hl) ha.2⟩
  | [], [], _ :: _, _, hl, _ => by simp at hl
  | [], _ :: _, _, h, _, _ => h.elim
  | _ :: _, [], _, h, _, _ => h.elim
  | _ :: _, _ :: _, [], _, hl, _ => by simp at hl

/-- What the method run for a call takes and gives, against the one
found: the same, or an override of it. -/
theorem over_facts (hwf : WfClasses P.classes) {mt mt' : Method} {s : Store} {vs : List Value}
    (h : mt' = mt ∨ P.overrides mt' mt = true) (hvs : AllTy P s vs (mt.params.map (·.2))) :
    vs.length = mt'.params.length ∧ AllTy P s vs (mt'.params.map (·.2)) ∧
      mt'.ret.le P.classes mt.ret = true ∧ mt'.block = mt.block := by
  rcases h with rfl | h
  · exact ⟨by rw [hvs.length]; simp, hvs, Ty.le_refl hwf _, rfl⟩
  · simp only [Program.overrides, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨hl, hall⟩, hret⟩, hblk⟩ := h
    exact ⟨by rw [hvs.length]; simp [hl], hvs.over hwf hl.symm hall, hret, hblk⟩

theorem zip_fst_snd : ∀ (ps : List (String × Ty)), (ps.map (·.1)).zip (ps.map (·.2)) = ps
  | [] => rfl
  | (x, t) :: ps => by simp [zip_fst_snd ps]

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
      exact ⟨Λ1, a, e.monoW evalWs_cons_left, f, g, i⟩
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
      exact ⟨Λ1, a, e.monoW evalWs_cons_left, f, g, i⟩
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
        -- The receiver is of a type, so made.
        have hmade : s.hasTy P (.obj l) [.cls o.cls] := by
          obtain ⟨a, ha, _⟩ := hasTy_iff.mp hv
          obtain ⟨o', ho', _, rfl⟩ := typeOf_obj ha
          rw [ho] at ho'; cases ho'
          exact hasTy_iff.mpr ⟨_, ha, .cls o.cls, List.mem_singleton.mpr rfl, Atom.le_refl hwf _⟩
        have := ih.send s Λ (.obj l) o.cls "==" mt [w] none [] hw
          ⟨l, o, rfl, ho, ClassTable.mem_ancestors_self hwf _⟩ hmade (by decide) hl hargs
          (by rw [hblk]; exact hnone)
        rw [hblk] at this
        exact this.weaken hwf hret
  | _ => exact plain _

omit hP horc ih in
/-- `(x, t)` of the parameters and types: the value given for `x`, of `t`. -/
theorem zip_val {s : Store} :
    ∀ {ps : List String} {ts : List Ty} {vs : List Value}, AllTy P s vs ts →
      ∀ x t, (x, t) ∈ ps.zip ts → ∃ v, (x, v) ∈ ps.zip vs ∧ s.hasTy P v t
  | [], _, _, _, _, _, hm => by simp at hm
  | _ :: _, [], _, _, _, _, hm => by simp at hm
  | p :: ps, t' :: ts, [], h, _, _, _ => h.elim
  | p :: ps, t' :: ts, v :: vs, ⟨h1, h2⟩, x, t, hm => by
    rcases List.mem_cons.mp hm with he | hm
    · cases he; exact ⟨v, List.mem_cons_self .., h1⟩
    · obtain ⟨w, hw, hwt⟩ := zip_val h2 x t hm
      exact ⟨w, List.mem_cons_of_mem _ hw, hwt⟩

omit hP horc ih in
/-- A frame of a method is one of its blocks' too. -/
theorem FrameCore.inBlock {c : Ctx} {Λ : List Ty} {vars : List (String × Nat)} {me : Value}
    {s : Store} (h : FrameCore P c Λ vars me s) (b : Bool) :
    FrameCore P { c with inBlock := b } Λ vars me s :=
  ⟨h.decls, h.inj, h.inStore, h.self, h.selfInit, h.selfObj⟩

omit hP horc ih in
theorem FrameCore.ofBlock {c : Ctx} {Λ : List Ty} {vars : List (String × Nat)} {me : Value}
    {s : Store} {b : Bool} (h : FrameCore P { c with inBlock := b } Λ vars me s) :
    FrameCore P c Λ vars me s :=
  ⟨h.decls, h.inj, h.inStore, h.self, h.selfInit, h.selfObj⟩

theorem block_succ : BlockGood P orc (n + 1) := by
  intro s Λ clo sig vs ws hw hgiven hvs
  obtain ⟨hch, hin⟩ := hgiven
  have hwf := hP.classes
  obtain ⟨vars, me, outer, ps, body⟩ := clo
  cases ws with
  | nil => simp [ChainAt] at hch
  | cons w ws' =>
  obtain ⟨c, Δ, ob⟩ := w
  simp only [ChainAt] at hch
  obtain ⟨hc, hcore, hch', habove, hps, hty, hret, hR, hJ⟩ := hch
  subst hc
  simp only [blockParamsOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at hps
  obtain ⟨⟨hlen, hnd⟩, hpd⟩ := hps
  -- Each parameter: a local, declared at least as wide as its type.
  have hdecl : ∀ x t, (x, t) ∈ ps.zip sig.params → ∃ d, c.decl x = some d ∧ t.le c.ct d = true :=
    fun x t hm => by
      have := hpd (x, t) hm
      simp only at this
      split at this
      · rename_i d hd; exact ⟨d, hd, this⟩
      · cases this
  have hlook : ∀ x ∈ ps, ∃ l, lookupVar vars x = some l := fun x hx => by
    obtain ⟨t, ht⟩ : ∃ t, (x, t) ∈ ps.zip sig.params := by
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hx
      have hil : i < sig.params.length := by rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hi).1
      exact ⟨sig.params[i], List.mem_iff_getElem?.mpr ⟨i, by simp [List.zip, List.getElem?_zipWith, hi, hil]⟩⟩
    obtain ⟨d, hd, _⟩ := hdecl x t ht
    obtain ⟨l, hl, _⟩ := hcore.decls x d hd
    exact ⟨l, hl⟩
  obtain ⟨s1, hb⟩ := bindAll_some (vars := vars) s (by rw [hlen, hvs.length]) hlook
  simp only [runBlock, hb]
  obtain ⟨hobjs, hlen1, hsame⟩ := bindAll_same hb
  have hval := bindAll_val hcore.inj hb hnd (fun x _ l hl => hcore.inStore x l (lookupVar_mem hl))
  have mono : ∀ {v : Value} {t : Ty}, s.hasTy c.prog v t → s1.hasTy c.prog v t := fun h => by
    unfold Store.hasTy Store.hasType Store.typeOf at *; rw [hobjs]; exact h
  -- Binding: each parameter's location gets a value of its declared type.
  have he1 : Ext c.prog (frameW vars ps) (fun _ => False) Λ Λ s s1 := by
    refine ⟨List.prefix_refl Λ, fun l v hv => ?_, fun l o ho => ⟨o, by rw [hobjs]; exact ho, rfl,
      rfl, fun _ h => h⟩, fun l o o' ho ho' _ _ _ _ _ => by rw [hobjs, ho] at ho'; cases ho'; rfl⟩
    by_cases hl : ∃ x ∈ ps, lookupVar vars x = some l
    · obtain ⟨x, hx, hxl⟩ := hl
      obtain ⟨t, ht⟩ : ∃ t, (x, t) ∈ ps.zip sig.params := by
        obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hx
        have hil : i < sig.params.length := by rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hi).1
        exact ⟨sig.params[i], List.mem_iff_getElem?.mpr ⟨i, by simp [List.zip, List.getElem?_zipWith, hi, hil]⟩⟩
      obtain ⟨w, hwm, hwt⟩ := zip_val hvs x t ht
      obtain ⟨l', hl', hw'⟩ := hval x w hwm
      rw [hxl] at hl'; cases hl'
      obtain ⟨d, hd, htd⟩ := hdecl x t ht
      obtain ⟨l'', hl'', hΛ⟩ := hcore.decls x d hd
      rw [hxl] at hl''; cases hl''
      exact ⟨w, hw', .inr ⟨⟨x, hx, hxl⟩, d, hΛ, mono (hasTy_le hwf hwt htd)⟩⟩
    · exact ⟨v, by rw [hsame l fun x hx hxl => hl ⟨x, hx, hxl⟩]; exact hv, .inl rfl⟩
  have hw1 : WfStore c.prog Λ s1 := ⟨by rw [hlen1]; exact hw.len, fun l o ho => by
    rw [hobjs] at ho
    obtain ⟨a, b, b2, d⟩ := hw.objs l o ho
    exact ⟨a, b, b2, fun i v f h0 h1 h2 => mono (d i v f h0 h1 h2)⟩⟩
  have hframe : ∀ l, frameW vars ps l → ¬ chainLocs outer l := fun l ⟨x, _, hxl⟩ hc =>
    Nat.lt_irrefl _ (habove l l ⟨x, lookupVar_mem hxl⟩ hc)
  have hf1 : FrameOK c.prog { c with inBlock := true } Λ ⟨vars, me, outer⟩ s1 ws' :=
    ⟨(hcore.stable he1).inBlock true, hch'.stable he1 _ _ _ (fun l hl hw => hframe l hw hl)
        (fun _ h => h.elim), habove,
      fun l hl => by rw [hlen1]; exact hin l (by simp only [chainLocs]; exact Or.inr hl),
      fun _ h => by simp at h⟩
  have hs1 : Sat c.prog c (blockEnv c Δ ps sig body) ⟨vars, me, outer⟩ s1 := by
    refine Sat.foldl_set _ (hR.reset_typed hcore he1 fun l h _ => ?_) fun x t hm => ?_
    · obtain ⟨x, hx, hxl⟩ := h; exact ⟨x, List.mem_append_left _ hx, hxl⟩
    · obtain ⟨w, hwm, hwt⟩ := zip_val hvs x t hm
      obtain ⟨l, hl, hw'⟩ := hval x w hwm
      obtain ⟨d, hd, htd⟩ := hdecl x t hm
      exact ⟨l, w, d, hl, hw', hd, mono hwt, mono (hasTy_le hwf hwt htd)⟩
  have := ih.eval { c with inBlock := true } _ body ob ⟨vars, me, outer⟩ s1 Λ ws' rfl hty hw1 hf1 hs1
  revert this
  generalize eval c.prog orc n ⟨vars, me, outer⟩ s1 body = r
  intro this
  cases r with
  | ok v s2 =>
    obtain ⟨Λ2, hw2, he2, hf2, hv2, ho2, _, _⟩ := this
    have he12 : Ext c.prog _ (fun _ => False) _ _ _ _ := (he1.trans he2 hw).mono (fun _ h => h)
      (fun _ h => h.elim False.elim fun ⟨_, hb, _⟩ => by simp at hb)
    have hblkW : ∀ l, (frameW vars ps l ∨ evalW ⟨vars, me, outer⟩ body l) →
        blkW (some (.mk vars me outer ps body)) l := by
      rintro l (⟨x, hx, hl⟩ | ⟨x, hx, hl⟩ | h) <;> simp only [blkW]
      · exact Or.inl ⟨x, List.mem_append_left _ hx, hl⟩
      · exact Or.inl ⟨x, List.mem_append_right _ hx, hl⟩
      · exact Or.inr h
    obtain ⟨Γb, hΓb, hsb⟩ := ho2
    refine ⟨Λ2, hw2, he12.monoW hblkW, hasTy_le hwf hv2 hret, ?_, fun l hl => ?_⟩
    · simp only [ChainAt]
      refine ⟨trivial, hf2.core.ofBlock, hf2.chain, habove, ?_, hty, hret,
        hR.reset_typed hcore he12 fun l h hfl => ?_, ?_⟩
      · simp only [blockParamsOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true]
        exact ⟨⟨hlen, hnd⟩, hpd⟩
      · rcases h with ⟨x, hx, hl⟩ | ⟨x, hx, hl⟩ | h
        · exact ⟨x, List.mem_append_left _ hx, hl⟩
        · exact ⟨x, List.mem_append_right _ hx, hl⟩
        · obtain ⟨y, hy⟩ := hfl
          exact absurd (habove l l ⟨y, hy⟩ (blkW_chain h)) (Nat.lt_irrefl _)
      · rw [hΓb]; exact hsb.join_right hwf
    · simp only [chainLocs] at hl
      rcases hl with ⟨x, hx⟩ | hl
      · exact hf2.core.inStore x l hx
      · exact hf2.chainIn l hl
  | returned v s2 =>
    obtain ⟨_, _, _, _, _, hib, _⟩ := this
    cases hib
  | raised => trivial
  | timeout => trivial
  | stuck => exact this

theorem send_succ : SendGood P orc (n + 1) := by
  intro s Λ recv k m mt vs blk ws hw hobj hrecv hni hl hvs hblk
  have hwf := hP.classes
  obtain ⟨l, o, rfl, ho, hk⟩ := hobj
  obtain ⟨mt', hl', hsub⟩ := Program.lookup_sub hwf (fun mt h => (hP.methods mt h).1) hl hk hni
  obtain ⟨hlen', hvs', hret', hblk'⟩ := over_facts hwf hsub hvs
  obtain ⟨hmem', howner, hname'⟩ := Program.lookup_spec hl'
  obtain ⟨hwfm, o', hty, hout, _⟩ := hP.methods mt' hmem'
  -- Not `initialize` (`Program.resolve`): its own parameters only.
  have hni' : (mt'.name == "initialize") = false := by simp [hname', hni]
  have hnotInit : (⟨P, mt', false, false⟩ : Ctx).inInit = false := hni'
  rw [hni'] at hty
  simp only [Bool.false_eq_true, if_false, List.append_nil] at hty
  -- The receiver is of a type: made.
  have hmade : s.typeOf (.obj l) = some (.cls o.cls) := by
    obtain ⟨a, ha, _⟩ := hasTy_iff.mp hrecv
    obtain ⟨o', ho', hall, rfl⟩ := typeOf_obj ha
    rw [ho] at ho'; cases ho'; exact ha
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
    ⟨s.locs ++ (mt'.locals.map (·.1)).map fun _ => .nil, s.objs⟩ (by rw [List.length_map, hlen']) hexists
  simp only [hb]
  obtain ⟨hobjs, hlen2, hsame⟩ := bindAll_same hb
  simp only [List.length_append, List.length_map] at hlen2
  have hge : ∀ x l', lookupVar (Store.allocVars s.locs.length (mt'.locals.map (·.1))) x = some l' →
      s.locs.length ≤ l' ∧ l' < s.locs.length + mt'.locals.length := fun x l' h => by
    have := mem_allocVars (lookupVar_mem h); simpa using this
  have mono : ∀ {v : Value} {t : Ty}, s.hasTy P v t → s2.hasTy P v t := fun h => by
    unfold Store.hasTy Store.hasType Store.typeOf at *; rw [hobjs]; exact h
  have he12 : Ext P (fun _ => False) (fun _ => False) Λ (Λ ++ mt'.locals.map (·.2)) s s2 := by
    refine ⟨List.prefix_append _ _, fun l' v hv => ⟨v, ?_, .inl rfl⟩, fun l' o' ho' =>
      ⟨o', by rw [hobjs]; exact ho', rfl, rfl, fun _ h => h⟩,
      fun _ o1 o2 h1 h2 _ _ _ _ _ => by rw [hobjs, h1] at h2; cases h2; rfl⟩
    have hl' := (List.getElem?_eq_some_iff.mp hv).1
    rw [hsame l' fun x _ hx => by have := (hge x l' hx).1; omega]
    simp [List.getElem?_append_left hl', hv]
  have hw2 : WfStore P (Λ ++ mt'.locals.map (·.2)) s2 :=
    ⟨by simp [hw.len, hlen2], fun l' o' ho' => by
      rw [hobjs] at ho'
      obtain ⟨a, b, b2, d⟩ := hw.objs l' o' ho'
      exact ⟨a, b, b2, fun i v f h0 h1 h2 => mono (d i v f h0 h1 h2)⟩⟩
  have hcore : FrameCore P ⟨P, mt', false, false⟩ (Λ ++ mt'.locals.map (·.2))
      (Store.allocVars s.locs.length (mt'.locals.map (·.1))) (.obj l) s2 := by
    refine ⟨fun x d hd => ?_, fun x y l' hx hy => ?_, fun x l' hm => ?_, fun _ => ?_,
      fun h => absurd h (by rw [hnotInit]; simp), ⟨l, rfl⟩⟩
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
    · refine hasTy_iff.mpr ⟨.cls o.cls, ?_, .cls mt'.owner, List.mem_singleton.mpr rfl, ?_⟩
      · exact typeOf_mono (fun l' o' h => ⟨o', by rw [hobjs]; exact h, rfl, rfl, fun _ h => h⟩) hmade
      · simpa [Atom.le, ClassTable.subclass_iff] using howner
  obtain ⟨hch, hin⟩ := hblk
  rw [← hblk'] at hch
  have hf2 : FrameOK P ⟨P, mt', false, false⟩ (Λ ++ mt'.locals.map (·.2))
      ⟨Store.allocVars s.locs.length (mt'.locals.map (·.1)), .obj l, blk⟩ s2 ws :=
    ⟨hcore, hch.stable he12 _ _ _ (fun _ _ h => h) (fun _ h => h.elim), fun l1 l2 ⟨x, hx⟩ hc => by
      have := (mem_allocVars hx).1; have := hin l2 hc; omega,
      fun l1 hc => by have := hin l1 hc; omega, fun h => absurd h (by rw [hnotInit]; simp)⟩
  have hs2 : Sat P ⟨P, mt', false, false⟩ (mt'.params.map fun (x, t) => (.local x, t))
      ⟨Store.allocVars s.locs.length (mt'.locals.map (·.1)), .obj l, blk⟩ s2 := by
    intro p t hp
    obtain ⟨x, rfl, hm⟩ := params_get hp
    have hd := decl_param hwfm hm
    obtain ⟨v, hvm, hvt⟩ := zip_val hvs' x t (by rw [zip_fst_snd]; exact hm)
    obtain ⟨lx, hlx, hv⟩ := bindAll_val hcore.inj hb hpnd
      (fun y _ l' hl' => by have := hge y l' hl'; simp; omega) x v hvm
    exact ⟨lx, v, t, hlx, hv, hd, mono hvt, mono hvt⟩
  have := ih.eval ⟨P, mt', false, false⟩ _ mt'.body o' _ s2 _ ws rfl hty hw2 hf2 hs2
  revert this
  generalize eval P orc n _ s2 mt'.body = r
  intro this
  have hrestrict : ∀ l', l' < s.locs.length →
      (False ∨ evalW ⟨Store.allocVars s.locs.length (mt'.locals.map (·.1)), .obj l, blk⟩ mt'.body l') →
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
    have hret3 : s3.hasTy P v mt.ret := by
      rcases hout (by rw [hname']; exact hni) with h | h
      · obtain ⟨_, h', _⟩ := ho3; rw [h] at h'; cases h'
      · exact hasTy_le hwf (hasTy_le hwf hv3 h) hret'
    refine ⟨Λ3, hw3, ((he12.trans he3 hw).mono (fun _ h => h) (fun _ h => h.elim id id)).restrict hrestrict, hret3, ?_, hf3.chainIn⟩
    rw [← hblk']; exact hf3.chain
  | returned v s3 =>
    obtain ⟨Λ3, hw3, he3, hf3, hv3, _⟩ := this
    have he3 := he3.mono (Wo' := fun _ => False) (fun _ h => h) (fun l h => (hnoW l h).elim)
    refine ⟨Λ3, hw3, ((he12.trans he3 hw).mono (fun _ h => h) (fun _ h => h.elim id id)).restrict hrestrict, hasTy_le hwf hv3 hret', ?_,
      hf3.chainIn⟩
    rw [← hblk']; exact hf3.chain
  | raised => trivial
  | timeout => trivial
  | stuck => exact this

end QuarzCore
