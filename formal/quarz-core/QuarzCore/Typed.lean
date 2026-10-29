/-
The typing rules as a relation (design §2): `Typed c Γ e o` is what
`check c Γ e = some o` says, rule by rule, in the form the metatheory
works with and that is read against docs/02. It is syntax-directed and
gives the same `Out` as `check`: what `check` accepts, `Typed` derives
(`check_typed`, Check.lean).
-/

import QuarzCore.Typing

namespace QuarzCore

mutual

inductive Typed : Ctx → Env → Expr → Out → Prop where
  | nil : Typed c Γ .nil (.plain [.nil] Γ)
  | tru : Typed c Γ .tru (.plain [.bool] Γ)
  | fls : Typed c Γ .fls (.plain [.bool] Γ)
  | int : Typed c Γ (.int k) (.plain [.int] Γ)
  | str : Typed c Γ (.str t) (.plain [.str] Γ)
  | flt : Typed c Γ (.flt t) (.plain [.float] Γ)
  /-- A local read: assigned on every path, holding `u`, annotated with a
  type at least `u`; a test of it narrows it to `u`'s truthy or falsy
  atoms. -/
  | var : Γ.get (.local x) = some u → u.le c.ct c.bounds t →
      Typed c Γ (.var x t) ⟨t, some Γ, narrow Γ (.local x) (truthyTy u),
        narrow Γ (.local x) (falsyTy c.ct u)⟩
  /-- A `var` field read: never narrowed. -/
  | fieldVar : c.field? f = some fd → (!c.inInit || (Γ.get (.field f)).isSome) = true →
      fd.var = true → fd.ty.le c.ct c.bounds t → Typed c Γ (.field f t) (.plain t Γ)
  /-- An immutable field read: narrowed as a local. -/
  | fieldImm : c.field? f = some fd → (!c.inInit || (Γ.get (.field f)).isSome) = true →
      fd.var = false → (Γ.get (.field f)).getD fd.ty = u →
      u.le c.ct c.bounds t →
      Typed c Γ (.field f t) ⟨t, some Γ, narrow Γ (.field f) (truthyTy u),
        narrow Γ (.field f) (falsyTy c.ct u)⟩
  | assign : Typed c Γ e o → c.decl x = some d → o.ty.le c.ct c.bounds d → o.out = some Δ →
      Typed c Γ (.assign x e) (.plain o.ty (Δ.set (.local x) o.ty))
  | assignDead : Typed c Γ e o → c.decl x = some d → o.ty.le c.ct c.bounds d → o.out = none →
      Typed c Γ (.assign x e) .dead
  /-- A field assigned: a `var` one, or in `initialize` (not in a block of
  it) any; there it holds a value from then on. -/
  | setField : c.field? f = some fd → (fd.var || (c.inInit && !c.inBlock)) = true →
      Typed c Γ e o → o.ty.le c.ct c.bounds fd.ty → o.out = some Δ →
      Typed c Γ (.setField f e) (.plain o.ty (if c.inInit then
        Δ.set (.field f) (if fd.var then fd.ty else o.ty) else Δ))
  | setFieldDead : c.field? f = some fd → (fd.var || (c.inInit && !c.inBlock)) = true → Typed c Γ e o →
      o.ty.le c.ct c.bounds fd.ty → o.out = none → Typed c Γ (.setField f e) .dead
  /-- `self`: in `initialize`, once every field is set; never in a default. -/
  | self : (!c.inDefault && (!c.inInit || c.allSet Γ)) = true →
      Typed c Γ .self (.plain c.selfTy Γ)
  /-- `new`: the class given well-formed arguments, the call's arguments
  its `initialize`'s as that class sees them (none without one). -/
  | new : c.argsWf k targs = true → TypedArgs c Γ args (.live tys Δ) →
      c.prog.lookupAt k targs "initialize" = some mi → (mi.block.isNone && argsOk c tys mi) = true →
      Typed c Γ (.new k targs args) (.plain [.cls k targs] Δ)
  | newNoInit : c.argsWf k targs = true → TypedArgs c Γ args (.live tys Δ) →
      c.prog.lookupAt k targs "initialize" = none → tys.isEmpty = true →
      Typed c Γ (.new k targs args) (.plain [.cls k targs] Δ)
  | newDead : c.argsWf k targs = true → TypedArgs c Γ args .dead →
      Typed c Γ (.new k targs args) .dead
  /-- `super(args)` in `initialize`: into the superclass (given the
  arguments this class gives it), the class's own fields assigned first;
  the inherited ones after. -/
  | superInit : c.superOk d Γ = true →
      TypedArgs c Γ args (.live tys Δ) →
      c.prog.lookupAt d (c.superArgs d) "initialize" = some mi →
      (mi.block.isNone && argsOk c tys mi) = true →
      Typed c Γ (.superInit d args) (.plain [.nil] (c.afterSuper Δ))
  | superNoInit : c.superOk d Γ = true →
      TypedArgs c Γ args (.live tys Δ) →
      c.prog.lookupAt d (c.superArgs d) "initialize" = none → tys.isEmpty = true →
      Typed c Γ (.superInit d args) (.plain [.nil] (c.afterSuper Δ))
  | superDead : c.superOk d Γ = true →
      TypedArgs c Γ args .dead → Typed c Γ (.superInit d args) .dead
  /-- A call: each atom of the receiver's type a class that has the
  method, the arguments fitting each, no block expected; its type the
  union of their results. -/
  | call : Typed c Γ r o → o.out = some Δ → TypedArgs c Δ args (.live tys Δ') →
      c.prog.resolve c.bounds o.ty m = some ms →
      (ms.all fun mt => mt.block.isNone && argsOk c tys mt) = true →
      Typed c Γ (.call r m args) (.plain (ms.flatMap (·.ret)) Δ')
  /-- A lambda: its body as a block of the method with its own locals,
  assigning only them (C0), from the locals as declared. -/
  | lambda : (!c.inInit && !c.inDefault) = true → c.prog.procClass ps.length = some k →
      (c.ct[k]?).map (·.params.length) = some (ps.length + 1) →
      c.lambdaOk ps own body = true →
      Typed (c.lambdaCtx ps own) (c.lambdaEnv Γ ps) body ob → ob.ty.le c.ct c.bounds ret →
      Typed c Γ (.lambda ps own ret body) (.plain [.cls k (ps.map (·.2) ++ [ret])] Γ)
  /-- A procedure's call: of its class, the arguments below its
  parameters, its result; no local of this frame written. -/
  | callProc : Typed c Γ f o → o.out = some Δ → TypedArgs c Δ args (.live tys Δ') →
      o.ty = [.cls k as] → c.prog.procClass (as.length - 1) = some k → as.length = tys.length + 1 →
      ((tys.zip as).all fun (t, u) => t.le c.ct c.bounds u) = true →
      Typed c Γ (.callProc f args) (.plain (as.getLast?.getD []) Δ')
  | callProcDeadRecv : Typed c Γ f o → o.out = none → Typed c Γ (.callProc f args) .dead
  | callProcDeadArgs : Typed c Γ f o → o.out = some Δ → TypedArgs c Δ args .dead →
      Typed c Γ (.callProc f args) .dead
  | callDeadRecv : Typed c Γ r o → o.out = none → Typed c Γ (.call r m args) .dead
  | callDeadArgs : Typed c Γ r o → o.out = some Δ → TypedArgs c Δ args .dead →
      Typed c Γ (.call r m args) .dead
  /-- A call with a block: the methods all take the same anonymous block;
  its body, checked from `blockEnv` (it runs 0 or more times, during the
  call), gives at most the block's result; after the call, what held
  before it with what the block assigns un-narrowed (it may have stopped
  anywhere: an exception the method rescued). -/
  | callBlk : Typed c Γ r o → o.out = some Δ → TypedArgs c Δ args (.live tys Δ') →
      c.prog.resolve c.bounds o.ty m = some ms → ms.head? = some m0 → m0.block = some sig →
      (ms.all fun mt' => mt'.block == some sig && argsOk c tys mt') = true →
      blockParamsOk c ps sig = true →
      Typed { c with inBlock := true } (blockEnv c Δ' ps sig body) body ob →
      ob.ty.le c.ct c.bounds sig.ret →
      Typed c Γ (.callBlk r m args ps body) (.plain (ms.flatMap (·.ret))
        (c.reset Δ' (ps ++ body.assigned)))
  | callBlkDeadRecv : Typed c Γ r o → o.out = none → Typed c Γ (.callBlk r m args ps body) .dead
  | callBlkDeadArgs : Typed c Γ r o → o.out = some Δ → TypedArgs c Δ args .dead →
      Typed c Γ (.callBlk r m args ps body) .dead
  | yield : c.meth.block = some sig → TypedArgs c Γ args (.live tys Δ) →
      tys.length = sig.params.length → ((tys.zip sig.params).all fun (t, u) => t.le c.ct c.bounds u) = true →
      Typed c Γ (.yield args) (.plain sig.ret Δ)
  | yieldDead : c.meth.block = some sig → TypedArgs c Γ args .dead →
      Typed c Γ (.yield args) .dead
  | prim : TypedArgs c Γ args (.live tys Δ) → tys.length = params.length →
      ((tys.zip params).all fun (t, u) => t.le c.ct c.bounds u) = true →
      Typed c Γ (.prim f args params ret) (.plain ret Δ)
  | primDead : TypedArgs c Γ args .dead → Typed c Γ (.prim f args params ret) .dead
  | seq : Typed c Γ a oa → oa.out = some Δ → Typed c Δ b ob → Typed c Γ (.seq a b) ob
  | seqDead : Typed c Γ a oa → oa.out = none → Typed c Γ (.seq a b) .dead
  /-- `if`: each branch where the test says so (dead where it cannot be). -/
  | ite : Typed c Γ cnd oc → TypedBranch c oc.tt t ot → TypedBranch c oc.ff e oe →
      Typed c Γ (.ite cnd t e) ⟨ot.ty ++ oe.ty, ojoin ot.out oe.out, ojoin ot.tt oe.tt,
        ojoin ot.ff oe.ff⟩
  /-- `while`: the test and the body from `Γ0`, what the loop assigns
  un-narrowed; the body ends with at least `Γ0`. -/
  | whileNever : c.reset Γ (Expr.assigned (.while cnd b)) = Γ0 → Typed c Γ0 cnd oc →
      oc.tt = none → Typed c Γ (.while cnd b) ⟨[.nil], oc.ff, oc.ff, oc.ff⟩
  | while : c.reset Γ (Expr.assigned (.while cnd b)) = Γ0 → Typed c Γ0 cnd oc →
      oc.tt = some Δ → Typed c Δ b ob → (ob.out.all (·.implies c.ct Γ0)) = true →
      Typed c Γ (.while cnd b) ⟨[.nil], oc.ff, oc.ff, oc.ff⟩
  | ret : c.inBlock = false → Typed c Γ e o → o.ty.le c.ct c.bounds c.meth.ret →
      (!c.inInit || o.out.all (c.allSet ·)) = true → Typed c Γ (.ret e) .dead
  | raise : Typed c Γ e o → o.ty.le c.ct c.bounds [.cls c.prog.exn []] → Typed c Γ (.raise e) .dead
  /-- `rescue`: the handler from what held before the body, what the body
  assigns un-narrowed, the exception in `x`; `els` after the body. -/
  | rescue : (!c.inInit && !c.inDefault) = true → c.decl x = some [.cls c.prog.exn []] →
      Typed c Γ b ob → TypedBranch c ob.out els oe →
      Typed c ((c.reset Γ b.assigned).set (.local x) [.cls c.prog.exn []]) h oh →
      Typed c Γ (.rescue b x h els) ⟨oe.ty ++ oh.ty, ojoin oe.out oh.out, ojoin oe.tt oh.tt,
        ojoin oe.ff oh.ff⟩
  /-- `ensure`: from what held before the body, what it assigns
  un-narrowed; after it, what it assigns as at its end. -/
  | ensure : (!c.inInit && !c.inDefault) = true → Typed c Γ b ob →
      Typed c (c.reset Γ b.assigned) e oe → oe.out = some Δe →
      Typed c Γ (.ensure b e) ⟨ob.ty, ob.out.map (·.takeFrom Δe e.assigned),
        ob.out.map (·.takeFrom Δe e.assigned), ob.out.map (·.takeFrom Δe e.assigned)⟩
  | ensureDead : (!c.inInit && !c.inDefault) = true → Typed c Γ b ob →
      Typed c (c.reset Γ b.assigned) e oe → oe.out = none → Typed c Γ (.ensure b e) .dead
  /-- The tests (design §2.1), each of a value: of a path, they narrow
  it (`testOut`). -/
  | isNil : Typed c Γ e o → o.out = some Δ →
      Typed c Γ (.isNil e) (testOut c e Δ (nilTy c.ct) (·.remove .nil))
  /-- A class test: of a class whose arguments follow from the static
  type (the run-time test sees the class only). -/
  | isA : Typed c Γ e o → o.out = some Δ → (a.closed && a.wf c.ct && verifiable c.ct o.ty a) = true →
      Typed c Γ (.isA e a) (testOut c e Δ (isATrue c.ct · a) (isAFalse c.ct · a))
  | eqNil : Typed c Γ e o → o.out = some Δ →
      Typed c Γ (.eqNil e) (testOut c e Δ (fun t => if finalRead c Δ e then t.keep [.nil] else t)
        (fun t => if finalRead c Δ e then t.remove .nil else t))
  | neNil : Typed c Γ e o → o.out = some Δ →
      Typed c Γ (.neNil e) (testOut c e Δ (fun t => if finalRead c Δ e then t.remove .nil else t)
        (fun t => if finalRead c Δ e then t.keep [.nil] else t))
  | eqTrue : Typed c Γ e o → o.out = some Δ →
      Typed c Γ (.eqTrue e) (testOut c e Δ (fun t => if finalRead c Δ e then t.keep [.bool] else t) id)
  | eqFalse : Typed c Γ e o → o.out = some Δ →
      Typed c Γ (.eqFalse e) (testOut c e Δ (fun t => if finalRead c Δ e then t.keep [.bool] else t) id)
  | testDead : Typed c Γ e o → o.out = none →
      (t = .isNil e ∨ (∃ a, t = .isA e a) ∨ t = .eqNil e ∨ t = .neNil e ∨ t = .eqTrue e ∨
        t = .eqFalse e) → Typed c Γ t .dead
  | and : Typed c Γ a oa → TypedBranch c oa.tt b ob →
      Typed c Γ (.and a b) ⟨oa.ty ++ ob.ty, ojoin oa.ff ob.out, ob.tt, ojoin oa.ff ob.ff⟩
  | or : Typed c Γ a oa → TypedBranch c oa.ff b ob →
      Typed c Γ (.or a b) ⟨oa.ty ++ ob.ty, ojoin oa.tt ob.out, ojoin oa.tt ob.tt, ob.ff⟩
  | not : Typed c Γ a oa → Typed c Γ (.not a) ⟨[.bool], oa.out, oa.ff, oa.tt⟩

/-- Code reached only where `Γ` holds (`some`), or not at all (`none`:
dead, accepted unchecked). -/
inductive TypedBranch : Ctx → Option Env → Expr → Out → Prop where
  | live : Typed c Γ e o → TypedBranch c (some Γ) e o
  | dead : TypedBranch c none e .dead

inductive TypedArgs : Ctx → Env → List Expr → ArgsOut → Prop where
  | nil : TypedArgs c Γ [] (.live [] Γ)
  | cons : Typed c Γ e o → o.out = some Δ → TypedArgs c Δ es (.live tys Δ') →
      TypedArgs c Γ (e :: es) (.live (o.ty :: tys) Δ')
  | consDead : Typed c Γ e o → o.out = none → TypedArgs c Γ (e :: es) .dead
  | restDead : Typed c Γ e o → o.out = some Δ → TypedArgs c Δ es .dead →
      TypedArgs c Γ (e :: es) .dead

end

end QuarzCore
