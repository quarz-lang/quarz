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
  /-- A local read: assigned on every path, holding `u`, annotated with a
  type at least `u`; a test of it narrows it to `u`'s truthy or falsy
  atoms. -/
  | var : Γ.get (.local x) = some u → u.le c.ct t →
      Typed c Γ (.var x t) ⟨t, some Γ, narrow Γ (.local x) (truthyTy u),
        narrow Γ (.local x) (falsyTy c.ct u)⟩
  /-- A `var` field read: never narrowed. -/
  | fieldVar : c.field? f = some fd → fd.var = true → fd.ty.le c.ct t →
      Typed c Γ (.field f t) (.plain t Γ)
  /-- An immutable field read: narrowed as a local. -/
  | fieldImm : c.field? f = some fd → fd.var = false → (Γ.get (.field f)).getD fd.ty = u →
      u.le c.ct t →
      Typed c Γ (.field f t) ⟨t, some Γ, narrow Γ (.field f) (truthyTy u),
        narrow Γ (.field f) (falsyTy c.ct u)⟩
  | assign : Typed c Γ e o → c.decl x = some d → o.ty.le c.ct d → o.out = some Δ →
      Typed c Γ (.assign x e) (.plain o.ty (Δ.set (.local x) o.ty))
  | assignDead : Typed c Γ e o → c.decl x = some d → o.ty.le c.ct d → o.out = none →
      Typed c Γ (.assign x e) .dead
  | setField : c.field? f = some fd → fd.var = true → Typed c Γ e o → o.ty.le c.ct fd.ty →
      o.out = some Δ → Typed c Γ (.setField f e) (.plain o.ty Δ)
  | setFieldDead : c.field? f = some fd → fd.var = true → Typed c Γ e o →
      o.ty.le c.ct fd.ty → o.out = none → Typed c Γ (.setField f e) .dead
  | self : Typed c Γ .self (.plain [.cls c.meth.owner] Γ)
  /-- `new`: the arguments the class's fields, in order. -/
  | new : k < c.ct.length → TypedArgs c Γ args (.live tys Δ) →
      tys.length = (c.ct.allFields k).length →
      ((tys.zip (c.ct.allFields k)).all fun (t, f) => t.le c.ct f.ty) = true →
      Typed c Γ (.new k args) (.plain [.cls k] Δ)
  | newDead : k < c.ct.length → TypedArgs c Γ args .dead → Typed c Γ (.new k args) .dead
  /-- A call: each atom of the receiver's type a class that has the
  method, the arguments fitting each, no block expected; its type the
  union of their results. -/
  | call : Typed c Γ r o → o.out = some Δ → TypedArgs c Δ args (.live tys Δ') →
      c.prog.resolve o.ty m = some ms →
      (ms.all fun mt => mt.block.isNone && argsOk c tys mt) = true →
      Typed c Γ (.call r m args) (.plain (ms.flatMap (·.ret)) Δ')
  | callDeadRecv : Typed c Γ r o → o.out = none → Typed c Γ (.call r m args) .dead
  | callDeadArgs : Typed c Γ r o → o.out = some Δ → TypedArgs c Δ args .dead →
      Typed c Γ (.call r m args) .dead
  /-- A call with a block: the methods all take the same anonymous block;
  its body, checked from `blockEnv` (it runs 0 or more times, during the
  call), gives at most the block's result; after the call, what held
  before it or what held at the body's end (design §2.2). -/
  | callBlk : Typed c Γ r o → o.out = some Δ → TypedArgs c Δ args (.live tys Δ') →
      c.prog.resolve o.ty m = some ms → ms.head? = some m0 → m0.block = some sig →
      (ms.all fun mt' => mt'.block == some sig && argsOk c tys mt') = true →
      blockParamsOk c ps sig = true →
      Typed { c with inBlock := true } (blockEnv c Δ' ps sig body) body ob →
      ob.ty.le c.ct sig.ret →
      Typed c Γ (.callBlk r m args ps body) (.plain (ms.flatMap (·.ret))
        (match ob.out with
          | some Γb => Δ'.join Γb
          | none => Δ'))
  | callBlkDeadRecv : Typed c Γ r o → o.out = none → Typed c Γ (.callBlk r m args ps body) .dead
  | callBlkDeadArgs : Typed c Γ r o → o.out = some Δ → TypedArgs c Δ args .dead →
      Typed c Γ (.callBlk r m args ps body) .dead
  | yield : c.meth.block = some sig → TypedArgs c Γ args (.live tys Δ) →
      tys.length = sig.params.length → ((tys.zip sig.params).all fun (t, u) => t.le c.ct u) = true →
      Typed c Γ (.yield args) (.plain sig.ret Δ)
  | yieldDead : c.meth.block = some sig → TypedArgs c Γ args .dead →
      Typed c Γ (.yield args) .dead
  | prim : TypedArgs c Γ args (.live tys Δ) → tys.length = params.length →
      ((tys.zip params).all fun (t, u) => t.le c.ct u) = true →
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
  | ret : c.inBlock = false → Typed c Γ e o → o.ty.le c.ct c.meth.ret →
      Typed c Γ (.ret e) .dead
  | raise : Typed c Γ .raise .dead
  /-- The tests (design §2.1), each of a value: of a path, they narrow
  it (`testOut`). -/
  | isNil : Typed c Γ e o → o.out = some Δ →
      Typed c Γ (.isNil e) (testOut c e Δ (nilTy c.ct) (·.remove .nil))
  | isA : Typed c Γ e o → o.out = some Δ →
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
