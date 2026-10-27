/-
The soundness theorem (design §4): a checked program, run with any fuel
and any oracle giving values of the types asked for, never gets stuck:
in particular, every read's value is of the type the checker narrowed it
to. By induction on the fuel, over the interpreter's five functions.
-/

import QuarzCore.ExtLemmas

set_option linter.deprecated false

namespace QuarzCore

variable (P : Program) (orc : Oracle)

/-- Values of the types, in order. -/
def AllTy (s : Store) : List Value → List Ty → Prop
  | [], [] => True
  | v :: vs, t :: ts => s.hasTy P v t ∧ AllTy s vs ts
  | _, _ => False

/-- What the arguments' evaluation gives. -/
def ArgsPost (c : Ctx) (ao : ArgsOut) (fr : Frame) (Λ : List Ty) (s : Store) (W : Nat → Prop) :
    ArgsResult → Prop
  | .ok vs s' => ∃ tys Δ, ao = .live tys Δ ∧ ∃ Λ', WfStore P Λ' s' ∧ Ext P W Λ Λ' s s' ∧
      FrameOK P c Λ' fr s' ∧ Sat P c Δ fr s' ∧ AllTy P s' vs tys
  | .other .stuck => False
  | .other (.ok _ _) => False
  | .other (.returned v s') => ∃ Λ', WfStore P Λ' s' ∧ Ext P W Λ Λ' s s' ∧ FrameOK P c Λ' fr s' ∧
      s'.hasTy P v c.meth.ret ∧ c.inBlock = false
  | .other _ => True

/-- The writes of evaluating `es` in `fr`. -/
def evalWs (fr : Frame) (es : List Expr) (l : Nat) : Prop :=
  (∃ e ∈ es, frameW fr.vars e.assigned l) ∨ blkW fr.blk l

def EvalGood (n : Nat) : Prop :=
  ∀ (c : Ctx) (Γ : Env) (e : Expr) (o : Out) (fr : Frame) (s : Store) (Λ : List Ty),
    c.prog = P → Typed c Γ e o → WfStore P Λ s → FrameOK P c Λ fr s → Sat P c Γ fr s →
    Post P c o fr Λ s (evalW fr e) (eval P orc n fr s e)

def ArgsGood (n : Nat) : Prop :=
  ∀ (c : Ctx) (Γ : Env) (es : List Expr) (ao : ArgsOut) (fr : Frame) (s : Store) (Λ : List Ty),
    c.prog = P → TypedArgs c Γ es ao → WfStore P Λ s → FrameOK P c Λ fr s → Sat P c Γ fr s →
    ArgsPost P c ao fr Λ s (evalWs fr es) (evalArgs P orc n fr s es)

/-- A block given to a method that takes `b`, as it may be. -/
def BlkGiven (Λ : List Ty) (s : Store) : Option BlockSig → Option Closure → Prop
  | none, none => True
  | some sig, some clo => ClosureOK P Λ s clo sig ∧ ∀ l, chainLocs (some clo) l → l < s.locs.length
  | _, _ => False

/-- What a call gives: never stuck; a value of the method's result type,
the store grown as the block's writes allow, the block as it was. -/
def SendPost (ret : Ty) (sig : Option BlockSig) (blk : Option Closure) (Λ : List Ty) (s : Store) :
    Result → Prop
  | .ok v s' => ∃ Λ', WfStore P Λ' s' ∧ Ext P (blkW blk) Λ Λ' s s' ∧ s'.hasTy P v ret ∧
      BlkGiven P Λ' s' sig blk
  | .stuck | .returned _ _ => False
  | _ => True

def SendGood (n : Nat) : Prop :=
  ∀ (s : Store) (Λ : List Ty) (recv : Value) (k : Nat) (m : String) (mt : Method)
    (vs : List Value) (blk : Option Closure),
    WfStore P Λ s → s.hasTy P recv [.cls k] → k ≠ 0 → P.lookup k m = some mt →
    AllTy P s vs (mt.params.map (·.2)) →
    BlkGiven P Λ s mt.block blk →
    SendPost P mt.ret mt.block blk Λ s (send P orc n s recv m vs blk)

def BlockGood (n : Nat) : Prop :=
  ∀ (s : Store) (Λ : List Ty) (clo : Closure) (sig : BlockSig) (vs : List Value),
    WfStore P Λ s → BlkGiven P Λ s (some sig) (some clo) →
    AllTy P s vs sig.params →
    SendPost P sig.ret (some sig) (some clo) Λ s (runBlock P orc n s clo vs)

/-- `v == w` (`w` nil, true or false): never stuck, a boolean or what a
user `==` gives (a boolean, `wfMethod`), no local written. -/
def EqualGood (n : Nat) : Prop :=
  ∀ (s : Store) (Λ : List Ty) (v w : Value) (t : Ty),
    WfStore P Λ s → s.hasTy P v t → (w = .nil ∨ w = .bool true ∨ w = .bool false) →
    SendPost P [.bool] none none Λ s (equal P orc n s v w)

structure Good (n : Nat) : Prop where
  eval : EvalGood P orc n
  args : ArgsGood P orc n
  send : SendGood P orc n
  block : BlockGood P orc n
  equal : EqualGood P orc n

/-- With no fuel, everything times out (but an empty argument list). -/
theorem good_zero : Good P orc 0 where
  eval := fun _ _ _ _ _ _ _ _ _ _ _ _ => by simp [eval, Post]
  args := fun c Γ es ao fr s Λ _ ht hw hf hs => by
    cases es with
    | nil =>
      cases ht
      exact ⟨[], Γ, rfl, Λ, hw, Ext.refl _ Λ s, hf, hs, trivial⟩
    | cons e es => simp [evalArgs, ArgsPost]
  send := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ => by simp [send, SendPost]
  block := fun _ _ _ _ _ _ _ _ => by simp [runBlock, SendPost]
  equal := fun _ _ _ _ _ _ _ _ => by simp [equal, SendPost]

theorem good (hP : WfProg P) (horc : OracleOK P orc) : ∀ n, Good P orc n := by
  intro n
  induction n with
  | zero => exact good_zero P orc
  | succ n ih => exact ⟨sorry, sorry, sorry, sorry, sorry⟩

end QuarzCore
