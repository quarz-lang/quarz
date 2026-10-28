import QuarzCore.Fuzz

open QuarzCore QuarzCore.Fuzz Plausible

/-- `fuzz [N]`: N random programs (default 20000); fails on the first
checked one that gets stuck. -/
def main (args : List String) : IO UInt32 := do
  let n := (args.head? >>= String.toNat?).getD 20000
  let mut checked := 0
  let mut inits := 0
  let mut ended := 0
  for i in [0:n] do
    let body ← Gen.run (genExpr 5) (i % 30 + 5)
    -- Every other program with a generated `D#initialize`.
    let P ← if i % 2 == 0 then pure (program body) else
      do pure (program (.seq (.new 4 [.int 3]) body) (← Gen.run (genInit 3) (i % 20 + 3)))
    if P.check then
      checked := checked + 1
      if i % 2 == 1 then inits := inits + 1
      match run P oracle 500 with
      | .stuck =>
        IO.eprintln s!"stuck: {repr body}\n{repr ((P.methods.find? (·.owner == 4)).map (·.body))}"
        return 1
      | .ok .. | .raised .. | .returned .. => ended := ended + 1
      | .timeout => pure ()
  IO.println s!"{n} programs, {checked} checked ({inits} with a generated initialize), {ended} of them ended; none stuck"
  return 0
