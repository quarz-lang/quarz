import QuarzCore.Fuzz

open QuarzCore QuarzCore.Fuzz Plausible

/-- `fuzz [N]`: N random programs (default 20000); fails on the first
checked one that gets stuck. -/
def main (args : List String) : IO UInt32 := do
  let n := (args.head? >>= String.toNat?).getD 20000
  let mut checked := 0
  let mut inits := 0
  let mut boxes := 0
  let mut variance := 0
  let mut ended := 0
  for i in [0:n] do
    let body ← Gen.run (genExpr 5) (i % 30 + 5)
    -- One program in four with a generated `D#initialize`, one in four
    -- opening with uses of the boxes, one in four a variance scenario.
    let P ← match i % 4 with
      | 1 => do pure (program (.seq (.new 4 [] [.int 3]) body) (← Gen.run (genInit 3) (i % 20 + 3)))
      | 2 => do pure (program (.seq (.assign "x" .nil)
          (.seq (← Gen.run (genBox 4) (i % 25 + 4)) (.seq (.var "x" [.int, .nil]) body))))
      | 3 => do pure (program (.seq (.assign "x" .nil) (← Gen.run (genVarSeq (i % 7 + 3)) 1)))
      | _ => pure (program body)
    if P.check then
      checked := checked + 1
      if i % 4 == 1 then inits := inits + 1
      if i % 4 == 2 then boxes := boxes + 1
      if i % 4 == 3 then variance := variance + 1
      match run P oracle 500 with
      | .stuck =>
        IO.eprintln s!"stuck: {repr P.main.body}\n{repr ((P.methods.find? (·.owner == 4)).map (·.body))}"
        return 1
      | .ok .. | .raised .. | .returned .. => ended := ended + 1
      | .timeout => pure ()
  IO.println s!"{n} programs, {checked} checked ({inits} with a generated initialize, {boxes} with the boxes, {variance} variance scenarios), {ended} of them ended; none stuck"
  return 0
