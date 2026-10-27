import QuarzCore.Fuzz

open QuarzCore QuarzCore.Fuzz Plausible

/-- `fuzz [N]`: N random programs (default 20000); fails on the first
checked one that gets stuck. -/
def main (args : List String) : IO UInt32 := do
  let n := (args.head? >>= String.toNat?).getD 20000
  let mut checked := 0
  let mut ended := 0
  for i in [0:n] do
    let body ← Gen.run (genExpr 5) (i % 30 + 5)
    let P := program body
    if P.check then
      checked := checked + 1
      match run P oracle 500 with
      | .stuck =>
        IO.eprintln s!"stuck: {repr body}"
        return 1
      | .ok .. | .raised .. | .returned .. => ended := ended + 1
      | .timeout => pure ()
  IO.println s!"{n} programs, {checked} checked, {ended} of them ended; none stuck"
  return 0
