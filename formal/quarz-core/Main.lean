import QuarzCore
import QuarzCore.Conformance

open QuarzCore

/-- `quarz check --tree FILE | lake exe conformance [--dump]`: whether the model
accepts the program the Rust checker accepted (exit 1 if not), or why it
is outside the model's range (exit 0, "out of range"). -/
def main (args : List String) : IO UInt32 := do
  let input ← (← IO.getStdin).readToEnd
  let j ← match Lean.Json.parse input with
    | .ok j => pure j
    | .error e => IO.eprintln s!"conformance: not JSON: {e}"; return 2
  match Conformance.program j with
  | .error why =>
    if why.startsWith "disagree" then
      IO.println s!"disagrees: {why}"
      return 1
    IO.println s!"out of range: {why}"
    return 0
  | .ok P =>
    if P.check then
      IO.println "agrees"
      return 0
    else
      -- Which method the model rejects.
      let bad := (P.main :: P.methods).filter fun mt => !(P.wfMethod mt && P.checkMethod mt)
      IO.println s!"disagrees: {bad.map fun mt => mt.name}"
      if args.contains "--dump" then
        for mt in bad do IO.println (repr mt)
      return 1
