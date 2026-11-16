/- B-T5F: baseline bench (Tip5Core only, no Tip5Fast import => compiled code uses the List versions). -/
import NockvmE2E.Exec.Tip5BenchLib
open NockvmE2E.Exec NockvmE2E.Exec.Tip5Bench
def main (args : List String) : IO UInt32 := do
  let n := (args.headD "300").toNat!
  let (ok, bad) := checkVectors Tip5Core.hashVarlen Tip5Core.hash10 Tip5Core.permute
  let m := Tip5Core.montify 1 == 4294967295 && Tip5Core.montify 122 == 523986009990 &&
    Tip5Core.montRed 45157629471412822477200 == 10514079938160
  IO.println s!"BASE vectors ok={ok} bad={bad} mont={m}"
  let ns ← timeIt Tip5Core.permute n
  IO.println s!"BASE permute: {ns} ns/call"
  let ns ← timeIt Tip5Core.hashVarlen n
  IO.println s!"BASE hashVarlen(16 limbs): {ns} ns/call"
  return (if bad == 0 && m then 0 else 1)
