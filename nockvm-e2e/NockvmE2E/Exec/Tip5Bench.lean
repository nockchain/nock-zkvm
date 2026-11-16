/- B-T5F: fast bench (imports Tip5Fast => csimp rewrites Tip5Core.* references in this module). -/
import NockvmE2E.Exec.Tip5BenchLib
import NockvmE2E.Exec.Tip5Fast
open NockvmE2E.Exec NockvmE2E.Exec.Tip5Bench
def main (args : List String) : IO UInt32 := do
  let n := (args.headD "300").toNat!
  let (ok, bad) := checkVectors Tip5Core.hashVarlen Tip5Core.hash10 Tip5Core.permute
  let m := Tip5Core.montify 1 == 4294967295 && Tip5Core.montify 122 == 523986009990 &&
    Tip5Core.montRed 45157629471412822477200 == 10514079938160
  -- cross-check against the un-rewritten slow originals (Lib was compiled before the csimp existed)
  let mut diff := 0
  for k in [0:20] do
    let inp := (List.range (k + 3)).map fun j => (k * 977 + j * 1234567891) % Tip5Core.P
    if Tip5Core.hashVarlen inp != Tip5Bench.slowHash inp then diff := diff + 1
  IO.println s!"FAST cross-check vs slow: {diff} differences of 20"
  IO.println s!"FAST vectors ok={ok} bad={bad} mont={m}"
  let ns ← timeIt Tip5Core.permute n
  IO.println s!"FAST permute: {ns} ns/call"
  let ns ← timeIt Tip5Core.hashVarlen n
  IO.println s!"FAST hashVarlen(16 limbs): {ns} ns/call"
  return (if bad == 0 && m && diff == 0 then 0 else 1)
