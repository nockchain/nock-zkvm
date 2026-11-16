/-
the side-proof (πF) production as ONE shared function, used by the prover (`nockvm-e2e-prove --family j9a` writes `<prog>.fix.json`) and by
`verify-fam fix-prove` (a thin wrapper).  Mathlib-free (imports VKp, Tip5Core, Tip5Fast).  The Tip5 oracles are verbatim copies of `VerifyFamMain`'s.
NOT zero-knowledge.
-/
import NockvmE2E.Exec.VKp
import NockvmE2E.Exec.Tip5Core
import NockvmE2E.Exec.Tip5Fast
set_option autoImplicit false

namespace NockvmE2E.Exec.FixProve
open NockvmE2E.Exec NockvmE2E.Exec.V

def tip5H : HFn := Tip5Core.hashVarlen
def tip5FS : FSFn := fun key nl =>
  match key with
  | [] => []
  | z :: ms =>
    Tip5Core.squeeze (ms.foldl (fun s m => Tip5Core.absorb s Tip5Core.tMsg m)
      (Tip5Core.absorb (Tip5Core.hashVarlen [Tip5Core.tIni]) Tip5Core.tIn z)) nl
def tip5FSfix : FSFn := fun key nl =>
  match key with
  | [] => []
  | z :: ms =>
    Tip5Core.squeeze (ms.foldl (fun s m => Tip5Core.absorb s Tip5Core.tMsg m)
      (Tip5Core.absorb (Tip5Core.hashVarlen [Tip5Core.tIni + 0x100]) Tip5Core.tIn z)) nl
def hFixT : HFn := hFix tip5H

/-- `ζ` of the main proof -/
def mainZeta (z : List Nat) (π : FlatProof) : VF.K3 :=
  VF.K3.ofLimbs (tip5FS (z :: [[], π.roots[0]!, π.roots[1]!, π.roots[2]!, π.roots[3]!]) 3)

/-- the side proof πF of the main proof `(z, π)` over the fixed columns of the full instance `X` (`none` if the setup gates fail) -/
def proveFixFor (X : ExecInst) (z : List Nat) (π : FlatProof) : Option FixProof :=
  (setupData' X hFixT).map fun D =>
    let zeta := mainZeta z π
    proveFix tip5H tip5FSfix D z (fixCtx π zeta) zeta

end NockvmE2E.Exec.FixProve
