/-
  Nock/RedTeam/Batch1350Thm54GeneratedFieldScan.lean

  Lane.  Notes only; no new theorem about the package.

  * **(A) The `generated` field ties nothing to the claim's result.**  The type of
    `OptimizedFullStrictNockVMROMPackage.generated` mentions `P8PublicClaim.subject` and
    `P8PublicClaim.formula` (the program) and does NOT mention `P8PublicClaim.result`: the
    generator's result `R` and the evaluator's result `r` are existentially FREE.
  * **(B) `primeField` mentions neither the claim nor any trace.**
  * **(C) The named forms are the fields.**  `GeneratedField.ClaimGenerated K claim Λ` and
    `GeneratedField.PrimeFieldElems F` unfold to the two field types (`Iff.rfl`).
-/
import Lean
import Nock.NockVMROM.Thm54.GeneratedField
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false

namespace Nock.RedTeam.Batch1350

open Lean Elab Command Meta
open Nock.NockVMROM.Thm54

def PKG : Name := `Nock.Walk37.Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage

/-- The scan: which of the claim's three projections the field type mentions. -/
def scan (env : Environment) (n : Name) : CommandElabM (Bool × Bool × Bool) := do
  let some ci := env.find? n | throwError m!"missing {n}"
  let cs := ci.type.getUsedConstants
  return (cs.contains ``P8PublicClaim.subject, cs.contains ``P8PublicClaim.formula,
    cs.contains ``P8PublicClaim.result)

run_cmd do
  let env ← getEnv
  let (s, f, r) ← scan env (PKG ++ `generated)
  logInfo m!"generated: mentions subject = {s}, formula = {f}, result = {r}"
  unless s ∧ f do throwError "instrument: generated does not mention the program (positive control)"
  if r then throwError "STOP: generated mentions P8PublicClaim.result"
  let (s', f', r') ← scan env (PKG ++ `primeField)
  logInfo m!"primeField: mentions subject = {s'}, formula = {f'}, result = {r'}"
  if s' ∨ f' ∨ r' then throwError "primeField mentions the claim"
  -- positive control on the `result` probe: the target's `p8` field reads it
  let (_, _, rp) ← scan env (`Nock.Walk37.Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage.OptimizedProductionGenuineTargetAt.p8)
  unless rp do throwError "positive control: the target's p8 does not mention P8PublicClaim.result"
  logInfo "Batch1350 (A)/(B): generated and primeField leave the claim's result free; positive control: p8 reads it"

section Forms

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]
  [CharP K (ringChar K)] [FiniteDimensional F K] {hOrb : ℕ}

/-- (C) `ClaimGenerated` at the package's claim and window is the `generated` field's type. -/
theorem generated_iff (P : OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage F K hOrb) :
    GeneratedField.ClaimGenerated K P.optimized.verifier.raw.claim P.optimized.Λ ↔
      ∃ (gfuel : ℕ) (G : Nock.Walk.NTree (TraceGen.GenComputeRow K)) (R : Noun) (fuel : ℕ)
        (r : Noun),
        TraceGen.genComputeSkeleton (K := K) gfuel P.optimized.verifier.raw.claim.subject
            P.optimized.verifier.raw.claim.formula = .ok (G, R) ∧
          FieldEmbedding.evalGBy (ringChar K) fuel P.optimized.verifier.raw.claim.subject
            P.optimized.verifier.raw.claim.formula = some r ∧
          TraceGen.programLeafBound (TraceGen.airReorder G) ≤ P.optimized.Λ :=
  Iff.rfl

/-- (C) every package carries it. -/
theorem generated_holds (P : OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage F K hOrb) :
    GeneratedField.ClaimGenerated K P.optimized.verifier.raw.claim P.optimized.Λ :=
  P.generated

/-- (C) `PrimeFieldElems F` is the `primeField` field's type. -/
theorem primeField_holds (P : OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage F K hOrb) :
    GeneratedField.PrimeFieldElems F :=
  P.primeField

end Forms

end Nock.RedTeam.Batch1350

#print axioms Nock.RedTeam.Batch1350.generated_iff
#print axioms Nock.RedTeam.Batch1350.generated_holds
#print axioms Nock.RedTeam.Batch1350.primeField_holds
