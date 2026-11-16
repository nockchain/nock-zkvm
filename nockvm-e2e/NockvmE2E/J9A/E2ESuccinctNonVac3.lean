/-
the instance-side part of `verdict9V` at the loaded instance `toy9R`, by kernel
evaluation, split per conjunct so no single `decide` carries `shapeOkF`/`setupGates` whole:
`famGatesFail famJ9A toy9R = none` needs `shapeOkF` (here split per conjunct, `shapeOkF_toy_split`), `shapeXOkF`, `chipsOkF`, `maskOkF`, `numeralOkF`;
then `toy9R.l = 170`, `claimOf toy9R.pubIn = some cToy`, `linkGate9 toy9R cToy`.  NOT covered: `setupGates` (OOM) and
`verifyOnlineE'` (runs on a proof, [executed] by the exe).
-/
import NockvmE2E.J9A.RunGate9

set_option autoImplicit false
set_option maxRecDepth 100000
set_option pp.deepTerms false
set_option pp.maxSteps 2000

namespace NockvmE2E.J9A.E2ESuccinctNonVac3
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.ShapeF NockvmE2E.J9A.LagrJ9A
open NockvmE2E.Exec.E2EMain (XI170)
open NockvmE2E.Exec.Toy9R
open NockvmE2E.Exec.J9AChips NockvmE2E.J9A.E2EJ9AToyR
open NockvmE2E.J9A.RunGate9 (claimOf)

theorem gate_toyV_l : toy9R.l = 170 := rfl

theorem gate_toyV_shapeX : shapeXOkF famJ9A (XI170 toy9R) = true := by decide +kernel

theorem gate_toyV_chips : chipsOkF famJ9A (XI170 toy9R) = true := by decide +kernel

theorem gate_toyV_mask : maskOkF famJ9A (XI170 toy9R) = true := by decide +kernel

theorem gate_toyV_numeral : numeralOkF famJ9A (XI170 toy9R) = true := by decide +kernel

theorem gate_toyV_claim : claimOf toy9R.pubIn = some cToy := NockvmE2E.J9A.RunGate9.claimOf_toy

theorem gate_toyV_link : NockvmE2E.J9A.RunGate9.linkGate9 (XI170 toy9R) cToy = true := NockvmE2E.J9A.RunGate9.gate_toy

/-- the whole instance side except `shapeOkF` and `setupGates` -/
theorem gate_toyV_rest :
    shapeXOkF famJ9A (XI170 toy9R) = true ∧ chipsOkF famJ9A (XI170 toy9R) = true ∧ maskOkF famJ9A (XI170 toy9R) = true ∧
    numeralOkF famJ9A (XI170 toy9R) = true ∧ toy9R.l = 170 ∧ claimOf toy9R.pubIn = some cToy ∧
    NockvmE2E.J9A.RunGate9.linkGate9 (XI170 toy9R) cToy = true :=
  ⟨gate_toyV_shapeX, gate_toyV_chips, gate_toyV_mask, gate_toyV_numeral, gate_toyV_l, gate_toyV_claim, gate_toyV_link⟩

end NockvmE2E.J9A.E2ESuccinctNonVac3

#print axioms NockvmE2E.J9A.E2ESuccinctNonVac3.gate_toyV_rest
