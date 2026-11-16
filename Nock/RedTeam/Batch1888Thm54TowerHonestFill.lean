/-
  Nock/RedTeam/Batch1888Thm54TowerHonestFill.lean

  **The honest fill interface of the tower compute chip, and the
  first C2 gate family.**

  * C1 interface (`TowerHonestFill.lean`): `TowerRowVals` (pure data), `srcColT`, `vclColT`, `honestQT`;
    placement `pull_honestQT_trace` (the pull-back of the honest row env reads `srcColT` on every source
    column the kept gates read), `towerEnv309_ext_of_src` / `towerEnv309_base_of_src` (the tower typed env
    reads back the row's `𝕂′` values whenever the role has an Im column or a zero Im half),
    `honestQT_congr` (per-column stagedness).
  * C2c, first family: `honest_vestige_aux2` (aux `2`, `correctedAccAfterStep`, holds in `𝕂′` at the
    honest fill with sampled-denominator roles `33..35` zero) and `accAfterChain_eval_zero` (core `81`).
  * Negative control `accStep_nonzero_control`: with roles `33..35` = 1 (other reads 0) the aux-2 body is
    `-1 ≠ 0`, so the zero-denominator fill is load-bearing (the vestige gate is not vacuously true).
  * Positive control `imOwner_controls`: the Im inverse names role 0 at column 327, role 56 at 477 and walk
    `W1` (code 63) at 486, matching `towerM`.
  UNCONFIRMED (not compiled here): the generator → `TowerRowVals` map, C2a/C2b/C2d, C3, honest_staged.
-/
import Nock.NockVMROM.Thm54.VclL.Compute.TowerHonestFill
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.P8Core.SVCompute.QueueTwins
import Nock.NockVMROM.Thm54.Unhosted309Events

set_option autoImplicit false

namespace Nock.RedTeam.Batch1888

open Nock Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD

/-- The aux-2 body over `ℚ` with denominators `1` and every other read `0`. -/
def ctlEnv : CorrectedFinalTypedEnv ℚ ℚ where
  baseTrace := fun _ => 0
  baseTraceNext := fun _ => 0
  extTrace := fun r => if r.val = 33 ∨ r.val = 34 ∨ r.val = 35 then 1 else 0
  extTraceNext := fun _ => 0
  chal := fun _ => 0
  extensionPublic := fun _ => 0
  scalarPublic := fun _ => 0
  certBase := fun _ => 0
  certExt := fun _ => 0
  expCol := 0

/-- **Negative control**: nonzero denominators break aux `2` (value `-1`). -/
theorem accStep_nonzero_control : correctedAccAfterStep.eval ctlEnv = -1 := by
  rw [correctedAccAfterStep_eq]
  simp [accStepTerm, CorrectedFinalTypedExpr.eval, ctlEnv]

/-- **Positive control** on the Im inverse. -/
theorem imOwner_controls :
    towerM.ext 0 = some 327 ∧ imOwner 0 = some 0 ∧ towerM.ext 56 = some 477 ∧ imOwner 50 = some 56 ∧
      towerM.walk 1 = some 486 ∧ imOwner 53 = some 63 := by
  decide +kernel

end Nock.RedTeam.Batch1888

#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.towerM_ext_owner
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.srcColT_im
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.pull_honestQT_trace
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.honestQT_congr
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.towerEnv309_ext_of_src
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.towerEnv309_base_of_src
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.correctedAccAfterStep_eq
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.accAfterStep_eval_zero
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.accAfterChain_eval_zero
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.honest_vestige_aux2
#print axioms Nock.RedTeam.Batch1888.accStep_nonzero_control
#print axioms Nock.RedTeam.Batch1888.imOwner_controls
