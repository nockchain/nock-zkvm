/-
  Nock/RedTeam/Batch1750Thm54VclLWalkSat.lean

  **1751: the whole-trace compute walk at VCL semantics
  (`W0`/`W1`).**
  * labels / line / coins at the gathered pull-back `SB` (one-hot from `VclSourceObligations.base15`);
    `count := SR.trace 303 = W0`, `acc := SR.trace 306 = W1`; `SR ↔ SB` for walk-free reads
    (`SR_eq_SB`, `eval_toSourceEnv309_of_noWalkVars`);
  * row 0 from `endpoint2_309` / `endpoint4_309` (`walkLn_row0`, `walkCount_row0`,
    `walkAccInit_row0`), last row `walkOut_last`; steps from `conditional_transition_soundness_vcl`
    (`walkLn_step`, `walkCount_step`, `walkAcc_step`);
  * **`vcl_walkSat`** (`WalkSat`, α = `alphaC`, seed = `seedOfClaim`, initial count `alphaC`, `D.N`
    rows), `vcl_walk_out`, **`vcl_bfsValid`**, **`vcl_tiling`** (outside `computeTilingEvent`);
  * `zZinv_at` / `vcomp_at`: the `z·z⁻¹` pin is a theorem at the layout (`nprSeed c.1 ≠ 0`), so
    every row is `V_comp` from `RowFactsP` alone.
-/
import Nock.NockVMROM.Thm54.VclL.Compute.WalkSatVCL
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.P8Core.SVCompute.QueueTwins
import Nock.NockVMROM.Thm54.Unhosted309Events

set_option autoImplicit false

namespace Nock.RedTeam.Batch1750

open Nock.NockVMROM.Thm54.VclL.Compute.WalkVCL

#print axioms SB_chal
#print axioms zZinv_at
#print axioms shift_trace
#print axioms shift_walk
#print axioms nextLabel_eval
#print axioms nextCC_eval
#print axioms nextCM_eval
#print axioms walkLn_row0
#print axioms walkCount_row0
#print axioms walkAccInit_row0
#print axioms walkOut_last
#print axioms walkLn_step
#print axioms walkCount_step
#print axioms walkAcc_step
#print axioms vcl_walkSat
#print axioms vcl_walk_out
#print axioms count_ne_ln
#print axioms count_eq_ln_last
#print axioms vcl_bfsValid
#print axioms vcl_tiling
#print axioms vcomp_at

end Nock.RedTeam.Batch1750
