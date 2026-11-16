/-
  Nock/RedTeam/Batch1934Thm54TowerHonestAccepted.lean

  **`honest_accepted` at the tower CF chip.**

  * `binds_T`: the honest columns `11 / 12` are the first / last-row masks.
  * `honest_accepted_T`: the tower CF chip `chipCFT` (via `if_pos` at `goodCFT_honest`) accepts the honest trace.
-/
import Nock.NockVMROM.Thm54.VclL.Compute.TowerHonestAccept
import Nock.NockVMROM.Thm54.TraceGen.GenFormRAxisLambda
import Nock.NockVMROM.Thm54.TraceGen.GenGoodSeedExists
import Nock.NockVMROM.Thm54.VclL.Compute.CompSoundnessVCL

namespace Nock.RedTeam.Batch1934
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD

#print axioms walkT_len
#print axioms walkT_pubAt
#print axioms gRow_axis
#print axioms rowHolds_T
#print axioms binds_T
#print axioms honest_accepted_T

end Nock.RedTeam.Batch1934
