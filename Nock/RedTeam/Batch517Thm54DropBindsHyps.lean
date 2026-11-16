/-
  Nock/RedTeam/Batch517Thm54DropBindsHyps.lean

  **Drop `TracesBindsHyps`.**

  `strategyOfTraces` still takes `TracesBindsHyps`.  K-level
  `recordHalfJoin_of_deployed` and `decode_fingerprint_of_topology`
  landed; `RemainingBindMemRec` / `ComputeJoinSoundRemaining` still
  block `BindsAt`.  Not restated at `SemanticSupportAt.ofBare`.
  Ledger `openConjunctsAfterWrap` stays length 5.
-/
import Nock.NockVMROM.Thm54.StrategyOfTracesCore
import Nock.RedTeam.Batch465Thm54DeployedRootLabelEqClaim
import Nock.RedTeam.Batch509Thm54WrapSpecialize
import Nock.RedTeam.Batch516Thm54ComputeJoinSound

set_option autoImplicit false

namespace Nock.RedTeam.Batch517

open Nock.RedTeam.Batch465
open Nock.RedTeam.Batch509

theorem bindsDropBlockersAfter_still_three :
    bindsDropBlockersAfter.length = 3 := by
  decide

theorem tracesBindsHyps_not_dropped :
    "strategyOfTraces takes TracesBindsHyps" ∈ CHIP_SFE_REMAINING_BEFORE_H15B := by
  decide

theorem openConjunctsAfterWrap_still_five :
    openConjunctsAfterWrap.length = 5 :=
  openConjunctsAfterWrap_length

theorem openConjunctsAfterVer_not_empty :
    Nock.RedTeam.Batch448.openConjunctsAfterVer ≠ [] := by
  decide

end Nock.RedTeam.Batch517

#print axioms Nock.RedTeam.Batch517.bindsDropBlockersAfter_still_three
#print axioms Nock.RedTeam.Batch517.tracesBindsHyps_not_dropped
#print axioms Nock.RedTeam.Batch517.openConjunctsAfterWrap_still_five
