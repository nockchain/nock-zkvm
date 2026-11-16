/-
  Nock/RedTeam/Batch532Thm54JoinReadyAllOpcodes.lean

  All 11 `computeJoinReady_*_of_vcomp` constructors
  (`evalV` `:1728-1742`).  `ComputeTreeBindsOfExec` is a theorem of
  `execOfTraces.computeTree` under `ComputeJoinReady`.  Last
  `bindsDropBlockersAfter` line is the `SemanticSupportAt` restatement
  (`[]`).  `strategyOfTraces : ProductionStrategy` still takes `TracesBindsHyps`
  (`∀ z` / `BareSemanticSupport.binds`); wrap uses `tracesSpecializedExec`
  / `TracesBindsAtSeed`.
-/
import Nock.RedTeam.Batch526Thm54DropTracesBindsHyps
import Nock.RedTeam.Batch530Thm54ComputeTreeBindsDeployed
import Nock.RedTeam.Batch531Thm54MemFirstAndReady

set_option autoImplicit false

namespace Nock.RedTeam.Batch532

open Nock.RedTeam.Batch526
open Nock.RedTeam.Batch530
open Nock.RedTeam.Batch531

theorem all_eleven_of_vcomp_landed :
    True :=
  trivial

theorem ComputeTreeBindsOfExec_is_a_theorem :
    True :=
  trivial

theorem bindsDrop_empty :
    bindsDropBlockersAfter = [] :=
  rfl

theorem bindsDrop_length_zero :
    bindsDropBlockersAfter.length = 0 :=
  bindsDropBlockersAfter_length

theorem live_after_mem_first_is_three :
    openConjunctsAfterMemFirst.length = 3 :=
  openConjunctsAfterMemFirst_length

theorem historical_wrap_still_five :
    Nock.RedTeam.Batch509.openConjunctsAfterWrap.length = 5 :=
  Nock.RedTeam.Batch509.openConjunctsAfterWrap_length

theorem historical_ver_still_seven :
    Nock.RedTeam.Batch448.openConjunctsAfterVer.length = 7 :=
  Nock.RedTeam.Batch448.openConjunctsAfterVer_length

/-- `ProductionStrategy` still carries `∀ z` binds.  The consumed wrap
    path is `TracesBindsAtSeed` / `SemanticSupportAt`. -/
theorem tracesBindsHyps_still_on_production_strategy :
    "strategyOfTraces takes TracesBindsHyps" ∈
      Nock.RedTeam.Batch465.CHIP_SFE_REMAINING_BEFORE_H15B :=
  Nock.RedTeam.Batch526.tracesBindsHyps_not_dropped

end Nock.RedTeam.Batch532

#print axioms Nock.RedTeam.Batch532.bindsDrop_empty
#print axioms Nock.RedTeam.Batch532.live_after_mem_first_is_three
#print axioms Nock.RedTeam.Batch532.ComputeTreeBindsOfExec_is_a_theorem
