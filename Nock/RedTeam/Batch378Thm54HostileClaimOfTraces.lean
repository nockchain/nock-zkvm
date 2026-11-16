/-
  Nock/RedTeam/Batch378Thm54HostileClaimOfTraces.lean

  **Semantic conclusion type at the built
  strategy.**  `hostile_claim_holds_of_deployed` is **not** inhabited:
  19 of 21 `AcceptedContent` conjuncts are open  and
  `TracesBindsHyps` is carried.
-/
import Nock.NockVMROM.Thm54.StrategyOfTracesCore
import Nock.RedTeam.Batch369Thm54HostileClaimOfDeployed
import Nock.RedTeam.Batch377Thm54AcceptedContentOfTraces

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch378

open Nock.NockVMROM.Thm54.StrategyOfTracesCore
open Nock.RedTeam.Batch369
open Nock.RedTeam.Batch377

/-- Uninhabited until the 19 open conjuncts and the join close. -/
abbrev HostileClaimHoldsOfDeployed :=
  @Nock.RedTeam.Batch369.HostileClaimHoldsOfDeployed

def spine := @Nock.NockVMROM.Thm54.ProductionP8Containment.accepted_outside_failureUnion_content

#check strategyOfTraces
#check HostileClaimHoldsOfDeployed

end Nock.RedTeam.Batch378

#print axioms Nock.RedTeam.Batch378.spine
