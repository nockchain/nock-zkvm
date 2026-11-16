/-
  Nock/RedTeam/Batch506Thm54AxisStructureRecord.lean

  Record.

  * `MemoryExactTopology (execOfTraces …)` from
    `DeployedAcceptanceAt` + `c ∉ optimizedFailureEvent` + remaining
    `hα` (`walkForestPrefixAlphaEvent`, paper `:1008`, not in the
    consumed union).
  * `ComputeExactTopology (execOfTraces …)` from chips +
    priced `hγ` (no extra hyp).
  * `AcceptedContent` topologies are on `specializedExec`;
    wrap-specialize `RVTWithArity` is the remaining join.  Ledger **7**.
  * Seed public: `memoryPublicOfTuple` slots 9..11 = `pkgPub`
    (receipt).  `walkSeed` pin kept.
-/
import Nock.RedTeam.Batch448Thm54VerTransfer
import Nock.RedTeam.Batch501Thm54MemoryTopology
import Nock.RedTeam.Batch502Thm54LedgerTransfer
import Nock.RedTeam.Batch505Thm54StructuralChecks

set_option autoImplicit false

namespace Nock.RedTeam.Batch506

open Nock.RedTeam.Batch448
open Nock.RedTeam.Batch501
open Nock.RedTeam.Batch502
open Nock.RedTeam.Batch505

theorem openConjunctsAfterVer_still_seven :
    openConjunctsAfterVer.length = 7 :=
  openConjunctsAfterVer_length

theorem ledger_unmoved_through_505 :
    openAfterStructuralChecks.length = 7 :=
  openAfterStructuralChecks_length

theorem seed_digest_unmoved :
    seedPublicDeletionStatus =
      "memoryPublicOfTuple 9..11 = pkgPub (receipt); ExactMemoryCoordinatePins.walkSeed kept; digest unmoved" :=
  rfl

theorem exec_topologies_landed :
    "computeTopology" ∈ openConjunctsAfterVer ∧
      "memoryTopology" ∈ openConjunctsAfterVer := by
  decide

end Nock.RedTeam.Batch506

#print axioms Nock.RedTeam.Batch506.openConjunctsAfterVer_still_seven
#print axioms Nock.RedTeam.Batch506.seed_digest_unmoved
