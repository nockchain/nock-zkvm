/-
  Nock/RedTeam/Batch512Thm54MemoryAlphaRecord.lean

  * Memory forest α-event of `:1008` in the consumed union;
    `memoryTopology_of_deployed_of_good` has no extra hypothesis.
  * `walkSeed` pin deleted; `walkSubst` / `walkBoundarySubst`
    write `Const 0` at `publicVal 1`; `exactMemoryWalkRowEnv` seed is
    `0`; `seedW = 0`.  Slots 9..11 remain in `pkgPub` (unread).
  * `wrapSpecializeJoinCompute` and `wrapSpecializeJoin` are
    theorems (`mapNTree` identity).  Ledger **7 → 5** by name
    (`openConjunctsAfterWrap`).  Memory transport still takes
    `remainingActiveMemPower`.
  * Chip root zeros land
    (`deployed_root_pt_counts_zero`); `RootAxisBoundaryAt` reduces to
    `remainingCountsPEvalZero`.  Ledger stays 5.
  * `d = 4`.
    Figures 123 / 122 / 120 by theorem.
-/
import Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
import Nock.RedTeam.Batch448Thm54VerTransfer
import Nock.RedTeam.Batch507Thm54MemoryForestAlpha
import Nock.RedTeam.Batch508Thm54SeedPublicDeleted
import Nock.RedTeam.Batch509Thm54WrapSpecialize
import Nock.RedTeam.Batch511Thm54AxisStructural

set_option autoImplicit false

namespace Nock.RedTeam.Batch512

open Nock.RedTeam.Batch448
open Nock.RedTeam.Batch508
open Nock.RedTeam.Batch509
open Nock.RedTeam.Batch511
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis

/-- Live open list after wrap-specialize, by name. -/
theorem openConjunctsAfterWrap_is_five :
    openConjunctsAfterWrap.length = 5 :=
  openConjunctsAfterWrap_length

theorem topology_names_dropped :
    "computeTopology" ∉ openConjunctsAfterWrap ∧
      "memoryTopology" ∉ openConjunctsAfterWrap :=
  topology_names_left

theorem live_five_from_historical_seven :
    openConjunctsAfterWrap =
      openConjunctsAfterVer.filter
        (fun n => n ≠ "computeTopology" ∧ n ≠ "memoryTopology") :=
  remaining_five_from_seven

theorem tracesBindsHyps_still_open :
    remainingJoin =
      "RecordHalfJoin + decode_fingerprint (H1.4); TsExists / remainingActiveMemPower" :=
  remainingJoin_is_recordHalfJoin

theorem seed_pin_deleted :
    walkSubst .publicVal 1 = .Const 0 ∧
      walkBoundarySubst .publicVal 1 = .Const 0 :=
  ⟨walkSubst_pub1_is_zero, walkBoundarySubst_pub1_is_zero⟩

theorem historical_openConjunctsAfterVer_still_seven :
    openConjunctsAfterVer.length = 7 :=
  openConjunctsAfterVer_length

end Nock.RedTeam.Batch512

#print axioms Nock.RedTeam.Batch512.openConjunctsAfterWrap_is_five
#print axioms Nock.RedTeam.Batch512.topology_names_dropped
#print axioms Nock.RedTeam.Batch512.seed_pin_deleted
