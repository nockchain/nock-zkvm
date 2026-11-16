/-
  Nock/RedTeam/Batch511Thm54AxisStructural.lean

  `axisStructural` / `structuralChecks` / the
  memory pair stay on the ledger.  Intended discharges:

  * `intermediate_matching` from `optimizedFullStrict_paired_records`
    on forest timestamps;
  * `read_timestamps_nodup` / `noWrapCheck` from
    `TimestampCollisionEvent`;
  * `ancestry` from memory topology + `deployed_row_vmem_at` +
    permutation;
  * `deployed_axis_lookup_correct` (`:1401`) ⇒ `mem_first_counts` /
    `mem_first_indicator`.

  Ledger **5**.
-/
import Nock.NockVMROM.Thm54.MemoryInternalPole
import Nock.NockVMROM.Thm54.TemplateAxisCounting
import Nock.NockVMROM.Thm54.FamilyMemoryRows
import Nock.RedTeam.Batch448Thm54VerTransfer
import Nock.RedTeam.Batch465Thm54DeployedRootLabelEqClaim
import Nock.RedTeam.Batch509Thm54WrapSpecialize
import Nock.RedTeam.Batch510Thm54RootBoundary

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch511

open Nock.RedTeam.Batch448
open Nock.RedTeam.Batch465
open Nock.RedTeam.Batch509
open Nock.RedTeam.Batch510

/-! ## Ledger stays 5 -/

def openAfterAxis : List String :=
  openAfterRootBoundary

theorem openAfterAxis_length :
    openAfterAxis.length = 5 :=
  openAfterRootBoundary_length

theorem remaining_four_still_on_ledger :
    "axisStructural" ∈ openAfterAxis ∧
      "structuralChecks" ∈ openAfterAxis ∧
      "mem_first_counts" ∈ openAfterAxis ∧
      "mem_first_indicator" ∈ openAfterAxis := by
  decide

theorem rootBoundary_still_on_ledger :
    "rootBoundary" ∈ openAfterAxis := by
  decide

/-- **Exact remaining statement** the chips do not supply.
    `Batch465.bindsDropBlockersAfter` names it. -/
def remainingJoin : String :=
  "RecordHalfJoin + decode_fingerprint (H1.4); TsExists / remainingActiveMemPower"

theorem remainingJoin_is_recordHalfJoin :
    remainingJoin =
      "RecordHalfJoin + decode_fingerprint (H1.4); TsExists / remainingActiveMemPower" :=
  rfl

theorem recordHalfJoin_is_binds_blocker :
    "memory MemoryTreeBinds: RecordHalfJoin + decode_fingerprint (H1.4)" ∈
      bindsDropBlockersAfter := by
  decide

theorem remainingJoin_nonempty : remainingJoin ≠ "" := by
  decide

end Nock.RedTeam.Batch511

#print axioms Nock.RedTeam.Batch511.openAfterAxis_length
#print axioms Nock.RedTeam.Batch511.recordHalfJoin_is_binds_blocker
