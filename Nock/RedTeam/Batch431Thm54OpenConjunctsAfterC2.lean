/-
  Nock/RedTeam/Batch431Thm54OpenConjunctsAfterC2.lean

  **`openConjunctsAfterC2`.**

  Target was +3 chip-closed (`vmem`, `memoryRows`, `io`) → 14/21.
  No vacuous `0 * length` advance.
-/
import Nock.RedTeam.Batch430Thm54TransferRemainingHole
import Nock.RedTeam.Batch398Thm54PublicConjuncts

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch431

/-- Intended post-C2 open list if transfer completed (7 names). -/
def openConjunctsAfterC2Target : List String :=
  ["mem_first_counts", "mem_first_indicator",
    "computeTopology", "memoryTopology", "axisStructural",
    "rootBoundary", "structuralChecks"]

theorem openConjunctsAfterC2Target_length :
    openConjunctsAfterC2Target.length = 7 := by decide

def openConjunctsAfterC2 : List String :=
  Nock.RedTeam.Batch398.openConjuncts

theorem openConjunctsAfterC2_length :
    openConjunctsAfterC2.length = 10 := by decide

theorem closed_count_after_c2 :
    21 - openConjunctsAfterC2.length = 11 := by decide

/-- Target was 14 closed; live remains 11. -/
theorem target_not_reached :
    openConjunctsAfterC2.length = 10 ∧
      openConjunctsAfterC2Target.length = 7 := by
  decide

theorem wrap_targets_remain :
    "vmem" ∈ openConjunctsAfterC2 ∧
      "memoryRows" ∈ openConjunctsAfterC2 ∧
      "io" ∈ openConjunctsAfterC2 :=
  Nock.RedTeam.Batch430.wrap_targets_still_open

theorem blocked_on_batch430 :
    Nock.RedTeam.Batch430.stopReason =
      "ver_eq_responseActive missing on deployed chip; blocks MemPower on verify_child and derivedResponseIO = hostileResponses" :=
  Nock.RedTeam.Batch430.stop_is_ver_pin

end Nock.RedTeam.Batch431

#print axioms Nock.RedTeam.Batch431.closed_count_after_c2
#print axioms Nock.RedTeam.Batch431.wrap_targets_remain
