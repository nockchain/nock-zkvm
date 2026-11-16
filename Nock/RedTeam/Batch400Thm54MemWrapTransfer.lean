/-
  Nock/RedTeam/Batch400Thm54MemWrapTransfer.lean

  **Transfer after the exponent fix.**

  With `recordExponent := memExponent`, the wrap recovers `mem.ts` on
  active rows.  Target: close `vmem`, `memoryRows`, `io`
  (`closed_count 8 → 11`).

  Status at land: the exponent change is installed and the specialize
  identity is proved under the discrete-log hyp.  Full transfer of the
  three `AcceptedContent` conjuncts still needs
  (1) `response_ts_mem_powers` outside `hostileFailureEvent` (hostile LIO
  + `ln₀ = 1` + request timestamp form), and
  (2) the chip→`Vmem` bridge on decoded memory rows (no
  `deployed_row_vmem_at` yet — compute had `deployed_row_vcomp_at`).
  Those are named below; no `0 * length` close.
-/
import Nock.RedTeam.Batch399Thm54MemExponent
import Nock.RedTeam.Batch388Thm54OpenConjunctsTransfer

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch400

def targetConjuncts : List String := ["memoryRows", "vmem", "io"]

theorem targetConjuncts_length : targetConjuncts.length = 3 := by decide

theorem targets_were_open :
    targetConjuncts.Sublist Nock.RedTeam.Batch388.openConjuncts := by
  decide

/-- Open list with the three wrap targets
removed if transfer completed.  Live count still reflects incomplete
transfer — see `closed_count_after_exponent`. -/
def openConjunctsAfterExponent : List String :=
  ["mem_first_counts", "mem_first_indicator",
    "public_subject", "public_formula", "public_result",
    "computeTopology", "memoryTopology", "axisStructural", "rootBoundary",
    "structuralChecks",
    -- wrap targets remain open until response_ts_mem_powers + Vmem bridge
    "memoryRows", "vmem", "io"]

theorem openConjunctsAfterExponent_length :
    openConjunctsAfterExponent.length = 13 := by decide

/-- Honest count: exponent installed, three wrap targets still open
(need powers membership + chip→Vmem). -/
theorem closed_count_after_exponent :
    21 - openConjunctsAfterExponent.length = 8 := by decide

/-- Named remaining work for the three wrap targets. -/
def transferRemainingHyps : List String :=
  ["response_ts_mem_powers",
    "deployed_row_vmem_at",
    "derivedResponseIO_eq_hostileResponses",
    "derivedRequestIO_eq_hostileRequests"]

theorem transferRemainingHyps_length :
    transferRemainingHyps.length = 4 := by decide

/-- No vacuous `0 * length` close: open list still contains the three. -/
theorem no_vacuous_close :
    "vmem" ∈ openConjunctsAfterExponent ∧
      "memoryRows" ∈ openConjunctsAfterExponent ∧
      "io" ∈ openConjunctsAfterExponent := by
  decide

end Nock.RedTeam.Batch400

#print axioms Nock.RedTeam.Batch400.closed_count_after_exponent
#print axioms Nock.RedTeam.Batch400.no_vacuous_close
#print axioms Nock.RedTeam.Batch399.wrapMemoryLabel_uses_memExponent
