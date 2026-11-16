/-
  Nock/RedTeam/Batch430Thm54TransferRemainingHole.lean

  Landed: `wrap_fixes_vmem_row` under `MemPower` / padding-zero
  (`WrapMemoryConjuncts`), `encRec_decodeMem_eq_rowRecord`,
  `specializedCfg_memoryInputs` (β := −interPole).

  Remaining hole (exact, no invented paper reading):

  1. **`MemPower` on every active memory row** (read_root *and*
     verify_child) is needed for wrap identity on `lblMAt`.
     `response_ts_mem_powers` covers only `hostileResponses`
     (`ver = 1`).  `verify_child` is not in `responseRecords`. Extending via
     `optimizedFullStrict_paired_records` needs
     `hostileReads` connected to responses, which requires
     `ver = op_read` / `responseActive(st)`.

  2. **`ver (role 39) = responseActive(st)`** is not a committed gate
     (only `verBool`).

  3. **`derivedRequestIO_eq_hostileRequests`** still needs the hostile
     generalization of `canonical_rowRequests`
     (`rowRequests = (activeRequestRecords decodePub).map encRec`).

  No `0 * length` close.
-/
import Nock.RedTeam.Batch429Thm54DeployedRowVmem
import Nock.RedTeam.Batch428Thm54HostileBetaPole
import Nock.RedTeam.Batch406Thm54IoBlocked
import Nock.RedTeam.Batch400Thm54MemWrapTransfer
import Nock.RedTeam.Batch398Thm54PublicConjuncts
import Nock.NockVMROM.Thm54.WrapMemoryConjuncts

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch430

/-- 429. -/
def remainingHyps : List String :=
  ["active_mem_ts_MemPower_incl_verify_child",
    "ver_eq_responseActive",
    "derivedRequestIO_eq_hostileRequests",
    "derivedResponseIO_eq_hostileResponses"]

theorem remainingHyps_length : remainingHyps.length = 4 := by decide

/-- Wrap identity is proved under MemPower; discharge is the hole. -/
theorem wrap_fixes_stated :
    ∃ (_ : Type), True :=
  ⟨Unit, trivial⟩

#check Nock.NockVMROM.Thm54.WrapMemoryConjuncts.wrap_fixes_vmem_row
#check Nock.NockVMROM.Thm54.WrapMemoryConjuncts.encRec_decodeMem_eq_rowRecord

theorem wrap_targets_still_open :
    "vmem" ∈ Nock.RedTeam.Batch398.openConjuncts ∧
      "memoryRows" ∈ Nock.RedTeam.Batch398.openConjuncts ∧
      "io" ∈ Nock.RedTeam.Batch398.openConjuncts := by
  decide

theorem closed_count_unmoved :
    21 - Nock.RedTeam.Batch398.openConjuncts.length = 11 :=
  Nock.RedTeam.Batch398.closed_count

/-- Exact remaining hole (no paper invention). -/
def stopReason : String :=
  "ver_eq_responseActive missing on deployed chip; blocks MemPower on verify_child and derivedResponseIO = hostileResponses"

theorem stop_is_ver_pin :
    stopReason =
      "ver_eq_responseActive missing on deployed chip; blocks MemPower on verify_child and derivedResponseIO = hostileResponses" :=
  rfl

end Nock.RedTeam.Batch430

#print axioms Nock.RedTeam.Batch430.closed_count_unmoved
#print axioms Nock.RedTeam.Batch430.stop_is_ver_pin
#print axioms Nock.NockVMROM.Thm54.WrapMemoryConjuncts.wrap_fixes_vmem_row
