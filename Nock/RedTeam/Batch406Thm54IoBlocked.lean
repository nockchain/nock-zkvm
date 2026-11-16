/-
  Nock/RedTeam/Batch406Thm54IoBlocked.lean

  `derivedRequestIO_eq_hostileRequests` and
  `derivedResponseIO_eq_hostileResponses` need the wrap to recover
  specialized memory/compute records so `IO.LIO` of derived lists
  matches hostile LIO.

  No conjunct closed.  `response_ts_mem_powers`  is proved; the other three
  `transferRemainingHyps` stay.
-/
import Nock.RedTeam.Batch405Thm54VmemPoleMismatch
import Nock.RedTeam.Batch404Thm54ResponseTsMemPowers
import Nock.RedTeam.Batch400Thm54MemWrapTransfer
import Nock.RedTeam.Batch398Thm54PublicConjuncts

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch406

def remainingHyps : List String :=
  Nock.RedTeam.Batch405.remainingAfter404

theorem remainingHyps_length : remainingHyps.length = 3 := by decide

theorem response_ts_proved :
    "response_ts_mem_powers" ∉ remainingHyps := by
  decide

theorem openConjuncts_length :
    Nock.RedTeam.Batch398.openConjuncts.length = 10 :=
  Nock.RedTeam.Batch398.openConjuncts_length

theorem closed_count : 21 - Nock.RedTeam.Batch398.openConjuncts.length = 11 :=
  Nock.RedTeam.Batch398.closed_count

theorem wrap_targets_still_open :
    "vmem" ∈ Nock.RedTeam.Batch398.openConjuncts ∧
      "memoryRows" ∈ Nock.RedTeam.Batch398.openConjuncts ∧
      "io" ∈ Nock.RedTeam.Batch398.openConjuncts :=
  Nock.RedTeam.Batch405.no_vacuous_close

theorem blocked_on_batch405_stop :
    Nock.RedTeam.Batch405.stopReason =
      "paper_reading: Inputs.β := -interPole (W4 Design A) or interV vs poleSource" :=
  Nock.RedTeam.Batch405.stop_is_paper_reading

end Nock.RedTeam.Batch406

#print axioms Nock.RedTeam.Batch406.closed_count
#print axioms Nock.RedTeam.Batch406.wrap_targets_still_open
#print axioms Nock.RedTeam.Batch406.blocked_on_batch405_stop
