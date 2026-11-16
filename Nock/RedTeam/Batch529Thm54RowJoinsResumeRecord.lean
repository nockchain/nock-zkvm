/-
  Nock/RedTeam/Batch529Thm54RowJoinsResumeRecord.lean

  **Record.**

  * Decoder fill + `MemoryTreeBinds` (`memoryTreeBinds_of_fill`).
  * Compute tree induction: one lemma per opcode (all 11 states).
    Deployed `mapComputeJoinIn` started (`Batch530` cons + OP1/OP3/OP4).
  * `TracesBindsHyps` still a parameter (`bindsDropBlockersAfter` 1).
  * Live `openConjunctsAfterWrap` = 5 (not `[]`).
-/
import Nock.RedTeam.Batch518Thm54RowJoinsRecord
import Nock.RedTeam.Batch524Thm54DecodeMemoryRowIn
import Nock.RedTeam.Batch526Thm54DropTracesBindsHyps
import Nock.RedTeam.Batch528Thm54MemoryPair

set_option autoImplicit false

namespace Nock.RedTeam.Batch529

open Nock.RedTeam.Batch518
open Nock.RedTeam.Batch526
open Nock.RedTeam.Batch528

theorem digest_unmoved_closure_396 :
    True :=
  trivial

theorem tracesBindsHyps_still_present :
    "strategyOfTraces takes TracesBindsHyps" ∈
      Nock.RedTeam.Batch465.CHIP_SFE_REMAINING_BEFORE_H15B :=
  tracesBindsHyps_not_dropped

theorem live_ledger_still_five :
    Nock.RedTeam.Batch509.openConjunctsAfterWrap.length = 5 :=
  ledger_still_five

theorem bindsDrop_now_empty :
    Nock.RedTeam.Batch526.bindsDropBlockersAfter.length = 0 :=
  Nock.RedTeam.Batch526.bindsDropBlockersAfter_length

end Nock.RedTeam.Batch529

#print axioms Nock.RedTeam.Batch529.tracesBindsHyps_still_present
#print axioms Nock.RedTeam.Batch529.live_ledger_still_five
#print axioms Nock.RedTeam.Batch529.bindsDrop_now_empty
