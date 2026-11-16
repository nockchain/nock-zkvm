/-
  Nock/RedTeam/Batch528Thm54MemoryPair.lean

  **Memory-pair last two.**

  `mem_first_counts` / `mem_first_indicator` stay on
  `openConjunctsAfterWrap`.  `remainingActiveMemPower` is already a
  theorem; it does not by itself close `countsP.eval α`.
-/
import Nock.RedTeam.Batch509Thm54WrapSpecialize
import Nock.RedTeam.Batch527Thm54LastFive

set_option autoImplicit false

namespace Nock.RedTeam.Batch528

open Nock.RedTeam.Batch509
open Nock.RedTeam.Batch527

theorem mem_first_still_open :
    "mem_first_counts" ∈ openConjunctsAfterWrap ∧
      "mem_first_indicator" ∈ openConjunctsAfterWrap := by
  decide

theorem ledger_still_five :
    openConjunctsAfterWrap.length = 5 :=
  live_openConjunctsAfterWrap_still_five

end Nock.RedTeam.Batch528

#print axioms Nock.RedTeam.Batch528.mem_first_still_open
#print axioms Nock.RedTeam.Batch528.ledger_still_five
