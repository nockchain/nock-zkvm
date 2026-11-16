/-
  Nock/RedTeam/Batch394Thm54OpenConjunctsRemaining.lean

  **Assembly, count still 8/21.**

  Prerequisite `closed_count ≥ 12` was unmet on live NR (8/21).
-/
import Nock.RedTeam.Batch388Thm54OpenConjunctsTransfer
import Nock.RedTeam.Batch389Thm54IoOfTracesRemaining
import Nock.RedTeam.Batch390Thm54WalkHypsRemaining
import Nock.RedTeam.Batch392Thm54PublicRemaining

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch394

def openConjuncts : List String := Nock.RedTeam.Batch388.openConjuncts

theorem openConjuncts_length : openConjuncts.length = 13 := by decide

theorem closed_count : 21 - openConjuncts.length = 8 := by decide

theorem same_as_transfer :
    openConjuncts = Nock.RedTeam.Batch388.openConjuncts := rfl

theorem not_h15a_done : openConjuncts ≠ [] := by decide

end Nock.RedTeam.Batch394

#print axioms Nock.RedTeam.Batch394.closed_count
#print axioms Nock.RedTeam.Batch394.not_h15a_done
