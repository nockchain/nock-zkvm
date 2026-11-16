/-
  Nock/RedTeam/Batch380Thm54OpenConjunctsFill.lean

  **`openConjuncts` after Part 1.**

  Successor of `Batch377.closedAcceptedContent_of_seed`:
  `closedAcceptedContent_of_good` takes `c ∉ hostileFailureEvent`
  and no extra `hz`.  Count stays **2 of 21** (`seed_ne`, `z_eq`).
  The wrap bridge is a lemma, not an `AcceptedContent` field:
  `vcomp` / `ln_chain` / `public_*` / `mem_*` stay named open.
-/
import Nock.NockVMROM.Thm54.AcceptedContentOfTracesFill
import Nock.RedTeam.Batch377Thm54AcceptedContentOfTraces

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch380

open Nock.RedTeam.Batch377
open Nock.NockVMROM.Thm54.AcceptedContentOfTracesFill

/-- Part-1 closed names.  Still `seed_ne` and `z_eq` only. -/
def closedNames : List String := ["seed_ne", "z_eq"]

theorem closedNames_length : closedNames.length = 2 := by
  decide

/-- Count 19. -/
def openConjuncts : List String :=
  Nock.RedTeam.Batch377.openConjuncts

theorem openConjuncts_length : openConjuncts.length = 19 :=
  Nock.RedTeam.Batch377.openConjuncts_length

theorem closed_count : 21 - openConjuncts.length = 2 :=
  Nock.RedTeam.Batch377.closed_count

#check Nock.RedTeam.Batch377.closedAcceptedContent_of_good

end Nock.RedTeam.Batch380

#print axioms Nock.RedTeam.Batch380.openConjuncts_length
#print axioms Nock.RedTeam.Batch380.closed_count
#print axioms Nock.RedTeam.Batch377.closedAcceptedContent_of_good
