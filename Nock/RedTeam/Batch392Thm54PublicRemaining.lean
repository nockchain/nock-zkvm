/-
  Nock/RedTeam/Batch392Thm54PublicRemaining.lean

  **`public_*` stay open.**

  `finalEndpointEqualityChecks` pin first-row F columns 0..10 to
  publics 20..30 (`OptimizedComputeFinal.lean`).  `AcceptedContent`
  `public_subject` / `public_formula` / `public_result` are K-side
  `decodePub.s/.f/.e` (`fpOf` 11/14/17) vs
  `enc (nprSeed c.1) claim`.  The F-side pin is not those
  fingerprints.
-/
import Nock.NockVMROM.Thm54.OptimizedComputeFinal
import Nock.RedTeam.Batch388Thm54OpenConjunctsTransfer

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch392

def publicStillOpen : List String :=
  ["public_subject", "public_formula", "public_result"]

theorem publicStillOpen_length : publicStillOpen.length = 3 := by decide

theorem public_subset_open :
    publicStillOpen.Sublist Nock.RedTeam.Batch388.openConjuncts := by
  decide

end Nock.RedTeam.Batch392

#print axioms Nock.RedTeam.Batch392.publicStillOpen_length
