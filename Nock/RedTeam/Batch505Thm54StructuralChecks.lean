/-
  Nock/RedTeam/Batch505Thm54StructuralChecks.lean

  `structuralChecks` and
  the memory pair (`mem_first_counts` / `mem_first_indicator`) stay
  on the ledger.  Not transferred: wrap-specialize join still open.
-/
import Nock.RedTeam.Batch448Thm54VerTransfer
import Nock.RedTeam.Batch504Thm54AxisStructural

set_option autoImplicit false

namespace Nock.RedTeam.Batch505

open Nock.RedTeam.Batch448
open Nock.RedTeam.Batch504

def openAfterStructuralChecks : List String :=
  openAfterAxisStructural

theorem openAfterStructuralChecks_length :
    openAfterStructuralChecks.length = 7 :=
  openAfterAxisStructural_length

theorem structuralChecks_still_open :
    "structuralChecks" ∈ openAfterStructuralChecks ∧
      "mem_first_counts" ∈ openAfterStructuralChecks ∧
      "mem_first_indicator" ∈ openAfterStructuralChecks := by
  decide

def remainingJoin : String :=
  "structuralChecksAt + deployed_axis_lookup_correct after specializedExec topology"

theorem remainingJoin_nonempty : remainingJoin ≠ "" := by
  decide

end Nock.RedTeam.Batch505

#print axioms Nock.RedTeam.Batch505.openAfterStructuralChecks_length
