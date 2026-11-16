/-
  Nock/RedTeam/Batch504Thm54AxisStructural.lean

  `axisStructural` stays
  on the ledger.  Intended: `intermediate_matching` from
  `optimizedFullStrict_paired_records` on `execOfTraces` timestamps;
  `read_timestamps_nodup` from `TimestampCollisionEvent`; `ancestry`
  from memory topology + `deployed_row_vmem_at` + permutation.  Not transferred: wrap-specialize join
  still open.
-/
import Nock.RedTeam.Batch448Thm54VerTransfer
import Nock.RedTeam.Batch503Thm54RootBoundary

set_option autoImplicit false

namespace Nock.RedTeam.Batch504

open Nock.RedTeam.Batch448
open Nock.RedTeam.Batch503

def openAfterAxisStructural : List String :=
  openAfterRootBoundary

theorem openAfterAxisStructural_length :
    openAfterAxisStructural.length = 7 :=
  openAfterRootBoundary_length

theorem axisStructural_still_open :
    "axisStructural" ∈ openAfterAxisStructural := by
  decide

def remainingJoin : String :=
  "ExactAxisStructuralRefinement of specializedExec (intermediate_matching / nodup / ancestry)"

theorem remainingJoin_nonempty : remainingJoin ≠ "" := by
  decide

end Nock.RedTeam.Batch504

#print axioms Nock.RedTeam.Batch504.openAfterAxisStructural_length
