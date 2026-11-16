/-
  Nock/RedTeam/Batch503Thm54RootBoundary.lean

  `rootBoundary` stays on
  the ledger.  The intended discharge is `RootAxisBoundaryAt` from
  `deployed_root_accumulators_zero` + decode bridge (committed axis
  polynomial at root `i` = root row `pt.counts`).
-/
import Nock.RedTeam.Batch448Thm54VerTransfer
import Nock.RedTeam.Batch502Thm54LedgerTransfer

set_option autoImplicit false

namespace Nock.RedTeam.Batch503

open Nock.RedTeam.Batch448
open Nock.RedTeam.Batch502

def openAfterRootBoundary : List String :=
  openAfterLedgerTransfer

theorem openAfterRootBoundary_length :
    openAfterRootBoundary.length = 7 :=
  openAfterLedgerTransfer_length

theorem rootBoundary_still_open :
    "rootBoundary" ∈ openAfterRootBoundary := by
  decide

def remainingJoin : String :=
  "RootAxisBoundaryAt from deployed_root_accumulators_zero + decode bridge, after specializedExec topology"

theorem remainingJoin_nonempty : remainingJoin ≠ "" := by
  decide

end Nock.RedTeam.Batch503

#print axioms Nock.RedTeam.Batch503.openAfterRootBoundary_length
