/-
  Nock/RedTeam/Batch527Thm54LastFive.lean

  **The last five wrap conjuncts.**

  Live ledger `openConjunctsAfterWrap` stays
  `mem_first_counts`, `mem_first_indicator`, `axisStructural`,
  `rootBoundary`, `structuralChecks`.  Target `[]` is not reached:
  `rootBoundary` still needs `remainingCountsPEvalZero`;
  `axisStructural` still needs `intermediate_matching` /
  `read_timestamps_nodup` / `ancestry`; the memory pair still needs
  `deployed_axis_lookup_correct`.
-/
import Nock.RedTeam.Batch509Thm54WrapSpecialize
import Nock.RedTeam.Batch518Thm54RowJoinsRecord

set_option autoImplicit false

namespace Nock.RedTeam.Batch527

open Nock.RedTeam.Batch509

theorem live_openConjunctsAfterWrap_still_five :
    openConjunctsAfterWrap.length = 5 :=
  Nock.RedTeam.Batch518.live_openConjunctsAfterWrap_is_five

theorem live_list_not_empty :
    openConjunctsAfterWrap ≠ [] :=
  Nock.RedTeam.Batch518.live_list_not_empty

theorem remaining_names :
    openConjunctsAfterWrap =
      ["mem_first_counts", "mem_first_indicator",
        "axisStructural", "rootBoundary", "structuralChecks"] :=
  rfl

end Nock.RedTeam.Batch527

#print axioms Nock.RedTeam.Batch527.live_openConjunctsAfterWrap_still_five
#print axioms Nock.RedTeam.Batch527.remaining_names
