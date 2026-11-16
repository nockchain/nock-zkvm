/-
  Nock/RedTeam/Batch4301Thm54J8r4aReprice.lean

  Summand #6 re-priced at
  `2N + 2J + g` (the list `allJ8C` at `g' = g + N`; #2 over-priced by `N`): the figure stays `< 2^-155`, tight.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.RepriceJ8

namespace Nock.RedTeam.Batch4301

open Nock.NockVMROM.Thm54.VclL.Handle

#check @RepriceJ8.service_budget_reprice
#check @RepriceJ8.figJ8X_155_census32
#check @RepriceJ8.figJ8X_not_156_32
#print axioms RepriceJ8.figJ8X_155_census32
#print axioms RepriceJ8.figJ8X_not_156_32
#print axioms RepriceJ8.probJ8X_lt_155_census32
#print axioms RepriceJ8.hcap_corner32

end Nock.RedTeam.Batch4301
