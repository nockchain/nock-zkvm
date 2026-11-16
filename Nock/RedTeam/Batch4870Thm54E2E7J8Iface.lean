/-
  Nock/RedTeam/Batch4870Thm54E2E7J8Iface.lean

* N2 `listJ8V`: the J-8 summand list at `probJ8V_final_clean`'s binders (absent `RR4A` / present `RR4`
    data, by `Pb.krootsV = 0`), and `epsilonOf_listJ8V`: `epsilonOf listJ8V < 2^-155`.
  * N1 `soundJ8V_pointwise`: `AcceptsJ8V … tr` outside every summand of `listJ8V` gives `HoldsN c`, for every
    trace `tr` (the pointwise premise of `LinkJ8NV` / `LinkJ8A`, now a named theorem).
  * N3 `oneRound_listJ8V`: every summand prices a nonempty coin set in one sampling round of `frameJ8` and reads
    only coins sampled no later.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.E2EJ8Iface

set_option autoImplicit false

namespace Nock.RedTeam.Batch4870

open Nock.NockVMROM.Thm54.VclL.Handle.E2EJ8Iface

#check @listJ8V
#check @epsilonOf_listJ8V
#check @soundJ8V_pointwise
#check @oneRound_listJ8V

#print axioms epsilonOf_listJ8V
#print axioms soundJ8V_pointwise
#print axioms oneRound_listJ8V

end Nock.RedTeam.Batch4870
