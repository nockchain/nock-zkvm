/-
  Nock/RedTeam/Batch4830Thm54J8ComplA.lean

  **J-8 general completeness, phase A, receipt for `Handle/ComplJ8`.**  The target statement
  and its obligation split: `ComplJ8Obligations` (the remaining lemmas), `honest_accepted_J8_of_obligations`
  (`AcceptsJ8V` at every good coin; the compute chip composed through `computeChipVCLHX_honest_sat`, `SmallX` from
  the two new run binders `ProgAxOK` / `ProgOp5OK`), `probJ8_notGood_le` (union bound), `exists_good`
  (non-vacuity when `ε_c < 1`), `complJ8_of_obligations` (all five conclusions).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8

namespace Nock.RedTeam.Batch4830

open Nock.NockVMROM.Thm54.VclL.Handle

#check @ComplJ8.ComplJ8Obligations
#check @ComplJ8.complJ8_of_obligations
#print axioms ComplJ8.smallX_of_binders
#print axioms ComplJ8.prob_exists_le
#print axioms ComplJ8.honest_accepted_J8_of_obligations
#print axioms ComplJ8.probJ8_notGood_le
#print axioms ComplJ8.exists_good
#print axioms ComplJ8.complJ8_of_obligations

end Nock.RedTeam.Batch4830
