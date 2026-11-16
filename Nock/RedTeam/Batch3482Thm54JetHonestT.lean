/-
  Nock/RedTeam/Batch3482Thm54JetHonestT.lean

  Honest acceptance of the tag-last J chip, matmul `n = 2`
  (kernel, `p = 1009` and Goldilocks); `n = 8` executable only.
-/
import Nock.Jet.ChipJ8THonest
import Nock.Jet.ChipJ8TDemo

namespace Nock.RedTeam.Batch3482

open Nock.Jet.ChipJ8T.Honest Nock.Jet.ChipJ8T.Demo

#print axioms toyT_gates
#print axioms toyT_bal
#print axioms toyT_tag_last
#print axioms toyRowsJ_sum_bal_fails
#print axioms toyT_sum_bal
#print axioms toyT_layout
#print axioms toyT_gates'
#print axioms toyT_bal'
#print axioms toyT_accepted
#print axioms demo2_rows
#print axioms demo2_layout
#print axioms demo2_gates
#print axioms demo2_bal
#print axioms demo2_tampered_one_gate

end Nock.RedTeam.Batch3482
