/-
  Nock/RedTeam/Batch4422Thm54JetHonestRAP.lean

  RAP-level honest acceptance of the tag-last J chip
  `jetChipJ8` (`RAP.SatisfiesWithPreprocessing`), generic in the rows, and its matmul `n = 2` toy
  instance at `p = 1009` (row-level facts by kernel `decide`).
-/
import Nock.Jet.ChipJ8THonestRAP
import Nock.Jet.ChipJ8THonestBal

namespace Nock.RedTeam.Batch4422

open Nock.Jet.ChipJ8T.HonestRAP Nock.Jet.ChipJ8T.HonestBal

#print axioms slot_honest
#print axioms jetChipJ8_honest_sat
#print axioms termJ_sum_of_mv
#print axioms jetChipJ8_honest_sat_pins
#print axioms toyPin_layout
#print axioms toyPin_gates
#print axioms toyPin_nodup
#print axioms toyPin_cov
#print axioms toyPin_mv
#print axioms toy_honest_sat

end Nock.RedTeam.Batch4422
