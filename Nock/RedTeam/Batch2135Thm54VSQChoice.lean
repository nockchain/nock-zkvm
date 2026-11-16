/-
  Nock/RedTeam/Batch2135Thm54VSQChoice.lean

  Additive.  New module
  `Thm54/VclL/Handle/ChoiceQ.lean`: `ioUB_pair_lt` (the two handle failure bounds are `< |𝕂|²` when the
  sizes are `< p`, `53 ≤ p`, `p³ ≤ |𝕂|`), `ringChar_cube_le_card`, `exists_pair_outside` /
  `exists_pair_outsideQ` (every VS trace pair has a `𝕂` pair outside `evX ∪ evP`, from the VS / VSQ checks
  and `2^63 < p` — NO new soundness hypothesis), `toVSV` / `toVSV_checks` (the VSQ verifier datum at the
  VS shape, checks transported).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ChoiceQ

namespace Nock.RedTeam.Batch2135

open Nock.NockVMROM.Thm54.VclL.Handle.ChoiceQ

#print axioms ioUB_pair_lt
#print axioms ringChar_cube_le_card
#print axioms exists_pair_outside
#print axioms exists_pair_outsideQ
#print axioms toVSV_checks

end Nock.RedTeam.Batch2135
