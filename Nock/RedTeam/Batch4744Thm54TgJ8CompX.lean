/-
  Nock/RedTeam/Batch4744Thm54TgJ8CompX.lean

  The executable check of the J-8
  compute chip `computeChipVCLHX` at the source gates: `gatesHX_src` (the chip's gate list is the coordinate
  expansion of the source gates), `srcOK_iff` / `rowOK_iff`, `checkCompX_iff`, and **`computeChipX_iff`**
  (`SatisfiesWithPreprocessing (computeChipVCLHX …) P ↔ checkCompX T = true` for an executable table with injective,
  `ω`-adjacent nodes and the row interpolants as trace).  NOT claimed: the other five chips (S4–S5), the trace built from the input inside `checkJ8_iff` (S7).  The native
  run on the example's compute row is `docs/j8/tgj8-comp-harness.lean.txt` (#eval, reported, not gated).
-/
import Nock.V1J8.CompX

namespace Nock.RedTeam.Batch4744

#check @Nock.V1J8.CompX.computeChipX_iff
#print axioms Nock.V1J8.CompX.toK_evalMZ
#print axioms Nock.V1J8.CompX.mix_eval
#print axioms Nock.V1J8.CompX.gatesHX_src
#print axioms Nock.V1J8.CompX.rowOK_iff
#print axioms Nock.V1J8.CompX.checkCompX_iff
#print axioms Nock.V1J8.CompX.computeChipX_iff
#print axioms Nock.V1Check.satisfies_iff_checkTable

end Nock.RedTeam.Batch4744
