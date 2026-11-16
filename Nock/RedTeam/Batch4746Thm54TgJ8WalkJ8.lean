/-
  Nock/RedTeam/Batch4746Thm54TgJ8WalkJ8.lean

  The executable check of the J-8 walk chip `walkChipJ8` (width `166`) at its source gates: **`checkWalkJ8_iff`** (`SatisfiesWithPreprocessing (walkChipJ8 deltaF kr powerBasis3 …) P ↔ checkWalkJ8 kr T = true`, fixed columns `isFirst`, `isLast`, `isRoot = [i < kr]`), an instance of `MemX.chipM_iff` (B4745).  NOT claimed: the chip at the frame coins `chalsMJ8 δ χ` (S7).  Native run on the example's one walk row: `docs/j8/tgj8-walk-harness.lean.txt` (#eval, reported, not gated).
-/
import Nock.V1J8.MemWalkJ8

namespace Nock.RedTeam.Batch4746

#check @Nock.V1J8.MemX.checkWalkJ8_iff
#print axioms Nock.V1J8.MemX.checkWalkJ8_iff

end Nock.RedTeam.Batch4746
