/-
  Nock/RedTeam/Batch4747Thm54TgJ8Atom.lean

  The executable checks of the
  J-8 atom chips at their source gates: **`checkAtomHQL_iff`** (`SatisfiesWithPreprocessing (atomChipHQL deltaF
  powerBasis3 …) P ↔ checkAtomHQL T = true`) and **`checkAtomHQ_iff`** (the same for `atomChipHQ`, `ChipsJ8.hsatA` /
  `hbindA`), masks `isFirst`, `isLast`; instances of `MemX.chipM_iff` (B4745).  NOT claimed: the chips at the frame
  coins `chalsAJ8Z δ χ` (S7).  Native run on the example's one atom row (the inert pad row):
  `docs/j8/tgj8-atom-harness.lean.txt` (#eval, reported, not gated).
-/
import Nock.V1J8.MemAtom

namespace Nock.RedTeam.Batch4747

#check @Nock.V1J8.MemX.checkAtomHQL_iff
#check @Nock.V1J8.MemX.checkAtomHQ_iff
#print axioms Nock.V1J8.MemX.checkAtomHQL_iff
#print axioms Nock.V1J8.MemX.checkAtomHQ_iff

end Nock.RedTeam.Batch4747
