/-
  Nock/RedTeam/Batch4748Thm54TgJ8JAW.lean

  The J chip and the atom walk,
  executably: present case **`checkJ8chip_iff`** (`SatisfiesWithPreprocessing (jetChipJ8 deltaF powerBasis3 …) P ↔
  checkJchip T = true`, the 18 layout-fixed columns `prepJ lay`) and **`checkAW_iff`** (`walkChipHQK`, masks
  `isFirst`, `isLast`, `isRoot`); the dispatch, verbatim on the predicates of `AcceptsJ8V`: **`checkJOK_iff`**
  (`JGenJ8.JChipOK … ↔ checkJOK T = true`) and **`checkAWOK_iff`** (`AcceptsJ8V.AWChipOK … ↔ checkAWOK kr T = true`),
  where injectivity, `ω`-adjacency, the root-count range and the absent-case zero publics are CHECKED, not assumed.
  NOT claimed: the chips at the frame coins `chalsJJ8 χ` / `chalsAJ8Z δ χ` (S7); a native run of the PRESENT branches
  (no honest jet / big-atom example yet).  Native run of the absent dispatch at the example:
  `docs/j8/tgj8-jaw-harness.lean.txt` (#eval, reported, not gated).
-/
import Nock.V1J8.MemJAW

namespace Nock.RedTeam.Batch4748

#check @Nock.V1J8.MemX.checkJOK_iff
#check @Nock.V1J8.MemX.checkAWOK_iff
#print axioms Nock.V1J8.MemX.checkJ8chip_iff
#print axioms Nock.V1J8.MemX.checkJOK_iff
#print axioms Nock.V1J8.MemX.checkAW_iff
#print axioms Nock.V1J8.MemX.checkAWOK_iff

end Nock.RedTeam.Batch4748
