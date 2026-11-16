/-
  Nock/RedTeam/Batch4745Thm54TgJ8CellKW.lean

  The generic
  executable check of an `expandChip` memory-side chip at its source gates (`srcM_expand`: the chip's gate list is
  the coordinate expansion of the template's base / `Expr` / mixed source gates; `srcOK_iff`, `rowOK_iff`,
  `checkM_iff`, **`chipM_iff`**), and its instance at the J-8 cell chip: **`checkCellKW_iff`**
  (`SatisfiesWithPreprocessing (cellChipHQKW deltaF powerBasis3 …) P ↔ checkCellKW T = true` for an executable table
  with injective, `ω`-adjacent nodes, the masks `isFirst`/`isLast`, and the row interpolants as trace).
  NOT claimed: the chip at the frame coins `chalsMJ8 δ χ` (the table's coins are `K3` values mapped by `K3.toK`; the
  bridge to `chalsMJ8` is S7), the walk / atom / J / atom-walk chips (B4746–B4748).  The native run on the
  example's two cell rows is `docs/j8/tgj8-cell-harness.lean.txt` (#eval, reported, not gated).
-/
import Nock.V1J8.MemCellKW

namespace Nock.RedTeam.Batch4745

#check @Nock.V1J8.MemX.checkCellKW_iff
#print axioms Nock.V1J8.MemX.toK_evalEZ
#print axioms Nock.V1J8.MemX.ext_eval
#print axioms Nock.V1J8.MemX.mixB_eval
#print axioms Nock.V1J8.MemX.srcM_expand
#print axioms Nock.V1J8.MemX.rowOK_iff
#print axioms Nock.V1J8.MemX.checkM_iff
#print axioms Nock.V1J8.MemX.chipM_iff
#print axioms Nock.V1J8.MemX.checkCellKW_iff

end Nock.RedTeam.Batch4745
