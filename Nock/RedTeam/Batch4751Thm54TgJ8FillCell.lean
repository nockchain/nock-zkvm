/-
  Nock/RedTeam/Batch4751Thm54TgJ8FillCell.lean

  The executable cell-KW fill
  of the example (`*[[0 0] [0 1]]`, rows `s0`, `f0`; `K6` arithmetic, computable) at any memory coins `k : Co` and
  multiplicities `mv mx mx1 mh`:
  * **`colZ_eq`**: every column `c < 242` of every row equals the honest builder's column function
    (`fullCol (HonestKW.colW (cellCol (cvals …)) … ivW avW)`) at `KC`, `powerBasis3`, `deltaF`;
  * **`cellTrace_eq`**: the interpolants of the fill are `InhabJ8MemCell.trM0` (given injective nodes and the handle
    coins of `chals` equal to `(γH′, ρH′)`); **`cellTrace_eq_frame`** / **`interpOf_cell`**: the same at the frame
    coins (`coOf χe`, `chalsMJ8 deltaF (toχ χe)`), the second for the checker's `interpOf`.
  NOT claimed: walk / atom equality (later receipts); any tracegen beyond the example.
-/
import Nock.V1J8.FillCell

namespace Nock.RedTeam.Batch4751

#check @Nock.V1J8.FillMem.colZ_eq
#check @Nock.V1J8.FillMem.cellTrace_eq
#check @Nock.V1J8.FillMem.interpOf_cell
#print axioms Nock.V1J8.FillMem.colZ_eq
#print axioms Nock.V1J8.FillMem.cellTrace_eq_frame
#print axioms Nock.V1J8.FillMem.interpOf_cell

end Nock.RedTeam.Batch4751
