/-
  Nock/RedTeam/Batch4891Thm54T0Compl.lean

  **completeness without `look_small` at `N`.**  `ComplJ8OfBalG.shape_small` / `look_small`
  are false at `Ty.N` (an `N` slot holds any noun), so they are restated under `NFree` (argument types
  mention no `N`); `exRows_small` goes through the new type-independent `ev_small`; the two production
  uses of smallness for constants (`ComplJ8OfBalJ` const case, `ComplJ8Jet` `blockOK_of_tpl` `a4`) read
  `honestRows_small` (constants are `F`-typed or `0`).  `N` cases added to `ComplJ8BigBound` /
  `ComplJ8RegLeaf` / gRows lemmas.  Statements of `complJ8_closed`, `complJ9B_closed`, `complJ9A_closed`,
  `complJ9A_closed_of` are unchanged (git diff).  Kernel-checked: the `#print axioms` below.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9AClosed
import Nock.NockVMROM.Thm54.VclL.Handle.ComplClosedChecked

namespace Nock.RedTeam.Batch4891

open Nock.NockVMROM.Thm54.VclL.Handle

#print axioms ComplJ9AClosed.complJ9A_closed
#print axioms ComplClosedChecked.complJ9A_closed_of
#print axioms ComplJ8OfBalG.ev_small
#print axioms ComplJ8OfBalG.look_small

end Nock.RedTeam.Batch4891
