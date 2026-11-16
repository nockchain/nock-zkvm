/-
  Nock/RedTeam/Batch4854Thm54J9BComplOf.lean

  **J-9 B general completeness, receipt for `Handle/ComplJ9BComp` and `Handle/ComplJ9BOf`.**
  * `ComplJ9BComp`: the compute chip at the J-9 publics `pubVJ9` (`claimKH_hdl`: under `HdlOK` the J-9 claim handle
    is the handle map, so no claim-leaf bound); `computeChip_sat9`, `staged_trCOf9`.
  * `ComplJ9BOf`: `j9DataOf` (`mb9`), the honest record `BRunG … AV FA` / `BRun9`, `good9` / `good9_run` /
    `good9_FA`, `compute_group9`, `claim_run9` (`hclI` at cell / big positions, `hcen'` via spines in `acs`),
    `famsA9_facts` / `famsA9_run`, `OpenJ9B` (the five carried fields), `obligations_of_run9`, `complJ9B_open`
    (`complJ9B_closed`'s conclusion with `OpenJ9B` carried).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BOf

set_option autoImplicit false

namespace Nock.RedTeam.Batch4854

open Nock.NockVMROM.Thm54.VclL.Handle

#print axioms ComplJ9BComp.claimKH_hdl
#print axioms ComplJ9BComp.computeChip_sat9
#print axioms ComplJ9BComp.staged_trCOf9
#print axioms ComplJ9BOf.good9
#print axioms ComplJ9BOf.good9_run
#print axioms ComplJ9BOf.good9_FA
#print axioms ComplJ9BOf.compute_group9
#print axioms ComplJ9BOf.claim_run9
#print axioms ComplJ9BOf.famsA9_facts
#print axioms ComplJ9BOf.famsA9_run
#print axioms ComplJ9BOf.jOK_run9
#print axioms ComplJ9BOf.cellOK_run9
#print axioms ComplJ9BOf.walkOK_run9
#print axioms ComplJ9BOf.obligations_of_run9
#print axioms ComplJ9BOf.complJ9B_open
#print axioms ComplJ9BOf.awOK_run9
#print axioms ComplJ9BOf.balF_run9
#print axioms ComplJ9BOf.complJ9B_run9
#print axioms ComplJ9BOf.extraPairs_claimBigs
#print axioms ComplJ9BOf.j9_mb_eq
#print axioms ComplJ9BOf.mbCountsP9_gen
#print axioms ComplJ9BOf.atomOK_B9

end Nock.RedTeam.Batch4854
