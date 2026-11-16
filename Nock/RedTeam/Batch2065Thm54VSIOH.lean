/-
  Nock/RedTeam/Batch2065Thm54VSIOH.lean

  **The handle IO summands at coins `{11, 12}`.**
  Additive.  New module `Thm54/VclL/Handle/IOVS.lean`:
  * read-set congruence: the compute request lists read only round-0 columns `< 43`
    (`rowReqs_congr`, `compReqs_congr`), the twins' lists only their round-0 base columns
    (`walkLists_congr` `< 25`, `cellProvs_congr` `< 130`); no coin, no public;
  * `ioSummandHX` (export, weight `ioFailureUnionBound 5 (3N + W) T |𝕂|`) and `ioSummandHP` (path,
    weight `ioFailureUnionBound 5 (2N) (2W) |𝕂|`): coins `{γH, ρH} = {χ₁₁, χ₁₂}`, `dep = ∅`,
    `readsOn` from staging (round-0 records);
  * `served_of_not_mem`: outside both summands, at an accepted coin under `V.Checks`, the two handle
    lookups are served.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.IOVS

namespace Nock.RedTeam.Batch2065

open Nock.NockVMROM.Thm54.VclL.Handle.IOVS

#print axioms rowReqs_congr
#print axioms compReqs_congr
#print axioms walkLists_congr
#print axioms cellProvs_congr
#print axioms evX_card
#print axioms evP_card
#print axioms ioSummandHX
#print axioms ioSummandHP
#print axioms mem_ioSummandHX
#print axioms lists_at
#print axioms served_of_not_mem

end Nock.RedTeam.Batch2065
