/-
  Nock/RedTeam/Batch1823Thm54VclLCoreQ7.lean

  **The `RowFacts` core at every node of the VCL `treeV`.**
  `HCFTree.treeV1` reads the `ln`-patched rows (`envsP`;
  `RowAxQ7` re-proved there).  Production `Thm54/VclL/Compute/CoreQ7.lean`: `cdOf` (the
  `ChipData` → `VerifierData` bridge, `BV_cdOf` by `rfl`), `treeV1_fst` (projection = the
  reconstruction over `TopoQ7.lblQ`), `rowFacts_core_Q7` (pubSt, zRow at `zQ`, vcomp, arity, link),
  `rowFacts_Q7` (`Batch1171.RowFacts` at `axB0Q7` from acceptance at `computeChipVCLQ7S` and the
  `α`-root / prefix-`γ` / `α`-tiling coin events — the body of the frame's `rowFactsAt` at VCL).
-/
import Nock.NockVMROM.Thm54.VclL.Compute.CoreQ7
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.P8Core.SVCompute.QueueTwins
import Nock.NockVMROM.Thm54.P8Core.SVWalk.ExpAlign
import Nock.NockVMROM.Thm54.Unhosted309Events

set_option autoImplicit false

namespace Nock.RedTeam.Batch1823

open Nock.NockVMROM.Thm54.VclL.Compute
open Nock.NockVMROM.Thm54.VclL.Compute.CoreQ7

#print axioms treeV_shape
#print axioms rowLabel_envsP_dec
#print axioms rowFacts_ax0_Q7
#print axioms inTree_mapNTree_eq
#print axioms inTree_mapNTree_of
#print axioms BV_cdOf
#print axioms treeV1_fst
#print axioms rowFacts_core_Q7
#print axioms rowFacts_Q7

end Nock.RedTeam.Batch1823
