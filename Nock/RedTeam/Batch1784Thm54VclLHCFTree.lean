/-
  Nock/RedTeam/Batch1784Thm54VclLHCFTree.lean

  **The hCF `tree` / `shape` fields at the VCL chip.**
  Production `Thm54/VclL/Compute/HCFTree.lean`: `tableVCLE` (232,
  `colRoundVCLE`), `envsV` (gathered pull-backs), `treeV` (M0's `SVWalk.computeTree`, no Form R),
  `shapeV` (B0 columns only, by type: selectors 0..12, serial 220), `treeV_shape` (`tree_shape`),
  `shapeV_size_le` (`shape_size`), `treeV_round` (`treeRound := 2`), `colRoundVCLE_le_two`.
-/
import Nock.NockVMROM.Thm54.VclL.Compute.HCFTree
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.P8Core.SVCompute.QueueTwins
import Nock.NockVMROM.Thm54.P8Core.SVWalk.ExpAlign
import Nock.NockVMROM.Thm54.Unhosted309Events

set_option autoImplicit false

namespace Nock.RedTeam.Batch1784

open Nock.NockVMROM.Thm54.VclL.Compute

#print axioms colRoundVCLE_le_two
#print axioms selCol_round0
#print axioms envsV_base
#print axioms envsV_expCol
#print axioms treeV_shape
#print axioms shapeV_size_le
#print axioms treeV_round

end Nock.RedTeam.Batch1784
