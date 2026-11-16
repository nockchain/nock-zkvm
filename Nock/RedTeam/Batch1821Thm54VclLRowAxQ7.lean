/-
  Nock/RedTeam/Batch1821Thm54VclLRowAxQ7.lean

  **Tree-node → row, the serial, `RowFacts.ax0/ax9` at
  `axB0Q7`.**  Production
  `Thm54/VclL/Compute/RowAxQ7.lean`: `inTree_buildT_label`, `inTree_mapNTree`, `treeV_node_row`
  (every node of `treeV` is a row's stride-2 label), `serial_eq_row` (accepted side-chip trace:
  column 220 of row r is r), `rowCarrier_eq_row` (`V.N ≤ ringChar K`), `treeV_label_row`
  (label = 2r), `rowFacts_ax0_Q7` / `rowFacts_ax9_Q7` (the two axis clauses at `axB0Q7`,
  `q = ringChar K`), `rowFacts_Q7_of_core` (the full `Batch1171.RowFacts` from the five carrier-free
  core facts, which are NOT proved here for VCL).
-/
import Nock.NockVMROM.Thm54.VclL.Compute.RowAxQ7
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.P8Core.SVCompute.QueueTwins
import Nock.NockVMROM.Thm54.P8Core.SVWalk.ExpAlign
import Nock.NockVMROM.Thm54.Unhosted309Events

set_option autoImplicit false

namespace Nock.RedTeam.Batch1821

open Nock.NockVMROM.Thm54.VclL.Compute

#print axioms inTree_buildT_label
#print axioms inTree_mapNTree
#print axioms treeV_node_row
#print axioms serial_eq_row
#print axioms rowCarrier_eq_row
#print axioms treeV_label_row
#print axioms row_ax_facts
#print axioms rowFacts_ax0_Q7
#print axioms rowFacts_ax9_Q7
#print axioms rowFacts_Q7_of_core

end Nock.RedTeam.Batch1821
