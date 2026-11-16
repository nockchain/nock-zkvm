/-
  Nock/RedTeam/Batch1830Thm54VclLNodeRecQ7.lean

  **`node_records` at the VCL compute chip.**
  Production `Thm54/VclL/Compute/NodeRecQ7.lean`:
  `exportRecsQ7` / `pathRecsQ7` (= `exportReqFactsQ7S` / `pathReqFactsQ7S` records, `rfl`),
  `mem_activeRecords`, `decodePub_e_oneHot` / `decodePub_sf2f_oneHot` (the two overlay-restored
  roles the path records read), `label_vcomp` (`Vcomp` at every patched label), `row_records_Q7`,
  `node_records_Q7` (the frame field's conclusion at `inlineRecords = 0`, keys `recKeyQ7'`, axes
  `joinRecordAxis` at `axB0Q7`): acceptance + injective adjacent nodes + `N ≤ char` + `z ≠ 0` /
  `z·z⁻¹`, no summand event.
-/
import Nock.NockVMROM.Thm54.VclL.Compute.NodeRecQ7
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.P8Core.SVCompute.QueueTwins
import Nock.NockVMROM.Thm54.P8Core.SVWalk.ExpAlign
import Nock.NockVMROM.Thm54.Unhosted309Events

set_option autoImplicit false

namespace Nock.RedTeam.Batch1830

open Nock.NockVMROM.Thm54.VclL.Compute.NodeRecQ7

#print axioms mem_activeRecords
#print axioms exportReqFactsQ7S_records
#print axioms pathReqFactsQ7S_records
#print axioms mem_exportRecs
#print axioms mem_pathRecs
#print axioms decodePub_e_oneHot
#print axioms decodePub_sf2f_oneHot
#print axioms label_vcomp
#print axioms row_records_Q7
#print axioms node_records_Q7
#print axioms Nock.NockVMROM.Thm54.VclL.RV.recordViewVCL_valid_axis

end Nock.RedTeam.Batch1830
