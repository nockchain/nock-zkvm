/-
  Nock/RedTeam/Batch1820Thm54VclLStride2.lean

  Production `Thm54/VclL/Compute/HCFTree.lean`: `treeV` /
  `shapeV` are the serial-labelled `treeV1` / `shapeV1` relabelled by `(st, S) ↦ (st, 2·S)`
  (`treeV_shape` via `mapNTree_comp'`, `shapeV_size_le` via `size_mapNTree'`, `treeV_round`,
  `treeV_label_even`).  `Thm54/VclL/Compute/KeysQ7.lean`: `rowOf`, `keyOfQ7`, `axB0Q7`, `recKeyQ7'`
  (path records defined through `keyOfQ7` at `Sr+2` / `Sr+3`), `recKey_s0'` / `recKey_s9'` at EVERY
  `Sr`, `recKeyQ7'_even`, the key clauses restated at label `2i`, `stride2_disjoint`.
  Negative control (stride 1): `keyOf_forces_collision`, `no_keyOf_at_serial_carrier` — at the serial
  carrier no `keyOf` meets both frame clauses (char > 7).
-/
import Nock.NockVMROM.Thm54.VclL.Compute.KeysQ7
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.P8Core.SVCompute.QueueTwins
import Nock.NockVMROM.Thm54.P8Core.SVWalk.ExpAlign
import Nock.NockVMROM.Thm54.Unhosted309Events

set_option autoImplicit false

namespace Nock.RedTeam.Batch1820

open Nock.NockVMROM.Thm54.VclL.Compute

#print axioms treeV_shape
#print axioms shapeV_size_le
#print axioms treeV_round
#print axioms treeV_label_even
#print axioms stride1_collides
#print axioms stride2_disjoint
#print axioms stride_ge_two_disjoint
#print axioms stride2_no_gap
#print axioms recKey_s0'
#print axioms recKey_s9'
#print axioms recKeyQ7'_even
#print axioms no_forced_collision
#print axioms export_key_clauseQ7'
#print axioms path_key_clauseQ7'
#print axioms axB0Q7_s0
#print axioms axB0Q7_s9
-- negative control (stride 1)
#print axioms keyOf_forces_collision
#print axioms no_keyOf_at_serial_carrier

end Nock.RedTeam.Batch1820
