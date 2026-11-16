/-
  Nock/RedTeam/Batch1671Thm54VclLRepairT4T6.lean

  Production:
  `P8Core/VclL/DyckRoot.lean`, `Consumers.lean`, `IOUnion.lean`.
-/
import Nock.NockVMROM.Thm54.P8Core.VclL.DyckRoot
import Nock.NockVMROM.Thm54.P8Core.VclL.Consumers
import Nock.NockVMROM.Thm54.P8Core.VclL.IOUnion
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.Unhosted309Events

set_option autoImplicit false

namespace Nock.RedTeam.Batch1671

open Nock Nock.NockVMROM.Thm54.VclL

theorem t5_max_two : (∀ s, lookupsVCL s ≤ 2) ∧ lookupsVCL .s6 = 2 ∧ lookupsVCL .s9 = 2 :=
  ⟨lookupsVCL_le_two, rfl, rfl⟩

end Nock.RedTeam.Batch1671

#print axioms Nock.NockVMROM.Thm54.VclL.dyck_cell_ne_zero
#print axioms Nock.NockVMROM.Thm54.VclL.dyck_natDegree_le
#print axioms Nock.NockVMROM.Thm54.VclL.enc_atom_dyck
#print axioms Nock.NockVMROM.Thm54.VclL.dyck_root_of_atom_collision
#print axioms Nock.NockVMROM.Thm54.VclL.dyckRoots_card_le
#print axioms Nock.NockVMROM.Thm54.VclL.cellDyckRootSeeds_card_le
#print axioms Nock.NockVMROM.Thm54.VclL.mem_cellDyckRootSeeds
#print axioms Nock.NockVMROM.Thm54.VclL.towerSeedSummand_mem_iff
#print axioms Nock.NockVMROM.Thm54.VclL.vclCellDyckRootSummand_shape
#print axioms Nock.NockVMROM.Thm54.VclL.vclCellDyckRootSummand_mem_iff
#print axioms Nock.NockVMROM.Thm54.VclL.hatom_of_not_mem_dyck
#print axioms Nock.NockVMROM.Thm54.VclL.chain_sound_outside
#print axioms Nock.NockVMROM.Thm54.VclL.chainAccF_eq
#print axioms Nock.NockVMROM.Thm54.VclL.fold_lt_goldilocks
#print axioms Nock.NockVMROM.Thm54.VclL.record_axis_exact
#print axioms Nock.NockVMROM.Thm54.VclL.path_record_axis_exact
#print axioms Nock.NockVMROM.Thm54.VclL.path_record_slot
#print axioms Nock.NockVMROM.Thm54.VclL.lookupsVCL_table
#print axioms Nock.NockVMROM.Thm54.VclL.lookupsVCL_le_two
#print axioms Nock.NockVMROM.Thm54.VclL.lookupsVCL_ne_three
#print axioms Nock.NockVMROM.Thm54.VclL.consumer_majorant_rows
#print axioms Nock.NockVMROM.Thm54.VclL.cons_right_unique
#print axioms Nock.NockVMROM.Thm54.VclL.genSkelOp9_record0
#print axioms Nock.NockVMROM.Thm54.VclL.genSkelCons_record0
#print axioms Nock.NockVMROM.Thm54.VclL.genSkel_states
#print axioms Nock.NockVMROM.Thm54.VclL.threeAccIOEvent_card_le
#print axioms Nock.NockVMROM.Thm54.VclL.vclIOEvent_card_le
#print axioms Nock.RedTeam.Batch1671.t5_max_two
