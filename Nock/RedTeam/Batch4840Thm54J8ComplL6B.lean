/-
  Nock/RedTeam/Batch4840Thm54J8ComplL6B.lean
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBal
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Enc

namespace Nock.RedTeam.Batch4840

open Nock.NockVMROM.Thm54.VclL.Handle

#print axioms ComplJ8OfBal.sum_serial
#print axioms ComplJ8OfBal.lTerm_cell
#print axioms ComplJ8OfBal.rTerm_cell
#print axioms ComplJ8OfBal.vSum_zero
#print axioms ComplJ8OfBal.acsP_closed
#print axioms ComplJ8OfBal.avT_zero_of
#print axioms ComplJ8OfBal.balV3_run
#print axioms ComplJ8OfBal.coinsJ_eq
#print axioms ComplJ8OfBal.coinsJX_eq
#print axioms ComplJ8OfBal.h3J_run
#print axioms ComplJ8OfBal.h1J_run
#print axioms ComplJ8OfBal.bfsTN_node
#print axioms ComplJ8OfBal.walkGen_nodes_perm
#print axioms ComplJ8OfBal.mx_spec
#print axioms ComplJ8OfBal.reads_slot
#print axioms ComplJ8OfBal.walkRows_node_cells
#print axioms ComplJ8OfBal.cxT_eq_wxT
#print axioms ComplJ8OfBal.balF1_run
#print axioms ComplJ8OfBal.balF_run
#print axioms ComplJ8OfBal.walkGen_dummy
#print axioms ComplJ8OfBal.walkRows_nodes_mem
#print axioms ComplJ8OfBal.preads_shape
#print axioms ComplJ8OfBal.wPairs_idxN
#print axioms ComplJ8OfBal.vs_eq
#print axioms ComplJ8OfBal.vs_nil
#print axioms ComplJ8OfBal.mxA_spec
#print axioms ComplJ8OfBal.acs_cell
#print axioms ComplJ8OfBal.axT_eq_vxT
#print axioms ComplJ8OfBal.axT_zero
#print axioms ComplJ8OfBal.comb_mem_acs
#print axioms ComplJ8OfBal.balF2_run
#print axioms ComplJ8OfBal.balF_closed
#print axioms ComplJ8OfBal.aE0_trace_col
#print axioms ComplJ8OfBal.aHx_two
#print axioms ComplJ8OfBal.acs_two
#print axioms ComplJ8OfBal.vhX_eq
#print axioms ComplJ8OfBal.balV2_of_inc
#print axioms ComplJ8OfBal.mhx_wrA
#print axioms ComplJ8OfBal.stepF_two
#print axioms ComplJ8OfBal.fold_two
#print axioms ComplJ8OfBal.dC_key
#print axioms ComplJ8OfBal.combOf_two
#print axioms ComplJ8OfBal.row_two
#print axioms ComplJ8OfBal.newBA_inc
#print axioms ComplJ8OfBal.incT_run
#print axioms ComplJ8OfBal.balV2_run
#print axioms ComplJ8Enc.dtWE_child
#print axioms ComplJ8Enc.dtWE_root
#print axioms ComplJ8Enc.walkRow0E_base
#print axioms ComplJ8Enc.walkRow0E_K
#print axioms ComplJ8Enc.walkOk_honest_listE
#print axioms ComplJ8Enc.walkChip_honest_listE
#print axioms ComplJ8Enc.walkChipHQK_honest_listE
#print axioms ComplJ8Enc.walkChipJ8_honest_listE
#print axioms ComplJ8Enc.wColBE_cong
#print axioms ComplJ8Enc.walkTrWE_staged
#print axioms ComplJ8Enc.cellRowsBE_baseFacts
#print axioms ComplJ8Enc.cellRowsBE_cons
#print axioms ComplJ8Enc.cellRowsBE_atomL
#print axioms ComplJ8Enc.cellRowsBE_atomR
#print axioms ComplJ8Enc.cellChip_honest_listE
#print axioms ComplJ8Enc.cellChipHQ_honest_listE
#print axioms ComplJ8Enc.cellChip_honest_list_bindE
#print axioms ComplJ8Enc.cellChipHQKW_honest_listE
#print axioms ComplJ8Enc.cellChipHQKW_honest_list_bindE
#print axioms ComplJ8Enc.rowsBE_base
#print axioms ComplJ8Enc.cellTrME_staged
#print axioms ComplJ8Of.encR_congr
#print axioms ComplJ8Of.encR_small
#print axioms ComplJ8Of.cellOK_run
#print axioms ComplJ8Of.walkOK_run
#print axioms ComplJ8Of.staged_run
#print axioms ComplJ8Of.obligations_of_run
#print axioms ComplJ8Of.complJ8
#print axioms ComplJ8OfBal.wxKey_eq0
#print axioms ComplJ8OfBal.wxKey_eq
#print axioms ComplJ8OfBal.cxT_eq_wxT
#print axioms ComplJ8OfBal.balF_closed
#print axioms ComplJ8OfBal.balV2_run

#print axioms ComplJ8OfBal.sum_sumAt
#print axioms ComplJ8OfBal.sum_map_ite'
#print axioms ComplJ8OfBal.cellPairs_sum
#print axioms ComplJ8OfBal.sum_flatMap_two
#print axioms ComplJ8OfBal.bigPairs_sum
#print axioms ComplJ8OfBal.vTerm_rowBE
#print axioms ComplJ8OfBal.ct_split
#print axioms ComplJ8OfBal.cvSum_gen
#print axioms ComplJ8OfBal.claimVec_kOf
#print axioms ComplJ8OfBal.addCells_inv
#print axioms ComplJ8OfBal.cellsOfRoots_inv
#print axioms ComplJ8OfBal.enc_leaf2
#print axioms ComplJ8OfBal.ekA_role
#print axioms ComplJ8OfBal.ekA_leaf
#print axioms ComplJ8OfBal.cells_cl_run
#print axioms ComplJ8OfBal.ccT_eq
#print axioms ComplJ8OfBal.cvT_run
#print axioms ComplJ8OfBal.newBA_mb
#print axioms ComplJ8OfBal.horner_two
#print axioms ComplJ8OfBal.mbT_run
#print axioms ComplJ8OfBal.keyVec_mb
#print axioms ComplJ8OfBal.big_key
#print axioms ComplJ8OfBal.child_big
#print axioms ComplJ8OfBal.bt_bh
#print axioms ComplJ8OfBal.claim_sum
#print axioms ComplJ8OfBal.pin_sum
#print axioms ComplJ8OfBal.balV1_run
#print axioms ComplJ8OfBal.balV_closed

end Nock.RedTeam.Batch4840
