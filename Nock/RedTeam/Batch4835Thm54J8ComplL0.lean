/-
  Nock/RedTeam/Batch4835Thm54J8ComplL0.lean

  The
  interface: `J8Data` (the generator DATA of one run at a generic modulus `p`: rows, calls, ids, regs, J nouns,
  `idx` / `rk` / `lay`, cells, big atoms, atom cell list, `H = hdlB`, `pd = pdX`, path / atom-walk reads and walk
  rows, compute base columns, J rows with the `mv` fix, multiplicities `mv mx mh mb mxA mhA`, atom inc data),
  `j8DataOf p Rg Rt hgen`, the J-8 instance `J8Counts` / `j8CountsOf`; sanity lemmas.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data

namespace Nock.RedTeam.Batch4835

open Nock.NockVMROM.Thm54.VclL.Handle

#check @ComplJ8Data.J8Data
#check @ComplJ8Data.j8DataOf
#check @ComplJ8Data.j8CountsOf
#print axioms ComplJ8Data.cells_nodup
#print axioms ComplJ8Data.cells_closed
#print axioms ComplJ8Data.mem_cells_of_subs
#print axioms ComplJ8Data.hdlOK_hdlP
#print axioms ComplJ8Data.hdlOK
#print axioms ComplJ8Data.hdlP_eq_hdl
#print axioms ComplJ8Data.handle_noun_cases
#print axioms ComplJ8Data.claim_mem_cells
#print axioms ComplJ8Data.j8_cells_nodup
#print axioms ComplJ8Data.toy_cells_H
#print axioms ComplJ8Data.cnt_append
#print axioms ComplJ8Data.bumpAll_getD
#print axioms ComplJ8Data.mv_eq_cnt
#print axioms ComplJ8Data.mx_eq_cnt
#print axioms ComplJ8Data.mh_eq_cnt
#print axioms ComplJ8Data.mb_eq_cnt
#print axioms ComplJ8Data.mxA_eq_cnt
#print axioms ComplJ8Data.mhA_eq_mxA
#print axioms ComplJ8Data.totalW_append
#print axioms ComplJ8Data.totalW_eq_sum_cnt
#print axioms ComplJ8Data.totalW_eq_of_cnt
#print axioms ComplJ8Data.cnt_provRecs
#print axioms ComplJ8Data.count_flatten_expand
#print axioms ComplJ8Data.balancedN_facts
#print axioms ComplJ8Data.balV_facts
#print axioms ComplJ8Data.balW_facts
#print axioms ComplJ8Data.balX_facts
#print axioms ComplJ8Data.balMB_facts
#print axioms ComplJ8Data.balAW_facts
#print axioms ComplJ8Data.vRecs_range
#print axioms ComplJ8Data.balV_facts'
#print axioms ComplJ8Data.walkGen_node
#print axioms ComplJ8Data.pathReads_root
#print axioms ComplJ8Data.ws_node_mem
#print axioms ComplJ8Data.wRecs_range
#print axioms ComplJ8Data.balW_facts'
#print axioms ComplJ8Data.mbRecs_range
#print axioms ComplJ8Data.awRecs_range
#print axioms ComplJ8Data.balMB_facts'
#print axioms ComplJ8Data.balAW_facts'
#print axioms ComplJ8Data.selS_eval
#print axioms ComplJ8Data.xEnt_cell
#print axioms ComplJ8Data.xcons_row_range
#print axioms ComplJ8Data.xRecs_compute_range
#print axioms ComplJ8Data.xRecs_range
#print axioms ComplJ8Data.balX_facts'
#print axioms ComplJ8Data.chainW_read
#print axioms ComplJ8Data.nodeW_read
#print axioms ComplJ8Data.blockW_read
#print axioms ComplJ8Data.honestJ8_read
#print axioms ComplJ8Data.keysOf_entsX_head
#print axioms ComplJ8Data.mvFixP_mem
#print axioms ComplJ8Data.jReads_range
#print axioms ComplJ8Data.balX_facts''

end Nock.RedTeam.Batch4835
