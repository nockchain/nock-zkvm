/-
  Nock/RedTeam/Batch4837Thm54J8ComplL6.lean

  The honest record of a run (`honestJ8Of`: common orbit height, nodes `ω^i`, the walk at the spec rows, the J rows,
  bad list `badList [(χ₁₃, |W|)] fams`) and the obligation groups discharged so far: compute (with `hpair` and
  `goodC`), staging, nodes, budget, claim, weights and figure, J chip, statics, cell table, J-8 walk; the concrete
  atom part `avOf` (atom table and atom walk traces and publics) and its staging; `obligations_of_run` and the
  Goldilocks statement `complJ8`, which carry the atom table, atom walk and balance obligations as `OpenJ8`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of

namespace Nock.RedTeam.Batch4837

open Nock.NockVMROM.Thm54.VclL.Handle

#print axioms ComplJ8Of.honestJ8Of
#print axioms ComplJ8Of.compute_group
#print axioms ComplJ8Of.staged_run
#print axioms ComplJ8Of.nodes_group
#print axioms ComplJ8Of.budget_run
#print axioms ComplJ8Of.claim_run
#print axioms ComplJ8Of.bad_group
#print axioms ComplJ8Of.jOK_run
#print axioms ComplJ8Of.stat_run
#print axioms ComplJ8Of.dRowW_split
#print axioms ComplJ8Of.famCellV_good
#print axioms ComplJ8Of.famCellH_OK
#print axioms ComplJ8Of.cellOK_run
#print axioms ComplJ8Of.walk_dRow_split
#print axioms ComplJ8Of.famWalkV_good
#print axioms ComplJ8Of.famWalkH_OK
#print axioms ComplJ8Of.walkOK_run

#print axioms ComplJ8Of.avOf
#print axioms ComplJ8Of.stA_run
#print axioms ComplJ8Of.stV_run
#print axioms ComplJ8Of.famsOf_facts
#print axioms ComplJ8Of.obligations_of_run
#print axioms ComplJ8Of.dvdOK_of_rows
#print axioms ComplJ8Of.cells_pos
#print axioms ComplJ8Of.complJ8

end Nock.RedTeam.Batch4837
