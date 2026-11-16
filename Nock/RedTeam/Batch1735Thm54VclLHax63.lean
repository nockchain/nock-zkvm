/-
  Nock/RedTeam/Batch1735Thm54VclLHax63.lean

  **V4c item 3 — `hax63 : programAxisBound < 2^63`.**

  Production: `Thm54/VclL/Compute/Hax63.lean` — `programAxisBound` (the max of the honest `ax`
  column over the generated BFS rows, skeleton-only), `rowAx_le_programAxisBound`,
  `depthOf_le_of_lt_pow`, `hax63_depth` (every row's path has `≤ 62` edges: `genPathRows_ok`'s `h62`),
  `hax63_fold_exact` (T4's exactness at every row at `q > 2^63`), `programAxisBound_le_of_rows`.
-/
import Nock.NockVMROM.Thm54.VclL.Compute.Hax63
import Nock.RedTeam.Batch1259Thm54HonestNonVacuityConcrete
import Nock.RedTeam.Batch1573Thm54ZeroBinderRows193

set_option autoImplicit false

namespace Nock.RedTeam.Batch1735

open Nock Nock.Walk Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.VclL.Compute

section
variable {K : Type} [Field K]

theorem axisBound_op1 : programAxisBound (airReorder (Batch1259.T0 (K := K))) = 0 := by
  rw [Batch1259.air0, programAxisBound, Batch1259.bfsRows0]
  simp [skelNode, genSkelOp1, honestAx]

theorem axisBound_op2 : programAxisBound (airReorder (Batch1573.T2 (K := K))) = 0 := by
  rw [Batch1573.air2, programAxisBound]
  simp [Batch1571.bfsRows_three_leaves, skelNode, genSkelOp1, genSkelOp2, honestAx]

theorem axisBound_op9 : programAxisBound (airReorder (Batch1573.T9 (K := K))) = 2 := by
  rw [Batch1573.air9, programAxisBound]
  simp [bfsRows_two_leaves, skelNode, genSkelOp1, genSkelOp9, honestAx, op9ParentFormula,
    op9ParentTail, op9AxisAtom]

theorem hax63_op1 : programAxisBound (airReorder (Batch1259.T0 (K := K))) < 2 ^ 63 := by
  rw [axisBound_op1]; norm_num
theorem hax63_op2 : programAxisBound (airReorder (Batch1573.T2 (K := K))) < 2 ^ 63 := by
  rw [axisBound_op2]; norm_num
theorem hax63_op9 : programAxisBound (airReorder (Batch1573.T9 (K := K))) < 2 ^ 63 := by
  rw [axisBound_op9]; norm_num

end

#print axioms rowAx_le_programAxisBound
#print axioms depthOf_le_of_lt_pow
#print axioms hax63_depth
#print axioms hax63_fold_exact
#print axioms programAxisBound_le_of_rows
#print axioms axisBound_op1
#print axioms axisBound_op2
#print axioms axisBound_op9
#print axioms hax63_op9

end Nock.RedTeam.Batch1735
