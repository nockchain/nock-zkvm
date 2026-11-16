/-
  Nock/RedTeam/Batch2050Thm54VSHonest.lean

  1. The cell rows of the honest memory datum of the run are `cellRows0 … (demT HJ.t).cells`
     (`honestJ_cellRows_eq`, `rfl`), and hash-consing carries to `cellRows0` beyond `idx`
     (`cellRows0_inj`, `cellRows0_noun_iff`, `cellRow0_idL_iff`).
  2. `rowOfSkel` builds the honest noun row of every generated row; `airReorder_rowShape`: every row of
     the AIR-reordered tree has the per-opcode semantic content `RowN.Sem`.
  3. `honest_row_base_gates`: the 52 arithmetic and 49 equality base gates of `computeChipVCLH` hold
     on the honest handle row of EVERY row of a run (generic; hypotheses: the OP5 operand atom bound
     and the first-row publics).  Both toys concretely (`toy1_gates`, `toy2_gates`), and a
     discriminating negative control (`toy1_bad_gate_fails`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.HonestToys

set_option autoImplicit false

namespace Nock.RedTeam.Batch2050

open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH

/-- Which gates are covered: 52 + 49 base gates; 18 + 12 remain. -/
theorem coverage_receipt :
    (arithGates (F := ℚ)).length = 52 ∧ (eqGates (F := ℚ)).length = 49 ∧
    (accGatesH (F := ℚ)).length = 18 ∧ (kGatesH (F := ℚ)).length = 12 := by
  decide +kernel

#print axioms honestJ_cellRows_eq
#print axioms honestVCLJ_of_run_t
#print axioms cellRows0_inj
#print axioms cellRows0_noun_iff
#print axioms cellRow0_idL_iff
#print axioms fdN_spec
#print axioms airReorder_rowShape
#print axioms arith_hold
#print axioms eq_hold
#print axioms base_gates_hold
#print axioms honest_row_base_gates
#print axioms toy1_gates
#print axioms toy2_gates
#print axioms toy1_bad_gate_fails
#print axioms coverage_receipt

end Nock.RedTeam.Batch2050
