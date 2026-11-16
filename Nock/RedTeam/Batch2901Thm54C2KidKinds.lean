/-
  Nock/RedTeam/Batch2901Thm54C2KidKinds.lean

  **The kid-kind gates.**
  Re-proved by the existing kernel theorems: width 123 (`widthHX_val`),
  degree `≤ 4` (`gatesHX_degree`), `keyOK` (`slotPairsX_keyOK`, `walkGatesX_keyOK`), serial-free
  (`arithGatesX_serialFree`).  `KidKinds` is derived (`RowDecodeVSX.kidKinds_of_gates`) and is a
  clause of `LocalVSX.RowSemX`; `RowsOKX` has no `kinds` premise.  Chip-level negative control:
  `ChipHX.swapped_s10T_child_rejected`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVSX

namespace Nock.RedTeam.Batch2901

open Nock Nock.Edit
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX
open Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVSX

example : (kidKindG (F := ℚ)).length = 23 ∧ widthHX = 123 := by decide

/-- The kid-kind gates read no serial-capable column and have degree 2. -/
example : (kidKindG (F := ℚ)).all serialFreeX = true ∧
    (kidKindG (F := ℚ)).all (fun g => decide (g.degree = 2)) = true := by decide +kernel

/-- Every real child position of every state is covered (`kidFormsX` lists exactly the non-chain
child formula handles of `childrenX`). -/
example : (List.range nStates).all (fun j =>
    ((childrenX j).zipIdx.filter (fun c => !((j == sS10 && c.2 == 2) || (j == sS10L && c.2 == 0)))).length
      = (kidFormsX.filter (fun jh => jh.1 == j)).length) = true := by decide

#print axioms kid_cell
#print axioms swapped_s10T_child_rejected
#print axioms kidKinds_of_gates
#print axioms holdsN_of_rowsVSX
#print axioms kidKinds_load_bearing
#print axioms widthHX_val
#print axioms gatesHX_degree
#print axioms slotPairsX_keyOK
#print axioms walkGatesX_keyOK
#print axioms arithGatesX_serialFree
#print axioms accGatesHX_serialFree
#print axioms eqGatesX_ok

end Nock.RedTeam.Batch2901
