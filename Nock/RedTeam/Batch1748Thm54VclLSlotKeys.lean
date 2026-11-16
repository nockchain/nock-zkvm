/-
  Nock/RedTeam/Batch1748Thm54VclLSlotKeys.lean

  **The generator at the repaired compute chip.**
  Production: `TraceGen/GenSlotKeys.lean`.

  * the 3-slot keys (`rowSlotKeys`, `demandOfRowsD`, reads `<= 3N`), slot 0 = `(formula, 3)` at every
    row the generator emits (`skelRows_slot0`), `fIdxOf` / `fIdx_mem_table` / `fIdx_decode`,
    `slot0_in_shallowLookups`, and `formula_key_clause_generated` (honest agreement with
    `FormulaLookup.formula_key_clause`; `xkeyOf_idx`);
  * fixtures below (`K := Rat`): `[1 5]` (one row, `fIdx = 0`) and `[[1 0] [1 1]]` (cons + two OP1).

  `mx = P + shallow`, compare `3N`:

  | program  | N     | shallow (was) | shallow (now) | mx (was) | mx (now) | 3N    | maxLook |
  |----------|-------|---------------|---------------|----------|----------|-------|---------|
  | dec 100  | 1200  | 799           | 1801          | 1199     | 2201     | 3600  | 3       |
  | dec 1000 | 12000 | 7999          | 18001         | 11999    | 22001    | 36000 | 3       |
  | add 100  | 1415  | 911           | 2024          | 1719     | 2832     | 4245  | 3       |
  | mul 10   | 2429  | 1553          | 3428          | 3653     | 5528     | 7287  | 3       |
  | fib 12   | 30979 | 19945         | 45655         | 22233    | 47943    | 92937 | 3       |
  | ifib 12  | 5605  | 3223          | 7612          | 7294     | 11683    | 16815 | 3       |
  | ack 22   | 833   | 536           | 1230          | 704      | 1398     | 2499  | 3       |

  (the compute-side export lookups alone `<= 3N` by `export_consumer_majorant`), `maxLook = 3`.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenSlotKeys
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.Unhosted309Events

set_option autoImplicit false
set_option maxRecDepth 20000

namespace Nock.RedTeam.Batch1748

open Nock Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.TraceGen

abbrev op1 : Noun := .cell (.atom 1) (.atom 5)
abbrev c0 : Noun := .cell (.atom 1) (.atom 0)
abbrev c1 : Noun := .cell (.atom 1) (.atom 1)
abbrev consF : Noun := .cell c0 c1

/-- The row the generator emits for `[1 5]` (the `genComputeSkeleton` OP1 arm, as written there). -/
def rows1 : List (GenComputeRow Rat) :=
  [skelNode (genSkelOp1 (.atom 0) op1 (.atom 5) (.atom 1)) [⟨op1, .atom 5, 3, 0⟩]]

/-- The rows of `[[1 0] [1 1]]` in BFS order (the autocons arm and its two OP1 children). -/
def rows3 : List (GenComputeRow Rat) :=
  [skelNode (genSkelCons (.atom 0) c0 c1 (.atom 0) (.atom 1)) [⟨consF, c1, 3, 0⟩],
   skelNode (genSkelOp1 (.atom 0) c0 (.atom 0) (.atom 1)) [⟨c0, .atom 0, 3, 0⟩],
   skelNode (genSkelOp1 (.atom 0) c1 (.atom 1) (.atom 1)) [⟨c1, .atom 1, 3, 0⟩]]

/-- One row, one slot key `([1 5], 3)`, `fIdx = 0`. -/
theorem fixture1 :
    rows1.length = 1 ∧ (demandOfRowsD rows1).reads = [(op1, 3)] ∧
      (rows1.map (fun g => fIdxOf (demandOfRowsD rows1) g)) = [0] := by decide +kernel

/-- Cons + two OP1: three rows, three slot-0 keys (all axis 3, depth 1), serials `0, 1, 2`. -/
theorem fixture3 :
    rows3.length = 3 ∧ (demandOfRowsD rows3).reads = [(consF, 3), (c0, 3), (c1, 3)] ∧
      (rows3.map (fun g => fIdxOf (demandOfRowsD rows3) g)) = [0, 1, 2] ∧
      (demandOfRowsD rows3).reads.length ≤ 3 * rows3.length := by decide +kernel

/-- NC: the pre-repair demand drops the OP1 rows' slot 0 (two of three reads missing). -/
theorem nc_prerepair_drops_slot0 : (demandOfRows rows3).reads = [(consF, 3)] := by decide +kernel

/-- The shallow lookups of the repaired fixture include every row's formula (`mx` counts them). -/
theorem fixture3_shallow :
    (shallowLookups (demandOfRowsD rows3).reads).length = 3 := by decide +kernel

end Nock.RedTeam.Batch1748

#print axioms Nock.RedTeam.Batch1748.fixture1
#print axioms Nock.RedTeam.Batch1748.fixture3
#print axioms Nock.RedTeam.Batch1748.nc_prerepair_drops_slot0
#print axioms Nock.RedTeam.Batch1748.fixture3_shallow
#print axioms Nock.NockVMROM.Thm54.VclL.slot_active_iff
#print axioms Nock.NockVMROM.Thm54.VclL.rowSlotKeys_length_le_three
#print axioms Nock.NockVMROM.Thm54.VclL.demandOfRowsD_reads_le
#print axioms Nock.NockVMROM.Thm54.VclL.rowSlotKeys_eq_inline_append
#print axioms Nock.NockVMROM.Thm54.VclL.demandOfRows_reads_sub
#print axioms Nock.NockVMROM.Thm54.VclL.genComputeSkeleton_slot0
#print axioms Nock.NockVMROM.Thm54.VclL.skelRows_slot0
#print axioms Nock.NockVMROM.Thm54.VclL.fIdx_mem_table
#print axioms Nock.NockVMROM.Thm54.VclL.fIdx_decode
#print axioms Nock.NockVMROM.Thm54.VclL.slot0_in_shallowLookups
#print axioms Nock.NockVMROM.Thm54.VclL.xkeyOf_idx
#print axioms Nock.NockVMROM.Thm54.VclL.formula_key_clause_generated
