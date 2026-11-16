/-
  Nock/RedTeam/Batch1794Thm54VclLRowModel.lean

  **The cell table's per-row gate equations ⇒
  `Table.RowOK`** (brief R-V2b (1)).  Production: `Thm54/VclL/Chips/QEval.lean`
  (the `𝕂′` reading of a `QE` through `Quad.mk`: `ev_add/sub/mul/scale/base/rlc`,
  `ev_eq_zero_of_gates`) and `Thm54/VclL/Chips/RowModel.lean` (`natOf` through `PrimeFieldElems`,
  `cellRow_gates`, `rowOK_of_gates`, `cellTable_serial`, `cellTable_accepts`).

  Negative control `rowGates_not_rowOK`: one row's gates do NOT range its child limbs — at
  `ZMod 97`, a row with `loL = 2^62` meets every per-row gate (`RowGates`) and is not `RowOK`.  The
  child-limb ranges come from the validity lookup (`ValidityServed`) and the providing row's bits
  (`rowOK_of_gates`), as designed.
-/
import Nock.NockVMROM.Thm54.VclL.Chips.RowModel
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.Unhosted309Events

namespace Nock.RedTeam.Batch1794

open Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.ComputeTable (FP)

#print axioms ev_mul
#print axioms ev_rlc
#print axioms ev_eq_zero_of_gates
#print axioms natOf_natCast
#print axioms eval_bitSum
#print axioms cellRow_gates
#print axioms rowOK_of_gates
#print axioms cellTable_rowGates
#print axioms cellTable_serial
#print axioms cellTable_accepts

/-- The NC row: weighted left child with `loL = 2^62` (out of range), `lo = (2^62 + 1) mod 97`. -/
def ncRow : CellRow 97 (ZMod 97) :=
  ⟨⟨0, 0, 0, true, true, 0, 0, (2 ^ 62 + 1) % 97, 0, 2 ^ 62, 0, 0, 0, 0, 1, 1⟩,
    FP.cons 1 ⟨1, 0, 0⟩ ⟨1, 0, 0⟩, ⟨1, 0, 0⟩, ⟨1, 0, 0⟩⟩

theorem rowGates_not_rowOK : RowGates (1 : ZMod 97) ncRow ∧ ¬ RowOK (1 : ZMod 97) ncRow := by
  refine ⟨⟨rfl, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩, ?_⟩
  intro h
  exact absurd h.loL_lt (by decide)

#print axioms rowGates_not_rowOK

end Nock.RedTeam.Batch1794
