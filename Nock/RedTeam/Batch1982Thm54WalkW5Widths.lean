/-
  Nock/RedTeam/Batch1982Thm54WalkW5Widths.lean

  **The widths of the composed shape, MEASURED, and the
  cells/step arithmetic on the six study programs.**

  * Widths (`rfl` on the elaborated shapes): `shapeVW` cell table **225**, walk table **132**
    (`LayoutW` 21 / 72 / 39); `shapeV` (VCL-L) cell **225**, path **112**.  The cell table is unchanged.
  * The numerators are checked below by `decide`; the per-program walk numerator is strictly smaller
    on all six (unpadded).
-/
import Nock.NockVMROM.Thm54.VclL.Chips.StandaloneVCLW

set_option autoImplicit false

namespace Nock.RedTeam.Batch1982

open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP

theorem walk_cell_width (hT hP : ℕ) : ((shapeVW hT hP).table (tCW hT hP)).width = 225 := rfl
theorem walk_walk_width (hT hP : ℕ) : ((shapeVW hT hP).table (tWW hT hP)).width = 132 := rfl
theorem vcl_cell_width (hT hP : ℕ) : ((shapeV hT hP).table (tC hT hP)).width = 225 := rfl
theorem vcl_path_width (hT hP : ℕ) : ((shapeV hT hP).table (tP hT hP)).width = 112 := rfl

/-- Memory cells (unpadded) with the walk vs VCL-L, per program `(N, D, P, T)`. -/
def cellsW (D T : ℕ) : ℕ := 225 * D + 132 * T
def cellsP (D P : ℕ) : ℕ := 225 * D + 112 * P

theorem dec_100 : cellsW 222 200 = 76350 ∧ cellsP 222 400 = 94750 := by decide
theorem add_100 : cellsW 331 303 = 114471 ∧ cellsP 331 808 = 164971 := by decide
theorem mul_10 : cellsW 391 555 = 161235 ∧ cellsP 391 2100 = 323175 := by decide
theorem ifib_12 : cellsW 1253 1617 = 495369 ∧ cellsP 1253 4071 = 737877 := by decide
theorem fib_12 : cellsW 688 1130 = 303960 ∧ cellsP 688 2288 = 411056 := by decide
theorem ack_22 : cellsW 102 81 = 33642 ∧ cellsP 102 168 = 41766 := by decide

end Nock.RedTeam.Batch1982
