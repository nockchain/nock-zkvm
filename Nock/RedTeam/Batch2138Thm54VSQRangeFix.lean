/-
  Nock/RedTeam/Batch2138Thm54VSQRangeFix.lean

  * Fix (edit of `MemHQ.lean`): `CellHQ.invHQ := 32`, `CellHQ.accHQ := 34` (were `36 / 38`, beyond the
    template's `36` roles); width `238` and `shapeVSQ` unchanged.
  * `RangeHQ.cellHQ_range` / `walkHQ_range`: every base read `< baseCols`, every `𝕂`-role read
    `< extCols` (cell `130 / 36`, walk `25 / 47`, every `kroots`); no equality / extension-only gates.
  * `RangeHQ.computeHQ_range` (kernel, templates at `F = ℚ`, `δ = 7`): columns `< 85` (`𝕂`-variables
    `i + 2 < 85`), challenge limbs `< 18`, public limbs `< 27`.
  * positive controls: `cell_old_gate_flagged` (the old role-`36` gate fails `mixBelow 36 130`),
    `compute_range_flags` (a read at `𝕂`-variable `83` is flagged).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.RangeHQ
import Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ

namespace Nock.RedTeam.Batch2138

open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.RangeHQ
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ

#print axioms colsBelow_mono
#print axioms mixBelow_mono
#print axioms cellHQ_range
#print axioms walkHQ_range
#print axioms computeHQ_range
#print axioms cell_old_gate_flagged
#print axioms compute_range_flags
#print axioms CellHQ.gates_deg_all
#print axioms cellChipHQ_width
#print axioms cellChipHQ_restrict_sat
#print axioms cellHQ_reads
#print axioms cellHQ_reads_control
#print axioms walkHQ_reads
#print axioms cell_factsQ
#print axioms walk_factsQ
#print axioms compute_factsQ

end Nock.RedTeam.Batch2138
