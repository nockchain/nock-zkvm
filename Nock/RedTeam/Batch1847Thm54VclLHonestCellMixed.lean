/-
  Nock/RedTeam/Batch1847Thm54VclLHonestCellMixed.lean

  **The honest cell table's mixed gates.**  Production: `VclL/Chips/HonestMemCellMixed.lean`.

  * `cell_mixed_gates_hold` — the `44` mixed gates of `Cell.mixedGates` vanish at the honest
    environment (`honestCellQ … vals`, gathered `𝕂`-environment) of row `i`, given
    `CellMixedFacts` (the semantic content of the `22` `𝕂′` equations: `p = FP.cons z l r`,
    atom pins, the five inverse equations at `FiniteIO.compress ⟨γ′, ρ′⟩` of the semantic key
    vectors, the zero-weight pins, the two accumulators' init / step / terminal) and
    `CellBaseFacts`.  `cell_qEqs_hold` is the `QE.ev` form; `cellEKh_trace` / `_traceNext` read the
    gathered role values off the interpolated columns.

  **Labelled.**  `Honest := PEmpty` is still in place.
-/
import Nock.NockVMROM.Thm54.VclL.Chips.HonestMemCellMixed
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.Unhosted309Events

namespace Nock.RedTeam.Batch1847

open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP

#print axioms cellEKh_trace
#print axioms cellEKh_traceNext
#print axioms cell_keyVec_v
#print axioms cell_keyVec_x
#print axioms cell_qEqs_hold
#print axioms cell_mixed_gates_hold

end Nock.RedTeam.Batch1847
