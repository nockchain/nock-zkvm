/-
  Nock/RedTeam/Batch2139Thm54VSQSatisfiable.lean

  New modules `CellTraceHQ`, `WalkTraceHQ`, `ComputeSatHQ`; additive.

  * `CellTraceHQ.cellChipHQ_accepts_honest`: the (fixed) cell twin accepts the honest `𝕂′` fill
    `cellTraceHQ` (inverse `den′⁻¹`, accumulator the prefix sum of `mh·den′⁻¹`) from original-cell
    acceptance of the honest columns, no vanishing `𝕂′` denominator and the `𝕂′` public = the total
    (the side conditions of `cellChipH_accepts_honest`, read at `𝕂′`).
  * `WalkTraceHQ.walkChipHQ_accepts_honest`: the same for the walk twin (`walkChipH_accepts_honest`'s
    conditions at `𝕂′`).
  * `ComputeSatHQ.computeChipVCLHQ_of_H` / `_of_VS`: the zero-extension (Im columns `70..84`) of every
    `computeChipVCLH`-accepted trace is `computeChipVCLHQ`-accepted at the same coin / public vectors
    when their `𝕂′` Im slots vanish — in particular at every VS vector `chalVH` / `pubVH`.
  * gate lemmas `QGates.cellHQ_gates_honest`, `QGates.walkHQ_gates_honest` (`QE.ev` computations).

  Non-vacuity is relative to the existing VS honest acceptance (`cell_acceptedW_gen`,
  `walk_acceptedW_gen`, `computeChipVCLH_honest_sat`), which carries the honest-run hypotheses.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.WalkTraceHQ
import Nock.NockVMROM.Thm54.VclL.Handle.ComputeSatHQ

namespace Nock.RedTeam.Batch2139

open Nock.NockVMROM.Thm54.VclL.Handle

#print axioms QGates.cellHQ_gates_honest
#print axioms QGates.walkHQ_gates_honest
#print axioms CellTraceHQ.cellChipHQ_accepts_honest
#print axioms WalkTraceHQ.walkChipHQ_accepts_honest
#print axioms ComputeSatHQ.slots_cast
#print axioms ComputeSatHQ.imAcc_zero
#print axioms ComputeSatHQ.slotGateQ_val
#print axioms ComputeSatHQ.computeChipVCLHQ_of_H
#print axioms ComputeSatHQ.computeChipVCLHQ_of_VS

end Nock.RedTeam.Batch2139
