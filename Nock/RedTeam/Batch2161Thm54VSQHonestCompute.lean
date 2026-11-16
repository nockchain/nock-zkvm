/-
  Nock/RedTeam/Batch2161Thm54VSQHonestCompute.lean

  New module `HonestCompQ`; additive.

  * `compTraceQ` / `compPolyQ`: the honest `𝕂′` compute columns (slot inverses and accumulators refilled
    over `𝕂′`, Re limbs `43..57`, Im limbs `70..84`);
  * `slotGateQ_eq_evalMQ`, `rowQ_facts`, `walk_gates_Q`;
  * **`computeChipVCLHQ_honest_sat`**: `computeChipVCLHQ` accepts `compPolyQ` with preprocessing, under
    `computeChipVCLH_honest_sat`'s hypotheses read at the `𝕂′` coins, the `𝕂′` terminals as Re / Im limbs
    and the priced `𝕂′` pole event `NotBadRow`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.HonestCompQ

namespace Nock.RedTeam.Batch2161

open Nock.NockVMROM.Thm54.VclL.Handle

#print axioms HonestCompQ.slotGateQ_eq_evalMQ
#print axioms HonestCompQ.rowQ_facts
#print axioms HonestCompQ.walk_gates_Q
#print axioms HonestCompQ.computeChipVCLHQ_honest_sat

end Nock.RedTeam.Batch2161
