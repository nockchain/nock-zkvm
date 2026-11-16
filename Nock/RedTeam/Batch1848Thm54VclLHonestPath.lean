/-
  Nock/RedTeam/Batch1848Thm54VclLHonestPath.lean

  **The honest path chip's gates.**  Production: `VclL/Chips/HonestMemPath.lean`.

  * `PathVals`, `pathCol`, `honestPathQ` (112-column interpolated trace), the environment lemmas
    (`pathEKh_trace`, `pathEKh_traceNext`, masks).
  * `path_base_gates_hold` — the `20` path base gates vanish at the honest environment of row `i`
    given `PathBaseFacts` (the length certificate `len + Σ 2^k bit_k = 62` at the last row, the
    chain tiling, the axis fold, `rootIdx` threading, `m` masked off non-last rows).
  * `path_qEqs_hold` / `path_mixed_gates_hold` — the `17` `𝕂′` equations / `34` mixed gates given
    `PathMixedFacts` (root threading, child edge `p' = l + side (r − l)`, the two inverse equations
    at `FiniteIO.compress ⟨γ′, ρ′⟩` of `pxKeyOf` / `pRecOf`, the two accumulators).

  **Labelled.**  `Honest := PEmpty` is still in place.
-/
import Nock.NockVMROM.Thm54.VclL.Chips.HonestMemPath
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.Unhosted309Events

namespace Nock.RedTeam.Batch1848

open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP

#print axioms pathEKh_trace
#print axioms pathEKh_traceNext
#print axioms path_base_gates_hold
#print axioms path_keyVec_x
#print axioms path_keyVec_p
#print axioms path_qEqs_hold
#print axioms path_mixed_gates_hold

end Nock.RedTeam.Batch1848
