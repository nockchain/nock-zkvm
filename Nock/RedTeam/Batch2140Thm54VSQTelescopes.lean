/-
  Nock/RedTeam/Batch2140Thm54VSQTelescopes.lean

  **The `𝕂′` handle telescopes of the three VSQ twins** (REPORT-Q2 item 1,
  first half).  New modules `TeleHQ` (memory) and `TeleCQ` (compute); additive.

  * memory: `qTelescope` (generic, `𝕂′` accumulators, base masks), `denKeyQ_ev` (a key denominator is
    `compress` at the `𝕂′` coins of the lifted key), `cellHQ_inv` / `cellHQ_telescope`
    (`Σ mh·invH′ = (pub₄, pub₅)`), `walkHQ_inv` / `walkHQ_telescopeX` (`Σ invX′ = (pub₄, pub₅)`) /
    `walkHQ_telescopeP` (`Σ mL·invL′ + mR·invR′ = (pub₆, pub₇)`);
  * compute: `slots_castSpec`, `denQH_val'` (compress at the compute `𝕂′` coins of the lifted key),
    `slotGateQ_val_spec`, `slot_atQ` (`slot_core` at `K := 𝕂′`), `termXQ_row` / `termPQ_row`,
    `compute_telescopeQ`, **`compXQ_sum` / `compPQ_sum`** (`Σ_{compXReqs} compress′(lift r)⁻¹ =
    (limbs 15, limbs 21)`, path at `18 / 24`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.TeleHQ
import Nock.NockVMROM.Thm54.VclL.Handle.TeleCQ

namespace Nock.RedTeam.Batch2140

open Nock.NockVMROM.Thm54.VclL.Handle

#print axioms TeleHQ.qTelescope
#print axioms TeleHQ.denKeyQ_ev
#print axioms TeleHQ.cellHQ_inv
#print axioms TeleHQ.cellHQ_telescope
#print axioms TeleHQ.cDenQ_eq
#print axioms TeleHQ.walkHQ_inv
#print axioms TeleHQ.walkHQ_telescopeX
#print axioms TeleHQ.walkHQ_telescopeP
#print axioms TeleHQ.wDenQ_eq
#print axioms TeleCQ.slots_castSpec
#print axioms TeleCQ.denQH_val'
#print axioms TeleCQ.slotGateQ_val_spec
#print axioms TeleCQ.slot_atQ
#print axioms TeleCQ.compute_telescopeQ
#print axioms TeleCQ.compXQ_sum
#print axioms TeleCQ.compPQ_sum

end Nock.RedTeam.Batch2140
