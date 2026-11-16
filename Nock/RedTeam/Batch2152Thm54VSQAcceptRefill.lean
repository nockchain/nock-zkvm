/-
  Nock/RedTeam/Batch2152Thm54VSQAcceptRefill.lean

  New module `AcceptVSQ`;
  additive.

  * `chiK`, the re-filled message `msgK` (compute `refillP`, cell `refillC`, walk `refillW`, requests `rhoK`,
    memory message `(y, yHK)`);
  * **`acceptsK`**: `AcceptsG (toVSV V) msgK (chiK χ γ ρ)` at every accepted VSQ coin outside the two `𝕂′` handle
    summands, at every pole-free `(γ, ρ)`; terminals from `kX_identity` / `kP_identity`;
  * `tracesK_off` (agreement off the handle blocks), `evX_congr` / `evP_congr`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptVSQ

namespace Nock.RedTeam.Batch2152

open Nock.NockVMROM.Thm54.VclL.Handle

#print axioms AcceptVSQ.claimValSum_chiK
#print axioms AcceptVSQ.goodC_K
#print axioms AcceptVSQ.totX_eq
#print axioms AcceptVSQ.totP_eq
#print axioms AcceptVSQ.yHK_eq
#print axioms AcceptVSQ.acceptsK
#print axioms AcceptVSQ.tracesK_off
#print axioms AcceptVSQ.evX_congr
#print axioms AcceptVSQ.evP_congr

end Nock.RedTeam.Batch2152
