/-
  Nock/RedTeam/Batch2067Thm54VSValIO.lean

  Additive.
  New module `Thm54/VclL/Handle/ValIOVS.lean`:
  * `ioSpecVS`: validity IO coins `(χ₄ + χ₆√δ, χ₅ + χ₇√δ)`, injective on `{4, 5, 6, 7}`;
  * `valReqs` / `valProvs`: coin-free validity record lists (claim records reading `χ₂ χ₃`, then the
    restricted cell twin's internal consumers; providers `(vKeyP, mv)`), zero coins and publics;
  * `valSummand`: coins `{4, 5, 6, 7}`, `dep = coinsBelow frameVS 1`, weight
    `ioFailureUnionBound 5 (3 + 2T) T |𝕂′|`; `valSummand_mass` (`/ |𝕂|⁴ = … 1 / |𝕂|²`);
  * `valLists_at`: at any coin the coin-free lists are the chip-typed lists at the real chals / publics;
  * `claims_provided_VS'`: `claims_provided_VS` with `hio` discharged outside `valSummand`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ValIOVS

namespace Nock.RedTeam.Batch2067

open Nock.NockVMROM.Thm54.VclL.Handle.ValIOVS

#print axioms ioSpecVS_disj
#print axioms valLists_staged
#print axioms valSummand
#print axioms mem_valSummand
#print axioms valSummand_mass
#print axioms valLists_at
#print axioms claims_provided_VS'

end Nock.RedTeam.Batch2067
