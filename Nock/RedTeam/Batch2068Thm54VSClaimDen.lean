/-
  Nock/RedTeam/Batch2068Thm54VSClaimDen.lean

  Additive.
  New module `Thm54/VclL/Handle/ClaimDenVS.lean`:
  * `claim_census_injΛ` / `claimH_genuineΛ`: the claim census at any fuel `Λ ≥ fuelChip`;
  * `claimFuel` = `max fuelChip (claim leaves)` (the claim's leaf count is public and unchecked);
  * `claim_table_VS`: `TableAccepts` of the decoded restricted cell table at VS (outside `valSummand`,
    `zVS ≠ 0` a hypothesis);
  * `claim_handles_VS`: every claim noun's public handle at `natOf (idx : 𝔽)` denotes it (outside
    `valSummand` and the claim census at `claimFuel`; seed and census are hypotheses, item 4).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ClaimDenVS

namespace Nock.RedTeam.Batch2068

open Nock.NockVMROM.Thm54.VclL.Handle.ClaimDenVS

#print axioms claim_census_injΛ
#print axioms claimH_genuineΛ
#print axioms claimNoun_leaves_le
#print axioms zVS_chals
#print axioms claim_table_VS
#print axioms claim_handles_VS

end Nock.RedTeam.Batch2068
