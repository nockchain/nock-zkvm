/-
  Nock/RedTeam/Batch2066Thm54VSClaimVS.lean

  Additive.
  New module `Thm54/VclL/Handle/ClaimVS.lean`:
  * `claim_decode`: a claim-shaped key `(enc z x, lo + hi√δ, idx)` equal to row `j`'s validity provider
    key is `ValidityProvided` at the decoded cell table (`natOf` halves and serial);
  * `ext_served`: the validity accumulator's weighted LogUp with an EXTERNAL consumer list summing to
    the public `ρ₀` serves every external record (outside the validity IO event, count `< p`);
  * `claims_provided_VS`: at VS (`AcceptsG`, `V.Checks` budget `3 + 2T`, `GoodCVS`'s `ρ₀ = claimValSum`),
    outside the validity IO event at `(χ₄ + χ₆√δ, χ₅ + χ₇√δ)`, every cell claim noun's verifier-computed
    record is `ValidityProvided` on the restricted cell trace.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ClaimVS

namespace Nock.RedTeam.Batch2066

open Nock.NockVMROM.Thm54.VclL.Handle.ClaimVS

#print axioms claim_decode
#print axioms ext_served
#print axioms cellVInternal_length_le
#print axioms chalsOK_VS
#print axioms claims_provided_VS

end Nock.RedTeam.Batch2066
