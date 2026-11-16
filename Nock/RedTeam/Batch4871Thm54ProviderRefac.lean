/-
  Nock/RedTeam/Batch4871Thm54ProviderRefac.lean

  **Provider-parametric refactor steps 0-3.**
  New modules `Handle/ProviderJ8`, `Handle/ProviderJ8Iff`, `Handle/ComplGeneric`, `Handle/ProviderJ9`; additive, no digest
  move, no statement change:
  * `acceptsGeneric_j8_iff`: `AcceptsGeneric J8providers claimJ8 budgetJ8 ↔ AcceptsJ8V`; `probGeneric_j8_final` and
    `probGeneric_j8_nonvacuous` carry the J-8 bound and non-vacuity through it.
  * `complGeneric_j8`: J-8 completeness from the 29 obligations regrouped by provider (`complGenericObligations_iff`).
  * `acceptsGeneric_j9_iff`: the same provider list with the J-9 B claim component `claimJ9` `↔ AcceptsJ9V`;
    `probGeneric_j9_final` carries `probJ9B_final_clean`; `acceptsGeneric_j9_of_accepts` transports any witness. -/
import Nock.NockVMROM.Thm54.VclL.Handle.ComplGeneric
import Nock.NockVMROM.Thm54.VclL.Handle.ProviderJ9

set_option autoImplicit false

namespace Nock.RedTeam.Batch4871

open Nock.NockVMROM.Thm54.VclL.Handle

#check @ProviderJ8.acceptsGeneric_j8_iff
#check @ProviderJ8.probGeneric_j8_final
#check @ProviderJ8.probGeneric_j8_nonvacuous
#check @ComplGeneric.complGeneric_j8
#check @ProviderJ9.acceptsGeneric_j9_iff
#check @ProviderJ9.probGeneric_j9_final

#print axioms ProviderJ8.acceptsGeneric_j8_iff
#print axioms ProviderJ8.probGeneric_j8_final
#print axioms ProviderJ8.probGeneric_j8_nonvacuous
#print axioms ComplGeneric.complGenericObligations_iff
#print axioms ComplGeneric.complGeneric_j8
#print axioms ProviderJ9.acceptsGeneric_j9_iff
#print axioms ProviderJ9.acceptsGeneric_j9_of_accepts
#print axioms ProviderJ9.probGeneric_j9_final

end Nock.RedTeam.Batch4871
