/-
  Nock/RedTeam/Batch2117Thm54VSFigures.lean

  **The claim-leaf bound and the figures at VS.**  Additive.
  New module `Thm54/VclL/Handle/EpsFigVS.lean`:
  * `numH`, `boundVCLH''_eq`, `numH_corner`; `standaloneVS_soundness_le` (probability `≤ boundVCLH''`);
  * `standaloneVS_122`: end to end.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.EpsFigVS

namespace Nock.RedTeam.Batch2117

open Nock.NockVMROM.Thm54.VclL.Handle.EpsFigVS

#print axioms claimFuel_le_of_leafBoundF
#print axioms claimFuel_eq_fuelChip
#print axioms boundVCLH''_eq
#print axioms numH_corner
#print axioms standaloneVS_soundness_le
#print axioms figVCLH''_two_pow_31
#print axioms figVCLH''_two_pow_32
#print axioms figVCLH''_kernel
#print axioms figVCLH''_not_123
#print axioms figVCLH''_not_121_at_32
#print axioms figVCLH''_not_143_kernel
#print axioms hx_alone_not_155
#print axioms hx_alone_not_154_at_32
#print axioms hx_alone_not_164_kernel
#print axioms others_fit_155
#print axioms standaloneVS_122

end Nock.RedTeam.Batch2117
