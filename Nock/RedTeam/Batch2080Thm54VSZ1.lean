/-
  Nock/RedTeam/Batch2080Thm54VSZ1.lean

  **The z1 read-set receipt.**
  Additive.  New module `Thm54/VclL/Handle/Z1VS.lean`:
  * `zp` / `zpM`: zero propagation of the selectors `{0, 5, 9}` (and of zero constants);
  * `base_z1_receipt` (exactly one base template gate reads `z1` off OP0/OP5/OP9), `z1_bool_flagged`
    (positive control: that gate is `z1·(z1−1)`), `k_z1_receipt` (no `𝕂` template gate does);
  * `baseGatesF_z1_irrel` / `kGatesF_z1_irrel`: off OP0/OP5/OP9 the deployed gates (other than the
    booleanity) are independent of column 13 (`𝕂` gates at a fixed `𝕂` environment).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.Z1VS

namespace Nock.RedTeam.Batch2080

open Nock.NockVMROM.Thm54.VclL.Handle.Z1VS

#print axioms z1_bool_flagged
#print axioms base_z1_receipt
#print axioms k_z1_receipt
#print axioms base_z1_free_or_bool
#print axioms baseGatesF_z1_irrel
#print axioms kGatesF_z1_irrel

end Nock.RedTeam.Batch2080
