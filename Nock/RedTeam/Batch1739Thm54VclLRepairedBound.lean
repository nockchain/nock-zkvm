/-
  Nock/RedTeam/Batch1739Thm54VclLRepairedBound.lean

  **Axioms receipts for the repaired VCL-L bound.**
  Production: `Thm54/VclL/Events/Bound.lean` §5 (`ioWorkKp`, `boundVCL'`).
-/
import Nock.NockVMROM.Thm54.VclL.Events.Bound
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.Unhosted309Events

set_option autoImplicit false

namespace Nock.RedTeam.Batch1739

open Nock.NockVMROM.Thm54.VclL.Events

#print axioms ioFUB_sq
#print axioms ioWorkKp_mono
#print axioms numGen_cornerKp
#print axioms figVCL'_two_pow_31
#print axioms figVCL'_two_pow_32
#print axioms figVCL'_kernel
#print axioms figVCL'_bench
#print axioms figVCL'_not_156
#print axioms figKp_wide_two_pow_31
#print axioms figK_kc3_fails
#print axioms figVCL_kc3_fails

end Nock.RedTeam.Batch1739
