/-
  Nock/RedTeam/Batch1787Thm54VclLChipQ7.lean

  **The Q7 compute chip.**
  * chip tuple `(e, w, s, d, k) = (3, 232, 321, 4, 2)` (`vclRAPQ7_fingerprint`; was 339 gates);
  * `chalKQ7` / `chalVQ7`: compute slot q <- frameVCL coin (0, 9, 11 dead; 5 = z1 inverse;
    IO gamma0/rho0 at limb bases 21/24), `computeChipQ7` the chip at frameVCL coins.
-/
import Nock.NockVMROM.Thm54.VclL.Compute.ChipQ7
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.Unhosted309Events

set_option autoImplicit false

namespace Nock.RedTeam.Batch1787

open Nock.NockVMROM.Thm54.VclL.Compute

#print axioms vclGatesQ7_sub
#print axioms vclGatesQ7_length
#print axioms vclGatesQ7_degree
#print axioms vclGatesQ7_deleted_count
#print axioms vclRAPQ7_fingerprint
#print axioms computeChipVCLQ7_sat_iff
#print axioms chalVQ7_io
#print axioms chalVQ7_dead

end Nock.RedTeam.Batch1787
