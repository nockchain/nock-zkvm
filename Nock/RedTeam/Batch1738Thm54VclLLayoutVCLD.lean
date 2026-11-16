/-
  Nock/RedTeam/Batch1738Thm54VclLLayoutVCLD.lean

  **`layoutVCLD`, the repaired chip as a `ChipLayoutP`.**

  Production: `Thm54/VclL/Compute/LayoutVCLD.lean`.
-/
import Nock.NockVMROM.Thm54.VclL.Compute.LayoutVCLD
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.Unhosted309Events

set_option autoImplicit false

namespace Nock.RedTeam.Batch1738

open Nock.NockVMROM.Thm54.VclL.Compute

#print axioms layoutVCLD_sat_iff
#print axioms layoutVCLD_gatesOK
#print axioms rowFactsP_vcomp
#print axioms rowFactsP_transition
#print axioms rowFactsP_queue

end Nock.RedTeam.Batch1738
