/-
  Nock/RedTeam/Batch1806Thm54VclLReqFactsQ7.lean

  **ReqFacts at the Q7 chip.**  Production `Thm54/VclL/Compute/ReqFactsQ7.lean`: the export / path accumulators' `reqFacts`
  re-instantiated at `computeChipVCLQ7` (`exportReqFactsQ7`, `pathReqFactsQ7` over
  `AcceptedRowsQ7`; `acceptedRowsQ7_of_sat` from acceptance, injective nodes, adjacency, hchar);
  `coinsV_chalVQ7`: at frameVCL coins the denominators read the IO coins (gamma0, rho0).
-/
import Nock.NockVMROM.Thm54.VclL.Compute.ReqFactsQ7
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.Unhosted309Events

set_option autoImplicit false

namespace Nock.RedTeam.Batch1806

open Nock.NockVMROM.Thm54.VclL.Compute

#print axioms export_invQ7
#print axioms path_invQ7
#print axioms exportReqFactsQ7
#print axioms pathReqFactsQ7
#print axioms selAt_of_gatesQ7
#print axioms acceptedRowsQ7_of_sat
#print axioms coinsV_chalVQ7

end Nock.RedTeam.Batch1806
