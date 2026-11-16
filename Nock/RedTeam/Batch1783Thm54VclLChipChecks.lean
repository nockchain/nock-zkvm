/-
  Nock/RedTeam/Batch1783Thm54VclLChipChecks.lean

  **The chip enforces the verifier's row checks.**  Production `Thm54/VclL/Compute/ChipV.lean`: `GoodV V` (R-LC8's `V.AdjacentC`,
  injective compute nodes, `hchar` on `K`; decidable), `computeChipVCLF ok` (rejecting gate `1 = 0`
  when `ok = false`; `sat_ok`), `chipOfV V` at `V.computeNodes` / `V.basis` / `V.orbitC` (width 232),
  `chipOfV_good`, `acceptedRows_of_chipOfV`, `chipOfV_exportReqFacts` / `chipOfV_pathReqFacts`
  (`reqFacts` from acceptance alone — no `Checks`, the `CompSoundnessFamily.reqFacts` shape).
-/
import Nock.NockVMROM.Thm54.VclL.Compute.ChipV
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.Unhosted309Events

set_option autoImplicit false

namespace Nock.RedTeam.Batch1783

open Nock.NockVMROM.Thm54.VclL.Compute

#print axioms vclGatesF_degree
#print axioms computeChipVCLF_sat_iff
#print axioms sat_ok
#print axioms chipOfV_width
#print axioms chipOfV_good
#print axioms acceptedRows_of_chipOfV
#print axioms chipOfV_exportReqFacts
#print axioms chipOfV_pathReqFacts

end Nock.RedTeam.Batch1783
