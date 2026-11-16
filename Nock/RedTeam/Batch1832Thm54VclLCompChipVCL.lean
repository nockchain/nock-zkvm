/-
  Nock/RedTeam/Batch1832Thm54VclLCompChipVCL.lean

  **The compute family's chip, `reqFacts`, `reqRecords`.**
  Production `Thm54/VclL/Compute/CompChipVCL.lean`:
  `GoodCF` (AdjacentC, injective nodes, hchar, `N ≤ char`, `ρ 0 = 0`), `pubCF` (ρ 1 / ρ 2 at the
  terminal publics), `chipCF` (the side chip when good, `computeChipVCLF … false` otherwise),
  `chipCF_width` / `chipCF_good` / `chipCF_sat`, `reqFactsCF` (all three accumulators at the IO coins
  `(χ4, χ5)`), `reqRecordsCF`, `reqRecsQ7_round1` (records read round ≤ 1 columns only), `reqBoundCF`
  (`0, 3N, N`), `reqFactsCF_length`.
-/
import Nock.NockVMROM.Thm54.VclL.Compute.CompChipVCL
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.P8Core.SVCompute.QueueTwins
import Nock.NockVMROM.Thm54.P8Core.SVWalk.ExpAlign
import Nock.NockVMROM.Thm54.Unhosted309Events

set_option autoImplicit false

namespace Nock.RedTeam.Batch1832

open Nock.NockVMROM.Thm54.VclL.Compute.CompChipVCL

#print axioms chipCF_width
#print axioms chipCF_good
#print axioms chipCF_sat
#print axioms reqFactsCF
#print axioms reqFactsCF_records
#print axioms reqFactsCF_length
#print axioms reqRecsQ7_round1
#print axioms reqRecsQ7_length_le
#print axioms limbVal_pubCF_export
#print axioms limbVal_pubCF_path

end Nock.RedTeam.Batch1832
