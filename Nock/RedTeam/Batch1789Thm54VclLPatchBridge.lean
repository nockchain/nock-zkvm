/-
  Nock/RedTeam/Batch1789Thm54VclLPatchBridge.lean

  **The patched / unpatched decode bridge.**  Production `Thm54/VclL/Compute/PatchQ7.lean` §6:
  * `lnPatch_source_trace` / `lnPatch_source_chal`: the patch moves only source columns 67/68
    (roles 54/55) and challenges 0, 9 and the lambda-power block;
  * `decodeInputs_z_lnPatch`, `decodeDec_lnPatch`, `decodePub_f_lnPatch`, `oneHot_lnPatch_iff`,
    `servedFormulaCell_lnPatch_iff`: everything `lookup_binds_head` reads agrees;
  * `computeChipVCLQ7_lookup_binds_head_row`: `lookup_binds_head` at the Q7 chip with every
    hypothesis and the conclusion at the UNPATCHED decode.
-/
import Nock.NockVMROM.Thm54.VclL.Compute.PatchQ7
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.Unhosted309Events

set_option autoImplicit false

namespace Nock.RedTeam.Batch1789

open Nock.NockVMROM.Thm54.VclL.Compute

#print axioms lnPatch_source_trace
#print axioms lnPatch_source_chal
#print axioms decodeInputs_z_lnPatch
#print axioms decodeDec_lnPatch
#print axioms decodePub_f_lnPatch
#print axioms oneHot_lnPatch_iff
#print axioms servedFormulaCell_lnPatch_iff
#print axioms computeChipVCLQ7_lookup_binds_head_row

end Nock.RedTeam.Batch1789
