/-
  Nock/RedTeam/Batch1788Thm54VclLPatchQ7.lean

  **`V_comp` at the Q7 chip through the patched row.**
  * positions 74/75 MEASURED (`walkCountAcc_lnPatch`, `residualRoles_measured`: they read
    residual roles 58/59), not taken from the instrument's hand-set `false`;
  * the deleted recurrences 50/58/65 vanish at the patched row (`deleted_rowLocal_zeroAt`,
    `decide +kernel`; `deleted_rowLocal_vanish`);
  * `q7_obligations_vcomp`, `computeChipVCLQ7_row_vcomp`, `computeChipVCLQ7_lookup_binds_head`
    (stated at the patched decode);
  * NC (silent): `q7_obligations_silent_09` - perturbing the challenge limbs of slots 0 / 9
    leaves the Q7 obligations unchanged (typed level; the F-level gates held at `envF`).
-/
import Nock.NockVMROM.Thm54.VclL.Compute.PatchQ7
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.Unhosted309Events

set_option autoImplicit false

namespace Nock.RedTeam.Batch1788

open Nock.NockVMROM.Thm54.VclL.Compute

#print axioms evalT_lnPatch
#print axioms evalW_lnPatch
#print axioms coreSemValue309_lnPatch
#print axioms walkCountAcc_lnPatch
#print axioms residualRoles_measured
#print axioms auxSemValue309_lnPatch
#print axioms VclSourceObligationsQ7.lnPatch
#print axioms VclSourceObligationsQ7.of_vclGatesQ7
#print axioms deleted_rowLocal_zeroAt
#print axioms deleted_rowLocal_vanish
#print axioms q7_obligations_vcomp
#print axioms computeChipVCLQ7_row_vcomp
#print axioms computeChipVCLQ7_lookup_binds_head
#print axioms lnPatch_gather_perturb
#print axioms q7_obligations_patch_iff
#print axioms q7_obligations_silent_09

end Nock.RedTeam.Batch1788
