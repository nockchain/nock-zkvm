/-
  Nock/RedTeam/Batch1736Thm54VclLRowDecode.lean

  **The VCL obligations and the row decode — chip
  acceptance ⇒ `V_comp` at `computeChipVCLD`.**

  Production: `Thm54/VclL/Compute/RowDecode.lean`.
  * `pullEnv`, `keptGates309_of_vclGates` (acceptance transports along `vclCol`, `eval_reindexE`).
  * `VclSourceObligations` (the 309 decomposition minus Form R — `formR99`, `formRLam`, core ids
    79/80 — and minus the arity-form exponent gates), `VclSourceObligations.of309` (positive
    control: implied by the 309 language), `.of_kept`, `.of_vclGates`.
  * `paperPackingRowLocal_eval_zero_vcl`, `vcompAt_of_rowLocal` (the `deployed_row_vcomp_at`
    argument, package-free), `oneHot_of_base15`, `vcl_obligations_vcomp`, `vcl_row_vcomp`.
  * At the chip: `computeChipVCLD_row_vcomp` (acceptance ⇒ `VcompAt` at every row node) and
    `computeChipVCLD_lookup_binds_head` (with the slot-0 record served as `[l r]`: `l` is the
    opcode atom, `f_t` the axis-3 child) — `lookup_binds_head_row`'s `V_comp` premise is now a
    consequence of acceptance; `fpAt_pullEnv` (the decoded fingerprints are the VCL row's own).
  Premises left: `hchar` (as at the deployed chip) and the row's `z·z⁻¹` pin (coin positions
  parametric).
-/
import Nock.NockVMROM.Thm54.VclL.Compute.RowDecode
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.Unhosted309Events

set_option autoImplicit false

namespace Nock.RedTeam.Batch1736

open Nock.NockVMROM.Thm54.VclL.Compute

#print axioms keptGates309_of_vclGates
#print axioms VclSourceObligations.of309
#print axioms VclSourceObligations.of_kept
#print axioms VclSourceObligations.of_vclGates
#print axioms paperPackingRowLocal_eval_zero_vcl
#print axioms vcompAt_of_rowLocal
#print axioms oneHot_of_base15
#print axioms vcl_obligations_vcomp
#print axioms vcl_row_vcomp
#print axioms fpAt_pullEnv
#print axioms computeChipVCLD_row_vcomp
#print axioms computeChipVCLD_lookup_binds_head

end Nock.RedTeam.Batch1736
