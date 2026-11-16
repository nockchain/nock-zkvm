/-
  Nock/RedTeam/Batch385Thm54WrapFixesVcomp.lean

  **`wrap_fixes_vcomp_row`.**

  The relative wrap is the identity on a `V_comp` row: `memBlk` pins
  inactive slots to `MemRec.zero` and the active `ln` / `mr.ts`
  equations.  Landed form:
  identity, not the `↔` weakening.
-/
import Nock.NockVMROM.Thm54.WrapFixesVcomp

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch385

noncomputable abbrev wrap_fixes_vcomp_row :=
  @Nock.NockVMROM.Thm54.WrapFixesVcomp.wrap_fixes_vcomp_row

noncomputable abbrev specializedExec_computePubAt_eq_decodePub_of_accepted :=
  @Nock.NockVMROM.Thm54.WrapFixesVcomp.specializedExec_computePubAt_eq_decodePub_of_accepted

noncomputable abbrev computeStateOf_of_oneHot :=
  @Nock.NockVMROM.Thm54.WrapFixesVcomp.computeStateOf_of_oneHot

#check wrap_fixes_vcomp_row
#check specializedExec_computePubAt_eq_decodePub_of_accepted

end Nock.RedTeam.Batch385

#print axioms Nock.NockVMROM.Thm54.WrapFixesVcomp.wrap_fixes_vcomp_row
#print axioms Nock.NockVMROM.Thm54.WrapFixesVcomp.specializedExec_computePubAt_eq_decodePub_of_accepted
