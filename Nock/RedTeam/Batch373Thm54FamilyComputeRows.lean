/-
  Nock/RedTeam/Batch373Thm54FamilyComputeRows.lean

  `deployed_row_vcomp_at` is `V_comp` at `rowEnvAt P c Qc i` from
  `SatisfiesWithPreprocessing (P.computeChipAt c) Qc` and
  `nprSeed c.1 ≠ 0`.  The honest-chip theorem is the named corollary
  `deployed_row_vcomp_honest_corollary`.
-/
import Nock.NockVMROM.Thm54.FamilyComputeRows

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch373

open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.DeployedComputeRows

noncomputable abbrev deployed_row_vcomp_at :=
  @Nock.NockVMROM.Thm54.FamilyComputeRows.deployed_row_vcomp_at

noncomputable abbrev rowEnvAt :=
  @Nock.NockVMROM.Thm54.FamilyComputeRows.rowEnvAt

#check deployed_row_vcomp_at

end Nock.RedTeam.Batch373

#print axioms Nock.NockVMROM.Thm54.FamilyComputeRows.deployed_row_vcomp_at
#print axioms Nock.NockVMROM.Thm54.FamilyComputeRows.zZinv_at_rowEnvAt
