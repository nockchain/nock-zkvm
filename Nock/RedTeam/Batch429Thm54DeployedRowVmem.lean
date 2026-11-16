/-
  Nock/RedTeam/Batch429Thm54DeployedRowVmem.lean

  **`deployed_row_vmem_at`.**

  Family memory chip acceptance ⇒ `Vmem` at the decoded row
  (`eqBlk ∧ interV`), with hostile β aligned to `poleSource`.
-/
import Nock.NockVMROM.Thm54.FamilyMemoryRows
import Nock.RedTeam.Batch428Thm54HostileBetaPole
import Nock.RedTeam.Batch400Thm54MemWrapTransfer

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch429

noncomputable abbrev deployed_row_vmem_at :=
  @Nock.NockVMROM.Thm54.FamilyMemoryRows.deployed_row_vmem_at

theorem hyp_was_remaining :
    "deployed_row_vmem_at" ∈ Nock.RedTeam.Batch400.transferRemainingHyps := by
  decide

#check deployed_row_vmem_at

end Nock.RedTeam.Batch429

#print axioms Nock.NockVMROM.Thm54.FamilyMemoryRows.deployed_row_vmem_at
#print axioms Nock.RedTeam.Batch429.hyp_was_remaining
