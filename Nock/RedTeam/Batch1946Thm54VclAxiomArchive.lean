/-
  Nock/RedTeam/Batch1946Thm54VclAxiomArchive.lean

  **Archived `#print axioms` of the VCL headline theorems.**
  Expected: `{propext, Classical.choice, Quot.sound}` (plus `Field.goldilocks_prime` for the Goldilocks theorem).
-/
import Nock.RedTeam.Batch1945Thm54RowTerms
import Nock.RedTeam.Batch1938Thm54VclCompletenessJoint
import Nock.RedTeam.Batch1885Thm54TowerLambdaSplit
import Nock.RedTeam.Batch1947Thm54VclCompletenessFigure

set_option autoImplicit false

namespace Nock.RedTeam.Batch1946

end Nock.RedTeam.Batch1946

-- soundness
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.compSoundnessVCLT
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.rowFactsAt_compSoundnessVCLT
#print axioms Nock.RedTeam.Batch1882.vcl_standalone_soundness'
#print axioms Nock.RedTeam.Batch1882.vcl_standalone_155'
#print axioms Nock.RedTeam.Batch1882.vcl_standalone_154'
#print axioms Nock.RedTeam.Batch1882.vcl_standalone_164'
-- honest side
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.HonestVCLT.hacc
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.honest_accepted_T
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.honest_staged_T
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.hrowX_T
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.hrowP_T
-- completeness
#print axioms Nock.RedTeam.Batch1938.vcl_completeness'
#print axioms Nock.RedTeam.Batch1938.vcl_completeness_goldilocks
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.epsilon_honestBadCF
#print axioms Nock.RedTeam.Batch1947.vcl_completeness_figure
