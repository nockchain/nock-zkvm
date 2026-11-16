/-
  Nock/RedTeam/Batch1864Thm54TowerDCompChip.lean

  **The tower CompChip wrapper, node_records / root_binds at
  the tower, `compSoundnessVCLT`.**  `GoodCFT` / `chipCFT` (rejecting unless the checks hold), `acceptedRowsQ7T_of_sat`,
  `reqFactsCFT` (+ records / round / bounds), `treeVG_pub_irrel_T`, `node_records_CFT`,
  `root_binds_CFT`, `compSoundnessVCLT : CompSoundnessFamily` at `Kio = Kfp = Quad delta`,
  `Z := seedSpecVCL`, `I := ioSpecVCLQuad`, `Honest := PEmpty` (SOUNDNESS fields only),
  `imFP_costaged` (round placement of the Im FP columns).
-/
import Nock.NockVMROM.Thm54.VclL.Compute.TowerCompFamilyT
import Nock.NockVMROM.Thm54.VclL.Compute.CompSoundnessVCL
import Nock.NockVMROM.Thm54.TraceGen.GenFormRAxisLambda
import Nock.NockVMROM.Thm54.TraceGen.GenGoodSeedExists

set_option autoImplicit false

namespace Nock.RedTeam.Batch1864
end Nock.RedTeam.Batch1864

open Nock.NockVMROM.Thm54.VclL.Compute

#print axioms TowerD.rejectChipT_unsat
#print axioms TowerD.chipCFT_good
#print axioms TowerD.chipCFT_sat
#print axioms TowerD.chipCFT_rejects_bad
#print axioms TowerD.acceptedRowsQ7T_of_sat
#print axioms TowerD.reqRecsT_round
#print axioms TowerD.reqFactsCFT
#print axioms TowerD.reqFactsCFT_records
#print axioms TowerD.reqFactsCFT_length
#print axioms TowerD.treeVG_pub_irrel_T
#print axioms TowerD.node_records_CFT
#print axioms TowerD.root_binds_CFT
#print axioms TowerD.imFP_costaged
#print axioms TowerD.compSoundnessVCLT
#print axioms CompSoundnessVCL.compSoundnessVCL
