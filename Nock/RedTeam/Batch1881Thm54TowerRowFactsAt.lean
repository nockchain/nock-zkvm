/-
  Nock/RedTeam/Batch1881Thm54TowerRowFactsAt.lean

  **`rowFactsAt` at the tower compute chip.**

  * `rowFacts_core_outsideG`: the five carrier-free `RowFacts` core facts at every node of `treeVG`
    at ANY gather, outside the tiling / alpha-root / prefix-gamma events (generic twin of the first
    half of `SummandsQ7.rowFacts_outside_core`; built on `rowFacts_core_Q7G`).
  * `tower_ft_leaf_ax` / `tower_fth_leaf_ax`: at `s0` / `s9` the `ax` and `ax`-Im gates force the tower
    decode of `f_t.leaf` / `f_th.leaf` to be `algebraMap (algebraMap axCol)`.
  * `towerRowFacts_ax0` / `towerRowFacts_ax9`: `RowFacts.ax0` / `ax9` at `axB0Q7` at every tower node.
  * `rowFacts_outside_CFT`: `Batch1171.RowFacts` at `axB0Q7`, seed `z' = (chi2, chi3)`, `q = ringChar K'`
    at every node of the tower tree, from acceptance at `chipCFT` + outside `summandsQ7T`.
  * `rowFactsAt_compSoundnessVCLT`: the frame's `rowFactsAt` for `compSoundnessVCLT` (was hypothesis
    `hrow` of `standalone_generic`).
-/
import Nock.NockVMROM.Thm54.VclL.Compute.TowerRowFactsAt
import Nock.NockVMROM.Thm54.TraceGen.GenFormRAxisLambda
import Nock.NockVMROM.Thm54.TraceGen.GenGoodSeedExists
import Nock.NockVMROM.Thm54.VclL.Compute.CompSoundnessVCL

namespace Nock.RedTeam.Batch1881

open Nock.NockVMROM.Thm54.VclL.Compute.TowerD

#print axioms rowFacts_core_outsideG
#print axioms tower_ft_leaf_ax
#print axioms tower_fth_leaf_ax
#print axioms towerRowFacts_ax0
#print axioms towerRowFacts_ax9
#print axioms rowFacts_outside_CFT
#print axioms rowFactsAt_compSoundnessVCLT

end Nock.RedTeam.Batch1881
