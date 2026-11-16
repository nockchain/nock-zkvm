/-
  Nock/RedTeam/Batch1859Thm54TowerDGenTree.lean

  **The V-level tree and core chain over a gather built from V.**
  `VerifierData` is untouched
  (`basis : Basis (Fin 3) F K` is the 𝕂-basis); the V-chain is parameterized by a `CoordGather F K'`
  (`ofBasis V.basis` today, `towerGather δ V.basis` at the tower).  `HCFTree`: `envsVG/envsPG/treeV1G/shapeV1G/treeVG/shapeVG` + lemmas; the old names are the `ofBasis`
  instance by `rfl` (`*_eq_G`).  `CoreQ7`: `cdOfGG`, `lblQ_eq_at1G`, `treeV1G_fst`, `rowFacts_core_Q7G`;
  `rowFacts_core_Q7` is its one-line `ofBasis` corollary.
-/
import Nock.NockVMROM.Thm54.VclL.Compute.CompSoundnessVCL
import Nock.NockVMROM.Thm54.VclL.Compute.TowerGather

set_option autoImplicit false

namespace Nock.RedTeam.Batch1859
end Nock.RedTeam.Batch1859

open Nock.NockVMROM.Thm54.VclL.Compute

#print axioms treeV1G_shape
#print axioms treeVG_shape
#print axioms treeVG_round
#print axioms treeVG_label_even
#print axioms treeV_shape
#print axioms treeV_eq_G
#print axioms CoreQ7.rowFacts_core_Q7G
#print axioms CoreQ7.rowFacts_core_Q7
#print axioms CoreQ7.rowFacts_Q7
#print axioms NodeRecQ7.node_records_Q7
#print axioms CompSoundnessVCL.compSoundnessVCL
