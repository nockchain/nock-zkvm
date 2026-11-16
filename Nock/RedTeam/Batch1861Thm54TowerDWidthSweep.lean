/-
  Nock/RedTeam/Batch1861Thm54TowerDWidthSweep.lean

  **Width-generic Q7 chain.**  `Fin 232` traces generalized to `Fin w` (WalkSatQ7,
  TopoQ7, CoreQ7, NodeRecQ7 record lists, `rowEnvs`) and the table `tableVCLE hC` to any `T` with
  `[WideTable T]` (HCFTree: width >= 232, agrees with `colRoundVCLE` on the first 232 columns, rounds
  <= 2; `tableVCLE_wide` is the instance).  KeysQ7 (`b0NatAt`, `recKeyQ7`, `keyOfQ7`, `axB0Q7`,
  `recKeyQ7'`, key clauses), HCFTree G-versions (`shapeV1G`, `envsVG_base`, `treeVG_round`,...),
  RecReaderQ7 key clauses, NodeRecQ7 `row_records_Q7G` / `node_records_Q7G` are now stated at any wide `T`;
  every 232 statement is a one-line corollary (`(T := tableVCLE hC)`), statements unchanged.
  `compSoundnessVCL` compiles unchanged.  RowAxQ7 (K-side serial/ax lemmas over `hsat`) stays at 232.
-/
import Nock.NockVMROM.Thm54.VclL.Compute.CompSoundnessVCL

set_option autoImplicit false

namespace Nock.RedTeam.Batch1861
end Nock.RedTeam.Batch1861

open Nock.NockVMROM.Thm54.VclL.Compute

#print axioms tableVCLE_wide
#print axioms treeV1G_shape
#print axioms treeVG_round
#print axioms NodeRecQ7.row_records_Q7G
#print axioms NodeRecQ7.node_records_Q7G
#print axioms NodeRecQ7.row_records_Q7
#print axioms NodeRecQ7.node_records_Q7
#print axioms CoreQ7.rowFacts_Q7
#print axioms CompSoundnessVCL.compSoundnessVCL
