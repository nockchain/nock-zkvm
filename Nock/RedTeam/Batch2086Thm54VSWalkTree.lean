/-
  Nock/RedTeam/Batch2086Thm54VSWalkTree.lean

  **The
  compute-walk tree extraction at VS.**  Additive.  New modules `Thm54/VclL/Handle/WalkLblVS.lean`
  (the label language: `fanS`, `enc`/`encT`, `clabOf`, `lblOf`, `foOf`, the commit relation `FV`,
  `fv_commit`) and `Thm54/VclL/Handle/WalkTreeVS.lean`: `stVS` (`StateSep`), `fv_respects`,
  **`cwEvent`** / **`cwEvent_card`** (`Walk_IOP_forest_final_card_of_label` at `kroots = 1`,
  `labelOf := enc`), `goal_of_not_mem`, `bfs_of_walk` (`Batch478.bfsValidF_of_ratio_gate`),
  `tile_of_walk` / `tileSet_card`, `encT_inj` (small handle values), **`tree_of_goal`** (one tree,
  root = row 1, every node a row in `[1, h]`, children = the row's `kids`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.WalkTreeVS

namespace Nock.RedTeam.Batch2086

open Nock.NockVMROM.Thm54.VclL.Handle.WalkLblVS Nock.NockVMROM.Thm54.VclL.Handle.WalkTreeVS

#print axioms fv_commit
#print axioms fv_respects
#print axioms cwEvent_card
#print axioms cwEvent_card_le
#print axioms goal_of_not_mem
#print axioms bfs_of_walk
#print axioms tile_of_walk
#print axioms tileSet_card
#print axioms encT_inj
#print axioms tree_of_goal

end Nock.RedTeam.Batch2086
