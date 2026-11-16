/-
  Nock/RedTeam/Batch2905Thm54C2WalkTreeX.lean

  **`WalkTreeVS` at `kidsX`.**
  `Handle/WalkLblVSX.lean` (label language: J-8 fanouts, wire kinds `0/1/2` encoded as numbers) and
  `Handle/WalkTreeVSX.lean` (`cwEvent_card`, `goal_of_not_mem`, `bfs_of_walk`, `tile_of_walk`,
  `tree_of_goal` at `kidsX`), plus `holdsN_of_walkX`: the walk's tree with `RowSemX` rows and a real
  root denoting the claim proves `HoldsN`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.WalkTreeVSX

namespace Nock.RedTeam.Batch2905

open Nock.Edit
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX
open Nock.NockVMROM.Thm54.VclL.Handle.WalkLblVSX
open Nock.NockVMROM.Thm54.VclL.Handle.WalkTreeVSX

/-- The J-8 fanouts are the lengths of `kidsX` (and of `ChipHX.childrenX`, `fanoutX_new`). -/
example : (fanS .s10, fanS .s10L, fanS .s10T, fanS .s11s, fanS .s11d, fanS .s11j) = (3, 1, 0, 1, 2, 1) :=
  rfl

#print axioms kidsX_length
#print axioms cwEvent_card
#print axioms goal_of_not_mem
#print axioms bfs_of_walk
#print axioms tile_of_walk
#print axioms tree_of_goal
#print axioms holdsN_of_walkX

end Nock.RedTeam.Batch2905
