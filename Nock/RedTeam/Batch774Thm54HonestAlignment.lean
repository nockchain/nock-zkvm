/-
  Nock/RedTeam/Batch774Thm54HonestAlignment.lean

  * `tiles_of_bfs` / `queued_of_bfs`: the BFS rows of an honest (fanout-correct) forest satisfy the
    tiling and queue hypotheses of `Batch771.bfs_rebuildForest` / `Batch773.expOf_requestList`
    (so the hypotheses are not vacuous, and the honest rows rebuild the committed forest:
    `honest_rebuild`).
  * The opcode sweep: `recordCount = arity` at all eleven states (so no opcode misaligns
    `expOf`'s `rowArity` prefix with `requestList`'s `recordCount` blocks), and `fanoutComp`'s
    values.
  * `requestList` at the `S(a) + j` index returns each row's own
    record, and `w`'s first request is at 1-based exponent `5 + recordCount x`
    (`gateSkel_w_exp`), the very number of `Batch757.wExp_eq`: the numbering the skeleton's
    `requestList` assigns IS the BFS prefix numbering, at both `x = OP0` and `x = OP1`.
-/
import Nock.RedTeam.Batch773Thm54ExpOfRequestList

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch774

open Nock
open Nock.Walk
open Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.StrategyOfTraces
open Nock.NockVMROM.Thm54.PreSeedCensus
open Nock.RedTeam.Batch771
open Nock.RedTeam.Batch772

/-! ## §A  honest rows satisfy the tiling and the queue -/

section Honest

variable {α : Type} (fo : α → ℕ)

theorem tiles_of_bfs (l : List (NTree α)) (hl : l ≠ []) (hwf : FanoutWF fo l) :
    Tiles fo l.length ((bfsForest l).map NTree.label) := by
  unfold Tiles
  have hmap : ((bfsForest l).map NTree.label).map fo = (bfsForest l).map
      (fun t => t.children.length) := by
    rw [List.map_map]
    exact List.map_congr_left (fun t ht => (hwf t ht).symm)
  rw [hmap, List.length_map]
  have h := bfsForest_eq_append_flatMap l hl
  have h2 := congrArg List.length h
  rw [List.length_append] at h2
  have h3 : ((bfsForest l).map (fun t => t.children.length)).sum =
      ((bfsForest l).flatMap NTree.children).length := by
    rw [List.length_flatMap]
  rw [h3]; omega

theorem queued_of_bfs (l : List (NTree α)) (hl : l ≠ []) (hwf : FanoutWF fo l) :
    Queued fo l.length ((bfsForest l).map NTree.label) := by
  intro i hi
  rw [List.length_map] at hi
  have hv := foCol_BFSValidF l hl (i + 1) (by omega) (by omega)
  rw [Sf_foCol, Nat.add_sub_cancel] at hv
  have hmap : (((bfsForest l).map NTree.label).take i).map fo =
      ((bfsForest l).take i).map (fun t => t.children.length) := by
    rw [← List.map_take, List.map_map]
    exact List.map_congr_left (fun t ht =>
      (hwf t (List.mem_of_mem_take ht)).symm)
  have h3 : (((bfsForest l).take i).map (fun t => t.children.length)).sum =
      (((bfsForest l).take i).flatMap NTree.children).length := by
    rw [List.length_flatMap]
  rw [hmap, h3]
  exact hv

/-- **The honest rows rebuild the committed forest**, and `bfs ∘ rebuildForest` returns them. -/
theorem honest_rebuild (l : List (NTree α)) (hwf : FanoutWF fo l) :
    rebuildForest fo l.length ((bfsForest l).map NTree.label) = l ∧
      (bfsForest (rebuildForest fo l.length ((bfsForest l).map NTree.label))).map NTree.label =
        (bfsForest l).map NTree.label := by
  have h := rebuildForest_bfs fo l hwf
  exact ⟨h, by rw [h]⟩

end Honest

/-! ## §B  the opcode sweep -/

/-- No opcode misaligns the exponent prefix (`rowArity` = `arity`) with the request blocks
(`recordCount`): the two tables agree at every state. -/
theorem arity_eq_recordCount_all :
    ∀ s : State, Nock.NockVMROM.Thm54.OptimizedHostileTimestamps.arity s =
      Nock.Framework.recordCount s := by
  intro s; cases s <;> rfl

/-- …and each state requests between `1` and `3` records, so `Fin 3` slots cover them. -/
theorem recordCount_between : ∀ s : State, 1 ≤ Nock.Framework.recordCount s ∧
    Nock.Framework.recordCount s ≤ 3 := by
  intro s; cases s <;> decide


/-- A skeleton row at state `st` whose record `i` is tagged `(tag, i)`. -/
def mkRow (st : State) (tag : ℕ) : ComputeRowSkeleton where
  state := st
  subject := .atom 0
  formula := .atom 0
  evaluation := .atom 0
  decomposition := fun _ _ => .atom 0
  subformula := fun _ _ _ => .atom 0
  memoryRecord := fun i _ => ⟨.atom tag, .atom i, 0⟩

/-- `[9 [cons [OP0 w] [OP1]] x]`, rows tagged by BFS position `0..4`. -/
def gateTree (x : State) : NTree ComputeRowSkeleton :=
  .node (mkRow .s9 0)
    [.node (mkRow .cons 1) [.node (mkRow .s0 3) [], .node (mkRow .s1 4) []],
     .node (mkRow x 2) []]

def gateSkel (x : State) : SemanticSkeleton := ⟨gateTree x, []⟩

theorem gateSkel_states (x : State) :
    (computeSkeletonRows (gateSkel x)).map ComputeRowSkeleton.state = [.s9, .cons, x, .s0, .s1] := by
  simp [computeSkeletonRows, gateSkel, gateTree, bfsForest, NTree.children, NTree.label, mkRow]

/-- **`w`'s request** (BFS row `3`, slot `0`) is at 1-based exponent `5 + recordCount x` — the
exponent prefix `S(3) + 0 + 1 = 3 + 1 + recordCount x + 1` — and it is `w`'s own record, at both
leaf arms `x = OP0` and `x = OP1`. -/
theorem gateSkel_w_exp (x : State) (hx : x = .s0 ∨ x = .s1) :
    ((requestList (gateSkel x))[4 + Nock.Framework.recordCount x]?).map
        (fun r => (r.root, r.child)) = some (.atom 3, .atom 0) := by
  rcases hx with rfl | rfl <;>
  simp [requestList, computeSkeletonRows, gateSkel, gateTree, bfsForest, NTree.children,
    NTree.label, mkRow, Nock.Framework.recordCount, List.finRange_succ]

end Nock.RedTeam.Batch774

#print axioms Nock.RedTeam.Batch774.tiles_of_bfs
#print axioms Nock.RedTeam.Batch774.queued_of_bfs
#print axioms Nock.RedTeam.Batch774.honest_rebuild
#print axioms Nock.RedTeam.Batch774.arity_eq_recordCount_all
#print axioms Nock.RedTeam.Batch774.recordCount_between
#print axioms Nock.RedTeam.Batch774.gateSkel_states
#print axioms Nock.RedTeam.Batch774.gateSkel_w_exp
