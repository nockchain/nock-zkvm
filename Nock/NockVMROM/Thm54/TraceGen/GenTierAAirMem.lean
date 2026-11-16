/-
  Nock/NockVMROM/Thm54/TraceGen/GenTierAAirMem.lean

  AIR-ordered (`dotTreeAir`) memory `MemoryNodesOK` and compute
  `ComputeNodesOK` / `BindComputeRow` / timestamp specialization.
  BFS index 2 is OP2, index 3 is the condition.  `dotTree` / `Gen.lean`
  are not edited.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenTierAMem
import Nock.NockVMROM.Thm54.TraceGen.GenTierAComputeLink

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk Nock.Noun Nock.NockVM
open Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.HonestCommitment

variable {K : Type} [Field K]

variable {lmb : K}

/-! ## AIR `MemoryNodesOK` -/

theorem assigned_rowOK_air (z α : K)
    (n : NTree (GenComputeRow K))
    (hn : InTree (bfsAssign (dotTreeAir (K := K))) n) :
    ∀ u ∈ genRowMemForest (encC z) z α lmb (extractNodeReqs n.label),
      MemoryNodesOK z α (mapNTree GenMemoryRow.node u) := by
  have hnF : n ∈ bfsForest [bfsAssign (dotTreeAir (K := K))] :=
    (mem_bfsForest _ n).mpr ⟨_, List.mem_singleton.mpr rfl, hn⟩
  have hlab := bfsAssign_bfsForest_labels (dotTreeAir (K := K))
  have hmem : n.label ∈ (bfsForest [bfsAssign (dotTreeAir (K := K))]).map NTree.label :=
    List.mem_map.mpr ⟨n, hnF, rfl⟩
  rw [hlab] at hmem
  simp only [List.mem_map] at hmem
  rcases hmem with ⟨i, hi, hieq⟩
  have hi' := lt_bfsRows_of_mem_range' (t := (dotTreeAir (K := K))) hi
  rw [← hieq, extractNodeReqs, bfsLabelAt_requests (dotTreeAir (K := K)) i hi']
  rcases dot_air_bfs_index i hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hget : (bfsRows (dotTreeAir (K := K)))[0] = (dotTreeAir (K := K)).label := by
      simp [dot_air_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTreeAir (K := K)) 1).stamp 0 g.requests) hget]
    simp [dotTreeAir, skelNode, extractNodeReqsAux_cons3]
    exact genRowMemForest_three_chain32_OK z α (.atom 6) dotCondFormula
      dotBranchPair dotThenFormula dotElseFormula
      (getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 1).stamp 0)
      (getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 1).stamp 1)
      (getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 1).stamp 2)
  · have hget : (bfsRows (dotTreeAir (K := K)))[1] = (dotOp2Tree (K := K)).label := by
      simp [dot_air_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTreeAir (K := K)) 2).stamp 0 g.requests) hget]
    simp [dotOp2Tree, skelNode, extractNodeReqsAux_cons2]
    exact genRowMemForest_chain32_OK z α (.atom 2) dotOp2B dotOp2C
      (getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 2).stamp 0)
      (getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 2).stamp 1)
  · have hget : (bfsRows (dotTreeAir (K := K)))[2] = (dotCondTree (K := K)).label := by
      simp [dot_air_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTreeAir (K := K)) 3).stamp 0 g.requests) hget]
    simp [dotCondTree, skelNode, extractNodeReqsAux_cons1]
    exact genRowMemForest_singleton_axis3_OK z α (.atom 1) (.atom 0)
      (getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 3).stamp 0)
  · have hget : (bfsRows (dotTreeAir (K := K)))[3] = (dotOp1BTree (K := K)).label := by
      simp [dot_air_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTreeAir (K := K)) 4).stamp 0 g.requests) hget]
    simp [dotOp1BTree, skelNode, extractNodeReqsAux_cons1]
    exact genRowMemForest_singleton_axis3_OK z α (.atom 1)
      (.cell (.atom 0) (.atom 1))
      (getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 4).stamp 0)
  · have hget : (bfsRows (dotTreeAir (K := K)))[4] = (dotOp1CTree (K := K)).label := by
      simp [dot_air_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTreeAir (K := K)) 5).stamp 0 g.requests) hget]
    simp [dotOp1CTree, skelNode, extractNodeReqsAux_cons1]
    exact genRowMemForest_singleton_axis3_OK z α (.atom 1) dotOp9Formula
      (getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 5).stamp 0)
  · have hget : (bfsRows (dotTreeAir (K := K)))[5] = (dotOp9Tree (K := K)).label := by
      simp [dot_air_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTreeAir (K := K)) 6).stamp 0 g.requests) hget]
    simp [dotOp9Tree, skelNode, extractNodeReqsAux_cons3]
    exact genRowMemForest_three_chain32_OK z α (.atom 9) (.atom 2)
      dotCoreFormula dotElem0 dotElem1
      (getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 6).stamp 0)
      (getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 6).stamp 1)
      (getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 6).stamp 2)
  · have hget : (bfsRows (dotTreeAir (K := K)))[6] = (dotOp9CoreTree (K := K)).label := by
      simp [dot_air_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTreeAir (K := K)) 7).stamp 0 g.requests) hget]
    simp [dotOp9CoreTree, skelNode, extractNodeReqsAux_cons1]
    exact genRowMemForest_singleton_axis3_OK z α (.atom 1) dotCore
      (getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 7).stamp 0)
  · have hget : (bfsRows (dotTreeAir (K := K)))[7] = (dotOp9InvokeTree (K := K)).label := by
      simp [dot_air_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTreeAir (K := K)) 8).stamp 0 g.requests) hget]
    simp [dotOp9InvokeTree, skelNode, extractNodeReqsAux_cons1]
    exact genRowMemForest_singleton_axis3_OK z α (.atom 1) (.atom 3)
      (getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 8).stamp 0)

theorem assignedMemForest_OK_air (z α : K) :
    ∀ u ∈ genMemForestFromTree (encC z) z α lmb (bfsAssign (dotTreeAir (K := K))),
      MemoryNodesOK z α (mapNTree GenMemoryRow.node u) :=
  genMemForestFromTree_of_rowOK z α _ (assigned_rowOK_air z α)

/-! ## AIR `BindComputeRow` / timestamp specialization -/

theorem bfsLabelAt_air_state (i : ℕ)
    (hi : i ∈ List.range' 1 (bfsForest [dotTreeAir (K := K)]).length) :
    (bfsLabelAt (dotTreeAir (K := K)) i).stamp.state =
      (bfsLabelAt (dotTreeAir (K := K)) i).skel.state :=
  bfsLabelAt_state _ i (lt_bfsRows_of_mem_range' hi)

theorem bfsLabelAt_air_bind (z α : K) (i : ℕ)
    (hi : i ∈ List.range' 1 (bfsForest [dotTreeAir (K := K)]).length) :
    BindComputeRow z (bfsLabelAt (dotTreeAir (K := K)) i).skel
      (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) i)).row := by
  rcases dot_air_bfs_index i hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hskel := bfsLabelAt_air_skel1 (K := K)
    have hstate : (bfsLabelAt (dotTreeAir (K := K)) 1).skel.state = State.s6 := by
      rw [hskel]; rfl
    rw [renderNode_op6_row z α _ hstate, hskel]
    refine genSkelOp6_bindCompute z α _ _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals simp [formulaHead, formulaTail, dotFormula, dotParentTail,
      dotBranchPair, dotCondFormula, dotThenFormula, dotElseFormula]
  · have hskel := bfsLabelAt_air_skel2 (K := K)
    have hstate : (bfsLabelAt (dotTreeAir (K := K)) 2).skel.state = State.s2 := by
      rw [hskel]; rfl
    rw [renderNode_op2_row z α _ hstate, hskel]
    refine genSkelOp2_bindCompute z α _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_
    all_goals simp [formulaHead, formulaTail, dotThenFormula, dotThenTail,
      dotOp2B, dotOp2C]
  · have hskel := bfsLabelAt_air_skel3 (K := K)
    have hstate : (bfsLabelAt (dotTreeAir (K := K)) 3).skel.state = State.s1 := by
      rw [hskel]; rfl
    rw [renderNode_op1_row z α _ hstate, hskel]
    simp [dotCondTree, skelNode]
    exact dot_op1_leaf_bind z α _ _ _ _ (by simp [formulaHead, dotCondFormula])
  · have hskel := bfsLabelAt_air_skel4 (K := K)
    have hstate : (bfsLabelAt (dotTreeAir (K := K)) 4).skel.state = State.s1 := by
      rw [hskel]; rfl
    rw [renderNode_op1_row z α _ hstate, hskel]
    simp [dotOp1BTree, skelNode]
    exact dot_op1_leaf_bind z α _ _ _ _ (by simp [formulaHead, dotOp2B])
  · have hskel := bfsLabelAt_air_skel5 (K := K)
    have hstate : (bfsLabelAt (dotTreeAir (K := K)) 5).skel.state = State.s1 := by
      rw [hskel]; rfl
    rw [renderNode_op1_row z α _ hstate, hskel]
    simp [dotOp1CTree, skelNode]
    exact dot_op1_leaf_bind z α _ _ _ _ (by simp [formulaHead, dotOp2C])
  · have hskel := bfsLabelAt_air_skel6 (K := K)
    have hstate : (bfsLabelAt (dotTreeAir (K := K)) 6).skel.state = State.s9 := by
      rw [hskel]; rfl
    rw [renderNode_op9_row z α _ hstate, hskel]
    refine genSkelOp9_bindCompute z α _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_
    all_goals simp [formulaHead, formulaTail, dotOp9Formula, dotOp9Tail,
      dotCoreFormula]
  · have hskel := bfsLabelAt_air_skel7 (K := K)
    have hstate : (bfsLabelAt (dotTreeAir (K := K)) 7).skel.state = State.s1 := by
      rw [hskel]; rfl
    rw [renderNode_op1_row z α _ hstate, hskel]
    simp [dotOp9CoreTree, skelNode]
    exact dot_op1_leaf_bind z α _ _ _ _ (by simp [formulaHead, dotCoreFormula])
  · have hskel := bfsLabelAt_air_skel8 (K := K)
    have hstate : (bfsLabelAt (dotTreeAir (K := K)) 8).skel.state = State.s1 := by
      rw [hskel]; rfl
    rw [renderNode_op1_row z α _ hstate, hskel]
    simp [dotOp9InvokeTree, skelNode]
    exact dot_op1_leaf_bind z α _ _ _ _ (by simp [formulaHead, dotArm, dotElem0])

theorem bfsLabelAt_air_specializes (z α : K) (i : ℕ)
    (hi : i ∈ List.range' 1 (bfsForest [dotTreeAir (K := K)]).length) :
    ComputeTimestampSpecializesAt α (bfsLabelAt (dotTreeAir (K := K)) i).stamp
      (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) i)).row := by
  have hst := bfsLabelAt_air_state i hi
  have hln : (bfsLabelAt (dotTreeAir (K := K)) i).stamp.lnPrevExponent ≤
      (bfsLabelAt (dotTreeAir (K := K)) i).stamp.lnExponent := by
    rw [bfsLabelAt_stamp (dotTreeAir (K := K)) i (lt_bfsRows_of_mem_range' hi)]
    exact stampOfAcc_lnPrev_le_lnExponent _ _
  have hrec : ∀ j : Fin 3,
      (bfsLabelAt (dotTreeAir (K := K)) i).stamp.lnPrevExponent ≤
        (bfsLabelAt (dotTreeAir (K := K)) i).stamp.recordExponent j := fun j => by
    rw [bfsLabelAt_stamp (dotTreeAir (K := K)) i (lt_bfsRows_of_mem_range' hi)]
    exact stampOfAcc_lnPrev_le_recordExponent _ _ j
  rcases dot_air_bfs_index i hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hstate : (bfsLabelAt (dotTreeAir (K := K)) 1).skel.state = State.s6 := by
      rw [bfsLabelAt_air_skel1]; rfl
    rw [renderNode_op6_row z α _ hstate]
    exact renderOp6Row_specializes z α _ _ (hst.trans hstate) hln hrec
  · have hstate : (bfsLabelAt (dotTreeAir (K := K)) 2).skel.state = State.s2 := by
      rw [bfsLabelAt_air_skel2]; rfl
    rw [renderNode_op2_row z α _ hstate]
    exact renderOp2Row_specializes z α _ _ (hst.trans hstate) hln hrec
  · have hstate : (bfsLabelAt (dotTreeAir (K := K)) 3).skel.state = State.s1 := by
      rw [bfsLabelAt_air_skel3]; rfl
    rw [renderNode_op1_row z α _ hstate]
    exact renderOp1Row_specializes z α _ _ (hst.trans hstate) hln hrec
  · have hstate : (bfsLabelAt (dotTreeAir (K := K)) 4).skel.state = State.s1 := by
      rw [bfsLabelAt_air_skel4]; rfl
    rw [renderNode_op1_row z α _ hstate]
    exact renderOp1Row_specializes z α _ _ (hst.trans hstate) hln hrec
  · have hstate : (bfsLabelAt (dotTreeAir (K := K)) 5).skel.state = State.s1 := by
      rw [bfsLabelAt_air_skel5]; rfl
    rw [renderNode_op1_row z α _ hstate]
    exact renderOp1Row_specializes z α _ _ (hst.trans hstate) hln hrec
  · have hstate : (bfsLabelAt (dotTreeAir (K := K)) 6).skel.state = State.s9 := by
      rw [bfsLabelAt_air_skel6]; rfl
    rw [renderNode_op9_row z α _ hstate]
    exact renderOp9Row_specializes z α _ _ (hst.trans hstate) hln hrec
  · have hstate : (bfsLabelAt (dotTreeAir (K := K)) 7).skel.state = State.s1 := by
      rw [bfsLabelAt_air_skel7]; rfl
    rw [renderNode_op1_row z α _ hstate]
    exact renderOp1Row_specializes z α _ _ (hst.trans hstate) hln hrec
  · have hstate : (bfsLabelAt (dotTreeAir (K := K)) 8).skel.state = State.s1 := by
      rw [bfsLabelAt_air_skel8]; rfl
    rw [renderNode_op1_row z α _ hstate]
    exact renderOp1Row_specializes z α _ _ (hst.trans hstate) hln hrec

/-! ## AIR compute nodes -/

def dotComputeNodesAir (z α : K) : NTree (ComputeNode K) :=
  mapNTree GenComputeRow.node (renderRows z α (bfsAssign (dotTreeAir (K := K))))

theorem dotComputeNodesAir_bfsForest (z α : K) :
    bfsForest [dotComputeNodesAir z α] =
      (bfsForest [bfsAssign (dotTreeAir (K := K))]).map
        (fun n => mapNTree GenComputeRow.node (renderRows z α n)) := by
  simp only [dotComputeNodesAir, renderRows_eq_mapNTree, mapNTree_comp]
  rw [show [mapNTree (GenComputeRow.node ∘ renderNode z α)
        (bfsAssign (dotTreeAir (K := K)))] =
      [bfsAssign (dotTreeAir (K := K))].map
        (mapNTree (GenComputeRow.node ∘ renderNode z α)) from rfl]
  rw [bfsForest_mapNTree]

theorem dotComputeNodesAir_OK (z α : K) :
    ComputeNodesOK z α (dotComputeNodesAir z α) := by
  intro t ht
  have hmem : t ∈ bfsForest [dotComputeNodesAir z α] :=
    (mem_bfsForest [dotComputeNodesAir z α] t).mpr
      ⟨dotComputeNodesAir z α, List.mem_singleton.mpr rfl, ht⟩
  rw [dotComputeNodesAir_bfsForest, bfsForest_bfsAssign_air, List.mem_map] at hmem
  obtain ⟨n, hn, rfl⟩ := hmem
  rw [List.mem_map] at hn
  obtain ⟨j, hj, rfl⟩ := hn
  have hnmem :
      buildTF 1 (foCol (bfsForest [dotTreeAir (K := K)]))
          (bfsLabelAt (dotTreeAir (K := K)))
          (bfsForest [dotTreeAir (K := K)]).length j ∈
        bfsForest [bfsAssign (dotTreeAir (K := K))] := by
    rw [bfsForest_bfsAssign_air]
    exact List.mem_map.mpr ⟨j, hj, rfl⟩
  have hch := bfsAssign_air_children_len hnmem
  have hnode :
      (mapNTree GenComputeRow.node
          (renderRows z α
            (buildTF 1 (foCol (bfsForest [dotTreeAir (K := K)]))
              (bfsLabelAt (dotTreeAir (K := K)))
              (bfsForest [dotTreeAir (K := K)]).length j))).label =
        (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) j)).node := by
    simp [renderRows_eq_mapNTree, mapNTree_label, buildTF_label, GenComputeRow.node]
  refine ⟨?flen, ?fstamp, ?fbind, ?ftime⟩
  · rw [mapNTree_children, renderRows_eq_mapNTree, mapNTree_children,
      List.length_map, List.length_map, hch]
    simp [buildTF_label, mapNTree_label,
      GenComputeRow.node, renderNode_op1_skel]
  · rw [hnode]
    simp [GenComputeRow.node, renderNode_op1_skel, renderNode_op1_stamp]
    exact bfsLabelAt_air_state j hj
  · rw [hnode]
    simp [GenComputeRow.node, renderNode_op1_skel]
    exact bfsLabelAt_air_bind z α j hj
  · rw [hnode]
    simp [GenComputeRow.node, renderNode_op1_stamp]
    exact bfsLabelAt_air_specializes z α j hj

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.assignedMemForest_OK_air
#print axioms Nock.NockVMROM.Thm54.TraceGen.dotComputeNodesAir_OK
