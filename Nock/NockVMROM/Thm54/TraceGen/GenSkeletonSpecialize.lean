/-
  Nock/NockVMROM/Thm54/TraceGen/GenSkeletonSpecialize.lean

  Timestamp specialization of every `render*Row`, then of `renderNode`,
  then `ComputeNodesOK` on `renderRows (bfsAssign t)` for any successful
  `genComputeSkeleton` tree.

  `Gen.lean` is not edited.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenSkeletonBind
import Nock.NockVMROM.Thm54.TraceGen.GenTierAData

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Noun Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.HonestCommitment
open ComputeTable

variable {K : Type} [Field K]

/-! ## Remaining `render*Row` timestamp specialization -/

theorem renderConsRow_specializes (z α : K) (stamp : ComputeTimestampRow)
    (skel : ComputeRowSkeleton) (hstate : stamp.state = State.cons)
    (hln : stamp.lnPrevExponent ≤ stamp.lnExponent)
    (hrec : ∀ i : Fin 3, stamp.lnPrevExponent ≤ stamp.recordExponent i) :
    ComputeTimestampSpecializesAt α stamp (renderConsRow z α stamp skel) := by
  refine ComputeTimestampSpecializesAt.of_absolute
    ?_ rfl ?_ rfl rfl ?_ ?_ hln hrec
  · simp [renderConsRow, hstate]
  · simp [renderConsRow, hstate]
  · intro i
    fin_cases i <;>
      simp [renderConsRow, computeMemRec, computeMemRecKind, hstate,
        Nock.Framework.recordCount, MemRec.zero]
  · intro i hi
    simp [computeMemRecKind, hstate, Nock.Framework.recordCount] at hi
    fin_cases i <;> simp_all [renderConsRow, computeMemRec, MemRec.zero]

theorem renderOp0Row_specializes (z α : K) (stamp : ComputeTimestampRow)
    (skel : ComputeRowSkeleton) (hstate : stamp.state = State.s0)
    (hln : stamp.lnPrevExponent ≤ stamp.lnExponent)
    (hrec : ∀ i : Fin 3, stamp.lnPrevExponent ≤ stamp.recordExponent i) :
    ComputeTimestampSpecializesAt α stamp (renderOp0Row z α stamp skel) := by
  refine ComputeTimestampSpecializesAt.of_absolute
    ?_ rfl ?_ rfl rfl ?_ ?_ hln hrec
  · simp [renderOp0Row, hstate]
  · simp [renderOp0Row, hstate]
  · intro i
    fin_cases i <;>
      simp [renderOp0Row, computeMemRec, computeMemRecKind, hstate,
        Nock.Framework.recordCount, MemRec.zero]
  · intro i hi
    simp [computeMemRecKind, hstate, Nock.Framework.recordCount] at hi
    fin_cases i <;> simp_all [renderOp0Row, computeMemRec, MemRec.zero]

theorem renderOp3Row_specializes (z α : K) (stamp : ComputeTimestampRow)
    (skel : ComputeRowSkeleton) (hstate : stamp.state = State.s3)
    (hln : stamp.lnPrevExponent ≤ stamp.lnExponent)
    (hrec : ∀ i : Fin 3, stamp.lnPrevExponent ≤ stamp.recordExponent i) :
    ComputeTimestampSpecializesAt α stamp (renderOp3Row z α stamp skel) := by
  refine ComputeTimestampSpecializesAt.of_absolute
    ?_ rfl ?_ rfl rfl ?_ ?_ hln hrec
  · simp [renderOp3Row, hstate]
  · simp [renderOp3Row, hstate]
  · intro i
    fin_cases i <;>
      simp [renderOp3Row, computeMemRec, computeMemRecKind, hstate,
        Nock.Framework.recordCount, MemRec.zero]
  · intro i hi
    simp [computeMemRecKind, hstate, Nock.Framework.recordCount] at hi
    fin_cases i <;> simp_all [renderOp3Row, computeMemRec, MemRec.zero]

theorem renderOp4Row_specializes (z α : K) (stamp : ComputeTimestampRow)
    (skel : ComputeRowSkeleton) (hstate : stamp.state = State.s4)
    (hln : stamp.lnPrevExponent ≤ stamp.lnExponent)
    (hrec : ∀ i : Fin 3, stamp.lnPrevExponent ≤ stamp.recordExponent i) :
    ComputeTimestampSpecializesAt α stamp (renderOp4Row z α stamp skel) := by
  refine ComputeTimestampSpecializesAt.of_absolute
    ?_ rfl ?_ rfl rfl ?_ ?_ hln hrec
  · simp [renderOp4Row, hstate]
  · simp [renderOp4Row, hstate]
  · intro i
    fin_cases i <;>
      simp [renderOp4Row, computeMemRec, computeMemRecKind, hstate,
        Nock.Framework.recordCount, MemRec.zero]
  · intro i hi
    simp [computeMemRecKind, hstate, Nock.Framework.recordCount] at hi
    fin_cases i <;> simp_all [renderOp4Row, computeMemRec, MemRec.zero]

theorem renderOp5Row_specializes (z α : K) (stamp : ComputeTimestampRow)
    (skel : ComputeRowSkeleton) (hstate : stamp.state = State.s5)
    (hln : stamp.lnPrevExponent ≤ stamp.lnExponent)
    (hrec : ∀ i : Fin 3, stamp.lnPrevExponent ≤ stamp.recordExponent i) :
    ComputeTimestampSpecializesAt α stamp (renderOp5Row z α stamp skel) := by
  refine ComputeTimestampSpecializesAt.of_absolute
    ?_ rfl ?_ rfl rfl ?_ ?_ hln hrec
  · simp [renderOp5Row, hstate]
  · simp [renderOp5Row, hstate]
  · intro i
    fin_cases i <;>
      simp [renderOp5Row, computeMemRec, computeMemRecKind, hstate,
        Nock.Framework.recordCount, MemRec.zero]
  · intro i hi
    simp [computeMemRecKind, hstate, Nock.Framework.recordCount] at hi
    fin_cases i <;> simp_all [renderOp5Row, computeMemRec, MemRec.zero]

theorem renderOp7Row_specializes (z α : K) (stamp : ComputeTimestampRow)
    (skel : ComputeRowSkeleton) (hstate : stamp.state = State.s7)
    (hln : stamp.lnPrevExponent ≤ stamp.lnExponent)
    (hrec : ∀ i : Fin 3, stamp.lnPrevExponent ≤ stamp.recordExponent i) :
    ComputeTimestampSpecializesAt α stamp (renderOp7Row z α stamp skel) := by
  refine ComputeTimestampSpecializesAt.of_absolute
    ?_ rfl ?_ rfl rfl ?_ ?_ hln hrec
  · simp [renderOp7Row, hstate]
  · simp [renderOp7Row, hstate]
  · intro i
    fin_cases i <;>
      simp [renderOp7Row, computeMemRec, computeMemRecKind, hstate,
        Nock.Framework.recordCount, MemRec.zero]
  · intro i hi
    simp [computeMemRecKind, hstate, Nock.Framework.recordCount] at hi
    fin_cases i <;> simp_all [renderOp7Row, computeMemRec, MemRec.zero]

theorem renderOp8Row_specializes (z α : K) (stamp : ComputeTimestampRow)
    (skel : ComputeRowSkeleton) (hstate : stamp.state = State.s8)
    (hln : stamp.lnPrevExponent ≤ stamp.lnExponent)
    (hrec : ∀ i : Fin 3, stamp.lnPrevExponent ≤ stamp.recordExponent i) :
    ComputeTimestampSpecializesAt α stamp (renderOp8Row z α stamp skel) := by
  refine ComputeTimestampSpecializesAt.of_absolute
    ?_ rfl ?_ rfl rfl ?_ ?_ hln hrec
  · simp [renderOp8Row, hstate]
  · simp [renderOp8Row, hstate]
  · intro i
    fin_cases i <;>
      simp [renderOp8Row, computeMemRec, computeMemRecKind, hstate,
        Nock.Framework.recordCount, MemRec.zero]
  · intro i hi
    simp [computeMemRecKind, hstate, Nock.Framework.recordCount] at hi
    fin_cases i <;> simp_all [renderOp8Row, computeMemRec, MemRec.zero]

/-- Rendered node specializes at its stamp whenever stamp/state agree. -/
theorem renderNode_specializes (z α : K) (g : GenComputeRow K)
    (hstate : g.stamp.state = g.skel.state)
    (hln : g.stamp.lnPrevExponent ≤ g.stamp.lnExponent)
    (hrec : ∀ i : Fin 3, g.stamp.lnPrevExponent ≤ g.stamp.recordExponent i) :
    ComputeTimestampSpecializesAt α g.stamp (renderNode z α g).row := by
  cases hst : g.skel.state
  · rw [renderNode_op0_row z α g hst]
    exact renderOp0Row_specializes z α g.stamp g.skel (hstate.trans hst) hln hrec
  · rw [renderNode_op1_row z α g hst]
    exact renderOp1Row_specializes z α g.stamp g.skel (hstate.trans hst) hln hrec
  · rw [renderNode_op2_row z α g hst]
    exact renderOp2Row_specializes z α g.stamp g.skel (hstate.trans hst) hln hrec
  · rw [renderNode_op3_row z α g hst]
    exact renderOp3Row_specializes z α g.stamp g.skel (hstate.trans hst) hln hrec
  · rw [renderNode_op4_row z α g hst]
    exact renderOp4Row_specializes z α g.stamp g.skel (hstate.trans hst) hln hrec
  · rw [renderNode_op5_row z α g hst]
    exact renderOp5Row_specializes z α g.stamp g.skel (hstate.trans hst) hln hrec
  · rw [renderNode_op6_row z α g hst]
    exact renderOp6Row_specializes z α g.stamp g.skel (hstate.trans hst) hln hrec
  · rw [renderNode_op7_row z α g hst]
    exact renderOp7Row_specializes z α g.stamp g.skel (hstate.trans hst) hln hrec
  · rw [renderNode_op8_row z α g hst]
    exact renderOp8Row_specializes z α g.stamp g.skel (hstate.trans hst) hln hrec
  · rw [renderNode_op9_row z α g hst]
    exact renderOp9Row_specializes z α g.stamp g.skel (hstate.trans hst) hln hrec
  · rw [renderNode_cons_row z α g hst]
    exact renderConsRow_specializes z α g.stamp g.skel (hstate.trans hst) hln hrec

theorem bfsLabelAt_specializes (z α : K) (t : NTree (GenComputeRow K))
    {i : ℕ} (hi : i ∈ List.range' 1 (bfsForest [t]).length) :
    ComputeTimestampSpecializesAt α (bfsLabelAt t i).stamp
      (renderNode z α (bfsLabelAt t i)).row :=
  renderNode_specializes z α (bfsLabelAt t i)
    (bfsLabelAt_state t i (lt_bfsRows_of_mem_range' hi))
    (by
      rw [bfsLabelAt_stamp t i (lt_bfsRows_of_mem_range' hi)]
      exact stampOfAcc_lnPrev_le_lnExponent _ _)
    (fun j => by
      rw [bfsLabelAt_stamp t i (lt_bfsRows_of_mem_range' hi)]
      exact stampOfAcc_lnPrev_le_recordExponent _ _ j)

/-! ## `ComputeNodesOK` on generated assigned trees -/

theorem renderRows_bfsAssign_bfsForest (z α : K) (t : NTree (GenComputeRow K)) :
    bfsForest [mapNTree GenComputeRow.node (renderRows z α (bfsAssign t))] =
      (bfsForest [bfsAssign t]).map
        (fun n => mapNTree GenComputeRow.node (renderRows z α n)) := by
  simp only [renderRows_eq_mapNTree, mapNTree_comp]
  rw [show [mapNTree (GenComputeRow.node ∘ renderNode z α) (bfsAssign t)] =
      [bfsAssign t].map
        (mapNTree (GenComputeRow.node ∘ renderNode z α)) from rfl]
  rw [bfsForest_mapNTree]

/-- Local validity of every committed compute node of a generated tree. -/
theorem genComputeSkeleton_computeNodes_OK
    (z α : K)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (hgen : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result)) :
    ComputeNodesOK z α
      (mapNTree GenComputeRow.node (renderRows z α (bfsAssign t))) := by
  intro u hu
  have hmem :
      u ∈ bfsForest
        [mapNTree GenComputeRow.node (renderRows z α (bfsAssign t))] :=
    (mem_bfsForest
        [mapNTree GenComputeRow.node (renderRows z α (bfsAssign t))] u).mpr
      ⟨_, List.mem_singleton.mpr rfl, hu⟩
  rw [renderRows_bfsAssign_bfsForest, bfsForest_bfsAssign, List.mem_map] at hmem
  obtain ⟨n, hn, rfl⟩ := hmem
  rw [List.mem_map] at hn
  obtain ⟨j, hj, rfl⟩ := hn
  have hnmem :
      buildTF 1 (foCol (bfsForest [t])) (bfsLabelAt t)
          (bfsForest [t]).length j ∈
        bfsForest [bfsAssign t] := by
    rw [bfsForest_bfsAssign]
    exact List.mem_map.mpr ⟨j, hj, rfl⟩
  have hch := genComputeSkeleton_bfsAssign_fanout hgen hnmem
  have hnode :
      (mapNTree GenComputeRow.node
          (renderRows z α
            (buildTF 1 (foCol (bfsForest [t])) (bfsLabelAt t)
              (bfsForest [t]).length j))).label =
        (renderNode z α (bfsLabelAt t j)).node := by
    simp [renderRows_eq_mapNTree, mapNTree_label, buildTF_label,
      GenComputeRow.node]
  refine ⟨?flen, ?fstamp, ?fbind, ?ftime⟩
  · rw [mapNTree_children, renderRows_eq_mapNTree, mapNTree_children,
      List.length_map, List.length_map, hch]
    simp [buildTF_label, mapNTree_label, GenComputeRow.node,
      renderNode_op1_skel]
  · rw [hnode]
    simp [GenComputeRow.node, renderNode_op1_skel, renderNode_op1_stamp]
    exact bfsLabelAt_state t j (lt_bfsRows_of_mem_range' hj)
  · rw [hnode]
    simp [GenComputeRow.node, renderNode_op1_skel]
    exact genComputeSkeleton_bfsLabelAt_bind z α hgen hj
  · rw [hnode]
    simp [GenComputeRow.node, renderNode_op1_stamp]
    exact bfsLabelAt_specializes z α t hj

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.renderNode_specializes
#print axioms Nock.NockVMROM.Thm54.TraceGen.genComputeSkeleton_computeNodes_OK
