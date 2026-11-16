/-
  Nock/NockVMROM/Thm54/TraceGen/GenTierANodup.lean

  Opcode-active request timestamps on the generated eight-row BFS render
  are `α^1..α^13` (`liveRecordExps_dot`).  `requestNodup` inhabits on
  `DotConfig769` because `orderOf (4 : ZMod 769) = 192 > 12`, so those
  thirteen powers are distinct.

  `DotConfig257` cannot inhabit `requestNodup` for `α = φ(4)`: `orderOf
  (4 : ZMod 257) = 8`, so `α^1 = α^9` and `α^5 = α^13`.  That field stays
  the table host.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenTierARows
import Nock.NockVMROM.Thm54.TraceGen.GenTierARowsAir
import Nock.NockVMROM.Thm54.TraceGen.GenTierAConfig769
import Nock.NockVMROM.Thm54.Language

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk Nock.NockVM
open Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy

variable {K : Type} [Field K]

theorem encRecC_ne_of_ts_ne {r s : MemRec K} {c : K} (h : r.ts ≠ s.ts) :
    encRecC r c ≠ encRecC s c := by
  intro he
  exact h (by have hc := congrFun he (7 : Fin 9); change r.ts = s.ts at hc; exact hc)

theorem encoded_nodup_of_ts_nodup (rs : List (MemRec K))
    (h : (rs.map (fun r => r.ts)).Nodup) :
    (rs.map (fun r => encRecC r 1)).Nodup := by
  refine (List.nodup_iff_injective_getElem (l := rs.map (fun r => encRecC r 1))).2 ?_
  intro i j hij
  have hlen : (rs.map (fun r => encRecC r 1)).length = (rs.map (fun r => r.ts)).length := by simp
  have hi : i.1 < (rs.map (fun r => r.ts)).length := by simpa [hlen] using i.2
  have hj : j.1 < (rs.map (fun r => r.ts)).length := by simpa [hlen] using j.2
  have hrs : rs[i.1].ts = rs[j.1].ts := by
    by_contra hne
    have henc : encRecC rs[i.1] 1 = encRecC rs[j.1] 1 := by
      simpa [List.getElem_map] using hij
    exact encRecC_ne_of_ts_ne hne henc
  have hts : (rs.map (fun r => r.ts))[i.1] = (rs.map (fun r => r.ts))[j.1] := by
    simpa [List.getElem_map] using hrs
  have inj := (List.nodup_iff_injective_getElem
      (l := rs.map (fun r => r.ts))).1 h
  have hij' : (⟨i.1, hi⟩ : Fin (rs.map (fun r => r.ts)).length) =
      ⟨j.1, hj⟩ := inj hts
  injection hij' with hval
  exact Fin.eq_of_val_eq hval

theorem recExp_eq_getRecordExp (stamp : ComputeTimestampRow) (i : Fin 3) :
    stamp.recordExponent i = getRecordExp stamp (i : ℕ) := by
  unfold getRecordExp
  rw [dif_pos i.isLt]

theorem liveRecordExps_named :
    getRecordExp (bfsLabelAt (dotTree (K := K)) 1).stamp 0 = 1 ∧
    getRecordExp (bfsLabelAt (dotTree (K := K)) 1).stamp 1 = 2 ∧
    getRecordExp (bfsLabelAt (dotTree (K := K)) 1).stamp 2 = 3 ∧
    getRecordExp (bfsLabelAt (dotTree (K := K)) 2).stamp 0 = 4 ∧
    getRecordExp (bfsLabelAt (dotTree (K := K)) 3).stamp 0 = 5 ∧
    getRecordExp (bfsLabelAt (dotTree (K := K)) 3).stamp 1 = 6 ∧
    getRecordExp (bfsLabelAt (dotTree (K := K)) 4).stamp 0 = 7 ∧
    getRecordExp (bfsLabelAt (dotTree (K := K)) 5).stamp 0 = 8 ∧
    getRecordExp (bfsLabelAt (dotTree (K := K)) 6).stamp 0 = 9 ∧
    getRecordExp (bfsLabelAt (dotTree (K := K)) 6).stamp 1 = 10 ∧
    getRecordExp (bfsLabelAt (dotTree (K := K)) 6).stamp 2 = 11 ∧
    getRecordExp (bfsLabelAt (dotTree (K := K)) 7).stamp 0 = 12 ∧
    getRecordExp (bfsLabelAt (dotTree (K := K)) 8).stamp 0 = 13 := by
  have h := liveRecordExps_dot (K := K)
  simp [List.cons.injEq] at h
  exact h

theorem range13_pows (α : K) :
    (List.range 13).map (fun i => α ^ (i + 1)) =
      [α ^ 1, α ^ 2, α ^ 3, α ^ 4, α ^ 5, α ^ 6, α ^ 7,
       α ^ 8, α ^ 9, α ^ 10, α ^ 11, α ^ 12, α ^ 13] :=
  rfl

private theorem row_s6 :
    (bfsLabelAt (dotTree (K := K)) 1).skel.state = State.s6 := by
  rw [bfsLabelAt_dot_skel1]; rfl

private theorem row_s1_2 :
    (bfsLabelAt (dotTree (K := K)) 2).skel.state = State.s1 := by
  rw [bfsLabelAt_dot_skel2]; rfl

private theorem row_s2 :
    (bfsLabelAt (dotTree (K := K)) 3).skel.state = State.s2 := by
  rw [bfsLabelAt_dot_skel3]; rfl

private theorem row_s1_4 :
    (bfsLabelAt (dotTree (K := K)) 4).skel.state = State.s1 := by
  rw [bfsLabelAt_dot_skel4]; rfl

private theorem row_s1_5 :
    (bfsLabelAt (dotTree (K := K)) 5).skel.state = State.s1 := by
  rw [bfsLabelAt_dot_skel5]; rfl

private theorem row_s9 :
    (bfsLabelAt (dotTree (K := K)) 6).skel.state = State.s9 := by
  rw [bfsLabelAt_dot_skel6]; rfl

private theorem row_s1_7 :
    (bfsLabelAt (dotTree (K := K)) 7).skel.state = State.s1 := by
  rw [bfsLabelAt_dot_skel7]; rfl

private theorem row_s1_8 :
    (bfsLabelAt (dotTree (K := K)) 8).skel.state = State.s1 := by
  rw [bfsLabelAt_dot_skel8]; rfl

theorem rendered_row1_ts (z α : K) :
    (activeRequestRecords
        (renderNode z α (bfsLabelAt (dotTree (K := K)) 1)).row.2.2.1).map
      (fun r => r.ts) =
      [α ^ 1, α ^ 2, α ^ 3] := by
  rw [renderNode_op6_row z α _ row_s6]
  simp [activeRequestRecords, renderOp6Row, recExp_eq_getRecordExp,
    liveRecordExps_named, pow_one]

theorem rendered_row2_ts (z α : K) :
    (activeRequestRecords
        (renderNode z α (bfsLabelAt (dotTree (K := K)) 2)).row.2.2.1).map
      (fun r => r.ts) =
      [α ^ 4] := by
  rw [renderNode_op1_row z α _ row_s1_2]
  simp [activeRequestRecords, renderOp1Row, recExp_eq_getRecordExp,
    liveRecordExps_named, pow_one]

theorem rendered_row3_ts (z α : K) :
    (activeRequestRecords
        (renderNode z α (bfsLabelAt (dotTree (K := K)) 3)).row.2.2.1).map
      (fun r => r.ts) =
      [α ^ 5, α ^ 6] := by
  rw [renderNode_op2_row z α _ row_s2]
  simp [activeRequestRecords, renderOp2Row, recExp_eq_getRecordExp,
    liveRecordExps_named, pow_one]

theorem rendered_row4_ts (z α : K) :
    (activeRequestRecords
        (renderNode z α (bfsLabelAt (dotTree (K := K)) 4)).row.2.2.1).map
      (fun r => r.ts) =
      [α ^ 7] := by
  rw [renderNode_op1_row z α _ row_s1_4]
  simp [activeRequestRecords, renderOp1Row, recExp_eq_getRecordExp,
    liveRecordExps_named, pow_one]

theorem rendered_row5_ts (z α : K) :
    (activeRequestRecords
        (renderNode z α (bfsLabelAt (dotTree (K := K)) 5)).row.2.2.1).map
      (fun r => r.ts) =
      [α ^ 8] := by
  rw [renderNode_op1_row z α _ row_s1_5]
  simp [activeRequestRecords, renderOp1Row, recExp_eq_getRecordExp,
    liveRecordExps_named, pow_one]

theorem rendered_row6_ts (z α : K) :
    (activeRequestRecords
        (renderNode z α (bfsLabelAt (dotTree (K := K)) 6)).row.2.2.1).map
      (fun r => r.ts) =
      [α ^ 9, α ^ 10, α ^ 11] := by
  rw [renderNode_op9_row z α _ row_s9]
  simp [activeRequestRecords, renderOp9Row, recExp_eq_getRecordExp,
    liveRecordExps_named, pow_one]

theorem rendered_row7_ts (z α : K) :
    (activeRequestRecords
        (renderNode z α (bfsLabelAt (dotTree (K := K)) 7)).row.2.2.1).map
      (fun r => r.ts) =
      [α ^ 12] := by
  rw [renderNode_op1_row z α _ row_s1_7]
  simp [activeRequestRecords, renderOp1Row, recExp_eq_getRecordExp,
    liveRecordExps_named, pow_one]

theorem rendered_row8_ts (z α : K) :
    (activeRequestRecords
        (renderNode z α (bfsLabelAt (dotTree (K := K)) 8)).row.2.2.1).map
      (fun r => r.ts) =
      [α ^ 13] := by
  rw [renderNode_op1_row z α _ row_s1_8]
  simp [activeRequestRecords, renderOp1Row, recExp_eq_getRecordExp,
    liveRecordExps_named, pow_one]

theorem rendered_request_timestamps (z α : K) :
    ([(renderNode z α (bfsLabelAt (dotTree (K := K)) 1)).row,
      (renderNode z α (bfsLabelAt (dotTree (K := K)) 2)).row,
      (renderNode z α (bfsLabelAt (dotTree (K := K)) 3)).row,
      (renderNode z α (bfsLabelAt (dotTree (K := K)) 4)).row,
      (renderNode z α (bfsLabelAt (dotTree (K := K)) 5)).row,
      (renderNode z α (bfsLabelAt (dotTree (K := K)) 6)).row,
      (renderNode z α (bfsLabelAt (dotTree (K := K)) 7)).row,
      (renderNode z α (bfsLabelAt (dotTree (K := K)) 8)).row].flatMap
        (fun row => activeRequestRecords row.2.2.1)).map
      (fun r => r.ts) =
      [α ^ 1, α ^ 2, α ^ 3, α ^ 4, α ^ 5, α ^ 6, α ^ 7,
       α ^ 8, α ^ 9, α ^ 10, α ^ 11, α ^ 12, α ^ 13] := by
  simp [List.flatMap_cons, List.flatMap_nil, List.map_append,
    rendered_row1_ts, rendered_row2_ts, rendered_row3_ts, rendered_row4_ts,
    rendered_row5_ts, rendered_row6_ts, rendered_row7_ts, rendered_row8_ts]

/-! ## AIR-ordered timestamps -/

theorem liveRecordExps_air_named :
    getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 1).stamp 0 = 1 ∧
    getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 1).stamp 1 = 2 ∧
    getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 1).stamp 2 = 3 ∧
    getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 2).stamp 0 = 4 ∧
    getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 2).stamp 1 = 5 ∧
    getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 3).stamp 0 = 6 ∧
    getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 4).stamp 0 = 7 ∧
    getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 5).stamp 0 = 8 ∧
    getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 6).stamp 0 = 9 ∧
    getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 6).stamp 1 = 10 ∧
    getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 6).stamp 2 = 11 ∧
    getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 7).stamp 0 = 12 ∧
    getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 8).stamp 0 = 13 := by
  have h := liveRecordExps_air (K := K)
  simp [List.cons.injEq] at h
  exact h

private theorem air_row_s6 :
    (bfsLabelAt (dotTreeAir (K := K)) 1).skel.state = State.s6 := by
  rw [bfsLabelAt_air_skel1]; rfl

private theorem air_row_s2 :
    (bfsLabelAt (dotTreeAir (K := K)) 2).skel.state = State.s2 := by
  rw [bfsLabelAt_air_skel2]; rfl

private theorem air_row_s1_3 :
    (bfsLabelAt (dotTreeAir (K := K)) 3).skel.state = State.s1 := by
  rw [bfsLabelAt_air_skel3]; rfl

private theorem air_row_s1_4 :
    (bfsLabelAt (dotTreeAir (K := K)) 4).skel.state = State.s1 := by
  rw [bfsLabelAt_air_skel4]; rfl

private theorem air_row_s1_5 :
    (bfsLabelAt (dotTreeAir (K := K)) 5).skel.state = State.s1 := by
  rw [bfsLabelAt_air_skel5]; rfl

private theorem air_row_s9 :
    (bfsLabelAt (dotTreeAir (K := K)) 6).skel.state = State.s9 := by
  rw [bfsLabelAt_air_skel6]; rfl

private theorem air_row_s1_7 :
    (bfsLabelAt (dotTreeAir (K := K)) 7).skel.state = State.s1 := by
  rw [bfsLabelAt_air_skel7]; rfl

private theorem air_row_s1_8 :
    (bfsLabelAt (dotTreeAir (K := K)) 8).skel.state = State.s1 := by
  rw [bfsLabelAt_air_skel8]; rfl

theorem rendered_air_row1_ts (z α : K) :
    (activeRequestRecords
        (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) 1)).row.2.2.1).map
      (fun r => r.ts) =
      [α ^ 1, α ^ 2, α ^ 3] := by
  rw [renderNode_op6_row z α _ air_row_s6]
  simp [activeRequestRecords, renderOp6Row, recExp_eq_getRecordExp,
    liveRecordExps_air_named, pow_one]

theorem rendered_air_row2_ts (z α : K) :
    (activeRequestRecords
        (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) 2)).row.2.2.1).map
      (fun r => r.ts) =
      [α ^ 4, α ^ 5] := by
  rw [renderNode_op2_row z α _ air_row_s2]
  simp [activeRequestRecords, renderOp2Row, recExp_eq_getRecordExp,
    liveRecordExps_air_named, pow_one]

theorem rendered_air_row3_ts (z α : K) :
    (activeRequestRecords
        (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) 3)).row.2.2.1).map
      (fun r => r.ts) =
      [α ^ 6] := by
  rw [renderNode_op1_row z α _ air_row_s1_3]
  simp [activeRequestRecords, renderOp1Row, recExp_eq_getRecordExp,
    liveRecordExps_air_named, pow_one]

theorem rendered_air_row4_ts (z α : K) :
    (activeRequestRecords
        (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) 4)).row.2.2.1).map
      (fun r => r.ts) =
      [α ^ 7] := by
  rw [renderNode_op1_row z α _ air_row_s1_4]
  simp [activeRequestRecords, renderOp1Row, recExp_eq_getRecordExp,
    liveRecordExps_air_named, pow_one]

theorem rendered_air_row5_ts (z α : K) :
    (activeRequestRecords
        (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) 5)).row.2.2.1).map
      (fun r => r.ts) =
      [α ^ 8] := by
  rw [renderNode_op1_row z α _ air_row_s1_5]
  simp [activeRequestRecords, renderOp1Row, recExp_eq_getRecordExp,
    liveRecordExps_air_named, pow_one]

theorem rendered_air_row6_ts (z α : K) :
    (activeRequestRecords
        (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) 6)).row.2.2.1).map
      (fun r => r.ts) =
      [α ^ 9, α ^ 10, α ^ 11] := by
  rw [renderNode_op9_row z α _ air_row_s9]
  simp [activeRequestRecords, renderOp9Row, recExp_eq_getRecordExp,
    liveRecordExps_air_named, pow_one]

theorem rendered_air_row7_ts (z α : K) :
    (activeRequestRecords
        (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) 7)).row.2.2.1).map
      (fun r => r.ts) =
      [α ^ 12] := by
  rw [renderNode_op1_row z α _ air_row_s1_7]
  simp [activeRequestRecords, renderOp1Row, recExp_eq_getRecordExp,
    liveRecordExps_air_named, pow_one]

theorem rendered_air_row8_ts (z α : K) :
    (activeRequestRecords
        (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) 8)).row.2.2.1).map
      (fun r => r.ts) =
      [α ^ 13] := by
  rw [renderNode_op1_row z α _ air_row_s1_8]
  simp [activeRequestRecords, renderOp1Row, recExp_eq_getRecordExp,
    liveRecordExps_air_named, pow_one]

theorem rendered_request_timestamps_air (z α : K) :
    ([(renderNode z α (bfsLabelAt (dotTreeAir (K := K)) 1)).row,
      (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) 2)).row,
      (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) 3)).row,
      (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) 4)).row,
      (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) 5)).row,
      (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) 6)).row,
      (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) 7)).row,
      (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) 8)).row].flatMap
        (fun row => activeRequestRecords row.2.2.1)).map
      (fun r => r.ts) =
      [α ^ 1, α ^ 2, α ^ 3, α ^ 4, α ^ 5, α ^ 6, α ^ 7,
       α ^ 8, α ^ 9, α ^ 10, α ^ 11, α ^ 12, α ^ 13] := by
  simp [List.flatMap_cons, List.flatMap_nil, List.map_append,
    rendered_air_row1_ts, rendered_air_row2_ts, rendered_air_row3_ts,
    rendered_air_row4_ts, rendered_air_row5_ts, rendered_air_row6_ts,
    rendered_air_row7_ts, rendered_air_row8_ts]

end Nock.NockVMROM.Thm54.TraceGen

namespace Nock.NockVMROM.Thm54.TraceGen.DotConfig257

open Nock Nock.Walk Nock.NockVM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen

theorem rawRequest_timestamps (z α : K) :
    (exec z α).rawRequests.map (fun r => r.ts) =
      [α ^ 1, α ^ 2, α ^ 3, α ^ 4, α ^ 5, α ^ 6, α ^ 7,
       α ^ 8, α ^ 9, α ^ 10, α ^ 11, α ^ 12, α ^ 13] := by
  rw [ExactExecution.rawRequests_eq_computeRows, computeRows_eq]
  exact rendered_request_timestamps z α

end Nock.NockVMROM.Thm54.TraceGen.DotConfig257

namespace Nock.NockVMROM.Thm54.TraceGen.DotConfig769

open Nock Nock.Walk Nock.NockVM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen

theorem computeRows_eq (z α : K) :
    (exec z α).computeRows =
      [(renderNode z α (bfsLabelAt (dotTreeAir (K := K)) 1)).row,
       (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) 2)).row,
       (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) 3)).row,
       (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) 4)).row,
       (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) 5)).row,
       (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) 6)).row,
       (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) 7)).row,
       (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) 8)).row] := by
  unfold ExactExecution.computeRows
  change (bfsForest [computeTree z α]).map NTree.label = _
  unfold computeTree
  rw [renderRows_eq_mapNTree, mapNTree_comp]
  rw [show [mapNTree (GenComputeRow.row ∘ renderNode z α)
        (bfsAssign (dotTreeAir (K := K)))] =
      [bfsAssign (dotTreeAir (K := K))].map
        (mapNTree (GenComputeRow.row ∘ renderNode z α)) from rfl]
  rw [bfsForest_mapNTree, List.map_map]
  have hcomp :
      NTree.label ∘ mapNTree (GenComputeRow.row ∘ renderNode z α) =
        (fun g => (renderNode z α g).row) ∘ NTree.label := by
    funext n
    change (mapNTree (GenComputeRow.row ∘ renderNode z α) n).label =
      (renderNode z α n.label).row
    rw [mapNTree_label]
    rfl
  rw [hcomp, ← List.map_map, bfsAssign_bfsForest_labels, List.map_map]
  have hlen : (bfsForest [dotTreeAir (K := K)]).length = 8 := by
    simp [dot_air_bfsForest]
  rw [hlen]
  rfl

theorem rawRequest_timestamps (z α : K) :
    (exec z α).rawRequests.map (fun r => r.ts) =
      [α ^ 1, α ^ 2, α ^ 3, α ^ 4, α ^ 5, α ^ 6, α ^ 7,
       α ^ 8, α ^ 9, α ^ 10, α ^ 11, α ^ 12, α ^ 13] := by
  rw [ExactExecution.rawRequests_eq_computeRows, computeRows_eq]
  exact rendered_request_timestamps_air z α

theorem four_pows_nodup :
    ((List.range 13).map (fun i => (4 : F) ^ (i + 1))).Nodup := by
  decide

theorem alphaA_pow (n : ℕ) : alphaA ^ n = φ ((4 : F) ^ n) := by
  simp [alphaA, map_pow]

theorem alpha_pows_nodup :
    ((List.range 13).map (fun i => alphaA ^ (i + 1))).Nodup := by
  have hmap :
      (List.range 13).map (fun i => alphaA ^ (i + 1)) =
        ((List.range 13).map (fun i => (4 : F) ^ (i + 1))).map φ := by
    simp [alphaA_pow, List.map_map, Function.comp]
  rw [hmap]
  exact four_pows_nodup.map φ_injective

theorem requestNodup :
    (exec seedZ alphaA).derivedRequestIO.Nodup := by
  -- The Form R request encode keeps `ts` at coordinate `7`.
  unfold ExactExecution.derivedRequestIO
  refine List.Nodup.of_map (fun f => f 7) ?_
  rw [List.map_map]
  show ((exec seedZ alphaA).rawRequests.map (fun r => r.ts)).Nodup
  rw [rawRequest_timestamps, ← range13_pows]
  exact alpha_pows_nodup

end Nock.NockVMROM.Thm54.TraceGen.DotConfig769

#print axioms Nock.NockVMROM.Thm54.TraceGen.DotConfig257.rawRequest_timestamps
#print axioms Nock.NockVMROM.Thm54.TraceGen.DotConfig769.requestNodup
#print axioms Nock.NockVMROM.Thm54.TraceGen.rendered_request_timestamps_air
