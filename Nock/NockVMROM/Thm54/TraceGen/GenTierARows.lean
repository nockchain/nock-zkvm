/-
  Nock/NockVMROM/Thm54/TraceGen/GenTierARows.lean

  The DotConfig257 execution's eight compute rows are the BFS-rendered
  `bfsLabelAt` nodes of `dotTree`, and the BFS `accAt` / record-exponent
  schedule on that tree is the consecutive live exponents `1..13`.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenTierAConfig

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk
open Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen

section AccAtDot
variable {K : Type} [Field K]

theorem accAt_dot_0 : accAt (dotTree (K := K)) 0 = 0 :=
  accAt_zero _

theorem bfsRows_dot_length :
    (bfsRows (dotTree (K := K))).length = 8 := by
  simp [dot_bfsRows]

theorem accAt_dot_1 : accAt (dotTree (K := K)) 1 = 3 := by
  have hk : 0 < (bfsRows (dotTree (K := K))).length := by simp [dot_bfsRows]
  rw [accAt_succ_of_lt (dotTree (K := K)) 0 hk, accAt_dot_0]
  have hskel :
      (bfsRows (dotTree (K := K)))[0].skel =
        (bfsLabelAt (dotTree (K := K)) 1).skel :=
    (bfsLabelAt_skel (dotTree (K := K)) 1 hk).symm
  rw [congrArg (fun s => Nock.Framework.recordCount s.state) hskel,
    bfsLabelAt_dot_skel1]
  have hs : dotOp6Skel.state = State.s6 := rfl
  rw [hs]
  rfl

theorem accAt_dot_2 : accAt (dotTree (K := K)) 2 = 4 := by
  have hk : 1 < (bfsRows (dotTree (K := K))).length := by simp [dot_bfsRows]
  rw [accAt_succ_of_lt (dotTree (K := K)) 1 hk, accAt_dot_1]
  have hskel :
      (bfsRows (dotTree (K := K)))[1].skel =
        (bfsLabelAt (dotTree (K := K)) 2).skel :=
    (bfsLabelAt_skel (dotTree (K := K)) 2 hk).symm
  rw [congrArg (fun s => Nock.Framework.recordCount s.state) hskel,
    bfsLabelAt_dot_skel2]
  have hs : (dotCondTree (K := K)).label.skel.state = State.s1 := rfl
  rw [hs]
  rfl

theorem accAt_dot_3 : accAt (dotTree (K := K)) 3 = 6 := by
  have hk : 2 < (bfsRows (dotTree (K := K))).length := by simp [dot_bfsRows]
  rw [accAt_succ_of_lt (dotTree (K := K)) 2 hk, accAt_dot_2]
  have hskel :
      (bfsRows (dotTree (K := K)))[2].skel =
        (bfsLabelAt (dotTree (K := K)) 3).skel :=
    (bfsLabelAt_skel (dotTree (K := K)) 3 hk).symm
  rw [congrArg (fun s => Nock.Framework.recordCount s.state) hskel,
    bfsLabelAt_dot_skel3]
  have hs : dotOp2Skel.state = State.s2 := rfl
  rw [hs]
  rfl

theorem accAt_dot_4 : accAt (dotTree (K := K)) 4 = 7 := by
  have hk : 3 < (bfsRows (dotTree (K := K))).length := by simp [dot_bfsRows]
  rw [accAt_succ_of_lt (dotTree (K := K)) 3 hk, accAt_dot_3]
  have hskel :
      (bfsRows (dotTree (K := K)))[3].skel =
        (bfsLabelAt (dotTree (K := K)) 4).skel :=
    (bfsLabelAt_skel (dotTree (K := K)) 4 hk).symm
  rw [congrArg (fun s => Nock.Framework.recordCount s.state) hskel,
    bfsLabelAt_dot_skel4]
  have hs : (dotOp1BTree (K := K)).label.skel.state = State.s1 := rfl
  rw [hs]
  rfl

theorem accAt_dot_5 : accAt (dotTree (K := K)) 5 = 8 := by
  have hk : 4 < (bfsRows (dotTree (K := K))).length := by simp [dot_bfsRows]
  rw [accAt_succ_of_lt (dotTree (K := K)) 4 hk, accAt_dot_4]
  have hskel :
      (bfsRows (dotTree (K := K)))[4].skel =
        (bfsLabelAt (dotTree (K := K)) 5).skel :=
    (bfsLabelAt_skel (dotTree (K := K)) 5 hk).symm
  rw [congrArg (fun s => Nock.Framework.recordCount s.state) hskel,
    bfsLabelAt_dot_skel5]
  have hs : (dotOp1CTree (K := K)).label.skel.state = State.s1 := rfl
  rw [hs]
  rfl

theorem accAt_dot_6 : accAt (dotTree (K := K)) 6 = 11 := by
  have hk : 5 < (bfsRows (dotTree (K := K))).length := by simp [dot_bfsRows]
  rw [accAt_succ_of_lt (dotTree (K := K)) 5 hk, accAt_dot_5]
  have hskel :
      (bfsRows (dotTree (K := K)))[5].skel =
        (bfsLabelAt (dotTree (K := K)) 6).skel :=
    (bfsLabelAt_skel (dotTree (K := K)) 6 hk).symm
  rw [congrArg (fun s => Nock.Framework.recordCount s.state) hskel,
    bfsLabelAt_dot_skel6]
  have hs : dotOp9Skel.state = State.s9 := rfl
  rw [hs]
  rfl

theorem accAt_dot_7 : accAt (dotTree (K := K)) 7 = 12 := by
  have hk : 6 < (bfsRows (dotTree (K := K))).length := by simp [dot_bfsRows]
  rw [accAt_succ_of_lt (dotTree (K := K)) 6 hk, accAt_dot_6]
  have hskel :
      (bfsRows (dotTree (K := K)))[6].skel =
        (bfsLabelAt (dotTree (K := K)) 7).skel :=
    (bfsLabelAt_skel (dotTree (K := K)) 7 hk).symm
  rw [congrArg (fun s => Nock.Framework.recordCount s.state) hskel,
    bfsLabelAt_dot_skel7]
  have hs : (dotOp9CoreTree (K := K)).label.skel.state = State.s1 := rfl
  rw [hs]
  rfl

theorem accAt_dot :
    accAt (dotTree (K := K)) 0 = 0 ∧
      accAt (dotTree (K := K)) 1 = 3 ∧
      accAt (dotTree (K := K)) 2 = 4 ∧
      accAt (dotTree (K := K)) 3 = 6 ∧
      accAt (dotTree (K := K)) 4 = 7 ∧
      accAt (dotTree (K := K)) 5 = 8 ∧
      accAt (dotTree (K := K)) 6 = 11 ∧
      accAt (dotTree (K := K)) 7 = 12 :=
  ⟨accAt_dot_0, accAt_dot_1, accAt_dot_2, accAt_dot_3,
    accAt_dot_4, accAt_dot_5, accAt_dot_6, accAt_dot_7⟩

theorem getRecordExp_stampOfAcc (st : ComputeTable.State) (acc i : ℕ)
    (hi : i < 3) (hlive : i < Nock.Framework.recordCount st) :
    getRecordExp (stampOfAcc st acc) i = acc + i + 1 := by
  unfold getRecordExp
  rw [dif_pos hi]
  exact stampOfAcc_recordExponent st acc ⟨i, hi⟩ hlive

theorem liveRecordExps_dot :
    [getRecordExp (bfsLabelAt (dotTree (K := K)) 1).stamp 0,
     getRecordExp (bfsLabelAt (dotTree (K := K)) 1).stamp 1,
     getRecordExp (bfsLabelAt (dotTree (K := K)) 1).stamp 2,
     getRecordExp (bfsLabelAt (dotTree (K := K)) 2).stamp 0,
     getRecordExp (bfsLabelAt (dotTree (K := K)) 3).stamp 0,
     getRecordExp (bfsLabelAt (dotTree (K := K)) 3).stamp 1,
     getRecordExp (bfsLabelAt (dotTree (K := K)) 4).stamp 0,
     getRecordExp (bfsLabelAt (dotTree (K := K)) 5).stamp 0,
     getRecordExp (bfsLabelAt (dotTree (K := K)) 6).stamp 0,
     getRecordExp (bfsLabelAt (dotTree (K := K)) 6).stamp 1,
     getRecordExp (bfsLabelAt (dotTree (K := K)) 6).stamp 2,
     getRecordExp (bfsLabelAt (dotTree (K := K)) 7).stamp 0,
     getRecordExp (bfsLabelAt (dotTree (K := K)) 8).stamp 0] =
      [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] := by
  have h1 : 1 - 1 < (bfsRows (dotTree (K := K))).length := by simp [dot_bfsRows]
  have h2 : 2 - 1 < (bfsRows (dotTree (K := K))).length := by simp [dot_bfsRows]
  have h3 : 3 - 1 < (bfsRows (dotTree (K := K))).length := by simp [dot_bfsRows]
  have h4 : 4 - 1 < (bfsRows (dotTree (K := K))).length := by simp [dot_bfsRows]
  have h5 : 5 - 1 < (bfsRows (dotTree (K := K))).length := by simp [dot_bfsRows]
  have h6 : 6 - 1 < (bfsRows (dotTree (K := K))).length := by simp [dot_bfsRows]
  have h7 : 7 - 1 < (bfsRows (dotTree (K := K))).length := by simp [dot_bfsRows]
  have h8 : 8 - 1 < (bfsRows (dotTree (K := K))).length := by simp [dot_bfsRows]
  rw [bfsLabelAt_stamp (dotTree (K := K)) 1 h1,
    bfsLabelAt_stamp (dotTree (K := K)) 2 h2,
    bfsLabelAt_stamp (dotTree (K := K)) 3 h3,
    bfsLabelAt_stamp (dotTree (K := K)) 4 h4,
    bfsLabelAt_stamp (dotTree (K := K)) 5 h5,
    bfsLabelAt_stamp (dotTree (K := K)) 6 h6,
    bfsLabelAt_stamp (dotTree (K := K)) 7 h7,
    bfsLabelAt_stamp (dotTree (K := K)) 8 h8]
  have hs1 :
      (bfsRows (dotTree (K := K)))[1 - 1].skel.state = State.s6 := by
    have hskel := (bfsLabelAt_skel (dotTree (K := K)) 1 h1).symm
    rw [congrArg (fun s => s.state) hskel, bfsLabelAt_dot_skel1]
    rfl
  have hs2 :
      (bfsRows (dotTree (K := K)))[2 - 1].skel.state = State.s1 := by
    have hskel := (bfsLabelAt_skel (dotTree (K := K)) 2 h2).symm
    rw [congrArg (fun s => s.state) hskel, bfsLabelAt_dot_skel2]
    rfl
  have hs3 :
      (bfsRows (dotTree (K := K)))[3 - 1].skel.state = State.s2 := by
    have hskel := (bfsLabelAt_skel (dotTree (K := K)) 3 h3).symm
    rw [congrArg (fun s => s.state) hskel, bfsLabelAt_dot_skel3]
    rfl
  have hs4 :
      (bfsRows (dotTree (K := K)))[4 - 1].skel.state = State.s1 := by
    have hskel := (bfsLabelAt_skel (dotTree (K := K)) 4 h4).symm
    rw [congrArg (fun s => s.state) hskel, bfsLabelAt_dot_skel4]
    rfl
  have hs5 :
      (bfsRows (dotTree (K := K)))[5 - 1].skel.state = State.s1 := by
    have hskel := (bfsLabelAt_skel (dotTree (K := K)) 5 h5).symm
    rw [congrArg (fun s => s.state) hskel, bfsLabelAt_dot_skel5]
    rfl
  have hs6 :
      (bfsRows (dotTree (K := K)))[6 - 1].skel.state = State.s9 := by
    have hskel := (bfsLabelAt_skel (dotTree (K := K)) 6 h6).symm
    rw [congrArg (fun s => s.state) hskel, bfsLabelAt_dot_skel6]
    rfl
  have hs7 :
      (bfsRows (dotTree (K := K)))[7 - 1].skel.state = State.s1 := by
    have hskel := (bfsLabelAt_skel (dotTree (K := K)) 7 h7).symm
    rw [congrArg (fun s => s.state) hskel, bfsLabelAt_dot_skel7]
    rfl
  have hs8 :
      (bfsRows (dotTree (K := K)))[8 - 1].skel.state = State.s1 := by
    have hskel := (bfsLabelAt_skel (dotTree (K := K)) 8 h8).symm
    rw [congrArg (fun s => s.state) hskel, bfsLabelAt_dot_skel8]
    rfl
  rw [hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8,
    accAt_dot_0, accAt_dot_1, accAt_dot_2, accAt_dot_3, accAt_dot_4,
    accAt_dot_5, accAt_dot_6, accAt_dot_7]
  rw [getRecordExp_stampOfAcc State.s6 0 0 (by omega) (by simp [Nock.Framework.recordCount]),
    getRecordExp_stampOfAcc State.s6 0 1 (by omega) (by simp [Nock.Framework.recordCount]),
    getRecordExp_stampOfAcc State.s6 0 2 (by omega) (by simp [Nock.Framework.recordCount]),
    getRecordExp_stampOfAcc State.s1 3 0 (by omega) (by simp [Nock.Framework.recordCount]),
    getRecordExp_stampOfAcc State.s2 4 0 (by omega) (by simp [Nock.Framework.recordCount]),
    getRecordExp_stampOfAcc State.s2 4 1 (by omega) (by simp [Nock.Framework.recordCount]),
    getRecordExp_stampOfAcc State.s1 6 0 (by omega) (by simp [Nock.Framework.recordCount]),
    getRecordExp_stampOfAcc State.s1 7 0 (by omega) (by simp [Nock.Framework.recordCount]),
    getRecordExp_stampOfAcc State.s9 8 0 (by omega) (by simp [Nock.Framework.recordCount]),
    getRecordExp_stampOfAcc State.s9 8 1 (by omega) (by simp [Nock.Framework.recordCount]),
    getRecordExp_stampOfAcc State.s9 8 2 (by omega) (by simp [Nock.Framework.recordCount]),
    getRecordExp_stampOfAcc State.s1 11 0 (by omega) (by simp [Nock.Framework.recordCount]),
    getRecordExp_stampOfAcc State.s1 12 0 (by omega) (by simp [Nock.Framework.recordCount])]

end AccAtDot

namespace DotConfig257

theorem computeRows_eq (z α : K) :
    (exec z α).computeRows =
      [(renderNode z α (bfsLabelAt (dotTree (K := K)) 1)).row,
       (renderNode z α (bfsLabelAt (dotTree (K := K)) 2)).row,
       (renderNode z α (bfsLabelAt (dotTree (K := K)) 3)).row,
       (renderNode z α (bfsLabelAt (dotTree (K := K)) 4)).row,
       (renderNode z α (bfsLabelAt (dotTree (K := K)) 5)).row,
       (renderNode z α (bfsLabelAt (dotTree (K := K)) 6)).row,
       (renderNode z α (bfsLabelAt (dotTree (K := K)) 7)).row,
       (renderNode z α (bfsLabelAt (dotTree (K := K)) 8)).row] := by
  unfold ExactExecution.computeRows
  change (bfsForest [computeTree z α]).map NTree.label = _
  unfold computeTree
  rw [renderRows_eq_mapNTree, mapNTree_comp]
  rw [show [mapNTree (GenComputeRow.row ∘ renderNode z α)
        (bfsAssign (dotTree (K := K)))] =
      [bfsAssign (dotTree (K := K))].map
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
  have hlen : (bfsForest [dotTree (K := K)]).length = 8 := by
    simp [dot_bfsForest]
  rw [hlen]
  rfl

end DotConfig257

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.DotConfig257.computeRows_eq
#print axioms Nock.NockVMROM.Thm54.TraceGen.accAt_dot
#print axioms Nock.NockVMROM.Thm54.TraceGen.liveRecordExps_dot
