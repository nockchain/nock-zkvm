/-
  Nock/NockVMROM/Thm54/TraceGen/GenTierARowsAir.lean

  BFS `accAt` / live-record-exponent schedule on the AIR-ordered tree
  `dotTreeAir` (children `[taken, condition]`).  OP2 (`recordCount` 2)
  sits at BFS index 2, so `accAt 2 = 5`; concatenated live exponents
  are still `1..13`.  `dotTree` / `Gen.lean` are not edited.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenTierARows
import Nock.NockVMROM.Thm54.TraceGen.GenTierAComputeLink

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk
open Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen

section AccAtAir
variable {K : Type} [Field K]

theorem accAt_air_0 : accAt (dotTreeAir (K := K)) 0 = 0 :=
  accAt_zero _

theorem bfsRows_air_length :
    (bfsRows (dotTreeAir (K := K))).length = 8 := by
  simp [dot_air_bfsRows]

theorem accAt_air_1 : accAt (dotTreeAir (K := K)) 1 = 3 := by
  have hk : 0 < (bfsRows (dotTreeAir (K := K))).length := by simp [dot_air_bfsRows]
  rw [accAt_succ_of_lt (dotTreeAir (K := K)) 0 hk, accAt_air_0]
  have hskel :
      (bfsRows (dotTreeAir (K := K)))[0].skel =
        (bfsLabelAt (dotTreeAir (K := K)) 1).skel :=
    (bfsLabelAt_skel (dotTreeAir (K := K)) 1 hk).symm
  rw [congrArg (fun s => Nock.Framework.recordCount s.state) hskel,
    bfsLabelAt_air_skel1]
  have hs : dotOp6Skel.state = State.s6 := rfl
  rw [hs]
  rfl

theorem accAt_air_2 : accAt (dotTreeAir (K := K)) 2 = 5 := by
  have hk : 1 < (bfsRows (dotTreeAir (K := K))).length := by simp [dot_air_bfsRows]
  rw [accAt_succ_of_lt (dotTreeAir (K := K)) 1 hk, accAt_air_1]
  have hskel :
      (bfsRows (dotTreeAir (K := K)))[1].skel =
        (bfsLabelAt (dotTreeAir (K := K)) 2).skel :=
    (bfsLabelAt_skel (dotTreeAir (K := K)) 2 hk).symm
  rw [congrArg (fun s => Nock.Framework.recordCount s.state) hskel,
    bfsLabelAt_air_skel2]
  have hs : (dotOp2Tree (K := K)).label.skel.state = State.s2 := rfl
  rw [hs]
  rfl

theorem accAt_air_3 : accAt (dotTreeAir (K := K)) 3 = 6 := by
  have hk : 2 < (bfsRows (dotTreeAir (K := K))).length := by simp [dot_air_bfsRows]
  rw [accAt_succ_of_lt (dotTreeAir (K := K)) 2 hk, accAt_air_2]
  have hskel :
      (bfsRows (dotTreeAir (K := K)))[2].skel =
        (bfsLabelAt (dotTreeAir (K := K)) 3).skel :=
    (bfsLabelAt_skel (dotTreeAir (K := K)) 3 hk).symm
  rw [congrArg (fun s => Nock.Framework.recordCount s.state) hskel,
    bfsLabelAt_air_skel3]
  have hs : (dotCondTree (K := K)).label.skel.state = State.s1 := rfl
  rw [hs]
  rfl

theorem accAt_air_4 : accAt (dotTreeAir (K := K)) 4 = 7 := by
  have hk : 3 < (bfsRows (dotTreeAir (K := K))).length := by simp [dot_air_bfsRows]
  rw [accAt_succ_of_lt (dotTreeAir (K := K)) 3 hk, accAt_air_3]
  have hskel :
      (bfsRows (dotTreeAir (K := K)))[3].skel =
        (bfsLabelAt (dotTreeAir (K := K)) 4).skel :=
    (bfsLabelAt_skel (dotTreeAir (K := K)) 4 hk).symm
  rw [congrArg (fun s => Nock.Framework.recordCount s.state) hskel,
    bfsLabelAt_air_skel4]
  have hs : (dotOp1BTree (K := K)).label.skel.state = State.s1 := rfl
  rw [hs]
  rfl

theorem accAt_air_5 : accAt (dotTreeAir (K := K)) 5 = 8 := by
  have hk : 4 < (bfsRows (dotTreeAir (K := K))).length := by simp [dot_air_bfsRows]
  rw [accAt_succ_of_lt (dotTreeAir (K := K)) 4 hk, accAt_air_4]
  have hskel :
      (bfsRows (dotTreeAir (K := K)))[4].skel =
        (bfsLabelAt (dotTreeAir (K := K)) 5).skel :=
    (bfsLabelAt_skel (dotTreeAir (K := K)) 5 hk).symm
  rw [congrArg (fun s => Nock.Framework.recordCount s.state) hskel,
    bfsLabelAt_air_skel5]
  have hs : (dotOp1CTree (K := K)).label.skel.state = State.s1 := rfl
  rw [hs]
  rfl

theorem accAt_air_6 : accAt (dotTreeAir (K := K)) 6 = 11 := by
  have hk : 5 < (bfsRows (dotTreeAir (K := K))).length := by simp [dot_air_bfsRows]
  rw [accAt_succ_of_lt (dotTreeAir (K := K)) 5 hk, accAt_air_5]
  have hskel :
      (bfsRows (dotTreeAir (K := K)))[5].skel =
        (bfsLabelAt (dotTreeAir (K := K)) 6).skel :=
    (bfsLabelAt_skel (dotTreeAir (K := K)) 6 hk).symm
  rw [congrArg (fun s => Nock.Framework.recordCount s.state) hskel,
    bfsLabelAt_air_skel6]
  have hs : dotOp9Skel.state = State.s9 := rfl
  rw [hs]
  rfl

theorem accAt_air_7 : accAt (dotTreeAir (K := K)) 7 = 12 := by
  have hk : 6 < (bfsRows (dotTreeAir (K := K))).length := by simp [dot_air_bfsRows]
  rw [accAt_succ_of_lt (dotTreeAir (K := K)) 6 hk, accAt_air_6]
  have hskel :
      (bfsRows (dotTreeAir (K := K)))[6].skel =
        (bfsLabelAt (dotTreeAir (K := K)) 7).skel :=
    (bfsLabelAt_skel (dotTreeAir (K := K)) 7 hk).symm
  rw [congrArg (fun s => Nock.Framework.recordCount s.state) hskel,
    bfsLabelAt_air_skel7]
  have hs : (dotOp9CoreTree (K := K)).label.skel.state = State.s1 := rfl
  rw [hs]
  rfl

theorem accAt_air :
    accAt (dotTreeAir (K := K)) 0 = 0 ∧
      accAt (dotTreeAir (K := K)) 1 = 3 ∧
      accAt (dotTreeAir (K := K)) 2 = 5 ∧
      accAt (dotTreeAir (K := K)) 3 = 6 ∧
      accAt (dotTreeAir (K := K)) 4 = 7 ∧
      accAt (dotTreeAir (K := K)) 5 = 8 ∧
      accAt (dotTreeAir (K := K)) 6 = 11 ∧
      accAt (dotTreeAir (K := K)) 7 = 12 :=
  ⟨accAt_air_0, accAt_air_1, accAt_air_2, accAt_air_3,
    accAt_air_4, accAt_air_5, accAt_air_6, accAt_air_7⟩

/-- Concatenated live exponents on `dotTreeAir` are still `1..13`.
    Index 2 is OP2 (`4,5`); index 3 is the condition (`6`). -/
theorem liveRecordExps_air :
    [getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 1).stamp 0,
     getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 1).stamp 1,
     getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 1).stamp 2,
     getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 2).stamp 0,
     getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 2).stamp 1,
     getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 3).stamp 0,
     getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 4).stamp 0,
     getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 5).stamp 0,
     getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 6).stamp 0,
     getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 6).stamp 1,
     getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 6).stamp 2,
     getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 7).stamp 0,
     getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 8).stamp 0] =
      [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] := by
  have h1 : 1 - 1 < (bfsRows (dotTreeAir (K := K))).length := by simp [dot_air_bfsRows]
  have h2 : 2 - 1 < (bfsRows (dotTreeAir (K := K))).length := by simp [dot_air_bfsRows]
  have h3 : 3 - 1 < (bfsRows (dotTreeAir (K := K))).length := by simp [dot_air_bfsRows]
  have h4 : 4 - 1 < (bfsRows (dotTreeAir (K := K))).length := by simp [dot_air_bfsRows]
  have h5 : 5 - 1 < (bfsRows (dotTreeAir (K := K))).length := by simp [dot_air_bfsRows]
  have h6 : 6 - 1 < (bfsRows (dotTreeAir (K := K))).length := by simp [dot_air_bfsRows]
  have h7 : 7 - 1 < (bfsRows (dotTreeAir (K := K))).length := by simp [dot_air_bfsRows]
  have h8 : 8 - 1 < (bfsRows (dotTreeAir (K := K))).length := by simp [dot_air_bfsRows]
  rw [bfsLabelAt_stamp (dotTreeAir (K := K)) 1 h1,
    bfsLabelAt_stamp (dotTreeAir (K := K)) 2 h2,
    bfsLabelAt_stamp (dotTreeAir (K := K)) 3 h3,
    bfsLabelAt_stamp (dotTreeAir (K := K)) 4 h4,
    bfsLabelAt_stamp (dotTreeAir (K := K)) 5 h5,
    bfsLabelAt_stamp (dotTreeAir (K := K)) 6 h6,
    bfsLabelAt_stamp (dotTreeAir (K := K)) 7 h7,
    bfsLabelAt_stamp (dotTreeAir (K := K)) 8 h8]
  have hs1 :
      (bfsRows (dotTreeAir (K := K)))[1 - 1].skel.state = State.s6 := by
    have hskel := (bfsLabelAt_skel (dotTreeAir (K := K)) 1 h1).symm
    rw [congrArg (fun s => s.state) hskel, bfsLabelAt_air_skel1]
    rfl
  have hs2 :
      (bfsRows (dotTreeAir (K := K)))[2 - 1].skel.state = State.s2 := by
    have hskel := (bfsLabelAt_skel (dotTreeAir (K := K)) 2 h2).symm
    rw [congrArg (fun s => s.state) hskel, bfsLabelAt_air_skel2]
    rfl
  have hs3 :
      (bfsRows (dotTreeAir (K := K)))[3 - 1].skel.state = State.s1 := by
    have hskel := (bfsLabelAt_skel (dotTreeAir (K := K)) 3 h3).symm
    rw [congrArg (fun s => s.state) hskel, bfsLabelAt_air_skel3]
    rfl
  have hs4 :
      (bfsRows (dotTreeAir (K := K)))[4 - 1].skel.state = State.s1 := by
    have hskel := (bfsLabelAt_skel (dotTreeAir (K := K)) 4 h4).symm
    rw [congrArg (fun s => s.state) hskel, bfsLabelAt_air_skel4]
    rfl
  have hs5 :
      (bfsRows (dotTreeAir (K := K)))[5 - 1].skel.state = State.s1 := by
    have hskel := (bfsLabelAt_skel (dotTreeAir (K := K)) 5 h5).symm
    rw [congrArg (fun s => s.state) hskel, bfsLabelAt_air_skel5]
    rfl
  have hs6 :
      (bfsRows (dotTreeAir (K := K)))[6 - 1].skel.state = State.s9 := by
    have hskel := (bfsLabelAt_skel (dotTreeAir (K := K)) 6 h6).symm
    rw [congrArg (fun s => s.state) hskel, bfsLabelAt_air_skel6]
    rfl
  have hs7 :
      (bfsRows (dotTreeAir (K := K)))[7 - 1].skel.state = State.s1 := by
    have hskel := (bfsLabelAt_skel (dotTreeAir (K := K)) 7 h7).symm
    rw [congrArg (fun s => s.state) hskel, bfsLabelAt_air_skel7]
    rfl
  have hs8 :
      (bfsRows (dotTreeAir (K := K)))[8 - 1].skel.state = State.s1 := by
    have hskel := (bfsLabelAt_skel (dotTreeAir (K := K)) 8 h8).symm
    rw [congrArg (fun s => s.state) hskel, bfsLabelAt_air_skel8]
    rfl
  rw [hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8,
    accAt_air_0, accAt_air_1, accAt_air_2, accAt_air_3, accAt_air_4,
    accAt_air_5, accAt_air_6, accAt_air_7]
  rw [getRecordExp_stampOfAcc State.s6 0 0 (by omega) (by simp [Nock.Framework.recordCount]),
    getRecordExp_stampOfAcc State.s6 0 1 (by omega) (by simp [Nock.Framework.recordCount]),
    getRecordExp_stampOfAcc State.s6 0 2 (by omega) (by simp [Nock.Framework.recordCount]),
    getRecordExp_stampOfAcc State.s2 3 0 (by omega) (by simp [Nock.Framework.recordCount]),
    getRecordExp_stampOfAcc State.s2 3 1 (by omega) (by simp [Nock.Framework.recordCount]),
    getRecordExp_stampOfAcc State.s1 5 0 (by omega) (by simp [Nock.Framework.recordCount]),
    getRecordExp_stampOfAcc State.s1 6 0 (by omega) (by simp [Nock.Framework.recordCount]),
    getRecordExp_stampOfAcc State.s1 7 0 (by omega) (by simp [Nock.Framework.recordCount]),
    getRecordExp_stampOfAcc State.s9 8 0 (by omega) (by simp [Nock.Framework.recordCount]),
    getRecordExp_stampOfAcc State.s9 8 1 (by omega) (by simp [Nock.Framework.recordCount]),
    getRecordExp_stampOfAcc State.s9 8 2 (by omega) (by simp [Nock.Framework.recordCount]),
    getRecordExp_stampOfAcc State.s1 11 0 (by omega) (by simp [Nock.Framework.recordCount]),
    getRecordExp_stampOfAcc State.s1 12 0 (by omega) (by simp [Nock.Framework.recordCount])]

end AccAtAir

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.accAt_air
#print axioms Nock.NockVMROM.Thm54.TraceGen.liveRecordExps_air
