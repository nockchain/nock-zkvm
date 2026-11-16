/-
  Nock/NockVMROM/Thm54/TraceGen/Op1MemoryTrace.lean

  The served memory trace
  `ServedMemoryTrace.ExactServedMemoryTrace 97 3 Op1Config.cfg Op1Config.exec semanticData` for the
  slice `*[0 [1 5]] = 5` over `K = ZMod 97`, `Λ = 3`, seed `z = 8`, `α = 4`.

  The five-row memory reconstruction `read_root -> decompose -> (halt, verify_child -> halt)` reads
  as the single-service axis tree

      read e (decompose halt (verify e 3 halt))

  where `e` is the timestamp exponent of the one committed record `([1 5], 5, 3, α)`.  The single
  root carries one service; the axis-`3` recursion is one `right` step of the paper's noun-indexed
  `VerifyRoute`/`ServiceWalk`.  `OP_1` has
  `requiredServedLookups = 0`, so `semanticCoverage` is vacuous.
-/
import Nock.NockVMROM.Thm54.TraceGen.Op1SemanticData
import Nock.NockVMROM.Thm54.ServedMemoryTrace
import Nock.NockVMROM.Thm54.AxisSoundness

namespace Nock.NockVMROM.Thm54.TraceGen.Op1Config

open Nock Nock.Walk Nock.NockVM Nock.MemoryTable Nock.ComputeTable
open Nock.AxisBatching Nock.AxisBatching.MTree Nock.AxisBridge
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ServedMemoryTrace
open Nock.NockVMROM.Thm54.SemanticTrace
open Nock.NockVMROM.Thm54.TraceGen.Op1Skeleton

/-! ## L. The exact axis tree and its single service -/

/-- The one committed record's timestamp `α = α^1` is closed under the exact challenge. -/
theorem ts_closed_req : TimestampClosedAt (cfg seedZ alphaA).challenges.α
    (requestRecord seedZ alphaA).ts :=
  ⟨1, by simp [requestRecord, cfg, alphaA]⟩

/-- The canonical timestamp exponent of the one committed record. -/
noncomputable def expReq : ℕ :=
  timestampExp (cfg seedZ alphaA).challenges.α (requestRecord seedZ alphaA).ts

theorem ts_eq_req : (requestRecord seedZ alphaA).ts =
    (cfg seedZ alphaA).challenges.α ^ expReq :=
  timestampExp_spec ts_closed_req

theorem memoryTreeAt_dummy :
    (execA seedZ alphaA).memoryTreeAt ⟨0, by norm_num [cfg]⟩ = dummyHaltTreeA seedZ := rfl

theorem memoryTreeAt_root :
    (execA seedZ alphaA).memoryTreeAt ⟨1, by norm_num [cfg]⟩ = readTreeA seedZ alphaA := rfl

theorem axisPath_three : axisPath 3 = [true] := by
  rw [axisPath_of_two_le (by norm_num)]
  norm_num [axisPath_of_lt_two]

set_option maxRecDepth 8000 in
/-- The OP1 axis tree: one `read`, one `decompose`, one `verify` at axis `3`, all leaves `halt`. -/
theorem axisTree_eq :
    exactAxisTree (cfg seedZ alphaA) (execA seedZ alphaA) ⟨1, by norm_num [cfg]⟩ =
      MTree.read expReq
        (MTree.decompose MTree.halt
          (MTree.verify expReq 3 MTree.halt)) := by
  rw [exactAxisTree, memoryTreeAt_root]
  simp [readTreeA, decomposeTreeA, headTreeA, verifyTreeA, tailTreeA,
    readRowA, decomposeRowA, headRowA, verifyRowA, tailRowA,
    readPubA, decomposePubA, headPubA, verifyPubA, tailPubA,
    readPub, decomposePub, headPub, verifyPub, tailPub,
    Nock.AxisBridge.ofNTree, Nock.AxisBridge.MemWalk.toMTree, timestampExpAt,
    expReq, requestRecord]

/-- The one authoritative service of the OP1 slice: the record `([1 5], 5, 3, α)` served at axis
`3` off the root noun `[1 5]` to the child noun `5`. -/
noncomputable def serviceReq : Service (cfg seedZ alphaA) (execA seedZ alphaA) where
  exponent := expReq
  record := requestRecord seedZ alphaA
  root := formulaNoun
  child := resultNoun
  axis := 3
  request_mem := by
    rw [show (execA seedZ alphaA).rawRequests = (exec seedZ alphaA).rawRequests from rfl,
      rawRequests_eq]; simp
  timestamp := ts_eq_req
  realization :=
    { root_realizes := rfl
      child_realizes := rfl
      axis_realizes := by norm_num [requestRecord] }
  served := by simp [formulaNoun, resultNoun, headNoun, Noun.slot]

/-! ## The single-root trace -/

/-- The recursively generated service traversal of the OP1 read root. -/
noncomputable def rootTrace : RootTrace (cfg seedZ alphaA) (execA seedZ alphaA)
    ⟨1, by norm_num [cfg]⟩ where
  subject := formulaNoun
  services := [serviceReq]
  recordPartition := by
    show rootResponseRecords (execA seedZ alphaA) ⟨1, by norm_num [cfg]⟩ = [serviceReq.record]
    rw [rootResponseRecords, memoryTreeAt_root]
    simp [readTreeA, decomposeTreeA, headTreeA, verifyTreeA, tailTreeA,
      readRowA, decomposeRowA, headRowA, verifyRowA, tailRowA,
      readPubA, decomposePubA, headPubA, verifyPubA, tailPubA,
    readPub, decomposePub, headPub, verifyPub, tailPub,
      bfsForest, MemoryTable.responseRecords, serviceReq]
  readPartition := by rw [axisTree_eq]; simp [serviceReq, readExps]
  verifyPartition := by rw [axisTree_eq]; simp [serviceReq, verifyExps]
  traversal := by
    rw [axisTree_eq]
    refine ServiceWalk.read serviceReq (by simp) rfl rfl ?_ ?_
    · rw [show serviceReq.axis = 3 from rfl, axisPath_three]
      refine VerifyRoute.right (by simp [readCount]) (by simp [verifyCount]) ?_
      exact VerifyRoute.here rfl (by norm_num [serviceReq, requestRecord])
        (by simp [readCount]) (by simp [verifyCount])
    · exact ServiceWalk.decompose ServiceWalk.halt (ServiceWalk.verify ServiceWalk.halt)

theorem dummyAxisTree_eq :
    exactAxisTree (cfg seedZ alphaA) (execA seedZ alphaA) ⟨0, by norm_num [cfg]⟩ =
      MTree.halt := by
  rw [exactAxisTree, memoryTreeAt_dummy]
  simp [dummyHaltTreeA, dummyHaltRowA, dummyHaltPubA, dummyHaltPub,
    Nock.AxisBridge.ofNTree, Nock.AxisBridge.MemWalk.toMTree, timestampExpAt]

noncomputable def dummyRootTrace : RootTrace (cfg seedZ alphaA) (execA seedZ alphaA)
    ⟨0, by norm_num [cfg]⟩ where
  subject := .atom 0
  services := []
  recordPartition := by
    simp [rootResponseRecords, memoryTreeAt_dummy, dummyHaltTreeA, dummyHaltRowA, dummyHaltPubA,
      dummyHaltPub,
      bfsForest, MemoryTable.responseRecords]
  readPartition := by rw [dummyAxisTree_eq]; simp [readExps]
  verifyPartition := by rw [dummyAxisTree_eq]; simp [verifyExps]
  traversal := by
    rw [dummyAxisTree_eq]
    exact ServiceWalk.halt

/-- Every one of the (two) authoritative memory roots. -/
noncomputable def rootTraces : ∀ i : Fin (cfg seedZ alphaA).kMem,
    RootTrace (cfg seedZ alphaA) (execA seedZ alphaA) i
  | ⟨0, _⟩ => dummyRootTrace
  | ⟨1, _⟩ => rootTrace
  | ⟨n + 2, h⟩ => absurd (show n + 2 < 2 by simp only [cfg] at h; exact h) (by omega)

theorem rootTraces_dummy : rootTraces ⟨0, by norm_num [cfg]⟩ = dummyRootTrace := rfl
theorem rootTraces_root : rootTraces ⟨1, by norm_num [cfg]⟩ = rootTrace := rfl

theorem finRange_kMem :
    List.finRange (cfg seedZ alphaA).kMem =
      [⟨0, by norm_num [cfg]⟩, ⟨1, by norm_num [cfg]⟩] := rfl

theorem forestTimestampPowers :
    (List.finRange (cfg seedZ alphaA).kMem).flatMap
      (fun i => (rootTraces i).timestampPowers) = [(cfg seedZ alphaA).challenges.α ^ expReq] := by
  rw [finRange_kMem]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
    rootTraces_dummy, rootTraces_root]
  simp [RootTrace.timestampPowers, RootTrace.exponents, dummyRootTrace, rootTrace, serviceReq]

theorem forestTimestampPowers_nodup :
    ((List.finRange (cfg seedZ alphaA).kMem).flatMap
      (fun i => (rootTraces i).timestampPowers)).Nodup := by
  rw [forestTimestampPowers]; simp

/-! ## Vacuous `semanticCoverage` (`OP_1` has `requiredServedLookups = 0`) -/

/-- The census tuple of a served lookup, robust to `castRowData` transport. -/
def lookupTuple {z : F} (l : ServedNounLookup z) :
    ComputeTable.MemRec F × Noun × ℕ × Noun :=
  (l.record, l.root, l.axis, l.child)

theorem castRowData_servedTuples
    {row₁ row₂ : ComputeTable.State × ComputeTable.DTcomp F}
    (h : row₁ = row₂) (d : ComputeRowSemanticData 97 3 row₂) :
    (castRowData h d).needs.served.map lookupTuple = d.needs.served.map lookupTuple := by
  subst h; rfl

theorem rowData_zero_servedTuples :
    (rowData ⟨0, by norm_num [cfg]⟩).needs.served.map lookupTuple = [] :=
  (castRowData_servedTuples computeRowAt_zero op1RowData).trans rfl

/-! ## The served memory trace -/

/-- The OP1 slice's exact served memory trace. -/
noncomputable def memoryTrace
    (hread : Vmem (memoryInputs seedZ) (readPub seedZ alphaA))
    (hdec : Vmem (memoryInputs seedZ) (decomposePub seedZ alphaA))
    (hver : Vmem (memoryInputs seedZ) (verifyPub seedZ alphaA)) :
    ExactServedMemoryTrace 97 3 (cfg seedZ alphaA) (exec seedZ alphaA)
      (semanticData hread hdec hver) (execA seedZ alphaA) where
  roots := rootTraces
  timestampPowersNodup := forestTimestampPowers_nodup
  forestIndexRange := by
    rw [forestTimestampPowers]; norm_num [IO.InRange, cfg]
  semanticCoverage := by
    intro row lookup hlookup
    have hl : lookup ∈ (rowData row).needs.served := hlookup
    have hmem : lookupTuple lookup ∈ (rowData row).needs.served.map lookupTuple :=
      List.mem_map_of_mem hl
    fin_cases row
    · rw [rowData_zero_servedTuples] at hmem; simp at hmem

end Nock.NockVMROM.Thm54.TraceGen.Op1Config

#print axioms Nock.NockVMROM.Thm54.TraceGen.Op1Config.memoryTrace
