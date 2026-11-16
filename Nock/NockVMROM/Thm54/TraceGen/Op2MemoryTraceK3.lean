/-
  Nock/NockVMROM/Thm54/TraceGen/Op2MemoryTraceK3.lean

  Stage 3 of the OP2 Layer-2 CORE, over `K3`: the same-execution served-memory
  trace `ExactServedMemoryTrace 97 7 cfg exec semanticData` for

      `*[0 [2 [1 [0 1]] [1 [1 5]]]] = 5`

  The twenty-three-row single-root reconstruction services FIVE committed records
  through five nested `read_root`/`verify_child` pairs.  The axis-2 (left) descent
  on the formula tail is the OP2-specific NMR shape.  `semanticCoverage` is vacuous: every `.s2`/`.s1` row has
  `requiredServedLookups = 0`.  There is no Layer-1 committed served-memory fixture;
  this is the reconstruction, not a served forest
-/
import Nock.NockVMROM.Thm54.TraceGen.Op2BuildablePartsK3
import Nock.NockVMROM.Thm54.ServedMemoryTrace
import Nock.NockVMROM.Thm54.AxisSoundness

namespace Nock.NockVMROM.Thm54.TraceGen.Op2ConfigK3

open Nock Nock.Walk Nock.NockVM
open Nock.ComputeTable Nock.MemoryTable
open Nock.AxisBatching Nock.AxisBatching.MTree
open Nock.AxisBridge
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ServedMemoryTrace
open Nock.NockVMROM.Thm54.SemanticTrace
open Nock.NockVMROM.Thm54.TraceGen

noncomputable section

/-! ## Canonical timestamp exponents of the five records -/

theorem ts_closed_recF :
    TimestampClosedAt (cfg seedZ alphaA).challenges.α (recF seedZ alphaA).ts :=
  ⟨1, by rw [ts_recF]; simp [cfg, alphaA]⟩
theorem ts_closed_recT :
    TimestampClosedAt (cfg seedZ alphaA).challenges.α (recT seedZ alphaA).ts :=
  ⟨2, by rw [ts_recT]; rfl⟩
theorem ts_closed_recB :
    TimestampClosedAt (cfg seedZ alphaA).challenges.α (recB seedZ alphaA).ts :=
  ⟨3, by rw [ts_recB]; rfl⟩
theorem ts_closed_recC :
    TimestampClosedAt (cfg seedZ alphaA).challenges.α (recC seedZ alphaA).ts :=
  ⟨4, by rw [ts_recC]; rfl⟩
theorem ts_closed_recS :
    TimestampClosedAt (cfg seedZ alphaA).challenges.α (recS seedZ alphaA).ts :=
  ⟨5, by rw [ts_recS]; rfl⟩

def expF : ℕ := timestampExp (cfg seedZ alphaA).challenges.α (recF seedZ alphaA).ts
def expT : ℕ := timestampExp (cfg seedZ alphaA).challenges.α (recT seedZ alphaA).ts
def expB : ℕ := timestampExp (cfg seedZ alphaA).challenges.α (recB seedZ alphaA).ts
def expC : ℕ := timestampExp (cfg seedZ alphaA).challenges.α (recC seedZ alphaA).ts
def expS : ℕ := timestampExp (cfg seedZ alphaA).challenges.α (recS seedZ alphaA).ts

theorem ts_eq_recF : (recF seedZ alphaA).ts = (cfg seedZ alphaA).challenges.α ^ expF :=
  timestampExp_spec ts_closed_recF
theorem ts_eq_recT : (recT seedZ alphaA).ts = (cfg seedZ alphaA).challenges.α ^ expT :=
  timestampExp_spec ts_closed_recT
theorem ts_eq_recB : (recB seedZ alphaA).ts = (cfg seedZ alphaA).challenges.α ^ expB :=
  timestampExp_spec ts_closed_recB
theorem ts_eq_recC : (recC seedZ alphaA).ts = (cfg seedZ alphaA).challenges.α ^ expC :=
  timestampExp_spec ts_closed_recC
theorem ts_eq_recS : (recS seedZ alphaA).ts = (cfg seedZ alphaA).challenges.α ^ expS :=
  timestampExp_spec ts_closed_recS

theorem expF_ne_expT : expF ≠ expT := by
  intro h
  have heq : (recF seedZ alphaA).ts = (recT seedZ alphaA).ts := by
    rw [ts_eq_recF, ts_eq_recT, h]
  rw [ts_recF, ts_recT] at heq
  exact alpha_pow_ne_12 heq
theorem expF_ne_expB : expF ≠ expB := by
  intro h
  have heq : (recF seedZ alphaA).ts = (recB seedZ alphaA).ts := by
    rw [ts_eq_recF, ts_eq_recB, h]
  rw [ts_recF, ts_recB] at heq
  exact alpha_pow_ne_13 heq
theorem expF_ne_expC : expF ≠ expC := by
  intro h
  have heq : (recF seedZ alphaA).ts = (recC seedZ alphaA).ts := by
    rw [ts_eq_recF, ts_eq_recC, h]
  rw [ts_recF, ts_recC] at heq
  exact alpha_pow_ne_14 heq
theorem expF_ne_expS : expF ≠ expS := by
  intro h
  have heq : (recF seedZ alphaA).ts = (recS seedZ alphaA).ts := by
    rw [ts_eq_recF, ts_eq_recS, h]
  rw [ts_recF, ts_recS] at heq
  exact alpha_pow_ne_15 heq
theorem expT_ne_expB : expT ≠ expB := by
  intro h
  have heq : (recT seedZ alphaA).ts = (recB seedZ alphaA).ts := by
    rw [ts_eq_recT, ts_eq_recB, h]
  rw [ts_recT, ts_recB] at heq
  exact alpha_pow_ne_23 heq
theorem expT_ne_expC : expT ≠ expC := by
  intro h
  have heq : (recT seedZ alphaA).ts = (recC seedZ alphaA).ts := by
    rw [ts_eq_recT, ts_eq_recC, h]
  rw [ts_recT, ts_recC] at heq
  exact alpha_pow_ne_24 heq
theorem expT_ne_expS : expT ≠ expS := by
  intro h
  have heq : (recT seedZ alphaA).ts = (recS seedZ alphaA).ts := by
    rw [ts_eq_recT, ts_eq_recS, h]
  rw [ts_recT, ts_recS] at heq
  exact alpha_pow_ne_25 heq
theorem expB_ne_expC : expB ≠ expC := by
  intro h
  have heq : (recB seedZ alphaA).ts = (recC seedZ alphaA).ts := by
    rw [ts_eq_recB, ts_eq_recC, h]
  rw [ts_recB, ts_recC] at heq
  exact alpha_pow_ne_34 heq
theorem expB_ne_expS : expB ≠ expS := by
  intro h
  have heq : (recB seedZ alphaA).ts = (recS seedZ alphaA).ts := by
    rw [ts_eq_recB, ts_eq_recS, h]
  rw [ts_recB, ts_recS] at heq
  exact alpha_pow_ne_35 heq
theorem expC_ne_expS : expC ≠ expS := by
  intro h
  have heq : (recC seedZ alphaA).ts = (recS seedZ alphaA).ts := by
    rw [ts_eq_recC, ts_eq_recS, h]
  rw [ts_recC, ts_recS] at heq
  exact alpha_pow_ne_45 heq

theorem expT_ne_expF : expT ≠ expF := fun h => expF_ne_expT h.symm
theorem expB_ne_expF : expB ≠ expF := fun h => expF_ne_expB h.symm
theorem expC_ne_expF : expC ≠ expF := fun h => expF_ne_expC h.symm
theorem expS_ne_expF : expS ≠ expF := fun h => expF_ne_expS h.symm
theorem expB_ne_expT : expB ≠ expT := fun h => expT_ne_expB h.symm
theorem expC_ne_expT : expC ≠ expT := fun h => expT_ne_expC h.symm
theorem expS_ne_expT : expS ≠ expT := fun h => expT_ne_expS h.symm
theorem expC_ne_expB : expC ≠ expB := fun h => expB_ne_expC h.symm
theorem expS_ne_expB : expS ≠ expB := fun h => expB_ne_expS h.symm
theorem expS_ne_expC : expS ≠ expC := fun h => expC_ne_expS h.symm

/-! ## The reified memory `MTree` of the single serviced root -/

theorem memoryTreeAt_zero :
    (execA seedZ alphaA).memoryTreeAt ⟨0, by norm_num [cfg]⟩ = rootTreeA seedZ alphaA := rfl

theorem axisPath_three : axisPath 3 = [true] := by
  rw [axisPath_of_two_le (by norm_num)]
  norm_num [axisPath_of_lt_two]

theorem axisPath_two : axisPath 2 = [false] := by
  rw [axisPath_of_two_le (by norm_num)]
  norm_num [axisPath_of_lt_two]

set_option maxRecDepth 400000 in
/-- The OP2 axis tree: formula@3, then the axis-2 left descent on the formula tail,
then the three child formula@3 services. -/
theorem op2AxisTree_eq :
    exactAxisTree (cfg seedZ alphaA) (execA seedZ alphaA) ⟨0, by norm_num [cfg]⟩ =
      MTree.read expF
        (MTree.decompose MTree.halt
          (MTree.verify expF 3
            (MTree.read expT
              (MTree.decompose
                (MTree.verify expT 2
                  (MTree.read expB
                    (MTree.decompose MTree.halt
                      (MTree.verify expB 3
                        (MTree.decompose MTree.halt MTree.halt)))))
                (MTree.read expC
                  (MTree.decompose MTree.halt
                    (MTree.verify expC 3
                      (MTree.read expS
                        (MTree.decompose MTree.halt
                          (MTree.verify expS 3 MTree.halt)))))))))) := by
  rw [exactAxisTree, memoryTreeAt_zero]
  simp [rootTreeA, tDecFA, tHalt2, tVerifyFA, tReadTA, tDecTA, tVerifyTA, tReadCA, tReadBA,
    tDecCA, tDecBA, tHaltC1, tVerifyCA, tHaltB1, tVerifyBA, tReadSA, tDecSf1, tDecSA,
    tHalt0, tHalt1s, tHaltS1, tVerifySA, tHalt5, mOne, mTwo, mLeaf, lblOf,
    Nock.AxisBridge.ofNTree, Nock.AxisBridge.MemWalk.toMTree, timestampExpAt,
    expF, expT, expB, expC, expS,
    pReadFA, pDecF, pHalt2, pVerifyFA, pReadTA, pDecT, pVerifyTA, pReadCA, pReadBA,
    pDecC, pDecB, pHaltC1, pVerifyCA, pHaltB1, pVerifyBA, pReadSA, pDecSf1, pDecS,
    pHalt0, pHalt1s, pHaltS1, pVerifySA, pHalt5,
    readPub, readPubA, decPub, haltPub, verifyPub, verifyPubA,
    recF, recT, recB, recC, recS]

/-! ## The five compute-side services -/

/-- Parent formula-open `[2 [b c]] @3`. -/
def serviceF : Service (cfg seedZ alphaA) (execA seedZ alphaA) where
  exponent := expF
  record := recF seedZ alphaA
  root := op2ParentFormula
  child := op2ParentTail
  axis := 3
  request_mem := by
    rw [show (execA seedZ alphaA).rawRequests = (exec seedZ alphaA).rawRequests from rfl,
      rawRequests_eq]; simp
  timestamp := ts_eq_recF
  realization :=
    { root_realizes := rfl
      child_realizes := rfl
      axis_realizes := by norm_num [recF] }
  served := by simp [op2ParentFormula, op2ParentTail, Noun.slot]

/-- Parent formula-tail `[b c] @2` — the axis-2 left descent. -/
def serviceT : Service (cfg seedZ alphaA) (execA seedZ alphaA) where
  exponent := expT
  record := recT seedZ alphaA
  root := op2ParentTail
  child := op2ChildFormula1
  axis := 2
  request_mem := by
    rw [show (execA seedZ alphaA).rawRequests = (exec seedZ alphaA).rawRequests from rfl,
      rawRequests_eq]; simp
  timestamp := ts_eq_recT
  realization :=
    { root_realizes := rfl
      child_realizes := rfl
      axis_realizes := by norm_num [recT] }
  served := by simp [op2ParentTail, op2ChildFormula1, Noun.slot]

/-- Child-one `[1 [0 1]] @3 → [0 1]`. -/
def serviceB : Service (cfg seedZ alphaA) (execA seedZ alphaA) where
  exponent := expB
  record := recB seedZ alphaA
  root := op2ChildFormula1
  child := op2Sf1
  axis := 3
  request_mem := by
    rw [show (execA seedZ alphaA).rawRequests = (exec seedZ alphaA).rawRequests from rfl,
      rawRequests_eq]; simp
  timestamp := ts_eq_recB
  realization :=
    { root_realizes := rfl
      child_realizes := rfl
      axis_realizes := by norm_num [recB] }
  served := by simp [op2ChildFormula1, op2Sf1, Noun.slot]

/-- Child-two `[1 [1 5]] @3 → [1 5]`. -/
def serviceC : Service (cfg seedZ alphaA) (execA seedZ alphaA) where
  exponent := expC
  record := recC seedZ alphaA
  root := op2ChildFormula2
  child := op2Sf2
  axis := 3
  request_mem := by
    rw [show (execA seedZ alphaA).rawRequests = (exec seedZ alphaA).rawRequests from rfl,
      rawRequests_eq]; simp
  timestamp := ts_eq_recC
  realization :=
    { root_realizes := rfl
      child_realizes := rfl
      axis_realizes := by norm_num [recC] }
  served := by simp [op2ChildFormula2, op2Sf2, Noun.slot]

/-- Child-three `[1 5] @3 → 5` (computed-subject child). -/
def serviceS : Service (cfg seedZ alphaA) (execA seedZ alphaA) where
  exponent := expS
  record := recS seedZ alphaA
  root := op2Sf2
  child := op2Result
  axis := 3
  request_mem := by
    rw [show (execA seedZ alphaA).rawRequests = (exec seedZ alphaA).rawRequests from rfl,
      rawRequests_eq]; simp
  timestamp := ts_eq_recS
  realization :=
    { root_realizes := rfl
      child_realizes := rfl
      axis_realizes := by norm_num [recS] }
  served := by simp [op2Sf2, op2Result, Noun.slot]

/-! ## The single serviced root's trace

`recordPartition` is the literal `read_root` BFS emission `(F,T,C,B,S)`.  The two
exponent partitions are the paper's positionless LogUp permutations against the
DFS axis-tree order `(F,T,B,C,S)`. -/

theorem rootResponseRecords_eq :
    rootResponseRecords (execA seedZ alphaA) ⟨0, by norm_num [cfg]⟩ =
      [recF seedZ alphaA, recT seedZ alphaA, recC seedZ alphaA,
        recB seedZ alphaA, recS seedZ alphaA] := by
  simp [rootResponseRecords, memoryTreeAt_zero, rootTreeA, tDecFA, tHalt2, tVerifyFA,
    tReadTA, tDecTA, tVerifyTA, tReadCA, tReadBA, tDecCA, tDecBA, tHaltC1, tVerifyCA,
    tHaltB1, tVerifyBA, tReadSA, tDecSf1, tDecSA, tHalt0, tHalt1s, tHaltS1, tVerifySA,
    tHalt5, mOne, mTwo, mLeaf, lblOf, bfsForest, MemoryTable.responseRecords,
    pReadFA, pDecF, pHalt2, pVerifyFA, pReadTA, pDecT, pVerifyTA, pReadCA, pReadBA,
    pDecC, pDecB, pHaltC1, pVerifyCA, pHaltB1, pVerifyBA, pReadSA, pDecSf1, pDecS,
    pHalt0, pHalt1s, pHaltS1, pVerifySA, pHalt5, readPub, readPubA, decPub, haltPub, verifyPub,
    verifyPubA]

/-- The exact semantic service partition of the OP2 slice's single serviced root. -/
def rootTrace : RootTrace (cfg seedZ alphaA) (execA seedZ alphaA)
    ⟨0, by norm_num [cfg]⟩ where
  subject := op2ParentFormula
  services := [serviceF, serviceT, serviceC, serviceB, serviceS]
  recordPartition := by
    rw [rootResponseRecords_eq]
    simp [serviceF, serviceT, serviceC, serviceB, serviceS]
  readPartition := by
    rw [op2AxisTree_eq]
    simp only [readExps, serviceF, serviceT, serviceC, serviceB, serviceS,
      List.map_cons, List.map_nil]
    exact List.Perm.cons _ (List.Perm.cons _ (List.Perm.swap _ _ _))
  verifyPartition := by
    rw [op2AxisTree_eq]
    simp only [verifyExps, serviceF, serviceT, serviceC, serviceB, serviceS,
      List.map_cons, List.map_nil]
    exact List.Perm.cons _ (List.Perm.cons _ (List.Perm.swap _ _ _))
  traversal := by
    rw [op2AxisTree_eq]
    -- read serviceF at the root formula noun
    refine ServiceWalk.read serviceF (by simp) rfl rfl ?_ ?_
    · rw [show serviceF.axis = 3 from rfl, axisPath_three]
      refine VerifyRoute.right (by simp [readCount]) (by simp [verifyCount]) ?_
      exact VerifyRoute.here rfl rfl
        (by simp [readCount, expT_ne_expF, expB_ne_expF, expC_ne_expF, expS_ne_expF])
        (by simp [verifyCount, expT_ne_expF, expB_ne_expF, expC_ne_expF, expS_ne_expF])
    · refine ServiceWalk.decompose ServiceWalk.halt ?_
      refine ServiceWalk.verify ?_
      -- read serviceT on the formula tail, axis-2 LEFT descent
      refine ServiceWalk.read serviceT (by simp) rfl rfl ?_ ?_
      · rw [show serviceT.axis = 2 from rfl, axisPath_two]
        refine VerifyRoute.left ?_
          (by simp [readCount, expC_ne_expT, expS_ne_expT])
          (by simp [verifyCount, expC_ne_expT, expS_ne_expT])
        exact VerifyRoute.here rfl rfl
          (by simp [readCount, expB_ne_expT])
          (by simp [verifyCount, expB_ne_expT])
      · refine ServiceWalk.decompose ?_ ?_
        · -- left: verify T wrapping child-one
          refine ServiceWalk.verify ?_
          refine ServiceWalk.read serviceB (by simp) rfl rfl ?_ ?_
          · rw [show serviceB.axis = 3 from rfl, axisPath_three]
            refine VerifyRoute.right (by simp [readCount]) (by simp [verifyCount]) ?_
            exact VerifyRoute.here rfl rfl (by simp [readCount]) (by simp [verifyCount])
          · exact ServiceWalk.decompose ServiceWalk.halt
              (ServiceWalk.verify (ServiceWalk.decompose ServiceWalk.halt ServiceWalk.halt))
        · -- right: child-two wrapping child-three
          refine ServiceWalk.read serviceC (by simp) rfl rfl ?_ ?_
          · rw [show serviceC.axis = 3 from rfl, axisPath_three]
            refine VerifyRoute.right (by simp [readCount]) (by simp [verifyCount]) ?_
            exact VerifyRoute.here rfl rfl
              (by simp [readCount, expS_ne_expC])
              (by simp [verifyCount, expS_ne_expC])
          · refine ServiceWalk.decompose ServiceWalk.halt ?_
            refine ServiceWalk.verify ?_
            refine ServiceWalk.read serviceS (by simp) rfl rfl ?_ ?_
            · rw [show serviceS.axis = 3 from rfl, axisPath_three]
              refine VerifyRoute.right (by simp [readCount]) (by simp [verifyCount]) ?_
              exact VerifyRoute.here rfl rfl (by simp [readCount]) (by simp [verifyCount])
            · exact ServiceWalk.decompose ServiceWalk.halt (ServiceWalk.verify ServiceWalk.halt)

def rootTraces : ∀ i : Fin (cfg seedZ alphaA).kMem,
    RootTrace (cfg seedZ alphaA) (execA seedZ alphaA) i
  | ⟨0, _⟩ => rootTrace
  | ⟨n + 1, h⟩ => absurd (show n + 1 < 1 by simp only [cfg] at h; exact h) (by omega)

theorem rootTraces_zero :
    rootTraces ⟨0, by norm_num [cfg]⟩ = rootTrace := rfl

theorem finRange_kMem :
    List.finRange (cfg seedZ alphaA).kMem = [⟨0, by norm_num [cfg]⟩] := rfl

/-! ## The aggregate `z^i` timestamp multiset closes -/

theorem forestTimestampPowers_eq :
    (List.finRange (cfg seedZ alphaA).kMem).flatMap
      (fun i => (rootTraces i).timestampPowers) =
      [alphaA, alphaA ^ 2, alphaA ^ 4, alphaA ^ 3, alphaA ^ 5] := by
  rw [finRange_kMem]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, rootTraces_zero]
  simp only [RootTrace.timestampPowers, RootTrace.exponents, rootTrace,
    List.map_cons, List.map_nil]
  rw [show (serviceF.exponent : ℕ) = expF from rfl,
    show (serviceT.exponent : ℕ) = expT from rfl,
    show (serviceC.exponent : ℕ) = expC from rfl,
    show (serviceB.exponent : ℕ) = expB from rfl,
    show (serviceS.exponent : ℕ) = expS from rfl,
    ← ts_eq_recF, ← ts_eq_recT, ← ts_eq_recC, ← ts_eq_recB, ← ts_eq_recS,
    ts_recF, ts_recT, ts_recC, ts_recB, ts_recS]

theorem forestTimestampPowers_nodup :
    ((List.finRange (cfg seedZ alphaA).kMem).flatMap
      (fun i => (rootTraces i).timestampPowers)).Nodup := by
  rw [forestTimestampPowers_eq]
  have h12 := alpha_pow_ne_12
  have h14 := alpha_pow_ne_14
  have h13 := alpha_pow_ne_13
  have h15 := alpha_pow_ne_15
  have h24 := alpha_pow_ne_24
  have h23 := alpha_pow_ne_23
  have h25 := alpha_pow_ne_25
  have h43 : alphaA ^ 4 ≠ alphaA ^ 3 := fun h => alpha_pow_ne_34 h.symm
  have h45 := alpha_pow_ne_45
  have h35 := alpha_pow_ne_35
  simp [List.nodup_cons, h12, h14, h13, h15, h24, h23, h25, h43, h45, h35]

theorem forestIndexRange :
    IO.InRange (cfg seedZ alphaA).Ksz
      ((List.finRange (cfg seedZ alphaA).kMem).flatMap
        (fun i => (rootTraces i).timestampPowers)).length := by
  rw [forestTimestampPowers_eq]
  norm_num [IO.InRange, cfg]

/-! ## Vacuous `semanticCoverage` (`OP_2`/`OP_1` have `requiredServedLookups = 0`) -/

def lookupTuple {z : K} (l : ServedNounLookup z) :
    ComputeTable.MemRec K × Noun × ℕ × Noun :=
  (l.record, l.root, l.axis, l.child)

theorem castRowData_servedTuples
    {row₁ row₂ : ComputeTable.State × ComputeTable.DTcomp K}
    (h : row₁ = row₂) (d : ComputeRowSemanticData 97 7 row₂) :
    (castRowData h d).needs.served.map lookupTuple = d.needs.served.map lookupTuple := by
  subst h; rfl

theorem rowData_zero_servedTuples :
    (rowData ⟨0, by norm_num [cfg]⟩).needs.served.map lookupTuple = [] :=
  (castRowData_servedTuples computeRowAt_zero parentRowData).trans rfl
theorem rowData_one_servedTuples :
    (rowData ⟨1, by norm_num [cfg]⟩).needs.served.map lookupTuple = [] :=
  (castRowData_servedTuples computeRowAt_one child1RowData).trans rfl
theorem rowData_two_servedTuples :
    (rowData ⟨2, by norm_num [cfg]⟩).needs.served.map lookupTuple = [] :=
  (castRowData_servedTuples computeRowAt_two child2RowData).trans rfl
theorem rowData_three_servedTuples :
    (rowData ⟨3, by norm_num [cfg]⟩).needs.served.map lookupTuple = [] :=
  (castRowData_servedTuples computeRowAt_three child3RowData).trans rfl

/-- The OP2/K3 slice's exact served memory trace. -/
def memoryTrace
    (hfirst :
      ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.counts = 0 ∧
        ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.indicator = 0) :
    ExactServedMemoryTrace 97 7 (cfg seedZ alphaA) (exec seedZ alphaA) (semanticData hfirst)
      (execA seedZ alphaA) where
  roots := rootTraces
  timestampPowersNodup := forestTimestampPowers_nodup
  forestIndexRange := by
    rw [forestTimestampPowers_eq]
    norm_num [IO.InRange, cfg]
  semanticCoverage := by
    intro row lookup hlookup
    have hl : lookup ∈ (rowData row).needs.served := hlookup
    have hmem : lookupTuple lookup ∈ (rowData row).needs.served.map lookupTuple :=
      List.mem_map_of_mem hl
    fin_cases row
    · rw [rowData_zero_servedTuples] at hmem; simp at hmem
    · rw [rowData_one_servedTuples] at hmem; simp at hmem
    · rw [rowData_two_servedTuples] at hmem; simp at hmem
    · rw [rowData_three_servedTuples] at hmem; simp at hmem

end

end Nock.NockVMROM.Thm54.TraceGen.Op2ConfigK3

#print axioms Nock.NockVMROM.Thm54.TraceGen.Op2ConfigK3.op2AxisTree_eq
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op2ConfigK3.rootTrace
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op2ConfigK3.memoryTrace
