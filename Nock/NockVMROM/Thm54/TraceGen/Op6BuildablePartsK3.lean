/-
  Nock/NockVMROM/Thm54/TraceGen/Op6BuildablePartsK3.lean

  Stage 4b of the OP6 Layer-2 CORE, over `K3`: the twelve non-semantic
  `BuildableNockExecution` side-obligations and compute-row acceptance
  for the fan-out-2 branch (if) program

      `*[0 [6 [[1 0] [[1 5] [1 6]]]]] = 5`

  Five unique requests `(F,T,P,C1,C2)` with timestamps `α,α²,α³,α⁴,α⁵`, five
  `read_root` / five `verify_child` wrappers, orbit capacity `2⁵ = 32`.  The atom
  bound is `q = 97 = ringChar K3`
-/
import Nock.NockVMROM.Thm54.TraceGen.Op6ConfigK3
import Nock.NockVMROM.Thm54.TraceGen.RowEncode

namespace Nock.NockVMROM.Thm54.TraceGen.Op6ConfigK3

open Nock Nock.Walk Nock.NockVM
open Nock.ComputeTable Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen

set_option linter.unusedSimpArgs false

/-! ## The characteristic of the table field -/

theorem ringChar_K3 : ringChar K = 97 :=
  CharP.eq K (ringChar.charP K) (inferInstanceAs (CharP K 97))

/-! ## BFS-flat compute and memory rows -/

theorem computeRows_eq :
    (exec seedZ alphaA).computeRows =
      [parentRow seedZ alphaA, child1Row seedZ alphaA, child2Row seedZ alphaA] := by
  simp [ExactExecution.computeRows, exec, computeTree, bfsForest]

theorem memoryRows_eq :
    (exec seedZ alphaA).memoryRows =
      [lblOf seedZ (pReadF seedZ alphaA),
       lblOf seedZ (pDecF seedZ alphaA),
       lblOf seedZ (pHalt6 seedZ alphaA),
       lblOf seedZ (pVerifyF seedZ alphaA),
       lblOf seedZ (pReadT seedZ alphaA),
       lblOf seedZ (pDecT seedZ alphaA),
       lblOf seedZ (pVerifyT seedZ alphaA),
       lblOf seedZ (pReadP seedZ alphaA),
       lblOf seedZ (pReadC2 seedZ alphaA),
       lblOf seedZ (pDecP seedZ alphaA),
       lblOf seedZ (pDecC2 seedZ alphaA),
       lblOf seedZ (pVerifyP seedZ alphaA),
       lblOf seedZ (pDecBranchD seedZ alphaA),
       lblOf seedZ (pHalt1_c2 seedZ alphaA),
       lblOf seedZ (pVerifyC2 seedZ alphaA),
       lblOf seedZ (pReadC1 seedZ alphaA),
       lblOf seedZ (pHalt1_d seedZ alphaA),
       lblOf seedZ (pHalt6_d seedZ alphaA),
       lblOf seedZ (pHalt0 seedZ alphaA),
       lblOf seedZ (pDecC1 seedZ alphaA),
       lblOf seedZ (pHalt1_c1 seedZ alphaA),
       lblOf seedZ (pVerifyC1 seedZ alphaA),
       lblOf seedZ (pHalt5 seedZ alphaA)] := by
  norm_num [ExactExecution.memoryRows, exec, rootTree, tDecF, tHalt6, tVerifyF, tReadT, tDecT,
    tVerifyT, tReadC2, tDecC2, tHalt1_c2, tVerifyC2, tHalt0,
    tReadP, tDecP, tVerifyP, tReadC1, tDecC1, tHalt1_c1, tVerifyC1, tHalt5,
    tDecBranchD, tHalt1_d, tHalt6_d,
    mLeaf, mOne, mTwo, bfsForest, NTree.size, totalSize]

/-! ## Distinct timestamps `α,α²,α³,α⁴,α⁵` in `K3` (`α = 4`) -/

theorem ts_recF : (recF seedZ alphaA).ts = alphaA := rfl
theorem ts_recT : (recT seedZ alphaA).ts = alphaA ^ 2 := rfl
theorem ts_recP : (recP seedZ alphaA).ts = alphaA ^ 3 := rfl
theorem ts_recC1 : (recC1 seedZ alphaA).ts = alphaA ^ 4 := rfl
theorem ts_recC2 : (recC2 seedZ alphaA).ts = alphaA ^ 5 := rfl

theorem alpha_pow_ne_12 : alphaA ≠ alphaA ^ 2 := by decide
theorem alpha_pow_ne_13 : alphaA ≠ alphaA ^ 3 := by decide
theorem alpha_pow_ne_14 : alphaA ≠ alphaA ^ 4 := by decide
theorem alpha_pow_ne_15 : alphaA ≠ alphaA ^ 5 := by decide
theorem alpha_pow_ne_23 : alphaA ^ 2 ≠ alphaA ^ 3 := by decide
theorem alpha_pow_ne_24 : alphaA ^ 2 ≠ alphaA ^ 4 := by decide
theorem alpha_pow_ne_25 : alphaA ^ 2 ≠ alphaA ^ 5 := by decide
theorem alpha_pow_ne_34 : alphaA ^ 3 ≠ alphaA ^ 4 := by decide
theorem alpha_pow_ne_35 : alphaA ^ 3 ≠ alphaA ^ 5 := by decide
theorem alpha_pow_ne_45 : alphaA ^ 4 ≠ alphaA ^ 5 := by decide

/-! ## Raw canonical IO projections of the slice -/

theorem rawRequests_eq :
    (exec seedZ alphaA).rawRequests =
      [recF seedZ alphaA, recT seedZ alphaA, recP seedZ alphaA,
       recC1 seedZ alphaA, recC2 seedZ alphaA] := by
  rw [ExactExecution.rawRequests_eq_computeRows, computeRows_eq]
  simp [NockVM.activeRequestRecords, parentRow, child1Row, child2Row,
    parentPub, child1Pub, child2Pub, op1PubOf]

theorem rawResponses_eq :
    (exec seedZ alphaA).rawResponses =
      [NockVM.formRRow (recF seedZ alphaA) MemoryTable.formRDefault,
      NockVM.formRRow (recT seedZ alphaA) MemoryTable.formRDefault,
      NockVM.formRRow (recP seedZ alphaA) MemoryTable.formRDefault,
       NockVM.formRRow (recC2 seedZ alphaA) MemoryTable.formRDefault,
       NockVM.formRRow (recC1 seedZ alphaA) MemoryTable.formRDefault] := by
  rw [ExactExecution.rawResponses_eq_memoryRows, memoryRows_eq]
  simp [MemoryTable.responseRecords, lblOf,
    pReadF, pDecF, pHalt6, pVerifyF, pReadT, pDecT, pVerifyT,
    pReadP, pReadC2, pDecP, pDecC2, pVerifyP, pReadC1, pDecC1, pHalt1_c1, pVerifyC1,
    pHalt5, pDecBranchD, pHalt1_d, pHalt6_d, pHalt1_c2, pVerifyC2, pHalt0,
    readPub, decPub, haltPub, verifyPub, MemRec.zero]

theorem consumedRecordList_eq :
    RowLayout.consumedRecordList (exec seedZ alphaA) =
      [NockVM.formRRow (recF seedZ alphaA) MemoryTable.formRDefault,
      NockVM.formRRow (recT seedZ alphaA) MemoryTable.formRDefault,
      NockVM.formRRow (recP seedZ alphaA) MemoryTable.formRDefault,
       NockVM.formRRow (recC2 seedZ alphaA) MemoryTable.formRDefault,
       NockVM.formRRow (recC1 seedZ alphaA) MemoryTable.formRDefault] := by
  unfold RowLayout.consumedRecordList
  rw [memoryRows_eq]
  simp [RowLayout.consumedRecords, lblOf,
    pReadF, pDecF, pHalt6, pVerifyF, pReadT, pDecT, pVerifyT,
    pReadP, pReadC2, pDecP, pDecC2, pVerifyP, pReadC1, pDecC1, pHalt1_c1, pVerifyC1,
    pHalt5, pDecBranchD, pHalt1_d, pHalt6_d, pHalt1_c2, pVerifyC2, pHalt0,
    readPub, decPub, haltPub, verifyPub, MemRec.zero]

theorem honestVer :
    ∀ row ∈ (exec seedZ alphaA).memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root) := by
  simp [memoryRows_eq, lblOf,
    pReadF, pDecF, pHalt6, pVerifyF, pReadT, pDecT, pVerifyT,
    pReadP, pReadC2, pDecP, pDecC2, pVerifyP, pReadC1, pDecC1, pHalt1_c1, pVerifyC1,
    pHalt5, pDecBranchD, pHalt1_d, pHalt6_d, pHalt1_c2, pVerifyC2, pHalt0,
    readPub, decPub, haltPub, verifyPub]

theorem pairedRecordLayout :
    RowLayout.PairedRecordLayout (exec seedZ alphaA) := by
  rw [RowLayout.PairedRecordLayout,
    ← RowLayout.rawResponses_eq_addedRecordList _ honestVer,
    rawResponses_eq, consumedRecordList_eq]

theorem encRec_ne_of_ts_ne {r s : ComputeTable.MemRec K} (h : r.ts ≠ s.ts) :
    NockVM.encRecFormR r MemoryTable.formRDefault ≠
      NockVM.encRecFormR s MemoryTable.formRDefault := by
  intro he
  exact h (by have hc := congrFun he (7 : Fin 9); change r.ts = s.ts at hc; exact hc)

/-! ## The twelve non-semantic `BuildableNockExecution` fields -/

theorem derived_requests :
    (exec seedZ alphaA).derivedRequestIO =
      [NockVM.encRecFormR (recF seedZ alphaA) MemoryTable.formRDefault,
          NockVM.encRecFormR (recT seedZ alphaA) MemoryTable.formRDefault,
       NockVM.encRecFormR (recP seedZ alphaA) MemoryTable.formRDefault,
           NockVM.encRecFormR (recC1 seedZ alphaA) MemoryTable.formRDefault,
       NockVM.encRecFormR (recC2 seedZ alphaA) MemoryTable.formRDefault] := by
  rw [ExactExecution.derivedRequestIO, rawRequests_eq]; rfl

theorem derived_responses :
    (exec seedZ alphaA).derivedResponseIO =
      [NockVM.encRecFormR (recF seedZ alphaA) MemoryTable.formRDefault,
          NockVM.encRecFormR (recT seedZ alphaA) MemoryTable.formRDefault,
       NockVM.encRecFormR (recP seedZ alphaA) MemoryTable.formRDefault,
           NockVM.encRecFormR (recC2 seedZ alphaA) MemoryTable.formRDefault,
       NockVM.encRecFormR (recC1 seedZ alphaA) MemoryTable.formRDefault] := by
  rw [ExactExecution.derivedResponseIO_eq_memoryRows, memoryRows_eq]
  simp [lblOf, MemoryTable.Pub.cprime, parentDec, parentPub, parentRow, pReadF, pDecF, pHalt6,
    pVerifyF, pReadT, pDecT, pVerifyT, pReadC2, pDecC2, pHalt1_c2, pVerifyC2, pHalt0, pReadP,
    pDecP, pVerifyP, pReadC1, pDecC1, pHalt1_c1, pVerifyC1, pHalt5, pDecBranchD, pHalt1_d,
    pHalt6_d, readPub, decPub, haltPub, verifyPub]

theorem requestNodup : (exec seedZ alphaA).derivedRequestIO.Nodup := by
  rw [derived_requests]
  have hFT : NockVM.encRecFormR (recF seedZ alphaA) MemoryTable.formRDefault ≠
      NockVM.encRecFormR (recT seedZ alphaA) MemoryTable.formRDefault :=
    encRec_ne_of_ts_ne (by rw [ts_recF, ts_recT]; exact alpha_pow_ne_12)
  have hFP : NockVM.encRecFormR (recF seedZ alphaA) MemoryTable.formRDefault ≠
      NockVM.encRecFormR (recP seedZ alphaA) MemoryTable.formRDefault :=
    encRec_ne_of_ts_ne (by rw [ts_recF, ts_recP]; exact alpha_pow_ne_13)
  have hFC1 : NockVM.encRecFormR (recF seedZ alphaA) MemoryTable.formRDefault ≠
      NockVM.encRecFormR (recC1 seedZ alphaA) MemoryTable.formRDefault :=
    encRec_ne_of_ts_ne (by rw [ts_recF, ts_recC1]; exact alpha_pow_ne_14)
  have hFC2 : NockVM.encRecFormR (recF seedZ alphaA) MemoryTable.formRDefault ≠
      NockVM.encRecFormR (recC2 seedZ alphaA) MemoryTable.formRDefault :=
    encRec_ne_of_ts_ne (by rw [ts_recF, ts_recC2]; exact alpha_pow_ne_15)
  have hTP : NockVM.encRecFormR (recT seedZ alphaA) MemoryTable.formRDefault ≠
      NockVM.encRecFormR (recP seedZ alphaA) MemoryTable.formRDefault :=
    encRec_ne_of_ts_ne (by rw [ts_recT, ts_recP]; exact alpha_pow_ne_23)
  have hTC1 : NockVM.encRecFormR (recT seedZ alphaA) MemoryTable.formRDefault ≠
      NockVM.encRecFormR (recC1 seedZ alphaA) MemoryTable.formRDefault :=
    encRec_ne_of_ts_ne (by rw [ts_recT, ts_recC1]; exact alpha_pow_ne_24)
  have hTC2 : NockVM.encRecFormR (recT seedZ alphaA) MemoryTable.formRDefault ≠
      NockVM.encRecFormR (recC2 seedZ alphaA) MemoryTable.formRDefault :=
    encRec_ne_of_ts_ne (by rw [ts_recT, ts_recC2]; exact alpha_pow_ne_25)
  have hPC1 : NockVM.encRecFormR (recP seedZ alphaA) MemoryTable.formRDefault ≠
      NockVM.encRecFormR (recC1 seedZ alphaA) MemoryTable.formRDefault :=
    encRec_ne_of_ts_ne (by rw [ts_recP, ts_recC1]; exact alpha_pow_ne_34)
  have hPC2 : NockVM.encRecFormR (recP seedZ alphaA) MemoryTable.formRDefault ≠
      NockVM.encRecFormR (recC2 seedZ alphaA) MemoryTable.formRDefault :=
    encRec_ne_of_ts_ne (by rw [ts_recP, ts_recC2]; exact alpha_pow_ne_35)
  have hC1C2 : NockVM.encRecFormR (recC1 seedZ alphaA) MemoryTable.formRDefault ≠
      NockVM.encRecFormR (recC2 seedZ alphaA) MemoryTable.formRDefault :=
    encRec_ne_of_ts_ne (by rw [ts_recC1, ts_recC2]; exact alpha_pow_ne_45)
  simp [hFT, hFP, hFC1, hFC2, hTP, hTC1, hTC2, hPC1, hPC2, hC1C2]

theorem memoryStateCounts :
    RowLayout.memoryStateCount (exec seedZ alphaA) .read_root = 5 ∧
      RowLayout.memoryStateCount (exec seedZ alphaA) .verify_child = 5 := by
  constructor <;>
    simp [RowLayout.memoryStateCount, RowLayout.fibreCount, memoryRows_eq, lblOf,
      pReadF, pDecF, pHalt6, pVerifyF, pReadT, pDecT, pVerifyT, pHalt5,
      pReadP, pDecP, pVerifyP, pReadC1, pDecC1, pHalt1_c1, pVerifyC1,
      pReadC2, pDecC2, pHalt1_c2, pVerifyC2, pHalt0,
      pDecBranchD, pHalt1_d, pHalt6_d,
      readPub, decPub, haltPub, verifyPub]

theorem recordCountBalance : RowLayout.RecordCountBalanced (exec seedZ alphaA) := by
  rw [RowLayout.RecordCountBalanced, memoryStateCounts.1, memoryStateCounts.2]

theorem q_le_ringChar : (97 : ℕ) ≤ ringChar K := by
  rw [ringChar_K3]

theorem two_ne_zero : (2 : K) ≠ 0 := by decide

theorem Ksz_lt_ringChar : (cfg seedZ alphaA).Ksz < ringChar K := by
  rw [ringChar_K3]; norm_num [cfg]

theorem programIOCapacity :
    (exec seedZ alphaA).derivedRequestIO.length + 1 ≤ 2 ^ (cfg seedZ alphaA).orbit.h := by
  rw [derived_requests]; norm_num [cfg, executionOrbit]

theorem memoryIOCapacity :
    (exec seedZ alphaA).derivedResponseIO.length + 1 ≤ 2 ^ (cfg seedZ alphaA).orbit.h := by
  rw [derived_responses]; norm_num [cfg, executionOrbit]

/-! ## Compute row acceptance -/

noncomputable section

theorem parent_accepts : Vcomp (compInputs seedZ alphaA) (parentPub seedZ alphaA)
    (parentDec seedZ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact GlobalCarryRecognizer.enc_cons seedZ_ne_zero op6Head op6ParentTail
  · ext <;>
      norm_num [parentPub, recF, parentDec, compInputs, fp, seedZ, alphaA]
  · simp [SVhead, headAtom, parentPub, parentDec, compInputs, fp, op6Head,
      GlobalCarryRecognizer.enc_atom, State.toNat, seedZ]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · ext <;>
        norm_num [parentPub, recT, parentDec, compInputs, fp, seedZ, alphaA]
    · exact (GlobalCarryRecognizer.enc_cons seedZ_ne_zero op6CondFormula op6BranchPair).symm
    · ext <;>
        norm_num [parentPub, recP, parentDec, compInputs, fp, seedZ, alphaA]
    · exact (GlobalCarryRecognizer.enc_cons seedZ_ne_zero op6BranchC op6BranchD).symm
    · simp [parentPub, compInputs]
  · refine ⟨rfl, ?_, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · simp only [parentPub, parentDec, fp, op6CondResult,
        GlobalCarryRecognizer.enc_atom, FP.atomFP, seedZ]
      simp
    · simp [parentPub, compInputs, fp, op6CondResult,
        GlobalCarryRecognizer.enc_atom, FP.atomFP, seedZ]
    · simp [parentPub, fp, op6CondResult, GlobalCarryRecognizer.enc_atom, FP.atomFP]
    · left
      simp [parentPub, fp, op6CondResult, GlobalCarryRecognizer.enc_atom, FP.atomFP]
    · exact ⟨rfl, rfl, rfl⟩

theorem child1_accepts : Vcomp (compInputs seedZ alphaA) (child1Pub seedZ alphaA)
    (op1DecOf seedZ op6Result) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact GlobalCarryRecognizer.enc_cons seedZ_ne_zero (.atom 1) op6Result
  · ext <;>
      norm_num [child1Pub, op1PubOf, recC1, op1DecOf, compInputs, fp, seedZ, alphaA,
        pow_succ, pow_two]
  · simp [SVhead, headAtom, child1Pub, op1PubOf, op1DecOf, fp, op1Head,
      GlobalCarryRecognizer.enc_atom, State.toNat, compInputs, seedZ]
  · exact ⟨rfl, rfl, by norm_num [child1Pub, op1PubOf, compInputs, pow_succ, alphaA]⟩
  · exact ⟨rfl, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

theorem child2_accepts : Vcomp (compInputs seedZ alphaA) (child2Pub seedZ alphaA)
    (op1DecOf seedZ op6CondResult) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact GlobalCarryRecognizer.enc_cons seedZ_ne_zero (.atom 1) op6CondResult
  · ext <;>
      norm_num [child2Pub, op1PubOf, recC2, op1DecOf, compInputs, fp, seedZ, alphaA,
        pow_succ, pow_two]
  · simp [SVhead, headAtom, child2Pub, op1PubOf, op1DecOf, fp, op1Head,
      GlobalCarryRecognizer.enc_atom, State.toNat, compInputs, seedZ]
  · exact ⟨rfl, rfl, by norm_num [child2Pub, op1PubOf, compInputs, pow_succ, alphaA]⟩
  · exact ⟨rfl, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

theorem computeRowsAccepted : (exec seedZ alphaA).ComputeRowsAccepted := by
  rw [ExactExecution.computeRowsAccepted_iff, computeRows_eq]
  intro row hrow
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
  rcases hrow with rfl | rfl | rfl
  · exact ⟨rfl, rfl, parent_accepts⟩
  · exact ⟨rfl, rfl, child1_accepts⟩
  · exact ⟨rfl, rfl, child2_accepts⟩

/-! ## BFS re-indexing of the canonical compute rows -/

theorem computeRowAt_zero :
    (exec seedZ alphaA).computeRowAt ⟨0, by norm_num [cfg]⟩ = parentRow seedZ alphaA := by
  norm_num [ExactExecution.computeRowAt, computeRows_eq, cfg]

theorem computeRowAt_one :
    (exec seedZ alphaA).computeRowAt ⟨1, by norm_num [cfg]⟩ = child1Row seedZ alphaA := by
  norm_num [ExactExecution.computeRowAt, computeRows_eq, cfg]

theorem computeRowAt_two :
    (exec seedZ alphaA).computeRowAt ⟨2, by norm_num [cfg]⟩ = child2Row seedZ alphaA := by
  norm_num [ExactExecution.computeRowAt, computeRows_eq, cfg]

end


theorem exec_encode : exec seedZ alphaA = (execA seedZ alphaA).encodeMem :=
  RowEncode.eq_encodeMem_of rfl (by
    simp [exec, execA, mOne, mTwo, mLeaf, mapNTree, lblOf, tHalt6, tHalt5, tHalt0, tVerifyC2,
      tHalt1_c2, tDecC2, tReadC2, tVerifyT, tVerifyC1, tHalt1_c1, tDecC1, tReadC1, tVerifyP,
      tHalt6_d, tHalt1_d, tDecBranchD, tDecP, tReadP, tDecT, tReadT, tVerifyF, tDecF, rootTree,
      tVerifyC2A, tDecC2A, tReadC2A, tVerifyTA, tVerifyC1A, tDecC1A, tReadC1A, tVerifyPA, tDecPA,
      tReadPA, tDecTA, tReadTA, tVerifyFA, tDecFA, rootTreeA, parentDec, parentPub, parentRow,
      pReadF, pDecF, pHalt6, pVerifyF, pReadT, pDecT, pVerifyT, pReadC2, pDecC2, pHalt1_c2,
      pVerifyC2, pHalt0, pReadP, pDecP, pVerifyP, pReadC1, pDecC1, pHalt1_c1, pVerifyC1, pHalt5,
      pReadFA, pVerifyFA, pReadTA, pVerifyTA, pReadC2A, pVerifyC2A, pReadPA, pVerifyPA, pReadC1A,
      pVerifyC1A, pDecBranchD, pHalt1_d, pHalt6_d, readPub, readPubA, verifyPub, verifyPubA,
      haltPub, decPub])

end Nock.NockVMROM.Thm54.TraceGen.Op6ConfigK3

#print axioms Nock.NockVMROM.Thm54.TraceGen.Op6ConfigK3.requestNodup
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op6ConfigK3.recordCountBalance
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op6ConfigK3.computeRowsAccepted
