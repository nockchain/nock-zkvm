/-
  Nock/NockVMROM/Thm54/TraceGen/Op7BuildablePartsK3.lean

  Stage 4b of the OP7 Layer-2 CORE, over `K3`: the twelve non-semantic
  `BuildableNockExecution` side-obligations and compute-row acceptance
  for the fan-out-2 compose program

      `*[0 [7 [1 3] [1 5]]] = 5`

  Four unique requests `(F,T,B,C)` with timestamps `α,…,α⁴`, four `read_root` /
  four `verify_child` wrappers, orbit capacity `2⁵ = 32`.  The atom bound is
  `q = 97 = ringChar K3`
-/
import Nock.NockVMROM.Thm54.TraceGen.Op7ConfigK3
import Nock.NockVMROM.Thm54.TraceGen.RowEncode
import Nock.NockVMROM.Thm54.HonestCommitment

namespace Nock.NockVMROM.Thm54.TraceGen.Op7ConfigK3

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
      [parentRow seedZ alphaA, child2Row seedZ alphaA, child1Row seedZ alphaA] := by
  simp [ExactExecution.computeRows, exec, computeTree, bfsForest]

theorem memoryRows_eq :
    (exec seedZ alphaA).memoryRows =
      [lblOf seedZ (pReadF seedZ alphaA),
       lblOf seedZ (pDecF seedZ alphaA),
       lblOf seedZ (pHalt7 seedZ alphaA),
       lblOf seedZ (pVerifyF seedZ alphaA),
       lblOf seedZ (pReadT seedZ alphaA),
       lblOf seedZ (pDecT seedZ alphaA),
       lblOf seedZ (pVerifyT seedZ alphaA),
       lblOf seedZ (pReadC seedZ alphaA),
       lblOf seedZ (pReadB seedZ alphaA),
       lblOf seedZ (pDecC seedZ alphaA),
       lblOf seedZ (pDecB seedZ alphaA),
       lblOf seedZ (pHaltC1 seedZ alphaA),
       lblOf seedZ (pVerifyC seedZ alphaA),
       lblOf seedZ (pHaltB1 seedZ alphaA),
       lblOf seedZ (pVerifyB seedZ alphaA),
       lblOf seedZ (pHalt5 seedZ alphaA),
       lblOf seedZ (pHalt3 seedZ alphaA)] := by
  simp [ExactExecution.memoryRows, exec, rootTree, tDecF, tHalt7, tVerifyF, tReadT, tDecT,
    tVerifyT, tReadC, tReadB, tDecC, tDecB, tHaltC1, tVerifyC, tHaltB1, tVerifyB, tHalt5,
    tHalt3, mLeaf, mOne, mTwo, bfsForest]

/-! ## Distinct timestamps `α,…,α⁴` in `K3` (`α = 4`) -/

theorem ts_recF : (recF seedZ alphaA).ts = alphaA := rfl
theorem ts_recT : (recT seedZ alphaA).ts = alphaA ^ 2 := rfl
theorem ts_recB : (recB seedZ alphaA).ts = alphaA ^ 4 := rfl
theorem ts_recC : (recC seedZ alphaA).ts = alphaA ^ 3 := rfl

theorem alpha_pow_ne_12 : alphaA ≠ alphaA ^ 2 := by decide
theorem alpha_pow_ne_13 : alphaA ≠ alphaA ^ 3 := by decide
theorem alpha_pow_ne_14 : alphaA ≠ alphaA ^ 4 := by decide
theorem alpha_pow_ne_23 : alphaA ^ 2 ≠ alphaA ^ 3 := by decide
theorem alpha_pow_ne_24 : alphaA ^ 2 ≠ alphaA ^ 4 := by decide
theorem alpha_pow_ne_34 : alphaA ^ 3 ≠ alphaA ^ 4 := by decide

/-! ## Raw canonical IO projections of the slice -/

theorem rawRequests_eq :
    (exec seedZ alphaA).rawRequests =
      [recF seedZ alphaA, recT seedZ alphaA, recC seedZ alphaA, recB seedZ alphaA] := by
  rw [ExactExecution.rawRequests_eq_computeRows, computeRows_eq]
  simp [NockVM.activeRequestRecords, parentRow, child1Row, child2Row,
    parentPub, child1Pub, child2Pub, op1PubOf]

theorem rawResponses_eq :
    (exec seedZ alphaA).rawResponses =
      [NockVM.formRRow (recF seedZ alphaA) MemoryTable.formRDefault,
      NockVM.formRRow (recT seedZ alphaA) MemoryTable.formRDefault,
      NockVM.formRRow (recC seedZ alphaA) MemoryTable.formRDefault,
      NockVM.formRRow (recB seedZ alphaA) MemoryTable.formRDefault] := by
  rw [ExactExecution.rawResponses_eq_memoryRows, memoryRows_eq]
  simp [MemoryTable.responseRecords, lblOf,
    pReadF, pDecF, pHalt7, pVerifyF, pReadT, pDecT, pVerifyT, pReadC, pReadB,
    pDecC, pDecB, pHaltC1, pVerifyC, pHaltB1, pVerifyB, pHalt5, pHalt3,
    readPub, decPub, haltPub, verifyPub]

theorem consumedRecordList_eq :
    RowLayout.consumedRecordList (exec seedZ alphaA) =
      [NockVM.formRRow (recF seedZ alphaA) MemoryTable.formRDefault,
      NockVM.formRRow (recT seedZ alphaA) MemoryTable.formRDefault,
      NockVM.formRRow (recC seedZ alphaA) MemoryTable.formRDefault,
      NockVM.formRRow (recB seedZ alphaA) MemoryTable.formRDefault] := by
  unfold RowLayout.consumedRecordList
  rw [memoryRows_eq]
  simp [RowLayout.consumedRecords, lblOf,
    pReadF, pDecF, pHalt7, pVerifyF, pReadT, pDecT, pVerifyT, pReadC, pReadB,
    pDecC, pDecB, pHaltC1, pVerifyC, pHaltB1, pVerifyB, pHalt5, pHalt3,
    readPub, decPub, haltPub, verifyPub]

theorem honestVer :
    ∀ row ∈ (exec seedZ alphaA).memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root) := by
  simp [memoryRows_eq, lblOf,
    pReadF, pDecF, pHalt7, pVerifyF, pReadT, pDecT, pVerifyT, pReadC, pReadB,
    pDecC, pDecB, pHaltC1, pVerifyC, pHaltB1, pVerifyB, pHalt5, pHalt3,
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
       NockVM.encRecFormR (recC seedZ alphaA) MemoryTable.formRDefault,
           NockVM.encRecFormR (recB seedZ alphaA) MemoryTable.formRDefault] := by
  rw [ExactExecution.derivedRequestIO, rawRequests_eq]; rfl

theorem derived_responses :
    (exec seedZ alphaA).derivedResponseIO =
      [NockVM.encRecFormR (recF seedZ alphaA) MemoryTable.formRDefault,
          NockVM.encRecFormR (recT seedZ alphaA) MemoryTable.formRDefault,
       NockVM.encRecFormR (recC seedZ alphaA) MemoryTable.formRDefault,
           NockVM.encRecFormR (recB seedZ alphaA) MemoryTable.formRDefault] := by
  rw [ExactExecution.derivedResponseIO_eq_memoryRows, memoryRows_eq]
  simp [lblOf, MemoryTable.Pub.cprime, parentDec, parentPub, parentRow, pReadF, pDecF, pHalt7,
    pVerifyF, pReadT, pDecT, pVerifyT, pReadC, pReadB, pDecC, pDecB, pHaltC1, pVerifyC, pHaltB1,
    pVerifyB, pHalt5, pHalt3, readPub, decPub, haltPub, verifyPub]

theorem requestNodup : (exec seedZ alphaA).derivedRequestIO.Nodup := by
  rw [derived_requests]
  have hFT : NockVM.encRecFormR (recF seedZ alphaA) MemoryTable.formRDefault ≠
      NockVM.encRecFormR (recT seedZ alphaA) MemoryTable.formRDefault :=
    encRec_ne_of_ts_ne (by rw [ts_recF, ts_recT]; exact alpha_pow_ne_12)
  have hFC : NockVM.encRecFormR (recF seedZ alphaA) MemoryTable.formRDefault ≠
      NockVM.encRecFormR (recC seedZ alphaA) MemoryTable.formRDefault :=
    encRec_ne_of_ts_ne (by rw [ts_recF, ts_recC]; exact alpha_pow_ne_13)
  have hFB : NockVM.encRecFormR (recF seedZ alphaA) MemoryTable.formRDefault ≠
      NockVM.encRecFormR (recB seedZ alphaA) MemoryTable.formRDefault :=
    encRec_ne_of_ts_ne (by rw [ts_recF, ts_recB]; exact alpha_pow_ne_14)
  have hTC : NockVM.encRecFormR (recT seedZ alphaA) MemoryTable.formRDefault ≠
      NockVM.encRecFormR (recC seedZ alphaA) MemoryTable.formRDefault :=
    encRec_ne_of_ts_ne (by rw [ts_recT, ts_recC]; exact alpha_pow_ne_23)
  have hTB : NockVM.encRecFormR (recT seedZ alphaA) MemoryTable.formRDefault ≠
      NockVM.encRecFormR (recB seedZ alphaA) MemoryTable.formRDefault :=
    encRec_ne_of_ts_ne (by rw [ts_recT, ts_recB]; exact alpha_pow_ne_24)
  have hCB : NockVM.encRecFormR (recC seedZ alphaA) MemoryTable.formRDefault ≠
      NockVM.encRecFormR (recB seedZ alphaA) MemoryTable.formRDefault :=
    encRec_ne_of_ts_ne (by rw [ts_recC, ts_recB]; exact alpha_pow_ne_34)
  simp [hFT, hFC, hFB, hTC, hTB, hCB]

theorem memoryStateCounts :
    RowLayout.memoryStateCount (exec seedZ alphaA) .read_root = 4 ∧
      RowLayout.memoryStateCount (exec seedZ alphaA) .verify_child = 4 := by
  constructor <;>
    simp [RowLayout.memoryStateCount, RowLayout.fibreCount, memoryRows_eq, lblOf,
      pReadF, pDecF, pHalt7, pVerifyF, pReadT, pDecT, pVerifyT, pReadC, pReadB,
      pDecC, pDecB, pHaltC1, pVerifyC, pHaltB1, pVerifyB, pHalt5, pHalt3,
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
  · exact GlobalCarryRecognizer.enc_cons seedZ_ne_zero op7Head op7ParentTail
  · ext <;>
      norm_num [parentPub, recF, parentDec, compInputs, fp, seedZ, alphaA]
  · simp [SVhead, headAtom, parentPub, parentDec, compInputs, fp, op7Head,
      GlobalCarryRecognizer.enc_atom, State.toNat, seedZ]
  · refine ⟨?_, ?_, ?_, ?_⟩
    · ext <;>
        norm_num [parentPub, recT, parentDec, compInputs, fp, seedZ, alphaA]
    · exact (GlobalCarryRecognizer.enc_cons seedZ_ne_zero op7ChildFormulaB
        op7ChildFormulaC).symm
    · rfl
    · simp [parentPub, compInputs]
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem child1_accepts : Vcomp (compInputs seedZ alphaA) (child1Pub seedZ alphaA)
    (op1DecOf seedZ op7Sb) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact GlobalCarryRecognizer.enc_cons seedZ_ne_zero (.atom 1) op7Sb
  · ext <;>
      norm_num [child1Pub, op1PubOf, recB, op1DecOf, compInputs, fp, seedZ, alphaA,
        pow_succ, pow_two]
  · simp [SVhead, headAtom, child1Pub, op1PubOf, op1DecOf, fp, op1Head,
      GlobalCarryRecognizer.enc_atom, State.toNat, compInputs, seedZ]
  · exact ⟨rfl, rfl, by simp [child1Pub, op1PubOf, compInputs, pow_succ]⟩
  · exact ⟨rfl, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

theorem child2_accepts : Vcomp (compInputs seedZ alphaA) (child2Pub seedZ alphaA)
    (op1DecOf seedZ op7Result) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact GlobalCarryRecognizer.enc_cons seedZ_ne_zero (.atom 1) op7Result
  · ext <;>
      norm_num [child2Pub, op1PubOf, recC, op1DecOf, compInputs, fp, seedZ, alphaA,
        pow_succ, pow_two]
  · simp [SVhead, headAtom, child2Pub, op1PubOf, op1DecOf, fp, op1Head,
      GlobalCarryRecognizer.enc_atom, State.toNat, compInputs, seedZ]
  · exact ⟨rfl, rfl, by simp [child2Pub, op1PubOf, compInputs, pow_succ]⟩
  · exact ⟨rfl, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

theorem computeRowsAccepted : (exec seedZ alphaA).ComputeRowsAccepted := by
  rw [ExactExecution.computeRowsAccepted_iff, computeRows_eq]
  intro row hrow
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
  rcases hrow with rfl | rfl | rfl
  · exact ⟨rfl, rfl, parent_accepts⟩
  · exact ⟨rfl, rfl, child2_accepts⟩
  · exact ⟨rfl, rfl, child1_accepts⟩

/-! ## BFS re-indexing of the canonical compute rows -/

theorem computeRowAt_zero :
    (exec seedZ alphaA).computeRowAt ⟨0, by norm_num [cfg]⟩ = parentRow seedZ alphaA := by
  norm_num [ExactExecution.computeRowAt, computeRows_eq, cfg]

theorem computeRowAt_one :
    (exec seedZ alphaA).computeRowAt ⟨1, by norm_num [cfg]⟩ = child2Row seedZ alphaA := by
  norm_num [ExactExecution.computeRowAt, computeRows_eq, cfg]

theorem computeRowAt_two :
    (exec seedZ alphaA).computeRowAt ⟨2, by norm_num [cfg]⟩ = child1Row seedZ alphaA := by
  norm_num [ExactExecution.computeRowAt, computeRows_eq, cfg]

end


theorem exec_encode : exec seedZ alphaA = (execA seedZ alphaA).encodeMem :=
  RowEncode.eq_encodeMem_of rfl (by
    simp [exec, execA, mOne, mTwo, mLeaf, mapNTree, lblOf, tHalt3, tVerifyB, tHaltB1, tDecB,
      tReadB, tVerifyT, tHalt5, tVerifyC, tHaltC1, tDecC, tReadC, tDecT, tReadT, tVerifyF, tHalt7,
      tDecF, rootTree, tVerifyBA, tDecBA, tReadBA, tVerifyTA, tVerifyCA, tDecCA, tReadCA, tDecTA,
      tReadTA, tVerifyFA, tDecFA, rootTreeA, parentDec, parentPub, parentRow, pReadF, pDecF,
      pHalt7, pVerifyF, pReadT, pDecT, pVerifyT, pReadC, pReadB, pDecC, pDecB, pHaltC1, pVerifyC,
      pHaltB1, pVerifyB, pHalt5, pHalt3, pReadFA, pVerifyFA, pReadTA, pVerifyTA, pReadCA, pReadBA,
      pVerifyCA, pVerifyBA, readPub, readPubA, verifyPub, verifyPubA, haltPub, decPub])

end Nock.NockVMROM.Thm54.TraceGen.Op7ConfigK3

#print axioms Nock.NockVMROM.Thm54.TraceGen.Op7ConfigK3.requestNodup
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op7ConfigK3.recordCountBalance
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op7ConfigK3.computeRowsAccepted
