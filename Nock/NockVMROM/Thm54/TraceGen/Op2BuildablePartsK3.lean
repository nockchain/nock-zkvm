/-
  Nock/NockVMROM/Thm54/TraceGen/Op2BuildablePartsK3.lean

  Stage 3 of the OP2 Layer-2 CORE, over `K3`: the twelve non-semantic
  `BuildableNockExecution` side-obligations for the fan-out-3 eval program

      `*[0 [2 [1 [0 1]] [1 [1 5]]]] = 5`

  Five unique requests `(F,T,B,C,S)` with timestamps `α,…,α⁵`, five `read_root` /
  five `verify_child` wrappers, orbit capacity `2⁵ = 32`.  The atom bound is
  `q = 97 = ringChar K3`
-/
import Nock.NockVMROM.Thm54.TraceGen.Op2LanguageK3
import Nock.NockVMROM.Thm54.MemoryMplus2L
import Nock.NockVMROM.Thm54.TraceGen.RowEncode

namespace Nock.NockVMROM.Thm54.TraceGen.Op2ConfigK3

open Nock Nock.Walk Nock.NockVM
open Nock.NockVMROM.Thm54

/-! ## The characteristic of the table field -/

/-- `ringChar K3 = 97` (from the `CharP K3 97` instance). -/
theorem ringChar_K3 : ringChar K = 97 :=
  CharP.eq K (ringChar.charP K) (inferInstanceAs (CharP K 97))

/-! ## Distinct timestamps `α,…,α⁵` in `K3` (`α = 4`) -/

theorem ts_recF : (recF seedZ alphaA).ts = alphaA := rfl
theorem ts_recT : (recT seedZ alphaA).ts = alphaA ^ 2 := rfl
theorem ts_recB : (recB seedZ alphaA).ts = alphaA ^ 3 := rfl
theorem ts_recC : (recC seedZ alphaA).ts = alphaA ^ 4 := rfl
theorem ts_recS : (recS seedZ alphaA).ts = alphaA ^ 5 := rfl

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
      [recF seedZ alphaA, recT seedZ alphaA, recB seedZ alphaA,
        recC seedZ alphaA, recS seedZ alphaA] := by
  rw [ExactExecution.rawRequests_eq_computeRows, computeRows_eq]
  simp [NockVM.activeRequestRecords, parentRow, child1Row, child2Row, child3Row,
    parentPub, child1Pub, child2Pub, child3Pub, op1PubOf]

theorem rawResponses_eq :
    (exec seedZ alphaA).rawResponses =
      [NockVM.formRRow (recF seedZ alphaA) MemoryTable.formRDefault,
      NockVM.formRRow (recT seedZ alphaA) MemoryTable.formRDefault,
      NockVM.formRRow (recC seedZ alphaA) MemoryTable.formRDefault,
        NockVM.formRRow (recB seedZ alphaA) MemoryTable.formRDefault,
        NockVM.formRRow (recS seedZ alphaA) MemoryTable.formRDefault] := by
  rw [ExactExecution.rawResponses_eq_memoryRows, memoryRows_eq]
  simp [MemoryTable.responseRecords, lblOf,
    pReadF, pDecF, pHalt2, pVerifyF, pReadT, pDecT, pVerifyT, pReadC, pReadB,
    pDecC, pDecB, pHaltC1, pVerifyC, pHaltB1, pVerifyB, pReadS, pDecSf1, pDecS,
    pHalt0, pHalt1s, pHaltS1, pVerifyS, pHalt5,
    readPub, decPub, haltPub, verifyPub]

theorem consumedRecordList_eq :
    RowLayout.consumedRecordList (exec seedZ alphaA) =
      [NockVM.formRRow (recF seedZ alphaA) MemoryTable.formRDefault,
      NockVM.formRRow (recT seedZ alphaA) MemoryTable.formRDefault,
      NockVM.formRRow (recC seedZ alphaA) MemoryTable.formRDefault,
        NockVM.formRRow (recB seedZ alphaA) MemoryTable.formRDefault,
        NockVM.formRRow (recS seedZ alphaA) MemoryTable.formRDefault] := by
  unfold RowLayout.consumedRecordList
  rw [memoryRows_eq]
  simp [RowLayout.consumedRecords, lblOf,
    pReadF, pDecF, pHalt2, pVerifyF, pReadT, pDecT, pVerifyT, pReadC, pReadB,
    pDecC, pDecB, pHaltC1, pVerifyC, pHaltB1, pVerifyB, pReadS, pDecSf1, pDecS,
    pHalt0, pHalt1s, pHaltS1, pVerifyS, pHalt5,
    readPub, decPub, haltPub, verifyPub]

theorem honestVer :
    ∀ row ∈ (exec seedZ alphaA).memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root) := by
  simp [memoryRows_eq, lblOf,
    pReadF, pDecF, pHalt2, pVerifyF, pReadT, pDecT, pVerifyT, pReadC, pReadB,
    pDecC, pDecB, pHaltC1, pVerifyC, pHaltB1, pVerifyB, pReadS, pDecSf1, pDecS,
    pHalt0, pHalt1s, pHaltS1, pVerifyS, pHalt5,
    readPub, decPub, haltPub, verifyPub]

theorem pairedRecordLayout :
    RowLayout.PairedRecordLayout (exec seedZ alphaA) := by
  rw [RowLayout.PairedRecordLayout,
    ← RowLayout.rawResponses_eq_addedRecordList _ honestVer,
    rawResponses_eq, consumedRecordList_eq]

/-- Records with distinct timestamps have distinct Form R encodings (slot `7` is `ts`). -/
theorem encRec_ne_of_ts_ne {r s : ComputeTable.MemRec K} (h : r.ts ≠ s.ts) :
    NockVM.encRecFormR r MemoryTable.formRDefault ≠
      NockVM.encRecFormR s MemoryTable.formRDefault := by
  intro he
  exact h (by have hc := congrFun he (7 : Fin 9); change r.ts = s.ts at hc; exact hc)

/-! ## The twelve non-semantic `BuildableNockExecution` fields -/

theorem requestNodup : (exec seedZ alphaA).derivedRequestIO.Nodup := by
  rw [derived_requests]
  have hFT : NockVM.encRecFormR (recF seedZ alphaA) MemoryTable.formRDefault ≠
      NockVM.encRecFormR (recT seedZ alphaA) MemoryTable.formRDefault :=
    encRec_ne_of_ts_ne (by rw [ts_recF, ts_recT]; exact alpha_pow_ne_12)
  have hFB : NockVM.encRecFormR (recF seedZ alphaA) MemoryTable.formRDefault ≠
      NockVM.encRecFormR (recB seedZ alphaA) MemoryTable.formRDefault :=
    encRec_ne_of_ts_ne (by rw [ts_recF, ts_recB]; exact alpha_pow_ne_13)
  have hFC : NockVM.encRecFormR (recF seedZ alphaA) MemoryTable.formRDefault ≠
      NockVM.encRecFormR (recC seedZ alphaA) MemoryTable.formRDefault :=
    encRec_ne_of_ts_ne (by rw [ts_recF, ts_recC]; exact alpha_pow_ne_14)
  have hFS : NockVM.encRecFormR (recF seedZ alphaA) MemoryTable.formRDefault ≠
      NockVM.encRecFormR (recS seedZ alphaA) MemoryTable.formRDefault :=
    encRec_ne_of_ts_ne (by rw [ts_recF, ts_recS]; exact alpha_pow_ne_15)
  have hTB : NockVM.encRecFormR (recT seedZ alphaA) MemoryTable.formRDefault ≠
      NockVM.encRecFormR (recB seedZ alphaA) MemoryTable.formRDefault :=
    encRec_ne_of_ts_ne (by rw [ts_recT, ts_recB]; exact alpha_pow_ne_23)
  have hTC : NockVM.encRecFormR (recT seedZ alphaA) MemoryTable.formRDefault ≠
      NockVM.encRecFormR (recC seedZ alphaA) MemoryTable.formRDefault :=
    encRec_ne_of_ts_ne (by rw [ts_recT, ts_recC]; exact alpha_pow_ne_24)
  have hTS : NockVM.encRecFormR (recT seedZ alphaA) MemoryTable.formRDefault ≠
      NockVM.encRecFormR (recS seedZ alphaA) MemoryTable.formRDefault :=
    encRec_ne_of_ts_ne (by rw [ts_recT, ts_recS]; exact alpha_pow_ne_25)
  have hBC : NockVM.encRecFormR (recB seedZ alphaA) MemoryTable.formRDefault ≠
      NockVM.encRecFormR (recC seedZ alphaA) MemoryTable.formRDefault :=
    encRec_ne_of_ts_ne (by rw [ts_recB, ts_recC]; exact alpha_pow_ne_34)
  have hBS : NockVM.encRecFormR (recB seedZ alphaA) MemoryTable.formRDefault ≠
      NockVM.encRecFormR (recS seedZ alphaA) MemoryTable.formRDefault :=
    encRec_ne_of_ts_ne (by rw [ts_recB, ts_recS]; exact alpha_pow_ne_35)
  have hCS : NockVM.encRecFormR (recC seedZ alphaA) MemoryTable.formRDefault ≠
      NockVM.encRecFormR (recS seedZ alphaA) MemoryTable.formRDefault :=
    encRec_ne_of_ts_ne (by rw [ts_recC, ts_recS]; exact alpha_pow_ne_45)
  simp [hFT, hFB, hFC, hFS, hTB, hTC, hTS, hBC, hBS, hCS]

theorem memoryStateCounts :
    RowLayout.memoryStateCount (exec seedZ alphaA) .read_root = 5 ∧
      RowLayout.memoryStateCount (exec seedZ alphaA) .verify_child = 5 := by
  constructor <;>
    simp [RowLayout.memoryStateCount, RowLayout.fibreCount, memoryRows_eq, lblOf,
      pReadF, pDecF, pHalt2, pVerifyF, pReadT, pDecT, pVerifyT, pReadC, pReadB,
      pDecC, pDecB, pHaltC1, pVerifyC, pHaltB1, pVerifyB, pReadS, pDecSf1, pDecS,
      pHalt0, pHalt1s, pHaltS1, pVerifyS, pHalt5,
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


theorem exec_encode : exec seedZ alphaA = (execA seedZ alphaA).encodeMem :=
  RowEncode.eq_encodeMem_of rfl (by
    simp [exec, execA, mOne, mTwo, mLeaf, mapNTree, lblOf, tHalt5, tVerifyS, tHaltS1, tDecS,
      tReadS, tHalt0, tHalt1s, tDecSf1, tVerifyB, tHaltB1, tDecB, tReadB, tVerifyC, tHaltC1,
      tDecC, tReadC, tVerifyT, tDecT, tReadT, tVerifyF, tHalt2, tDecF, rootTree, tVerifySA,
      tDecSA, tReadSA, tVerifyBA, tDecBA, tReadBA, tVerifyCA, tDecCA, tReadCA, tVerifyTA, tDecTA,
      tReadTA, tVerifyFA, tDecFA, rootTreeA, parentDec, parentPub, parentRow, pReadF, pDecF,
      pHalt2, pVerifyF, pReadT, pDecT, pVerifyT, pReadC, pReadB, pDecC, pDecB, pHaltC1, pVerifyC,
      pHaltB1, pVerifyB, pReadS, pDecSf1, pDecS, pHalt0, pHalt1s, pHaltS1, pVerifyS, pHalt5,
      pReadFA, pVerifyFA, pReadTA, pVerifyTA, pReadCA, pReadBA, pVerifyCA, pVerifyBA, pReadSA,
      pVerifySA, readPub, readPubA, verifyPub, verifyPubA, haltPub, decPub])

end Nock.NockVMROM.Thm54.TraceGen.Op2ConfigK3

#print axioms Nock.NockVMROM.Thm54.TraceGen.Op2ConfigK3.requestNodup
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op2ConfigK3.recordCountBalance
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op2ConfigK3.ringChar_K3
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op2ConfigK3.rawRequests_eq
