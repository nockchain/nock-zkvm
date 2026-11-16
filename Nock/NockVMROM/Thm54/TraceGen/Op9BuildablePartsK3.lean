/-
  Nock/NockVMROM/Thm54/TraceGen/Op9BuildablePartsK3.lean

  Stage 4a of the OP9 Layer-2 CORE, over `K3`: the twelve non-semantic
  `BuildableNockExecution` side-obligations for the fan-out-2 invoke program

      `*[0 [9 [2 [1 [[1 7] [1 9]]]]]] = 7`

  Five unique requests `(F,T,Arm,CoreF,ArmF)` with timestamps `α,…,α⁵`, five
  `read_root` / five `verify_child` wrappers, orbit capacity `2⁵ = 32`.
  The atom bound is `q = 97 = ringChar K3`
-/
import Nock.NockVMROM.Thm54.TraceGen.Op9MemoryTraceK3
import Nock.NockVMROM.Thm54.MemoryMplus2L
import Nock.NockVMROM.Thm54.TraceGen.RowEncode

namespace Nock.NockVMROM.Thm54.TraceGen.Op9ConfigK3

open Nock Nock.Walk Nock.NockVM
open Nock.ComputeTable Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen

/-! ## The characteristic of the table field -/

theorem ringChar_K3 : ringChar K = 97 :=
  CharP.eq K (ringChar.charP K) (inferInstanceAs (CharP K 97))

/-! ## BFS-flat memory rows -/

theorem memoryRows_eq :
    (exec seedZ alphaA).memoryRows =
      [lblOf seedZ (pReadF seedZ alphaA),
       lblOf seedZ (pReadArm seedZ alphaA),
       lblOf seedZ (pDecPF seedZ alphaA),
       lblOf seedZ (pDecCN_B seedZ alphaA),
       lblOf seedZ (pHalt9 seedZ alphaA),
       lblOf seedZ (pVerifyF seedZ alphaA),
       lblOf seedZ (pVerifyArm seedZ alphaA),
       lblOf seedZ (pDecCT_B seedZ alphaA),
       lblOf seedZ (pReadT seedZ alphaA),
       lblOf seedZ (pReadArmF seedZ alphaA),
       lblOf seedZ (pHaltH1_B2 seedZ alphaA),
       lblOf seedZ (pHaltA9_B seedZ alphaA),
       lblOf seedZ (pDecPT seedZ alphaA),
       lblOf seedZ (pDecArmB seedZ alphaA),
       lblOf seedZ (pVerifyT seedZ alphaA),
       lblOf seedZ (pReadCoreF seedZ alphaA),
       lblOf seedZ (pHaltH1_B1 seedZ alphaA),
       lblOf seedZ (pVerifyArmF seedZ alphaA),
       lblOf seedZ (pHaltA2 seedZ alphaA),
       lblOf seedZ (pDecCF seedZ alphaA),
       lblOf seedZ (pHaltA7_B seedZ alphaA),
       lblOf seedZ (pHaltH1a seedZ alphaA),
       lblOf seedZ (pVerifyCoreF seedZ alphaA),
       lblOf seedZ (pDecCN seedZ alphaA),
       lblOf seedZ (pDecArmA seedZ alphaA),
       lblOf seedZ (pDecCTA seedZ alphaA),
       lblOf seedZ (pHaltH1b seedZ alphaA),
       lblOf seedZ (pHaltA7 seedZ alphaA),
       lblOf seedZ (pHaltH1c seedZ alphaA),
       lblOf seedZ (pHaltA9 seedZ alphaA)] := by
  simp [ExactExecution.memoryRows, exec, rootTreeA, rootTreeB, mOne, mTwo, mLeaf, bfsForest]

/-! ## Raw canonical IO projections of the slice -/

theorem rawResponses_eq :
    (exec seedZ alphaA).rawResponses =
      [NockVM.formRRow (recF seedZ alphaA) MemoryTable.formRDefault,
      NockVM.formRRow (recArm seedZ alphaA) MemoryTable.formRDefault,
      NockVM.formRRow (recT seedZ alphaA) MemoryTable.formRDefault,
        NockVM.formRRow (recArmF seedZ alphaA) MemoryTable.formRDefault,
        NockVM.formRRow (recCoreF seedZ alphaA) MemoryTable.formRDefault] := by
  rw [ExactExecution.rawResponses_eq_memoryRows, memoryRows_eq]
  simp [MemoryTable.responseRecords, lblOf,
    pReadF, pDecPF, pHalt9, pVerifyF, pReadT, pDecPT, pVerifyT, pHaltA2,
    pReadCoreF, pDecCF, pHaltH1a, pVerifyCoreF, pDecCN, pDecArmA, pHaltH1b, pHaltA7,
    pDecCTA, pHaltH1c, pHaltA9,
    pReadArm, pDecCN_B, pVerifyArm, pReadArmF, pDecArmB, pHaltH1_B1, pVerifyArmF,
    pHaltA7_B, pDecCT_B, pHaltH1_B2, pHaltA9_B,
    readPub, decPub, haltPub, verifyPub]

theorem consumedRecordList_eq :
    RowLayout.consumedRecordList (exec seedZ alphaA) =
      [NockVM.formRRow (recF seedZ alphaA) MemoryTable.formRDefault,
      NockVM.formRRow (recArm seedZ alphaA) MemoryTable.formRDefault,
      NockVM.formRRow (recT seedZ alphaA) MemoryTable.formRDefault,
        NockVM.formRRow (recArmF seedZ alphaA) MemoryTable.formRDefault,
        NockVM.formRRow (recCoreF seedZ alphaA) MemoryTable.formRDefault] := by
  unfold RowLayout.consumedRecordList
  rw [memoryRows_eq]
  simp [RowLayout.consumedRecords, lblOf,
    pReadF, pDecPF, pHalt9, pVerifyF, pReadT, pDecPT, pVerifyT, pHaltA2,
    pReadCoreF, pDecCF, pHaltH1a, pVerifyCoreF, pDecCN, pDecArmA, pHaltH1b, pHaltA7,
    pDecCTA, pHaltH1c, pHaltA9,
    pReadArm, pDecCN_B, pVerifyArm, pReadArmF, pDecArmB, pHaltH1_B1, pVerifyArmF,
    pHaltA7_B, pDecCT_B, pHaltH1_B2, pHaltA9_B,
    readPub, decPub, haltPub, verifyPub]

theorem honestVer :
    ∀ row ∈ (exec seedZ alphaA).memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root) := by
  simp [memoryRows_eq, lblOf,
    pReadF, pDecPF, pHalt9, pVerifyF, pReadT, pDecPT, pVerifyT, pHaltA2,
    pReadCoreF, pDecCF, pHaltH1a, pVerifyCoreF, pDecCN, pDecArmA, pHaltH1b, pHaltA7,
    pDecCTA, pHaltH1c, pHaltA9,
    pReadArm, pDecCN_B, pVerifyArm, pReadArmF, pDecArmB, pHaltH1_B1, pVerifyArmF,
    pHaltA7_B, pDecCT_B, pHaltH1_B2, pHaltA9_B,
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

/-! ## Derived IO (encoded record lists) -/

theorem derived_requests :
    (exec seedZ alphaA).derivedRequestIO =
      [NockVM.encRecFormR (recF seedZ alphaA) MemoryTable.formRDefault,
          NockVM.encRecFormR (recT seedZ alphaA) MemoryTable.formRDefault,
        NockVM.encRecFormR (recArm seedZ alphaA) MemoryTable.formRDefault,
            NockVM.encRecFormR (recCoreF seedZ alphaA) MemoryTable.formRDefault,
        NockVM.encRecFormR (recArmF seedZ alphaA) MemoryTable.formRDefault] := by
  rw [ExactExecution.derivedRequestIO_eq_computeRows, computeRows_eq]
  simp [NockVM.activeRequestRecords, parentRow, child1Row, child2Row,
    parentPub, child1Pub, child2Pub, op1PubOf]

theorem derived_responses :
    (exec seedZ alphaA).derivedResponseIO =
      [NockVM.encRecFormR (recF seedZ alphaA) MemoryTable.formRDefault,
          NockVM.encRecFormR (recArm seedZ alphaA) MemoryTable.formRDefault,
        NockVM.encRecFormR (recT seedZ alphaA) MemoryTable.formRDefault,
            NockVM.encRecFormR (recArmF seedZ alphaA) MemoryTable.formRDefault,
        NockVM.encRecFormR (recCoreF seedZ alphaA) MemoryTable.formRDefault] := by
  rw [ExactExecution.derivedResponseIO_eq_memoryRows, memoryRows_eq]
  simp [lblOf, MemoryTable.Pub.cprime, parentDec, parentPub, parentRow, pReadF, pDecPF, pHalt9,
    pVerifyF, pReadT, pDecPT, pVerifyT, pHaltA2, pReadCoreF, pDecCF, pHaltH1a, pVerifyCoreF,
    pDecCN, pHaltH1b, pHaltA7, pHaltH1c, pHaltA9, pReadArm, pDecCN_B, pVerifyArm, pReadArmF,
    pDecArmB, pHaltH1_B1, pVerifyArmF, pHaltA7_B, pDecCT_B, pHaltH1_B2, pHaltA9_B, readPub,
    decPub, haltPub, verifyPub]

/-! ## The twelve non-semantic `BuildableNockExecution` fields -/

theorem requestNodup : (exec seedZ alphaA).derivedRequestIO.Nodup := by
  rw [derived_requests]
  have hFT : NockVM.encRecFormR (recF seedZ alphaA) MemoryTable.formRDefault ≠
      NockVM.encRecFormR (recT seedZ alphaA) MemoryTable.formRDefault :=
    encRec_ne_of_ts_ne (by rw [ts_recF, ts_recT]; exact alpha_pow_ne_12)
  have hFArm : NockVM.encRecFormR (recF seedZ alphaA) MemoryTable.formRDefault ≠
      NockVM.encRecFormR (recArm seedZ alphaA) MemoryTable.formRDefault :=
    encRec_ne_of_ts_ne (by rw [ts_recF, ts_recArm]; exact alpha_pow_ne_13)
  have hFCoreF : NockVM.encRecFormR (recF seedZ alphaA) MemoryTable.formRDefault ≠
      NockVM.encRecFormR (recCoreF seedZ alphaA) MemoryTable.formRDefault :=
    encRec_ne_of_ts_ne (by rw [ts_recF, ts_recCoreF]; exact alpha_pow_ne_14)
  have hFArmF : NockVM.encRecFormR (recF seedZ alphaA) MemoryTable.formRDefault ≠
      NockVM.encRecFormR (recArmF seedZ alphaA) MemoryTable.formRDefault :=
    encRec_ne_of_ts_ne (by rw [ts_recF, ts_recArmF]; exact alpha_pow_ne_15)
  have hTArm : NockVM.encRecFormR (recT seedZ alphaA) MemoryTable.formRDefault ≠
      NockVM.encRecFormR (recArm seedZ alphaA) MemoryTable.formRDefault :=
    encRec_ne_of_ts_ne (by rw [ts_recT, ts_recArm]; exact alpha_pow_ne_23)
  have hTCoreF : NockVM.encRecFormR (recT seedZ alphaA) MemoryTable.formRDefault ≠
      NockVM.encRecFormR (recCoreF seedZ alphaA) MemoryTable.formRDefault :=
    encRec_ne_of_ts_ne (by rw [ts_recT, ts_recCoreF]; exact alpha_pow_ne_24)
  have hTArmF : NockVM.encRecFormR (recT seedZ alphaA) MemoryTable.formRDefault ≠
      NockVM.encRecFormR (recArmF seedZ alphaA) MemoryTable.formRDefault :=
    encRec_ne_of_ts_ne (by rw [ts_recT, ts_recArmF]; exact alpha_pow_ne_25)
  have hArmCoreF : NockVM.encRecFormR (recArm seedZ alphaA) MemoryTable.formRDefault ≠
      NockVM.encRecFormR (recCoreF seedZ alphaA) MemoryTable.formRDefault :=
    encRec_ne_of_ts_ne (by rw [ts_recArm, ts_recCoreF]; exact alpha_pow_ne_34)
  have hArmArmF : NockVM.encRecFormR (recArm seedZ alphaA) MemoryTable.formRDefault ≠
      NockVM.encRecFormR (recArmF seedZ alphaA) MemoryTable.formRDefault :=
    encRec_ne_of_ts_ne (by rw [ts_recArm, ts_recArmF]; exact alpha_pow_ne_35)
  have hCoreFArmF : NockVM.encRecFormR (recCoreF seedZ alphaA) MemoryTable.formRDefault ≠
      NockVM.encRecFormR (recArmF seedZ alphaA) MemoryTable.formRDefault :=
    encRec_ne_of_ts_ne (by rw [ts_recCoreF, ts_recArmF]; exact alpha_pow_ne_45)
  simp [hFT, hFArm, hFCoreF, hFArmF, hTArm, hTCoreF, hTArmF, hArmCoreF, hArmArmF, hCoreFArmF]

theorem memoryStateCounts :
    RowLayout.memoryStateCount (exec seedZ alphaA) .read_root = 5 ∧
      RowLayout.memoryStateCount (exec seedZ alphaA) .verify_child = 5 := by
  constructor <;>
    simp [RowLayout.memoryStateCount, RowLayout.fibreCount, memoryRows_eq, lblOf,
      pReadF, pDecPF, pHalt9, pVerifyF, pReadT, pDecPT, pVerifyT, pHaltA2,
      pReadCoreF, pDecCF, pHaltH1a, pVerifyCoreF, pDecCN, pDecArmA, pHaltH1b, pHaltA7,
      pDecCTA, pHaltH1c, pHaltA9,
      pReadArm, pDecCN_B, pVerifyArm, pReadArmF, pDecArmB, pHaltH1_B1, pVerifyArmF,
      pHaltA7_B, pDecCT_B, pHaltH1_B2, pHaltA9_B,
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
  · exact GlobalCarryRecognizer.enc_cons seedZ_ne_zero op9Head op9ParentTail
  · ext <;>
      norm_num [parentPub, recF, parentDec, compInputs, fp, seedZ, alphaA]
  · simp [SVhead, headAtom, parentPub, parentDec, compInputs, fp, op9Head,
      GlobalCarryRecognizer.enc_atom, State.toNat, seedZ]
  · refine ⟨?_, ?_, ?_, ?_⟩
    · ext <;>
        norm_num [parentPub, recT, parentDec, compInputs, fp, seedZ, alphaA]
    · exact (GlobalCarryRecognizer.enc_cons seedZ_ne_zero op9AxisAtom op9CoreFormula).symm
    · have hleaf : Polynomial.eval (8 : K) (NPR.listPoly (NPR.leafF (K := K) (.atom 2))) = (2 : K) := by
        change Polynomial.eval seedZ _ = _
        rw [← GlobalCarryRecognizer.enc_leaf, GlobalCarryRecognizer.enc_atom]; rfl
      ext <;>
        simp [parentPub, recArm, parentDec, compInputs, fp, seedZ, alphaA, op9AxisAtom, hleaf]
    · simp [parentPub, compInputs]
  · have h := GlobalCarryRecognizer.enc_atom (K := K) seedZ 2
    refine ⟨rfl, rfl, rfl, rfl, ⟨rfl, rfl, rfl⟩, ?_, ?_⟩
    · change (fp seedZ op9AxisAtom).size = (compInputs seedZ alphaA).z
      simp only [fp, op9AxisAtom, h, FP.atomFP_size, compInputs]
    · change (fp seedZ op9AxisAtom).dyck = 0
      rw [fp, op9AxisAtom, GlobalCarryRecognizer.enc_dyck]
      simp [NPR.dyckBits, Noun.dyckWord, Noun.shape, Nock.BTree.encode, NPR.listPoly_nil]

theorem child1_accepts : Vcomp (compInputs seedZ alphaA) (child1Pub seedZ alphaA)
    (op1DecOf seedZ op9CoreNoun) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact GlobalCarryRecognizer.enc_cons seedZ_ne_zero (.atom 1) op9CoreNoun
  · ext <;>
      norm_num [child1Pub, op1PubOf, recCoreF, op1DecOf, compInputs, fp, seedZ, alphaA,
        pow_succ, pow_two]
  · simp [SVhead, headAtom, child1Pub, op1PubOf, op1DecOf, fp, op1Head,
      GlobalCarryRecognizer.enc_atom, State.toNat, compInputs, seedZ]
  · exact ⟨rfl, rfl, by simp [child1Pub, op1PubOf, compInputs, pow_succ]⟩
  · exact ⟨rfl, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

theorem child2_accepts : Vcomp (compInputs seedZ alphaA) (child2Pub seedZ alphaA)
    (op1DecOf seedZ op9Result) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact GlobalCarryRecognizer.enc_cons seedZ_ne_zero (.atom 1) op9Result
  · ext <;>
      norm_num [child2Pub, op1PubOf, recArmF, op1DecOf, compInputs, fp, seedZ, alphaA,
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
  · exact ⟨rfl, rfl, child1_accepts⟩
  · exact ⟨rfl, rfl, child2_accepts⟩

end


theorem exec_encode : exec seedZ alphaA = (execA seedZ alphaA).encodeMem :=
  RowEncode.eq_encodeMem_of rfl (by
    simp [exec, execA, mOne, mTwo, mLeaf, mapNTree, lblOf, rootTreeA, rootTreeAView, rootTreeB,
      rootTreeBView, parentDec, parentPub, parentRow, pReadF, pDecPF, pHalt9, pVerifyF, pReadT,
      pDecPT, pVerifyT, pHaltA2, pReadCoreF, pDecCF, pHaltH1a, pVerifyCoreF, pDecCN, pDecArmA,
      pHaltH1b, pHaltA7, pDecCTA, pHaltH1c, pHaltA9, pReadArm, pDecCN_B, pVerifyArm, pReadArmF,
      pDecArmB, pHaltH1_B1, pVerifyArmF, pHaltA7_B, pDecCT_B, pHaltH1_B2, pHaltA9_B, pReadFA,
      pVerifyFA, pReadTA, pVerifyTA, pReadCoreFA, pVerifyCoreFA, pReadArmA, pVerifyArmA,
      pReadArmFA, pVerifyArmFA, readPub, readPubA, verifyPub, verifyPubA, haltPub, decPub])

end Nock.NockVMROM.Thm54.TraceGen.Op9ConfigK3

#print axioms Nock.NockVMROM.Thm54.TraceGen.Op9ConfigK3.requestNodup
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op9ConfigK3.recordCountBalance
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op9ConfigK3.computeRowsAccepted
