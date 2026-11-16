/-
  Nock/NockVMROM/Thm54/TraceGen/Op5DataK3.lean

  Stage 3 of the OP5 Layer-2 CORE, over `K3`: the assembled
  `Op5Execution : BuildableNockExecution (ZMod 97) K3` — all fourteen fields —
  and the directly-built literal-node commitment `HonestCommitment.Data Op5Execution`
  for the fan-out-2 equality-test program

      `*[0 [5 [1 3] [1 4]]] = 1`
-/
import Nock.NockVMROM.Thm54.TraceGen.Op5LanguageK3
import Nock.NockVMROM.Thm54.TraceGen.Op5SkeletonK3
import Nock.NockVMROM.Thm54.HonestCommitment

namespace Nock.NockVMROM.Thm54.TraceGen.Op5ConfigK3

open Nock Nock.Walk Nock.ComputeTable Nock.MemoryTable
open Nock.NockVMROM.Thm54
open SemanticStrategy
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.TraceGen.Op5Skeleton
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
  (ComputeTimestampSpecializesAt MemoryTimestampSpecializesAt)

set_option linter.unusedSimpArgs false

/-! ## The assembled buildable execution -/

noncomputable def Op5Execution
    (hfirst :
      ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.counts = 0 ∧
        ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.indicator = 0) :
    BuildableNockExecution F K where
  q := 97
  q_gt_one := by norm_num
  Λ := 5
  cfg := cfg seedZ alphaA
  execA := execA seedZ alphaA
  exec := exec seedZ alphaA
  exec_encode := exec_encode
  semanticData := semanticData hfirst
  memoryTrace := memoryTrace hfirst
  requestNodup := requestNodup
  recordCountBalance := recordCountBalance
  q_le_ringChar := q_le_ringChar
  two_ne_zero := two_ne_zero
  Ksz_lt_ringChar := Ksz_lt_ringChar
  programIOCapacity := programIOCapacity
  memoryIOCapacity := memoryIOCapacity

/-! ## Row-skeleton bindings of the concrete rows -/

theorem bind_parentRow :
    BindComputeRow seedZ Op5Skeleton.parentRow (parentRow seedZ alphaA) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro slot
    cases slot <;>
      simp [decActive, hasTailDecomposition, decFP, bindFP, fp,
        Op5Skeleton.parentRow, parentRow, parentDec, op5Head, Op5Skeleton.op5Head]
  · intro i
    fin_cases i
    · rw [dif_pos (by decide)]
      intro slot
      cases slot <;>
        simp [Op5Skeleton.parentRow, computeSubformulaFPs, ComputeTable.sfTriple,
          parentRow, parentPub, tripleFP, bindFP, fp]
    · rw [dif_pos (by decide)]
      intro slot
      cases slot <;>
        simp [Op5Skeleton.parentRow, computeSubformulaFPs, ComputeTable.sfTriple,
          parentRow, parentPub, tripleFP, bindFP, fp]
    · rw [dif_neg (by decide)]
      simp [computeSubformulaFPs, parentRow, parentPub, ComputeTable.sfTriple]
  · intro i
    fin_cases i
    · rw [dif_pos (by decide)]
      exact ⟨rfl, rfl, rfl⟩
    · rw [dif_pos (by decide)]
      exact ⟨rfl, rfl, rfl⟩
    · rw [dif_neg (by decide)]
      simp [computeMemRec, computeMemRecKind, Nock.Framework.recordCount,
        parentRow, parentPub, MemRec.zero]

theorem bind_child1Row :
    BindComputeRow seedZ Op5Skeleton.child1Row (child1Row seedZ alphaA) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro slot
    cases slot <;>
      simp [decActive, hasTailDecomposition, decFP, bindFP, fp,
        Op5Skeleton.child1Row, Op5Skeleton.op1Row, child1Row, op1DecOf,
        op1Head, Op5Skeleton.op1Head]
  · intro i
    have hi : ¬ ((i : ℕ) < ComputeTable.fanoutComp Op5Skeleton.child1Row.state) := by
      simp [Op5Skeleton.child1Row, Op5Skeleton.op1Row, ComputeTable.fanoutComp]
    rw [dif_neg hi]
    fin_cases i <;>
      simp [computeSubformulaFPs, ComputeTable.sfTriple, child1Row, child1Pub, op1PubOf]
  · intro i
    fin_cases i
    · exact ⟨rfl, rfl, rfl⟩
    · rfl
    · rfl

theorem bind_child2Row :
    BindComputeRow seedZ Op5Skeleton.child2Row (child2Row seedZ alphaA) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro slot
    cases slot <;>
      simp [decActive, hasTailDecomposition, decFP, bindFP, fp,
        Op5Skeleton.child2Row, Op5Skeleton.op1Row, child2Row, op1DecOf,
        op1Head, Op5Skeleton.op1Head]
  · intro i
    have hi : ¬ ((i : ℕ) < ComputeTable.fanoutComp Op5Skeleton.child2Row.state) := by
      simp [Op5Skeleton.child2Row, Op5Skeleton.op1Row, ComputeTable.fanoutComp]
    rw [dif_neg hi]
    fin_cases i <;>
      simp [computeSubformulaFPs, ComputeTable.sfTriple, child2Row, child2Pub, op1PubOf]
  · intro i
    fin_cases i
    · exact ⟨rfl, rfl, rfl⟩
    · rfl
    · rfl

/-! ### Memory-row bindings -/

theorem bind_readF :
    BindMemoryRowA seedZ Op5Skeleton.skReadF (lblOf seedZ (pReadFA seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i
    · rfl
    · simp [Op5Skeleton.skReadF, Op5Skeleton.readRow, MemoryTable.fanoutMem,
        memoryChildCell, lblOf, pReadFA, readPub]
  · exact ⟨rfl, rfl, rfl⟩

theorem bind_decF :
    BindMemoryRowA seedZ Op5Skeleton.skDecF (lblOf seedZ (pDecF seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i <;> rfl
  · rfl

theorem bind_halt5 :
    BindMemoryRowA seedZ Op5Skeleton.skHalt5 (lblOf seedZ (pHalt5 seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, rfl⟩
  · simp [Op5Skeleton.skHalt5, Op5Skeleton.haltRow, lblOf, pHalt5, haltPub, bindFP, fp]
  · intro i
    have hi : ¬ ((i : ℕ) < MemoryTable.fanoutMem Op5Skeleton.skHalt5.state) := by
      simp [Op5Skeleton.skHalt5, Op5Skeleton.haltRow, MemoryTable.fanoutMem]
    rw [dif_neg hi]
    fin_cases i <;> rfl
  · rfl

theorem bind_verifyF :
    BindMemoryRowA seedZ Op5Skeleton.skVerifyF (lblOf seedZ (pVerifyFA seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i
    · rfl
    · simp [Op5Skeleton.skVerifyF, Op5Skeleton.verifyRow, MemoryTable.fanoutMem,
        memoryChildCell, lblOf, pVerifyFA, verifyPub]
  · exact ⟨rfl, rfl, rfl⟩

theorem bind_readT :
    BindMemoryRowA seedZ Op5Skeleton.skReadT (lblOf seedZ (pReadTA seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i
    · rfl
    · simp [Op5Skeleton.skReadT, Op5Skeleton.readRow, MemoryTable.fanoutMem,
        memoryChildCell, lblOf, pReadTA, readPub]
  · exact ⟨rfl, rfl, rfl⟩

theorem bind_decT :
    BindMemoryRowA seedZ Op5Skeleton.skDecT (lblOf seedZ (pDecT seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i <;> rfl
  · rfl

theorem bind_verifyT :
    BindMemoryRowA seedZ Op5Skeleton.skVerifyT (lblOf seedZ (pVerifyTA seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i
    · rfl
    · simp [Op5Skeleton.skVerifyT, Op5Skeleton.verifyRow, MemoryTable.fanoutMem,
        memoryChildCell, lblOf, pVerifyTA, verifyPub]
  · exact ⟨rfl, rfl, rfl⟩

theorem bind_readC :
    BindMemoryRowA seedZ Op5Skeleton.skReadC (lblOf seedZ (pReadCA seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i
    · rfl
    · simp [Op5Skeleton.skReadC, Op5Skeleton.readRow, MemoryTable.fanoutMem,
        memoryChildCell, lblOf, pReadCA, readPub]
  · exact ⟨rfl, rfl, rfl⟩

theorem bind_readB :
    BindMemoryRowA seedZ Op5Skeleton.skReadB (lblOf seedZ (pReadBA seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i
    · rfl
    · simp [Op5Skeleton.skReadB, Op5Skeleton.readRow, MemoryTable.fanoutMem,
        memoryChildCell, lblOf, pReadBA, readPub]
  · exact ⟨rfl, rfl, rfl⟩

theorem bind_decC :
    BindMemoryRowA seedZ Op5Skeleton.skDecC (lblOf seedZ (pDecC seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i <;> rfl
  · rfl

theorem bind_decB :
    BindMemoryRowA seedZ Op5Skeleton.skDecB (lblOf seedZ (pDecB seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i <;> rfl
  · rfl

theorem bind_haltC1 :
    BindMemoryRowA seedZ Op5Skeleton.skHaltC1 (lblOf seedZ (pHaltC1 seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, rfl⟩
  · simp [Op5Skeleton.skHaltC1, Op5Skeleton.haltRow, lblOf, pHaltC1, haltPub, bindFP, fp]
  · intro i
    have hi : ¬ ((i : ℕ) < MemoryTable.fanoutMem Op5Skeleton.skHaltC1.state) := by
      simp [Op5Skeleton.skHaltC1, Op5Skeleton.haltRow, MemoryTable.fanoutMem]
    rw [dif_neg hi]
    fin_cases i <;> rfl
  · rfl

theorem bind_verifyC :
    BindMemoryRowA seedZ Op5Skeleton.skVerifyC (lblOf seedZ (pVerifyCA seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i
    · rfl
    · simp [Op5Skeleton.skVerifyC, Op5Skeleton.verifyRow, MemoryTable.fanoutMem,
        memoryChildCell, lblOf, pVerifyCA, verifyPub]
  · exact ⟨rfl, rfl, rfl⟩

theorem bind_haltB1 :
    BindMemoryRowA seedZ Op5Skeleton.skHaltB1 (lblOf seedZ (pHaltB1 seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, rfl⟩
  · simp [Op5Skeleton.skHaltB1, Op5Skeleton.haltRow, lblOf, pHaltB1, haltPub, bindFP, fp]
  · intro i
    have hi : ¬ ((i : ℕ) < MemoryTable.fanoutMem Op5Skeleton.skHaltB1.state) := by
      simp [Op5Skeleton.skHaltB1, Op5Skeleton.haltRow, MemoryTable.fanoutMem]
    rw [dif_neg hi]
    fin_cases i <;> rfl
  · rfl

theorem bind_verifyB :
    BindMemoryRowA seedZ Op5Skeleton.skVerifyB (lblOf seedZ (pVerifyBA seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i
    · rfl
    · simp [Op5Skeleton.skVerifyB, Op5Skeleton.verifyRow, MemoryTable.fanoutMem,
        memoryChildCell, lblOf, pVerifyBA, verifyPub]
  · exact ⟨rfl, rfl, rfl⟩

theorem bind_halt4 :
    BindMemoryRowA seedZ Op5Skeleton.skHalt4 (lblOf seedZ (pHalt4 seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, rfl⟩
  · simp [Op5Skeleton.skHalt4, Op5Skeleton.haltRow, lblOf, pHalt4, haltPub, bindFP, fp]
  · intro i
    have hi : ¬ ((i : ℕ) < MemoryTable.fanoutMem Op5Skeleton.skHalt4.state) := by
      simp [Op5Skeleton.skHalt4, Op5Skeleton.haltRow, MemoryTable.fanoutMem]
    rw [dif_neg hi]
    fin_cases i <;> rfl
  · rfl

theorem bind_halt3 :
    BindMemoryRowA seedZ Op5Skeleton.skHalt3 (lblOf seedZ (pHalt3 seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, rfl⟩
  · simp [Op5Skeleton.skHalt3, Op5Skeleton.haltRow, lblOf, pHalt3, haltPub, bindFP, fp]
  · intro i
    have hi : ¬ ((i : ℕ) < MemoryTable.fanoutMem Op5Skeleton.skHalt3.state) := by
      simp [Op5Skeleton.skHalt3, Op5Skeleton.haltRow, MemoryTable.fanoutMem]
    rw [dif_neg hi]
    fin_cases i <;> rfl
  · rfl

/-! ## The literal committed node trees -/

noncomputable def parentNode : ComputeNode K where
  skel := Op5Skeleton.parentRow
  stamp :=
    { state := .s5
      lnPrevExponent := 0
      lnExponent := 2
      recordExponent := fun
        | 0 => 1
        | 1 => 2
        | _ => 0 }
  row := parentRow seedZ alphaA

noncomputable def child1Node : ComputeNode K where
  skel := Op5Skeleton.child1Row
  stamp := { state := .s1, lnPrevExponent := 2, lnExponent := 3, recordExponent := fun _ => 3 }
  row := child1Row seedZ alphaA

noncomputable def child2Node : ComputeNode K where
  skel := Op5Skeleton.child2Row
  stamp := { state := .s1, lnPrevExponent := 3, lnExponent := 4, recordExponent := fun _ => 4 }
  row := child2Row seedZ alphaA

noncomputable def op5ComputeTree : NTree (ComputeNode K) :=
  .node parentNode [.node child1Node [], .node child2Node []]

noncomputable def nReadF : MemoryNode K where
  skel := Op5Skeleton.skReadF
  stamp := { state := .read_root, recordExponent := 1 }
  row := lblOf seedZ (pReadFA seedZ alphaA)
noncomputable def nDecF : MemoryNode K where
  skel := Op5Skeleton.skDecF
  stamp := { state := .decompose, recordExponent := 0 }
  row := lblOf seedZ (pDecF seedZ alphaA)
noncomputable def nHalt5 : MemoryNode K where
  skel := Op5Skeleton.skHalt5
  stamp := { state := .halt, recordExponent := 0 }
  row := lblOf seedZ (pHalt5 seedZ alphaA)
noncomputable def nVerifyF : MemoryNode K where
  skel := Op5Skeleton.skVerifyF
  stamp := { state := .verify_child, recordExponent := 1 }
  row := lblOf seedZ (pVerifyFA seedZ alphaA)
noncomputable def nReadT : MemoryNode K where
  skel := Op5Skeleton.skReadT
  stamp := { state := .read_root, recordExponent := 2 }
  row := lblOf seedZ (pReadTA seedZ alphaA)
noncomputable def nDecT : MemoryNode K where
  skel := Op5Skeleton.skDecT
  stamp := { state := .decompose, recordExponent := 0 }
  row := lblOf seedZ (pDecT seedZ alphaA)
noncomputable def nVerifyT : MemoryNode K where
  skel := Op5Skeleton.skVerifyT
  stamp := { state := .verify_child, recordExponent := 2 }
  row := lblOf seedZ (pVerifyTA seedZ alphaA)
noncomputable def nReadC : MemoryNode K where
  skel := Op5Skeleton.skReadC
  stamp := { state := .read_root, recordExponent := 4 }
  row := lblOf seedZ (pReadCA seedZ alphaA)
noncomputable def nReadB : MemoryNode K where
  skel := Op5Skeleton.skReadB
  stamp := { state := .read_root, recordExponent := 3 }
  row := lblOf seedZ (pReadBA seedZ alphaA)
noncomputable def nDecC : MemoryNode K where
  skel := Op5Skeleton.skDecC
  stamp := { state := .decompose, recordExponent := 0 }
  row := lblOf seedZ (pDecC seedZ alphaA)
noncomputable def nDecB : MemoryNode K where
  skel := Op5Skeleton.skDecB
  stamp := { state := .decompose, recordExponent := 0 }
  row := lblOf seedZ (pDecB seedZ alphaA)
noncomputable def nHaltC1 : MemoryNode K where
  skel := Op5Skeleton.skHaltC1
  stamp := { state := .halt, recordExponent := 0 }
  row := lblOf seedZ (pHaltC1 seedZ alphaA)
noncomputable def nVerifyC : MemoryNode K where
  skel := Op5Skeleton.skVerifyC
  stamp := { state := .verify_child, recordExponent := 4 }
  row := lblOf seedZ (pVerifyCA seedZ alphaA)
noncomputable def nHaltB1 : MemoryNode K where
  skel := Op5Skeleton.skHaltB1
  stamp := { state := .halt, recordExponent := 0 }
  row := lblOf seedZ (pHaltB1 seedZ alphaA)
noncomputable def nVerifyB : MemoryNode K where
  skel := Op5Skeleton.skVerifyB
  stamp := { state := .verify_child, recordExponent := 3 }
  row := lblOf seedZ (pVerifyBA seedZ alphaA)
noncomputable def nHalt4 : MemoryNode K where
  skel := Op5Skeleton.skHalt4
  stamp := { state := .halt, recordExponent := 0 }
  row := lblOf seedZ (pHalt4 seedZ alphaA)
noncomputable def nHalt3 : MemoryNode K where
  skel := Op5Skeleton.skHalt3
  stamp := { state := .halt, recordExponent := 0 }
  row := lblOf seedZ (pHalt3 seedZ alphaA)

noncomputable def op5MemTree : NTree (MemoryNode K) :=
  .node nReadF
    [.node nDecF
      [.node nHalt5 [],
       .node nVerifyF
         [.node nReadT
           [.node nDecT
             [.node nVerifyT
               [.node nReadB
                 [.node nDecB
                   [.node nHaltB1 [],
                    .node nVerifyB [.node nHalt3 []]]]],
              .node nReadC
                [.node nDecC
                  [.node nHaltC1 [],
                   .node nVerifyC [.node nHalt4 []]]]]]]]]

/-! ## Timestamp specialization of each concrete row -/

theorem parent_specializes :
    ComputeTimestampSpecializesAt alphaA parentNode.stamp (parentRow seedZ alphaA) := by
  refine ComputeTimestampSpecializesAt.of_absolute rfl rfl rfl ?_ ?_ ?_ ?_
    (by decide) (fun i => by fin_cases i <;> decide)
  · show (parentPub seedZ alphaA).ln_prev = alphaA ^ 0
    simp [parentPub, pow_zero]
  · show (parentPub seedZ alphaA).ln = alphaA ^ 2
    simp [parentPub]
  · intro i
    fin_cases i <;>
      simp [parentNode, computeMemRec, computeMemRecKind, Nock.Framework.recordCount,
        parentRow, parentPub, recF, recT, MemRec.zero, pow_one]
  · intro i hi
    fin_cases i <;>
      simp_all [parentNode, computeMemRec, computeMemRecKind, Nock.Framework.recordCount,
        parentRow, parentPub, MemRec.zero]

theorem child1_specializes :
    ComputeTimestampSpecializesAt alphaA child1Node.stamp (child1Row seedZ alphaA) := by
  refine ComputeTimestampSpecializesAt.of_absolute rfl rfl rfl ?_ ?_ ?_ ?_
    (by decide) (fun i => by fin_cases i <;> decide)
  · show (child1Pub seedZ alphaA).ln_prev = alphaA ^ 2
    simp [child1Pub, op1PubOf]
  · show (child1Pub seedZ alphaA).ln = alphaA ^ 3
    simp [child1Pub, op1PubOf, pow_succ, pow_two]
  · intro i
    fin_cases i <;>
      simp [child1Node, computeMemRec, computeMemRecKind, Nock.Framework.recordCount,
        child1Row, child1Pub, op1PubOf, recB, MemRec.zero]
  · intro i hi
    fin_cases i <;>
      simp_all [child1Node, computeMemRec, computeMemRecKind, Nock.Framework.recordCount,
        child1Row, child1Pub, op1PubOf, MemRec.zero]

theorem child2_specializes :
    ComputeTimestampSpecializesAt alphaA child2Node.stamp (child2Row seedZ alphaA) := by
  refine ComputeTimestampSpecializesAt.of_absolute rfl rfl rfl ?_ ?_ ?_ ?_
    (by decide) (fun i => by fin_cases i <;> decide)
  · show (child2Pub seedZ alphaA).ln_prev = alphaA ^ 3
    simp [child2Pub, op1PubOf, pow_succ, pow_two]
  · show (child2Pub seedZ alphaA).ln = alphaA ^ 4
    simp [child2Pub, op1PubOf, pow_succ, pow_two]
  · intro i
    fin_cases i <;>
      simp [child2Node, computeMemRec, computeMemRecKind, Nock.Framework.recordCount,
        child2Row, child2Pub, op1PubOf, recC, MemRec.zero]
  · intro i hi
    fin_cases i <;>
      simp_all [child2Node, computeMemRec, computeMemRecKind, Nock.Framework.recordCount,
        child2Row, child2Pub, op1PubOf, MemRec.zero]

theorem readF_specializes :
    MemoryTimestampSpecializesAt alphaA nReadF.stamp (lblOf seedZ (pReadFA seedZ alphaA)) :=
  ⟨rfl, rfl, by simp [nReadF, memoryMemRecKind, lblOf, pReadFA, readPub, recF, pow_one],
    by simp [nReadF, memoryMemRecKind]⟩
theorem decF_specializes :
    MemoryTimestampSpecializesAt alphaA nDecF.stamp (lblOf seedZ (pDecF seedZ alphaA)) :=
  ⟨rfl, rfl, by simp [nDecF, memoryMemRecKind, lblOf, pDecF, decPub, MemRec.zero],
    by simp [nDecF, memoryMemRecKind, lblOf, pDecF, decPub, MemRec.zero]⟩
theorem halt5_specializes :
    MemoryTimestampSpecializesAt alphaA nHalt5.stamp (lblOf seedZ (pHalt5 seedZ alphaA)) :=
  ⟨rfl, rfl, by simp [nHalt5, memoryMemRecKind, lblOf, pHalt5, haltPub, MemRec.zero],
    by simp [nHalt5, memoryMemRecKind, lblOf, pHalt5, haltPub, MemRec.zero]⟩
theorem verifyF_specializes :
    MemoryTimestampSpecializesAt alphaA nVerifyF.stamp (lblOf seedZ (pVerifyFA seedZ alphaA)) :=
  ⟨rfl, rfl, by simp [nVerifyF, memoryMemRecKind, lblOf, pVerifyFA, verifyPub, recF, pow_one],
    by simp [nVerifyF, memoryMemRecKind]⟩
theorem readT_specializes :
    MemoryTimestampSpecializesAt alphaA nReadT.stamp (lblOf seedZ (pReadTA seedZ alphaA)) :=
  ⟨rfl, rfl, by simp [nReadT, memoryMemRecKind, lblOf, pReadTA, readPub, recT],
    by simp [nReadT, memoryMemRecKind]⟩
theorem decT_specializes :
    MemoryTimestampSpecializesAt alphaA nDecT.stamp (lblOf seedZ (pDecT seedZ alphaA)) :=
  ⟨rfl, rfl, by simp [nDecT, memoryMemRecKind, lblOf, pDecT, decPub, MemRec.zero],
    by simp [nDecT, memoryMemRecKind, lblOf, pDecT, decPub, MemRec.zero]⟩
theorem verifyT_specializes :
    MemoryTimestampSpecializesAt alphaA nVerifyT.stamp (lblOf seedZ (pVerifyTA seedZ alphaA)) :=
  ⟨rfl, rfl, by simp [nVerifyT, memoryMemRecKind, lblOf, pVerifyTA, verifyPub, recT],
    by simp [nVerifyT, memoryMemRecKind]⟩
theorem readC_specializes :
    MemoryTimestampSpecializesAt alphaA nReadC.stamp (lblOf seedZ (pReadCA seedZ alphaA)) :=
  ⟨rfl, rfl, by simp [nReadC, memoryMemRecKind, lblOf, pReadCA, readPub, recC],
    by simp [nReadC, memoryMemRecKind]⟩
theorem readB_specializes :
    MemoryTimestampSpecializesAt alphaA nReadB.stamp (lblOf seedZ (pReadBA seedZ alphaA)) :=
  ⟨rfl, rfl, by simp [nReadB, memoryMemRecKind, lblOf, pReadBA, readPub, recB],
    by simp [nReadB, memoryMemRecKind]⟩
theorem decC_specializes :
    MemoryTimestampSpecializesAt alphaA nDecC.stamp (lblOf seedZ (pDecC seedZ alphaA)) :=
  ⟨rfl, rfl, by simp [nDecC, memoryMemRecKind, lblOf, pDecC, decPub, MemRec.zero],
    by simp [nDecC, memoryMemRecKind, lblOf, pDecC, decPub, MemRec.zero]⟩
theorem decB_specializes :
    MemoryTimestampSpecializesAt alphaA nDecB.stamp (lblOf seedZ (pDecB seedZ alphaA)) :=
  ⟨rfl, rfl, by simp [nDecB, memoryMemRecKind, lblOf, pDecB, decPub, MemRec.zero],
    by simp [nDecB, memoryMemRecKind, lblOf, pDecB, decPub, MemRec.zero]⟩
theorem haltC1_specializes :
    MemoryTimestampSpecializesAt alphaA nHaltC1.stamp (lblOf seedZ (pHaltC1 seedZ alphaA)) :=
  ⟨rfl, rfl, by simp [nHaltC1, memoryMemRecKind, lblOf, pHaltC1, haltPub, MemRec.zero],
    by simp [nHaltC1, memoryMemRecKind, lblOf, pHaltC1, haltPub, MemRec.zero]⟩
theorem verifyC_specializes :
    MemoryTimestampSpecializesAt alphaA nVerifyC.stamp (lblOf seedZ (pVerifyCA seedZ alphaA)) :=
  ⟨rfl, rfl, by simp [nVerifyC, memoryMemRecKind, lblOf, pVerifyCA, verifyPub, recC],
    by simp [nVerifyC, memoryMemRecKind]⟩
theorem haltB1_specializes :
    MemoryTimestampSpecializesAt alphaA nHaltB1.stamp (lblOf seedZ (pHaltB1 seedZ alphaA)) :=
  ⟨rfl, rfl, by simp [nHaltB1, memoryMemRecKind, lblOf, pHaltB1, haltPub, MemRec.zero],
    by simp [nHaltB1, memoryMemRecKind, lblOf, pHaltB1, haltPub, MemRec.zero]⟩
theorem verifyB_specializes :
    MemoryTimestampSpecializesAt alphaA nVerifyB.stamp (lblOf seedZ (pVerifyBA seedZ alphaA)) :=
  ⟨rfl, rfl, by simp [nVerifyB, memoryMemRecKind, lblOf, pVerifyBA, verifyPub, recB],
    by simp [nVerifyB, memoryMemRecKind]⟩
theorem halt4_specializes :
    MemoryTimestampSpecializesAt alphaA nHalt4.stamp (lblOf seedZ (pHalt4 seedZ alphaA)) :=
  ⟨rfl, rfl, by simp [nHalt4, memoryMemRecKind, lblOf, pHalt4, haltPub, MemRec.zero],
    by simp [nHalt4, memoryMemRecKind, lblOf, pHalt4, haltPub, MemRec.zero]⟩
theorem halt3_specializes :
    MemoryTimestampSpecializesAt alphaA nHalt3.stamp (lblOf seedZ (pHalt3 seedZ alphaA)) :=
  ⟨rfl, rfl, by simp [nHalt3, memoryMemRecKind, lblOf, pHalt3, haltPub, MemRec.zero],
    by simp [nHalt3, memoryMemRecKind, lblOf, pHalt3, haltPub, MemRec.zero]⟩

/-! ## Local node validity -/

theorem op5ComputeTree_OK :
    ComputeNodesOK seedZ alphaA op5ComputeTree := by
  refine ComputeNodesOK.mk' ⟨?_, rfl, bind_parentRow, parent_specializes⟩ ?_
  · simp [parentNode, Op5Skeleton.parentRow, ComputeTable.fanoutComp]
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ComputeNodesOK.mk' ⟨by simp [child1Node, Op5Skeleton.child1Row, Op5Skeleton.op1Row,
        ComputeTable.fanoutComp], rfl, bind_child1Row, child1_specializes⟩ (by simp)
    · exact ComputeNodesOK.mk' ⟨by simp [child2Node, Op5Skeleton.child2Row, Op5Skeleton.op1Row,
        ComputeTable.fanoutComp], rfl, bind_child2Row, child2_specializes⟩ (by simp)

theorem op5MemTree_OK :
    MemoryNodesOK seedZ alphaA op5MemTree := by
  refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_readF, readF_specializes⟩ ?_
  intro c hc; simp only [List.mem_cons, List.not_mem_nil, or_false] at hc; subst hc
  refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_decF, decF_specializes⟩ ?_
  intro d hd; simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl
  · exact MemoryNodesOK.mk' ⟨rfl, rfl, bind_halt5, halt5_specializes⟩ (by simp)
  · refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_verifyF, verifyF_specializes⟩ ?_
    intro e he; simp only [List.mem_cons, List.not_mem_nil, or_false] at he; subst he
    refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_readT, readT_specializes⟩ ?_
    intro f hf; simp only [List.mem_cons, List.not_mem_nil, or_false] at hf; subst hf
    refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_decT, decT_specializes⟩ ?_
    intro g hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_verifyT, verifyT_specializes⟩ ?_
      intro h hh; simp only [List.mem_cons, List.not_mem_nil, or_false] at hh; subst hh
      refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_readB, readB_specializes⟩ ?_
      intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; subst hi
      refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_decB, decB_specializes⟩ ?_
      intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl
      · exact MemoryNodesOK.mk' ⟨rfl, rfl, bind_haltB1, haltB1_specializes⟩ (by simp)
      · refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_verifyB, verifyB_specializes⟩ ?_
        intro k hk; simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; subst hk
        exact MemoryNodesOK.mk' ⟨rfl, rfl, bind_halt3, halt3_specializes⟩ (by simp)
    · refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_readC, readC_specializes⟩ ?_
      intro h hh; simp only [List.mem_cons, List.not_mem_nil, or_false] at hh; subst hh
      refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_decC, decC_specializes⟩ ?_
      intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact MemoryNodesOK.mk' ⟨rfl, rfl, bind_haltC1, haltC1_specializes⟩ (by simp)
      · refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_verifyC, verifyC_specializes⟩ ?_
        intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; subst hj
        exact MemoryNodesOK.mk' ⟨rfl, rfl, bind_halt4, halt4_specializes⟩ (by simp)

/-! ## The committed skeleton is exactly `Op5Skeleton.semanticSkeleton` -/

theorem skeletonOfNodes_eq :
    skeletonOfNodes op5ComputeTree [op5MemTree] = Op5Skeleton.semanticSkeleton := by
  simp [skeletonOfNodes, op5ComputeTree, op5MemTree, mapNTree, Op5Skeleton.semanticSkeleton,
    Op5Skeleton.computeTree, parentNode, child1Node, child2Node,
    nReadF, nDecF, nHalt5, nVerifyF, nReadT, nDecT, nVerifyT, nReadC, nReadB, nDecC, nDecB,
    nHaltC1, nVerifyC, nHaltB1, nVerifyB, nHalt4, nHalt3,
    Op5Skeleton.readFTree, Op5Skeleton.tDecF, Op5Skeleton.tHalt5,
    Op5Skeleton.tVerifyF, Op5Skeleton.tReadT, Op5Skeleton.tDecT, Op5Skeleton.tVerifyT,
    Op5Skeleton.tReadC, Op5Skeleton.tReadB, Op5Skeleton.tDecC, Op5Skeleton.tDecB,
    Op5Skeleton.tHaltC1, Op5Skeleton.tVerifyC, Op5Skeleton.tHaltB1, Op5Skeleton.tVerifyB,
    Op5Skeleton.tHalt4, Op5Skeleton.tHalt3,
    Op5Skeleton.mLeaf, Op5Skeleton.mOne, Op5Skeleton.mTwo]

/-! ## The honest commitment -/

noncomputable def data
    (hfirst :
      ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.counts = 0 ∧
        ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.indicator = 0) :
    Data (Op5Execution hfirst) where
  computeNodes := op5ComputeTree
  memoryNodes := [op5MemTree]
  compute_rows := by
    show mapNTree ComputeNode.row op5ComputeTree = (exec seedZ alphaA).computeTree
    simp [op5ComputeTree, parentNode, child1Node, child2Node, mapNTree, exec, execA,
      computeTree]
  memory_rows := by
    show [op5MemTree].map (mapNTree MemoryNode.row) = (execA seedZ alphaA).memoryForest
    simp [op5MemTree, nReadF, nDecF, nHalt5, nVerifyF, nReadT, nDecT, nVerifyT, nReadC,
      nReadB, nDecC, nDecB, nHaltC1, nVerifyC, nHaltB1, nVerifyB, nHalt4, nHalt3,
      mapNTree, exec, execA, rootTreeA, tDecFA, tHalt5,
      tVerifyFA, tReadTA, tDecTA, tVerifyTA, tReadCA, tReadBA, tDecCA, tDecBA, tHaltC1, tVerifyCA,
      tHaltB1, tVerifyBA, tHalt4, tHalt3,
      mLeaf, mOne, mTwo]
  computeOK := op5ComputeTree_OK
  memoryOK := by
    intro t ht
    simp only [List.mem_singleton] at ht
    subst ht
    exact op5MemTree_OK
  root_line_exponent := rfl
  root_line_origin := rfl
  nounSizeBound := 5
  Λ := 5
  slotSemantics := skeletonOfNodes_eq ▸ Op5Skeleton.slotSemantics
  recordEquations := skeletonOfNodes_eq ▸ Op5Skeleton.recordEquations
  census := skeletonOfNodes_eq ▸ Op5Skeleton.census
  sizeWindowBound := skeletonOfNodes_eq ▸ Op5Skeleton.sizeWindowBound
  q_eq_ringChar := by show (97 : ℕ) = ringChar K; exact ringChar_K3.symm
  skeletonBounded := skeletonOfNodes_eq ▸ Op5Skeleton.skeletonBounded
  combinedBounded := skeletonOfNodes_eq ▸ Op5Skeleton.combinedBounded

theorem data_skeleton
    (hfirst :
      ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.counts = 0 ∧
        ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.indicator = 0) :
    (data hfirst).skeleton = Op5Skeleton.semanticSkeleton :=
  skeletonOfNodes_eq

end Nock.NockVMROM.Thm54.TraceGen.Op5ConfigK3

#print axioms Nock.NockVMROM.Thm54.TraceGen.Op5ConfigK3.Op5Execution
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op5ConfigK3.data
