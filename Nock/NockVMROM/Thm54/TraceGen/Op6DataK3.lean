/-
  Nock/NockVMROM/Thm54/TraceGen/Op6DataK3.lean

  Stage 3 of the OP6 Layer-2 CORE, over `K3`: the assembled
  `Op6Execution : BuildableNockExecution (ZMod 97) K3` — all fourteen fields —
  and the directly-built literal-node commitment `HonestCommitment.Data Op6Execution`
  for the fan-out-2 branch (if) program

      `*[0 [6 [[1 0] [[1 5] [1 6]]]]] = 5`
-/
import Nock.NockVMROM.Thm54.TraceGen.Op6LanguageK3
import Nock.NockVMROM.Thm54.TraceGen.Op6SkeletonK3
import Nock.NockVMROM.Thm54.HonestCommitment

namespace Nock.NockVMROM.Thm54.TraceGen.Op6ConfigK3

open Nock Nock.Walk Nock.ComputeTable Nock.MemoryTable
open Nock.NockVMROM.Thm54
open SemanticStrategy
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.TraceGen.Op6Skeleton
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
  (ComputeTimestampSpecializesAt MemoryTimestampSpecializesAt)

set_option linter.unusedSimpArgs false

/-! ## The assembled buildable execution -/

noncomputable def Op6Execution
    (hfirst :
      ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.counts = 0 ∧
        ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.indicator = 0) :
    BuildableNockExecution F K where
  q := 97
  q_gt_one := by norm_num
  Λ := 7
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
    BindComputeRow seedZ Op6Skeleton.parentRow (parentRow seedZ alphaA) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro slot
    cases slot <;>
      simp [decActive, hasTailDecomposition, decFP, bindFP, fp,
        Op6Skeleton.parentRow, parentRow, parentDec, op6Head, Op6Skeleton.op6Head]
  · intro i
    fin_cases i
    · rw [dif_pos (by decide)]
      intro slot
      cases slot <;>
        simp [Op6Skeleton.parentRow, computeSubformulaFPs, ComputeTable.sfTriple,
          parentRow, parentPub, tripleFP, bindFP, fp]
    · rw [dif_pos (by decide)]
      intro slot
      cases slot <;>
        simp [Op6Skeleton.parentRow, computeSubformulaFPs, ComputeTable.sfTriple,
          parentRow, parentPub, tripleFP, bindFP, fp]
    · rw [dif_neg (by decide)]
      simp [computeSubformulaFPs, parentRow, parentPub, ComputeTable.sfTriple]
  · intro i
    fin_cases i
    · rw [dif_pos (by decide)]
      exact ⟨rfl, rfl, rfl⟩
    · rw [dif_pos (by decide)]
      exact ⟨rfl, rfl, rfl⟩
    · rw [dif_pos (by decide)]
      exact ⟨rfl, rfl, rfl⟩

theorem bind_child1Row :
    BindComputeRow seedZ Op6Skeleton.child1Row (child1Row seedZ alphaA) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro slot
    cases slot <;>
      simp [decActive, hasTailDecomposition, decFP, bindFP, fp,
        Op6Skeleton.child1Row, Op6Skeleton.op1Row, child1Row, op1DecOf,
        op1Head, Op6Skeleton.op1Head]
  · intro i
    have hi : ¬ ((i : ℕ) < ComputeTable.fanoutComp Op6Skeleton.child1Row.state) := by
      simp [Op6Skeleton.child1Row, Op6Skeleton.op1Row, ComputeTable.fanoutComp]
    rw [dif_neg hi]
    fin_cases i <;>
      simp [computeSubformulaFPs, ComputeTable.sfTriple, child1Row, child1Pub, op1PubOf]
  · intro i
    fin_cases i
    · exact ⟨rfl, rfl, rfl⟩
    · rfl
    · rfl

theorem bind_child2Row :
    BindComputeRow seedZ Op6Skeleton.child2Row (child2Row seedZ alphaA) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro slot
    cases slot <;>
      simp [decActive, hasTailDecomposition, decFP, bindFP, fp,
        Op6Skeleton.child2Row, Op6Skeleton.op1Row, child2Row, op1DecOf,
        op1Head, Op6Skeleton.op1Head]
  · intro i
    have hi : ¬ ((i : ℕ) < ComputeTable.fanoutComp Op6Skeleton.child2Row.state) := by
      simp [Op6Skeleton.child2Row, Op6Skeleton.op1Row, ComputeTable.fanoutComp]
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
    BindMemoryRowA seedZ Op6Skeleton.skReadF (lblOf seedZ (pReadFA seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i
    · rfl
    · simp [Op6Skeleton.skReadF, Op6Skeleton.readRow, MemoryTable.fanoutMem,
        memoryChildCell, lblOf, pReadFA, readPub]
  · exact ⟨rfl, rfl, rfl⟩

theorem bind_decF :
    BindMemoryRowA seedZ Op6Skeleton.skDecF (lblOf seedZ (pDecF seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i <;> rfl
  · rfl

theorem bind_halt6 :
    BindMemoryRowA seedZ Op6Skeleton.skHalt6 (lblOf seedZ (pHalt6 seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, rfl⟩
  · simp [Op6Skeleton.skHalt6, Op6Skeleton.haltRow, lblOf, pHalt6, haltPub, bindFP, fp]
  · intro i
    have hi : ¬ ((i : ℕ) < MemoryTable.fanoutMem Op6Skeleton.skHalt6.state) := by
      simp [Op6Skeleton.skHalt6, Op6Skeleton.haltRow, MemoryTable.fanoutMem]
    rw [dif_neg hi]
    fin_cases i <;> rfl
  · rfl

theorem bind_verifyF :
    BindMemoryRowA seedZ Op6Skeleton.skVerifyF (lblOf seedZ (pVerifyFA seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i
    · rfl
    · simp [Op6Skeleton.skVerifyF, Op6Skeleton.verifyRow, MemoryTable.fanoutMem,
        memoryChildCell, lblOf, pVerifyFA, verifyPub]
  · exact ⟨rfl, rfl, rfl⟩

theorem bind_readT :
    BindMemoryRowA seedZ Op6Skeleton.skReadT (lblOf seedZ (pReadTA seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i
    · rfl
    · simp [Op6Skeleton.skReadT, Op6Skeleton.readRow, MemoryTable.fanoutMem,
        memoryChildCell, lblOf, pReadTA, readPub]
  · exact ⟨rfl, rfl, rfl⟩

theorem bind_decT :
    BindMemoryRowA seedZ Op6Skeleton.skDecT (lblOf seedZ (pDecT seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i <;> rfl
  · rfl

theorem bind_verifyT :
    BindMemoryRowA seedZ Op6Skeleton.skVerifyT (lblOf seedZ (pVerifyTA seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i
    · rfl
    · simp [Op6Skeleton.skVerifyT, Op6Skeleton.verifyRow, MemoryTable.fanoutMem,
        memoryChildCell, lblOf, pVerifyTA, verifyPub]
  · exact ⟨rfl, rfl, rfl⟩

theorem bind_readC2 :
    BindMemoryRowA seedZ Op6Skeleton.skReadC2 (lblOf seedZ (pReadC2A seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i
    · rfl
    · simp [Op6Skeleton.skReadC2, Op6Skeleton.readRow, MemoryTable.fanoutMem,
        memoryChildCell, lblOf, pReadC2A, readPub]
  · exact ⟨rfl, rfl, rfl⟩

theorem bind_decC2 :
    BindMemoryRowA seedZ Op6Skeleton.skDecC2 (lblOf seedZ (pDecC2 seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i <;> rfl
  · rfl

theorem bind_halt1_c2 :
    BindMemoryRowA seedZ Op6Skeleton.skHalt1_c2 (lblOf seedZ (pHalt1_c2 seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, rfl⟩
  · simp [Op6Skeleton.skHalt1_c2, Op6Skeleton.haltRow, lblOf, pHalt1_c2, haltPub, bindFP, fp]
  · intro i
    have hi : ¬ ((i : ℕ) < MemoryTable.fanoutMem Op6Skeleton.skHalt1_c2.state) := by
      simp [Op6Skeleton.skHalt1_c2, Op6Skeleton.haltRow, MemoryTable.fanoutMem]
    rw [dif_neg hi]
    fin_cases i <;> rfl
  · rfl

theorem bind_verifyC2 :
    BindMemoryRowA seedZ Op6Skeleton.skVerifyC2 (lblOf seedZ (pVerifyC2A seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i
    · rfl
    · simp [Op6Skeleton.skVerifyC2, Op6Skeleton.verifyRow, MemoryTable.fanoutMem,
        memoryChildCell, lblOf, pVerifyC2A, verifyPub]
  · exact ⟨rfl, rfl, rfl⟩

theorem bind_halt0 :
    BindMemoryRowA seedZ Op6Skeleton.skHalt0 (lblOf seedZ (pHalt0 seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, rfl⟩
  · simp [Op6Skeleton.skHalt0, Op6Skeleton.haltRow, lblOf, pHalt0, haltPub, bindFP, fp]
  · intro i
    have hi : ¬ ((i : ℕ) < MemoryTable.fanoutMem Op6Skeleton.skHalt0.state) := by
      simp [Op6Skeleton.skHalt0, Op6Skeleton.haltRow, MemoryTable.fanoutMem]
    rw [dif_neg hi]
    fin_cases i <;> rfl
  · rfl

theorem bind_readP :
    BindMemoryRowA seedZ Op6Skeleton.skReadP (lblOf seedZ (pReadPA seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i
    · rfl
    · simp [Op6Skeleton.skReadP, Op6Skeleton.readRow, MemoryTable.fanoutMem,
        memoryChildCell, lblOf, pReadPA, readPub]
  · exact ⟨rfl, rfl, rfl⟩

theorem bind_decP :
    BindMemoryRowA seedZ Op6Skeleton.skDecP (lblOf seedZ (pDecP seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i <;> rfl
  · rfl

theorem bind_verifyP :
    BindMemoryRowA seedZ Op6Skeleton.skVerifyP (lblOf seedZ (pVerifyPA seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i
    · rfl
    · simp [Op6Skeleton.skVerifyP, Op6Skeleton.verifyRow, MemoryTable.fanoutMem,
        memoryChildCell, lblOf, pVerifyPA, verifyPub]
  · exact ⟨rfl, rfl, rfl⟩

theorem bind_readC1 :
    BindMemoryRowA seedZ Op6Skeleton.skReadC1 (lblOf seedZ (pReadC1A seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i
    · rfl
    · simp [Op6Skeleton.skReadC1, Op6Skeleton.readRow, MemoryTable.fanoutMem,
        memoryChildCell, lblOf, pReadC1A, readPub]
  · exact ⟨rfl, rfl, rfl⟩

theorem bind_decC1 :
    BindMemoryRowA seedZ Op6Skeleton.skDecC1 (lblOf seedZ (pDecC1 seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i <;> rfl
  · rfl

theorem bind_halt1_c1 :
    BindMemoryRowA seedZ Op6Skeleton.skHalt1_c1 (lblOf seedZ (pHalt1_c1 seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, rfl⟩
  · simp [Op6Skeleton.skHalt1_c1, Op6Skeleton.haltRow, lblOf, pHalt1_c1, haltPub, bindFP, fp]
  · intro i
    have hi : ¬ ((i : ℕ) < MemoryTable.fanoutMem Op6Skeleton.skHalt1_c1.state) := by
      simp [Op6Skeleton.skHalt1_c1, Op6Skeleton.haltRow, MemoryTable.fanoutMem]
    rw [dif_neg hi]
    fin_cases i <;> rfl
  · rfl

theorem bind_verifyC1 :
    BindMemoryRowA seedZ Op6Skeleton.skVerifyC1 (lblOf seedZ (pVerifyC1A seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i
    · rfl
    · simp [Op6Skeleton.skVerifyC1, Op6Skeleton.verifyRow, MemoryTable.fanoutMem,
        memoryChildCell, lblOf, pVerifyC1A, verifyPub]
  · exact ⟨rfl, rfl, rfl⟩

theorem bind_halt5 :
    BindMemoryRowA seedZ Op6Skeleton.skHalt5 (lblOf seedZ (pHalt5 seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, rfl⟩
  · simp [Op6Skeleton.skHalt5, Op6Skeleton.haltRow, lblOf, pHalt5, haltPub, bindFP, fp]
  · intro i
    have hi : ¬ ((i : ℕ) < MemoryTable.fanoutMem Op6Skeleton.skHalt5.state) := by
      simp [Op6Skeleton.skHalt5, Op6Skeleton.haltRow, MemoryTable.fanoutMem]
    rw [dif_neg hi]
    fin_cases i <;> rfl
  · rfl

theorem bind_decBranchD :
    BindMemoryRowA seedZ Op6Skeleton.skDecBranchD (lblOf seedZ (pDecBranchD seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i <;> rfl
  · rfl

theorem bind_halt1_d :
    BindMemoryRowA seedZ Op6Skeleton.skHalt1_d (lblOf seedZ (pHalt1_d seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, rfl⟩
  · simp [Op6Skeleton.skHalt1_d, Op6Skeleton.haltRow, lblOf, pHalt1_d, haltPub, bindFP, fp]
  · intro i
    have hi : ¬ ((i : ℕ) < MemoryTable.fanoutMem Op6Skeleton.skHalt1_d.state) := by
      simp [Op6Skeleton.skHalt1_d, Op6Skeleton.haltRow, MemoryTable.fanoutMem]
    rw [dif_neg hi]
    fin_cases i <;> rfl
  · rfl

theorem bind_halt6_d :
    BindMemoryRowA seedZ Op6Skeleton.skHalt6_d (lblOf seedZ (pHalt6_d seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, rfl⟩
  · simp [Op6Skeleton.skHalt6_d, Op6Skeleton.haltRow, lblOf, pHalt6_d, haltPub, bindFP, fp]
  · intro i
    have hi : ¬ ((i : ℕ) < MemoryTable.fanoutMem Op6Skeleton.skHalt6_d.state) := by
      simp [Op6Skeleton.skHalt6_d, Op6Skeleton.haltRow, MemoryTable.fanoutMem]
    rw [dif_neg hi]
    fin_cases i <;> rfl
  · rfl

/-! ## The literal committed node trees -/

noncomputable def parentNode : ComputeNode K where
  skel := Op6Skeleton.parentRow
  stamp :=
    { state := .s6
      lnPrevExponent := 0
      lnExponent := 3
      recordExponent := fun
        | 0 => 1
        | 1 => 2
        | _ => 3 }
  row := parentRow seedZ alphaA

noncomputable def child1Node : ComputeNode K where
  skel := Op6Skeleton.child1Row
  stamp := { state := .s1, lnPrevExponent := 3, lnExponent := 4, recordExponent := fun _ => 4 }
  row := child1Row seedZ alphaA

noncomputable def child2Node : ComputeNode K where
  skel := Op6Skeleton.child2Row
  stamp := { state := .s1, lnPrevExponent := 4, lnExponent := 5, recordExponent := fun _ => 5 }
  row := child2Row seedZ alphaA

noncomputable def op6ComputeTree : NTree (ComputeNode K) :=
  .node parentNode [.node child1Node [], .node child2Node []]

noncomputable def nReadF : MemoryNode K where
  skel := Op6Skeleton.skReadF
  stamp := { state := .read_root, recordExponent := 1 }
  row := lblOf seedZ (pReadFA seedZ alphaA)
noncomputable def nDecF : MemoryNode K where
  skel := Op6Skeleton.skDecF
  stamp := { state := .decompose, recordExponent := 0 }
  row := lblOf seedZ (pDecF seedZ alphaA)
noncomputable def nHalt6 : MemoryNode K where
  skel := Op6Skeleton.skHalt6
  stamp := { state := .halt, recordExponent := 0 }
  row := lblOf seedZ (pHalt6 seedZ alphaA)
noncomputable def nVerifyF : MemoryNode K where
  skel := Op6Skeleton.skVerifyF
  stamp := { state := .verify_child, recordExponent := 1 }
  row := lblOf seedZ (pVerifyFA seedZ alphaA)
noncomputable def nReadT : MemoryNode K where
  skel := Op6Skeleton.skReadT
  stamp := { state := .read_root, recordExponent := 2 }
  row := lblOf seedZ (pReadTA seedZ alphaA)
noncomputable def nDecT : MemoryNode K where
  skel := Op6Skeleton.skDecT
  stamp := { state := .decompose, recordExponent := 0 }
  row := lblOf seedZ (pDecT seedZ alphaA)
noncomputable def nVerifyT : MemoryNode K where
  skel := Op6Skeleton.skVerifyT
  stamp := { state := .verify_child, recordExponent := 2 }
  row := lblOf seedZ (pVerifyTA seedZ alphaA)
noncomputable def nReadC2 : MemoryNode K where
  skel := Op6Skeleton.skReadC2
  stamp := { state := .read_root, recordExponent := 5 }
  row := lblOf seedZ (pReadC2A seedZ alphaA)
noncomputable def nDecC2 : MemoryNode K where
  skel := Op6Skeleton.skDecC2
  stamp := { state := .decompose, recordExponent := 0 }
  row := lblOf seedZ (pDecC2 seedZ alphaA)
noncomputable def nHalt1_c2 : MemoryNode K where
  skel := Op6Skeleton.skHalt1_c2
  stamp := { state := .halt, recordExponent := 0 }
  row := lblOf seedZ (pHalt1_c2 seedZ alphaA)
noncomputable def nVerifyC2 : MemoryNode K where
  skel := Op6Skeleton.skVerifyC2
  stamp := { state := .verify_child, recordExponent := 5 }
  row := lblOf seedZ (pVerifyC2A seedZ alphaA)
noncomputable def nHalt0 : MemoryNode K where
  skel := Op6Skeleton.skHalt0
  stamp := { state := .halt, recordExponent := 0 }
  row := lblOf seedZ (pHalt0 seedZ alphaA)
noncomputable def nReadP : MemoryNode K where
  skel := Op6Skeleton.skReadP
  stamp := { state := .read_root, recordExponent := 3 }
  row := lblOf seedZ (pReadPA seedZ alphaA)
noncomputable def nDecP : MemoryNode K where
  skel := Op6Skeleton.skDecP
  stamp := { state := .decompose, recordExponent := 0 }
  row := lblOf seedZ (pDecP seedZ alphaA)
noncomputable def nVerifyP : MemoryNode K where
  skel := Op6Skeleton.skVerifyP
  stamp := { state := .verify_child, recordExponent := 3 }
  row := lblOf seedZ (pVerifyPA seedZ alphaA)
noncomputable def nReadC1 : MemoryNode K where
  skel := Op6Skeleton.skReadC1
  stamp := { state := .read_root, recordExponent := 4 }
  row := lblOf seedZ (pReadC1A seedZ alphaA)
noncomputable def nDecC1 : MemoryNode K where
  skel := Op6Skeleton.skDecC1
  stamp := { state := .decompose, recordExponent := 0 }
  row := lblOf seedZ (pDecC1 seedZ alphaA)
noncomputable def nHalt1_c1 : MemoryNode K where
  skel := Op6Skeleton.skHalt1_c1
  stamp := { state := .halt, recordExponent := 0 }
  row := lblOf seedZ (pHalt1_c1 seedZ alphaA)
noncomputable def nVerifyC1 : MemoryNode K where
  skel := Op6Skeleton.skVerifyC1
  stamp := { state := .verify_child, recordExponent := 4 }
  row := lblOf seedZ (pVerifyC1A seedZ alphaA)
noncomputable def nHalt5 : MemoryNode K where
  skel := Op6Skeleton.skHalt5
  stamp := { state := .halt, recordExponent := 0 }
  row := lblOf seedZ (pHalt5 seedZ alphaA)
noncomputable def nDecBranchD : MemoryNode K where
  skel := Op6Skeleton.skDecBranchD
  stamp := { state := .decompose, recordExponent := 0 }
  row := lblOf seedZ (pDecBranchD seedZ alphaA)
noncomputable def nHalt1_d : MemoryNode K where
  skel := Op6Skeleton.skHalt1_d
  stamp := { state := .halt, recordExponent := 0 }
  row := lblOf seedZ (pHalt1_d seedZ alphaA)
noncomputable def nHalt6_d : MemoryNode K where
  skel := Op6Skeleton.skHalt6_d
  stamp := { state := .halt, recordExponent := 0 }
  row := lblOf seedZ (pHalt6_d seedZ alphaA)

noncomputable def op6MemTree : NTree (MemoryNode K) :=
  .node nReadF
    [.node nDecF
      [.node nHalt6 [],
       .node nVerifyF
         [.node nReadT
           [.node nDecT
             [.node nVerifyT
               [.node nReadC2
                 [.node nDecC2
                   [.node nHalt1_c2 [],
                    .node nVerifyC2 [.node nHalt0 []]]]],
              .node nReadP
                [.node nDecP
                  [.node nVerifyP
                    [.node nReadC1
                      [.node nDecC1
                        [.node nHalt1_c1 [],
                         .node nVerifyC1 [.node nHalt5 []]]]],
                   .node nDecBranchD
                     [.node nHalt1_d [],
                      .node nHalt6_d []]]]]]]]]

/-! ## Timestamp specialization of each concrete row -/

theorem parent_specializes :
    ComputeTimestampSpecializesAt alphaA parentNode.stamp (parentRow seedZ alphaA) := by
  refine ComputeTimestampSpecializesAt.of_absolute rfl rfl rfl ?_ ?_ ?_ ?_
    (by decide) (fun i => by fin_cases i <;> decide)
  · show (parentPub seedZ alphaA).ln_prev = alphaA ^ 0
    simp [parentPub, pow_zero]
  · show (parentPub seedZ alphaA).ln = alphaA ^ 3
    simp [parentPub]
  · intro i
    fin_cases i <;>
      simp [parentNode, computeMemRec, computeMemRecKind, Nock.Framework.recordCount,
        parentRow, parentPub, recF, recT, recP, pow_one]
  · intro i hi
    fin_cases i <;>
      simp_all [parentNode, computeMemRec, computeMemRecKind, Nock.Framework.recordCount,
        parentRow, parentPub, MemRec.zero]

theorem child1_specializes :
    ComputeTimestampSpecializesAt alphaA child1Node.stamp (child1Row seedZ alphaA) := by
  refine ComputeTimestampSpecializesAt.of_absolute rfl rfl rfl ?_ ?_ ?_ ?_
    (by decide) (fun i => by fin_cases i <;> decide)
  · show (child1Pub seedZ alphaA).ln_prev = alphaA ^ 3
    simp [child1Pub, op1PubOf]
  · show (child1Pub seedZ alphaA).ln = alphaA ^ 4
    simp [child1Pub, op1PubOf, pow_succ]
  · intro i
    fin_cases i <;>
      simp [child1Node, computeMemRec, computeMemRecKind, Nock.Framework.recordCount,
        child1Row, child1Pub, op1PubOf, recC1, MemRec.zero]
  · intro i hi
    fin_cases i <;>
      simp_all [child1Node, computeMemRec, computeMemRecKind, Nock.Framework.recordCount,
        child1Row, child1Pub, op1PubOf, MemRec.zero]

theorem child2_specializes :
    ComputeTimestampSpecializesAt alphaA child2Node.stamp (child2Row seedZ alphaA) := by
  refine ComputeTimestampSpecializesAt.of_absolute rfl rfl rfl ?_ ?_ ?_ ?_
    (by decide) (fun i => by fin_cases i <;> decide)
  · show (child2Pub seedZ alphaA).ln_prev = alphaA ^ 4
    simp [child2Pub, op1PubOf]
  · show (child2Pub seedZ alphaA).ln = alphaA ^ 5
    simp [child2Pub, op1PubOf, pow_succ]
  · intro i
    fin_cases i <;>
      simp [child2Node, computeMemRec, computeMemRecKind, Nock.Framework.recordCount,
        child2Row, child2Pub, op1PubOf, recC2, MemRec.zero]
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
theorem halt6_specializes :
    MemoryTimestampSpecializesAt alphaA nHalt6.stamp (lblOf seedZ (pHalt6 seedZ alphaA)) :=
  ⟨rfl, rfl, by simp [nHalt6, memoryMemRecKind, lblOf, pHalt6, haltPub, MemRec.zero],
    by simp [nHalt6, memoryMemRecKind, lblOf, pHalt6, haltPub, MemRec.zero]⟩
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
theorem readC2_specializes :
    MemoryTimestampSpecializesAt alphaA nReadC2.stamp (lblOf seedZ (pReadC2A seedZ alphaA)) :=
  ⟨rfl, rfl, by simp [nReadC2, memoryMemRecKind, lblOf, pReadC2A, readPub, recC2],
    by simp [nReadC2, memoryMemRecKind]⟩
theorem decC2_specializes :
    MemoryTimestampSpecializesAt alphaA nDecC2.stamp (lblOf seedZ (pDecC2 seedZ alphaA)) :=
  ⟨rfl, rfl, by simp [nDecC2, memoryMemRecKind, lblOf, pDecC2, decPub, MemRec.zero],
    by simp [nDecC2, memoryMemRecKind, lblOf, pDecC2, decPub, MemRec.zero]⟩
theorem halt1_c2_specializes :
    MemoryTimestampSpecializesAt alphaA nHalt1_c2.stamp (lblOf seedZ (pHalt1_c2 seedZ alphaA)) :=
  ⟨rfl, rfl, by simp [nHalt1_c2, memoryMemRecKind, lblOf, pHalt1_c2, haltPub, MemRec.zero],
    by simp [nHalt1_c2, memoryMemRecKind, lblOf, pHalt1_c2, haltPub, MemRec.zero]⟩
theorem verifyC2_specializes :
    MemoryTimestampSpecializesAt alphaA nVerifyC2.stamp (lblOf seedZ (pVerifyC2A seedZ alphaA)) :=
  ⟨rfl, rfl, by simp [nVerifyC2, memoryMemRecKind, lblOf, pVerifyC2A, verifyPub, recC2],
    by simp [nVerifyC2, memoryMemRecKind]⟩
theorem halt0_specializes :
    MemoryTimestampSpecializesAt alphaA nHalt0.stamp (lblOf seedZ (pHalt0 seedZ alphaA)) :=
  ⟨rfl, rfl, by simp [nHalt0, memoryMemRecKind, lblOf, pHalt0, haltPub, MemRec.zero],
    by simp [nHalt0, memoryMemRecKind, lblOf, pHalt0, haltPub, MemRec.zero]⟩
theorem readP_specializes :
    MemoryTimestampSpecializesAt alphaA nReadP.stamp (lblOf seedZ (pReadPA seedZ alphaA)) :=
  ⟨rfl, rfl, by simp [nReadP, memoryMemRecKind, lblOf, pReadPA, readPub, recP],
    by simp [nReadP, memoryMemRecKind]⟩
theorem decP_specializes :
    MemoryTimestampSpecializesAt alphaA nDecP.stamp (lblOf seedZ (pDecP seedZ alphaA)) :=
  ⟨rfl, rfl, by simp [nDecP, memoryMemRecKind, lblOf, pDecP, decPub, MemRec.zero],
    by simp [nDecP, memoryMemRecKind, lblOf, pDecP, decPub, MemRec.zero]⟩
theorem verifyP_specializes :
    MemoryTimestampSpecializesAt alphaA nVerifyP.stamp (lblOf seedZ (pVerifyPA seedZ alphaA)) :=
  ⟨rfl, rfl, by simp [nVerifyP, memoryMemRecKind, lblOf, pVerifyPA, verifyPub, recP],
    by simp [nVerifyP, memoryMemRecKind]⟩
theorem readC1_specializes :
    MemoryTimestampSpecializesAt alphaA nReadC1.stamp (lblOf seedZ (pReadC1A seedZ alphaA)) :=
  ⟨rfl, rfl, by simp [nReadC1, memoryMemRecKind, lblOf, pReadC1A, readPub, recC1],
    by simp [nReadC1, memoryMemRecKind]⟩
theorem decC1_specializes :
    MemoryTimestampSpecializesAt alphaA nDecC1.stamp (lblOf seedZ (pDecC1 seedZ alphaA)) :=
  ⟨rfl, rfl, by simp [nDecC1, memoryMemRecKind, lblOf, pDecC1, decPub, MemRec.zero],
    by simp [nDecC1, memoryMemRecKind, lblOf, pDecC1, decPub, MemRec.zero]⟩
theorem halt1_c1_specializes :
    MemoryTimestampSpecializesAt alphaA nHalt1_c1.stamp (lblOf seedZ (pHalt1_c1 seedZ alphaA)) :=
  ⟨rfl, rfl, by simp [nHalt1_c1, memoryMemRecKind, lblOf, pHalt1_c1, haltPub, MemRec.zero],
    by simp [nHalt1_c1, memoryMemRecKind, lblOf, pHalt1_c1, haltPub, MemRec.zero]⟩
theorem verifyC1_specializes :
    MemoryTimestampSpecializesAt alphaA nVerifyC1.stamp (lblOf seedZ (pVerifyC1A seedZ alphaA)) :=
  ⟨rfl, rfl, by simp [nVerifyC1, memoryMemRecKind, lblOf, pVerifyC1A, verifyPub, recC1],
    by simp [nVerifyC1, memoryMemRecKind]⟩
theorem halt5_specializes :
    MemoryTimestampSpecializesAt alphaA nHalt5.stamp (lblOf seedZ (pHalt5 seedZ alphaA)) :=
  ⟨rfl, rfl, by simp [nHalt5, memoryMemRecKind, lblOf, pHalt5, haltPub, MemRec.zero],
    by simp [nHalt5, memoryMemRecKind, lblOf, pHalt5, haltPub, MemRec.zero]⟩
theorem decBranchD_specializes :
    MemoryTimestampSpecializesAt alphaA nDecBranchD.stamp (lblOf seedZ (pDecBranchD seedZ alphaA)) :=
  ⟨rfl, rfl, by simp [nDecBranchD, memoryMemRecKind, lblOf, pDecBranchD, decPub, MemRec.zero],
    by simp [nDecBranchD, memoryMemRecKind, lblOf, pDecBranchD, decPub, MemRec.zero]⟩
theorem halt1_d_specializes :
    MemoryTimestampSpecializesAt alphaA nHalt1_d.stamp (lblOf seedZ (pHalt1_d seedZ alphaA)) :=
  ⟨rfl, rfl, by simp [nHalt1_d, memoryMemRecKind, lblOf, pHalt1_d, haltPub, MemRec.zero],
    by simp [nHalt1_d, memoryMemRecKind, lblOf, pHalt1_d, haltPub, MemRec.zero]⟩
theorem halt6_d_specializes :
    MemoryTimestampSpecializesAt alphaA nHalt6_d.stamp (lblOf seedZ (pHalt6_d seedZ alphaA)) :=
  ⟨rfl, rfl, by simp [nHalt6_d, memoryMemRecKind, lblOf, pHalt6_d, haltPub, MemRec.zero],
    by simp [nHalt6_d, memoryMemRecKind, lblOf, pHalt6_d, haltPub, MemRec.zero]⟩

/-! ## Local node validity -/

theorem op6ComputeTree_OK :
    ComputeNodesOK seedZ alphaA op6ComputeTree := by
  refine ComputeNodesOK.mk' ⟨?_, rfl, bind_parentRow, parent_specializes⟩ ?_
  · simp [parentNode, Op6Skeleton.parentRow, ComputeTable.fanoutComp]
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ComputeNodesOK.mk' ⟨by simp [child1Node, Op6Skeleton.child1Row, Op6Skeleton.op1Row,
        ComputeTable.fanoutComp], rfl, bind_child1Row, child1_specializes⟩ (by simp)
    · exact ComputeNodesOK.mk' ⟨by simp [child2Node, Op6Skeleton.child2Row, Op6Skeleton.op1Row,
        ComputeTable.fanoutComp], rfl, bind_child2Row, child2_specializes⟩ (by simp)

theorem op6MemTree_OK :
    MemoryNodesOK seedZ alphaA op6MemTree := by
  refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_readF, readF_specializes⟩ ?_
  intro c hc; simp only [List.mem_cons, List.not_mem_nil, or_false] at hc; subst hc
  refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_decF, decF_specializes⟩ ?_
  intro d hd; simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl
  · exact MemoryNodesOK.mk' ⟨rfl, rfl, bind_halt6, halt6_specializes⟩ (by simp)
  · refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_verifyF, verifyF_specializes⟩ ?_
    intro e he; simp only [List.mem_cons, List.not_mem_nil, or_false] at he; subst he
    refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_readT, readT_specializes⟩ ?_
    intro f hf; simp only [List.mem_cons, List.not_mem_nil, or_false] at hf; subst hf
    refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_decT, decT_specializes⟩ ?_
    intro g hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_verifyT, verifyT_specializes⟩ ?_
      intro h hh; simp only [List.mem_cons, List.not_mem_nil, or_false] at hh; subst hh
      refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_readC2, readC2_specializes⟩ ?_
      intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; subst hi
      refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_decC2, decC2_specializes⟩ ?_
      intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl
      · exact MemoryNodesOK.mk' ⟨rfl, rfl, bind_halt1_c2, halt1_c2_specializes⟩ (by simp)
      · refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_verifyC2, verifyC2_specializes⟩ ?_
        intro k hk; simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; subst hk
        exact MemoryNodesOK.mk' ⟨rfl, rfl, bind_halt0, halt0_specializes⟩ (by simp)
    · refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_readP, readP_specializes⟩ ?_
      intro h hh; simp only [List.mem_cons, List.not_mem_nil, or_false] at hh; subst hh
      refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_decP, decP_specializes⟩ ?_
      intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_verifyP, verifyP_specializes⟩ ?_
        intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; subst hj
        refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_readC1, readC1_specializes⟩ ?_
        intro k hk; simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; subst hk
        refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_decC1, decC1_specializes⟩ ?_
        intro l hl; simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl
        · exact MemoryNodesOK.mk' ⟨rfl, rfl, bind_halt1_c1, halt1_c1_specializes⟩ (by simp)
        · refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_verifyC1, verifyC1_specializes⟩ ?_
          intro m hm; simp only [List.mem_cons, List.not_mem_nil, or_false] at hm; subst hm
          exact MemoryNodesOK.mk' ⟨rfl, rfl, bind_halt5, halt5_specializes⟩ (by simp)
      · refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_decBranchD, decBranchD_specializes⟩ ?_
        intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl
        · exact MemoryNodesOK.mk' ⟨rfl, rfl, bind_halt1_d, halt1_d_specializes⟩ (by simp)
        · exact MemoryNodesOK.mk' ⟨rfl, rfl, bind_halt6_d, halt6_d_specializes⟩ (by simp)

/-! ## The committed skeleton is exactly `Op6Skeleton.semanticSkeleton` -/

theorem skeletonOfNodes_eq :
    skeletonOfNodes op6ComputeTree [op6MemTree] = Op6Skeleton.semanticSkeleton := by
  simp [skeletonOfNodes, op6ComputeTree, op6MemTree, mapNTree, Op6Skeleton.semanticSkeleton,
    Op6Skeleton.computeTree, parentNode, child1Node, child2Node,
    nReadF, nDecF, nHalt6, nVerifyF, nReadT, nDecT, nVerifyT,
    nReadC2, nDecC2, nHalt1_c2, nVerifyC2, nHalt0,
    nReadP, nDecP, nVerifyP, nReadC1, nDecC1, nHalt1_c1, nVerifyC1, nHalt5,
    nDecBranchD, nHalt1_d, nHalt6_d,
    Op6Skeleton.readFTree, Op6Skeleton.tDecF, Op6Skeleton.tHalt6, Op6Skeleton.tVerifyF,
    Op6Skeleton.tReadT, Op6Skeleton.tDecT, Op6Skeleton.tVerifyT,
    Op6Skeleton.tReadC2, Op6Skeleton.tDecC2, Op6Skeleton.tHalt1_c2,
    Op6Skeleton.tVerifyC2, Op6Skeleton.tHalt0,
    Op6Skeleton.tReadP, Op6Skeleton.tDecP, Op6Skeleton.tVerifyP,
    Op6Skeleton.tReadC1, Op6Skeleton.tDecC1, Op6Skeleton.tHalt1_c1,
    Op6Skeleton.tVerifyC1, Op6Skeleton.tHalt5,
    Op6Skeleton.tDecBranchD, Op6Skeleton.tHalt1_d, Op6Skeleton.tHalt6_d,
    Op6Skeleton.mLeaf, Op6Skeleton.mOne, Op6Skeleton.mTwo]

/-! ## The honest commitment -/

noncomputable def data
    (hfirst :
      ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.counts = 0 ∧
        ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.indicator = 0) :
    Data (Op6Execution hfirst) where
  computeNodes := op6ComputeTree
  memoryNodes := [op6MemTree]
  compute_rows := by
    show mapNTree ComputeNode.row op6ComputeTree = (exec seedZ alphaA).computeTree
    simp [op6ComputeTree, parentNode, child1Node, child2Node, mapNTree, exec, execA,
      computeTree]
  memory_rows := by
    show [op6MemTree].map (mapNTree MemoryNode.row) = (execA seedZ alphaA).memoryForest
    simp [op6MemTree, nReadF, nDecF, nHalt6, nVerifyF, nReadT, nDecT, nVerifyT,
      nReadC2, nDecC2, nHalt1_c2, nVerifyC2, nHalt0,
      nReadP, nDecP, nVerifyP, nReadC1, nDecC1, nHalt1_c1, nVerifyC1, nHalt5,
      nDecBranchD, nHalt1_d, nHalt6_d,
      mapNTree, exec, execA, rootTreeA, tDecFA, tHalt6, tVerifyFA, tReadTA, tDecTA, tVerifyTA,
      tReadC2A, tDecC2A, tHalt1_c2, tVerifyC2A, tHalt0,
      tReadPA, tDecPA, tVerifyPA, tReadC1A, tDecC1A, tHalt1_c1, tVerifyC1A, tHalt5,
      tDecBranchD, tHalt1_d, tHalt6_d,
      mLeaf, mOne, mTwo]
  computeOK := op6ComputeTree_OK
  memoryOK := by
    intro t ht
    simp only [List.mem_singleton] at ht
    subst ht
    exact op6MemTree_OK
  root_line_exponent := rfl
  root_line_origin := rfl
  nounSizeBound := 7
  Λ := 7
  slotSemantics := skeletonOfNodes_eq ▸ Op6Skeleton.slotSemantics
  recordEquations := skeletonOfNodes_eq ▸ Op6Skeleton.recordEquations
  census := skeletonOfNodes_eq ▸ Op6Skeleton.census
  sizeWindowBound := skeletonOfNodes_eq ▸ Op6Skeleton.sizeWindowBound
  q_eq_ringChar := by show (97 : ℕ) = ringChar K; exact ringChar_K3.symm
  skeletonBounded := skeletonOfNodes_eq ▸ Op6Skeleton.skeletonBounded
  combinedBounded := skeletonOfNodes_eq ▸ Op6Skeleton.combinedBounded

theorem data_skeleton
    (hfirst :
      ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.counts = 0 ∧
        ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.indicator = 0) :
    (data hfirst).skeleton = Op6Skeleton.semanticSkeleton :=
  skeletonOfNodes_eq

end Nock.NockVMROM.Thm54.TraceGen.Op6ConfigK3

#print axioms Nock.NockVMROM.Thm54.TraceGen.Op6ConfigK3.Op6Execution
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op6ConfigK3.data
