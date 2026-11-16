/-
  Nock/NockVMROM/Thm54/TraceGen/Op2DataK3.lean

  Stage 3 of the OP2 Layer-2 CORE, over `K3`: the assembled
  `Op2Execution : BuildableNockExecution (ZMod 97) K3` — all fourteen fields —
  and the directly-built literal-node commitment `HonestCommitment.Data Op2Execution`
  for the fan-out-3 eval program

      `*[0 [2 [1 [0 1]] [1 [1 5]]]] = 5`

  The two semantic-CORE fields come from `Op2SemanticDataK3` / `Op2MemoryTraceK3`;
  the twelve non-semantic fields from `Op2BuildablePartsK3`.  The six census
  obligations are transported from `Op2Skeleton` along `skeletonOfNodes_eq`.
  `Λ = 7` (the parent formula has seven atoms)
-/
import Nock.NockVMROM.Thm54.TraceGen.Op2MemoryTraceK3
import Nock.NockVMROM.Thm54.TraceGen.Op2SkeletonK3
import Nock.NockVMROM.Thm54.HonestCommitment

namespace Nock.NockVMROM.Thm54.TraceGen.Op2ConfigK3

open Nock Nock.Walk Nock.ComputeTable Nock.MemoryTable
open Nock.NockVMROM.Thm54
open SemanticStrategy
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.TraceGen.Op2Skeleton
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
  (ComputeTimestampSpecializesAt MemoryTimestampSpecializesAt)

set_option linter.unusedSimpArgs false

/-! ## The assembled buildable execution -/

/-- The OP2/K3 slice's complete `BuildableNockExecution` — all fourteen fields explicitly named. -/
noncomputable def Op2Execution
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
    BindComputeRow seedZ Op2Skeleton.parentRow (parentRow seedZ alphaA) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro slot
    cases slot <;>
      simp [decActive, hasTailDecomposition, decFP, bindFP, fp,
        Op2Skeleton.parentRow, parentRow, parentDec, op2Head, Op2Skeleton.op2Head]
  · intro i
    fin_cases i
    · rw [dif_pos (by decide)]
      intro slot
      cases slot <;>
        simp [Op2Skeleton.parentRow, computeSubformulaFPs, ComputeTable.sfTriple,
          parentRow, parentPub, tripleFP, bindFP, fp]
    · rw [dif_pos (by decide)]
      intro slot
      cases slot <;>
        simp [Op2Skeleton.parentRow, computeSubformulaFPs, ComputeTable.sfTriple,
          parentRow, parentPub, tripleFP, bindFP, fp]
    · rw [dif_pos (by decide)]
      intro slot
      cases slot <;>
        simp [Op2Skeleton.parentRow, computeSubformulaFPs, ComputeTable.sfTriple,
          parentRow, parentPub, tripleFP, bindFP, fp]
  · intro i
    fin_cases i
    · rw [dif_pos (by decide)]
      exact ⟨rfl, rfl, rfl⟩
    · rw [dif_pos (by decide)]
      exact ⟨rfl, rfl, rfl⟩
    · rw [dif_neg (by decide)]
      simp [computeMemRec, parentRow, parentPub, MemRec.zero]

theorem bind_child1Row :
    BindComputeRow seedZ Op2Skeleton.child1Row (child1Row seedZ alphaA) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro slot
    cases slot <;>
      simp [decActive, hasTailDecomposition, decFP, bindFP, fp,
        Op2Skeleton.child1Row, Op2Skeleton.op1Row, child1Row, op1DecOf,
        op1Head, Op2Skeleton.op1Head]
  · intro i
    have hi : ¬ ((i : ℕ) < ComputeTable.fanoutComp Op2Skeleton.child1Row.state) := by
      simp [Op2Skeleton.child1Row, Op2Skeleton.op1Row, ComputeTable.fanoutComp]
    rw [dif_neg hi]
    fin_cases i <;>
      simp [computeSubformulaFPs, ComputeTable.sfTriple, child1Row, child1Pub, op1PubOf]
  · intro i
    fin_cases i
    · exact ⟨rfl, rfl, rfl⟩
    · rfl
    · rfl

theorem bind_child2Row :
    BindComputeRow seedZ Op2Skeleton.child2Row (child2Row seedZ alphaA) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro slot
    cases slot <;>
      simp [decActive, hasTailDecomposition, decFP, bindFP, fp,
        Op2Skeleton.child2Row, Op2Skeleton.op1Row, child2Row, op1DecOf,
        op1Head, Op2Skeleton.op1Head]
  · intro i
    have hi : ¬ ((i : ℕ) < ComputeTable.fanoutComp Op2Skeleton.child2Row.state) := by
      simp [Op2Skeleton.child2Row, Op2Skeleton.op1Row, ComputeTable.fanoutComp]
    rw [dif_neg hi]
    fin_cases i <;>
      simp [computeSubformulaFPs, ComputeTable.sfTriple, child2Row, child2Pub, op1PubOf]
  · intro i
    fin_cases i
    · exact ⟨rfl, rfl, rfl⟩
    · rfl
    · rfl

theorem bind_child3Row :
    BindComputeRow seedZ Op2Skeleton.child3Row (child3Row seedZ alphaA) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro slot
    cases slot <;>
      simp [decActive, hasTailDecomposition, decFP, bindFP, fp,
        Op2Skeleton.child3Row, Op2Skeleton.op1Row, child3Row, op1DecOf,
        op1Head, Op2Skeleton.op1Head]
  · intro i
    have hi : ¬ ((i : ℕ) < ComputeTable.fanoutComp Op2Skeleton.child3Row.state) := by
      simp [Op2Skeleton.child3Row, Op2Skeleton.op1Row, ComputeTable.fanoutComp]
    rw [dif_neg hi]
    fin_cases i <;>
      simp [computeSubformulaFPs, ComputeTable.sfTriple, child3Row, child3Pub, op1PubOf]
  · intro i
    fin_cases i
    · exact ⟨rfl, rfl, rfl⟩
    · rfl
    · rfl

/-! ### Memory-row bindings -/

theorem bind_readF :
    BindMemoryRowA seedZ Op2Skeleton.skReadF (lblOf seedZ (pReadFA seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i
    · rfl
    · simp [Op2Skeleton.skReadF, Op2Skeleton.readRow, MemoryTable.fanoutMem,
        memoryChildCell, lblOf, pReadFA, readPub]
  · exact ⟨rfl, rfl, rfl⟩

theorem bind_decF :
    BindMemoryRowA seedZ Op2Skeleton.skDecF (lblOf seedZ (pDecF seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i <;> rfl
  · rfl

theorem bind_halt2 :
    BindMemoryRowA seedZ Op2Skeleton.skHalt2 (lblOf seedZ (pHalt2 seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, rfl⟩
  · simp [Op2Skeleton.skHalt2, Op2Skeleton.haltRow, lblOf, pHalt2, haltPub, bindFP, fp]
  · intro i
    have hi : ¬ ((i : ℕ) < MemoryTable.fanoutMem Op2Skeleton.skHalt2.state) := by
      simp [Op2Skeleton.skHalt2, Op2Skeleton.haltRow, MemoryTable.fanoutMem]
    rw [dif_neg hi]
    fin_cases i <;> rfl
  · rfl

theorem bind_verifyF :
    BindMemoryRowA seedZ Op2Skeleton.skVerifyF (lblOf seedZ (pVerifyFA seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i
    · rfl
    · simp [Op2Skeleton.skVerifyF, Op2Skeleton.verifyRow, MemoryTable.fanoutMem,
        memoryChildCell, lblOf, pVerifyFA, verifyPub]
  · exact ⟨rfl, rfl, rfl⟩

theorem bind_readT :
    BindMemoryRowA seedZ Op2Skeleton.skReadT (lblOf seedZ (pReadTA seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i
    · rfl
    · simp [Op2Skeleton.skReadT, Op2Skeleton.readRow, MemoryTable.fanoutMem,
        memoryChildCell, lblOf, pReadTA, readPub]
  · exact ⟨rfl, rfl, rfl⟩

theorem bind_decT :
    BindMemoryRowA seedZ Op2Skeleton.skDecT (lblOf seedZ (pDecT seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i <;> rfl
  · rfl

theorem bind_verifyT :
    BindMemoryRowA seedZ Op2Skeleton.skVerifyT (lblOf seedZ (pVerifyTA seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i
    · rfl
    · simp [Op2Skeleton.skVerifyT, Op2Skeleton.verifyRow, MemoryTable.fanoutMem,
        memoryChildCell, lblOf, pVerifyTA, verifyPub]
  · exact ⟨rfl, rfl, rfl⟩

theorem bind_readC :
    BindMemoryRowA seedZ Op2Skeleton.skReadC (lblOf seedZ (pReadCA seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i
    · rfl
    · simp [Op2Skeleton.skReadC, Op2Skeleton.readRow, MemoryTable.fanoutMem,
        memoryChildCell, lblOf, pReadCA, readPub]
  · exact ⟨rfl, rfl, rfl⟩

theorem bind_readB :
    BindMemoryRowA seedZ Op2Skeleton.skReadB (lblOf seedZ (pReadBA seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i
    · rfl
    · simp [Op2Skeleton.skReadB, Op2Skeleton.readRow, MemoryTable.fanoutMem,
        memoryChildCell, lblOf, pReadBA, readPub]
  · exact ⟨rfl, rfl, rfl⟩

theorem bind_decC :
    BindMemoryRowA seedZ Op2Skeleton.skDecC (lblOf seedZ (pDecC seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i <;> rfl
  · rfl

theorem bind_decB :
    BindMemoryRowA seedZ Op2Skeleton.skDecB (lblOf seedZ (pDecB seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i <;> rfl
  · rfl

theorem bind_haltC1 :
    BindMemoryRowA seedZ Op2Skeleton.skHaltC1 (lblOf seedZ (pHaltC1 seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, rfl⟩
  · simp [Op2Skeleton.skHaltC1, Op2Skeleton.haltRow, lblOf, pHaltC1, haltPub, bindFP, fp]
  · intro i
    have hi : ¬ ((i : ℕ) < MemoryTable.fanoutMem Op2Skeleton.skHaltC1.state) := by
      simp [Op2Skeleton.skHaltC1, Op2Skeleton.haltRow, MemoryTable.fanoutMem]
    rw [dif_neg hi]
    fin_cases i <;> rfl
  · rfl

theorem bind_verifyC :
    BindMemoryRowA seedZ Op2Skeleton.skVerifyC (lblOf seedZ (pVerifyCA seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i
    · rfl
    · simp [Op2Skeleton.skVerifyC, Op2Skeleton.verifyRow, MemoryTable.fanoutMem,
        memoryChildCell, lblOf, pVerifyCA, verifyPub]
  · exact ⟨rfl, rfl, rfl⟩

theorem bind_haltB1 :
    BindMemoryRowA seedZ Op2Skeleton.skHaltB1 (lblOf seedZ (pHaltB1 seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, rfl⟩
  · simp [Op2Skeleton.skHaltB1, Op2Skeleton.haltRow, lblOf, pHaltB1, haltPub, bindFP, fp]
  · intro i
    have hi : ¬ ((i : ℕ) < MemoryTable.fanoutMem Op2Skeleton.skHaltB1.state) := by
      simp [Op2Skeleton.skHaltB1, Op2Skeleton.haltRow, MemoryTable.fanoutMem]
    rw [dif_neg hi]
    fin_cases i <;> rfl
  · rfl

theorem bind_verifyB :
    BindMemoryRowA seedZ Op2Skeleton.skVerifyB (lblOf seedZ (pVerifyBA seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i
    · rfl
    · simp [Op2Skeleton.skVerifyB, Op2Skeleton.verifyRow, MemoryTable.fanoutMem,
        memoryChildCell, lblOf, pVerifyBA, verifyPub]
  · exact ⟨rfl, rfl, rfl⟩

theorem bind_readS :
    BindMemoryRowA seedZ Op2Skeleton.skReadS (lblOf seedZ (pReadSA seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i
    · rfl
    · simp [Op2Skeleton.skReadS, Op2Skeleton.readRow, MemoryTable.fanoutMem,
        memoryChildCell, lblOf, pReadSA, readPub]
  · exact ⟨rfl, rfl, rfl⟩

theorem bind_decSf1 :
    BindMemoryRowA seedZ Op2Skeleton.skDecSf1 (lblOf seedZ (pDecSf1 seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i <;> rfl
  · rfl

theorem bind_decS :
    BindMemoryRowA seedZ Op2Skeleton.skDecS (lblOf seedZ (pDecS seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i <;> rfl
  · rfl

theorem bind_halt0 :
    BindMemoryRowA seedZ Op2Skeleton.skHalt0 (lblOf seedZ (pHalt0 seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, rfl⟩
  · simp [Op2Skeleton.skHalt0, Op2Skeleton.haltRow, lblOf, pHalt0, haltPub, bindFP, fp]
  · intro i
    have hi : ¬ ((i : ℕ) < MemoryTable.fanoutMem Op2Skeleton.skHalt0.state) := by
      simp [Op2Skeleton.skHalt0, Op2Skeleton.haltRow, MemoryTable.fanoutMem]
    rw [dif_neg hi]
    fin_cases i <;> rfl
  · rfl

theorem bind_halt1s :
    BindMemoryRowA seedZ Op2Skeleton.skHalt1s (lblOf seedZ (pHalt1s seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, rfl⟩
  · simp [Op2Skeleton.skHalt1s, Op2Skeleton.haltRow, lblOf, pHalt1s, haltPub, bindFP, fp]
  · intro i
    have hi : ¬ ((i : ℕ) < MemoryTable.fanoutMem Op2Skeleton.skHalt1s.state) := by
      simp [Op2Skeleton.skHalt1s, Op2Skeleton.haltRow, MemoryTable.fanoutMem]
    rw [dif_neg hi]
    fin_cases i <;> rfl
  · rfl

theorem bind_haltS1 :
    BindMemoryRowA seedZ Op2Skeleton.skHaltS1 (lblOf seedZ (pHaltS1 seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, rfl⟩
  · simp [Op2Skeleton.skHaltS1, Op2Skeleton.haltRow, lblOf, pHaltS1, haltPub, bindFP, fp]
  · intro i
    have hi : ¬ ((i : ℕ) < MemoryTable.fanoutMem Op2Skeleton.skHaltS1.state) := by
      simp [Op2Skeleton.skHaltS1, Op2Skeleton.haltRow, MemoryTable.fanoutMem]
    rw [dif_neg hi]
    fin_cases i <;> rfl
  · rfl

theorem bind_verifyS :
    BindMemoryRowA seedZ Op2Skeleton.skVerifyS (lblOf seedZ (pVerifySA seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i
    · rfl
    · simp [Op2Skeleton.skVerifyS, Op2Skeleton.verifyRow, MemoryTable.fanoutMem,
        memoryChildCell, lblOf, pVerifySA, verifyPub]
  · exact ⟨rfl, rfl, rfl⟩

theorem bind_halt5 :
    BindMemoryRowA seedZ Op2Skeleton.skHalt5 (lblOf seedZ (pHalt5 seedZ)) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, rfl⟩
  · simp [Op2Skeleton.skHalt5, Op2Skeleton.haltRow, lblOf, pHalt5, haltPub, bindFP, fp]
  · intro i
    have hi : ¬ ((i : ℕ) < MemoryTable.fanoutMem Op2Skeleton.skHalt5.state) := by
      simp [Op2Skeleton.skHalt5, Op2Skeleton.haltRow, MemoryTable.fanoutMem]
    rw [dif_neg hi]
    fin_cases i <;> rfl
  · rfl

/-! ## The literal committed node trees -/

noncomputable def parentNode : ComputeNode K where
  skel := Op2Skeleton.parentRow
  stamp :=
    { state := .s2
      lnPrevExponent := 0
      lnExponent := 2
      recordExponent := fun
        | 0 => 1
        | 1 => 2
        | _ => 0 }
  row := parentRow seedZ alphaA

noncomputable def child1Node : ComputeNode K where
  skel := Op2Skeleton.child1Row
  stamp := { state := .s1, lnPrevExponent := 2, lnExponent := 3, recordExponent := fun _ => 3 }
  row := child1Row seedZ alphaA

noncomputable def child2Node : ComputeNode K where
  skel := Op2Skeleton.child2Row
  stamp := { state := .s1, lnPrevExponent := 3, lnExponent := 4, recordExponent := fun _ => 4 }
  row := child2Row seedZ alphaA

noncomputable def child3Node : ComputeNode K where
  skel := Op2Skeleton.child3Row
  stamp := { state := .s1, lnPrevExponent := 4, lnExponent := 5, recordExponent := fun _ => 5 }
  row := child3Row seedZ alphaA

noncomputable def op2ComputeTree : NTree (ComputeNode K) :=
  .node parentNode [.node child1Node [], .node child2Node [], .node child3Node []]

noncomputable def nReadF : MemoryNode K where
  skel := Op2Skeleton.skReadF
  stamp := { state := .read_root, recordExponent := 1 }
  row := lblOf seedZ (pReadFA seedZ alphaA)
noncomputable def nDecF : MemoryNode K where
  skel := Op2Skeleton.skDecF
  stamp := { state := .decompose, recordExponent := 0 }
  row := lblOf seedZ (pDecF seedZ alphaA)
noncomputable def nHalt2 : MemoryNode K where
  skel := Op2Skeleton.skHalt2
  stamp := { state := .halt, recordExponent := 0 }
  row := lblOf seedZ (pHalt2 seedZ alphaA)
noncomputable def nVerifyF : MemoryNode K where
  skel := Op2Skeleton.skVerifyF
  stamp := { state := .verify_child, recordExponent := 1 }
  row := lblOf seedZ (pVerifyFA seedZ alphaA)
noncomputable def nReadT : MemoryNode K where
  skel := Op2Skeleton.skReadT
  stamp := { state := .read_root, recordExponent := 2 }
  row := lblOf seedZ (pReadTA seedZ alphaA)
noncomputable def nDecT : MemoryNode K where
  skel := Op2Skeleton.skDecT
  stamp := { state := .decompose, recordExponent := 0 }
  row := lblOf seedZ (pDecT seedZ alphaA)
noncomputable def nVerifyT : MemoryNode K where
  skel := Op2Skeleton.skVerifyT
  stamp := { state := .verify_child, recordExponent := 2 }
  row := lblOf seedZ (pVerifyTA seedZ alphaA)
noncomputable def nReadC : MemoryNode K where
  skel := Op2Skeleton.skReadC
  stamp := { state := .read_root, recordExponent := 4 }
  row := lblOf seedZ (pReadCA seedZ alphaA)
noncomputable def nReadB : MemoryNode K where
  skel := Op2Skeleton.skReadB
  stamp := { state := .read_root, recordExponent := 3 }
  row := lblOf seedZ (pReadBA seedZ alphaA)
noncomputable def nDecC : MemoryNode K where
  skel := Op2Skeleton.skDecC
  stamp := { state := .decompose, recordExponent := 0 }
  row := lblOf seedZ (pDecC seedZ alphaA)
noncomputable def nDecB : MemoryNode K where
  skel := Op2Skeleton.skDecB
  stamp := { state := .decompose, recordExponent := 0 }
  row := lblOf seedZ (pDecB seedZ alphaA)
noncomputable def nHaltC1 : MemoryNode K where
  skel := Op2Skeleton.skHaltC1
  stamp := { state := .halt, recordExponent := 0 }
  row := lblOf seedZ (pHaltC1 seedZ alphaA)
noncomputable def nVerifyC : MemoryNode K where
  skel := Op2Skeleton.skVerifyC
  stamp := { state := .verify_child, recordExponent := 4 }
  row := lblOf seedZ (pVerifyCA seedZ alphaA)
noncomputable def nHaltB1 : MemoryNode K where
  skel := Op2Skeleton.skHaltB1
  stamp := { state := .halt, recordExponent := 0 }
  row := lblOf seedZ (pHaltB1 seedZ alphaA)
noncomputable def nVerifyB : MemoryNode K where
  skel := Op2Skeleton.skVerifyB
  stamp := { state := .verify_child, recordExponent := 3 }
  row := lblOf seedZ (pVerifyBA seedZ alphaA)
noncomputable def nReadS : MemoryNode K where
  skel := Op2Skeleton.skReadS
  stamp := { state := .read_root, recordExponent := 5 }
  row := lblOf seedZ (pReadSA seedZ alphaA)
noncomputable def nDecSf1 : MemoryNode K where
  skel := Op2Skeleton.skDecSf1
  stamp := { state := .decompose, recordExponent := 0 }
  row := lblOf seedZ (pDecSf1 seedZ alphaA)
noncomputable def nDecS : MemoryNode K where
  skel := Op2Skeleton.skDecS
  stamp := { state := .decompose, recordExponent := 0 }
  row := lblOf seedZ (pDecS seedZ alphaA)
noncomputable def nHalt0 : MemoryNode K where
  skel := Op2Skeleton.skHalt0
  stamp := { state := .halt, recordExponent := 0 }
  row := lblOf seedZ (pHalt0 seedZ alphaA)
noncomputable def nHalt1s : MemoryNode K where
  skel := Op2Skeleton.skHalt1s
  stamp := { state := .halt, recordExponent := 0 }
  row := lblOf seedZ (pHalt1s seedZ alphaA)
noncomputable def nHaltS1 : MemoryNode K where
  skel := Op2Skeleton.skHaltS1
  stamp := { state := .halt, recordExponent := 0 }
  row := lblOf seedZ (pHaltS1 seedZ alphaA)
noncomputable def nVerifyS : MemoryNode K where
  skel := Op2Skeleton.skVerifyS
  stamp := { state := .verify_child, recordExponent := 5 }
  row := lblOf seedZ (pVerifySA seedZ alphaA)
noncomputable def nHalt5 : MemoryNode K where
  skel := Op2Skeleton.skHalt5
  stamp := { state := .halt, recordExponent := 0 }
  row := lblOf seedZ (pHalt5 seedZ)

/-- The committed memory node tree, matching `rootTree seedZ alphaA`'s topology. -/
noncomputable def op2MemTree : NTree (MemoryNode K) :=
  .node nReadF
    [.node nDecF
      [.node nHalt2 [],
       .node nVerifyF
         [.node nReadT
           [.node nDecT
             [.node nVerifyT
               [.node nReadB
                 [.node nDecB
                   [.node nHaltB1 [],
                    .node nVerifyB
                      [.node nDecSf1 [.node nHalt0 [], .node nHalt1s []]]]]],
              .node nReadC
                [.node nDecC
                  [.node nHaltC1 [],
                   .node nVerifyC
                     [.node nReadS
                       [.node nDecS
                         [.node nHaltS1 [],
                          .node nVerifyS [.node nHalt5 []]]]]]]]]]]]

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

theorem child3_specializes :
    ComputeTimestampSpecializesAt alphaA child3Node.stamp (child3Row seedZ alphaA) := by
  refine ComputeTimestampSpecializesAt.of_absolute rfl rfl rfl ?_ ?_ ?_ ?_
    (by decide) (fun i => by fin_cases i <;> decide)
  · show (child3Pub seedZ alphaA).ln_prev = alphaA ^ 4
    simp [child3Pub, op1PubOf, pow_succ, pow_two]
  · show (child3Pub seedZ alphaA).ln = alphaA ^ 5
    simp [child3Pub, op1PubOf, pow_succ, pow_two]
  · intro i
    fin_cases i <;>
      simp [child3Node, computeMemRec, computeMemRecKind, Nock.Framework.recordCount,
        child3Row, child3Pub, op1PubOf, recS, MemRec.zero]
  · intro i hi
    fin_cases i <;>
      simp_all [child3Node, computeMemRec, computeMemRecKind, Nock.Framework.recordCount,
        child3Row, child3Pub, op1PubOf, MemRec.zero]

theorem readF_specializes :
    MemoryTimestampSpecializesAt alphaA nReadF.stamp (lblOf seedZ (pReadFA seedZ alphaA)) :=
  ⟨rfl, rfl, by simp [nReadF, memoryMemRecKind, lblOf, pReadFA, readPub, recF, pow_one],
    by simp [nReadF, memoryMemRecKind]⟩
theorem decF_specializes :
    MemoryTimestampSpecializesAt alphaA nDecF.stamp (lblOf seedZ (pDecF seedZ alphaA)) :=
  ⟨rfl, rfl, by simp [nDecF, memoryMemRecKind, lblOf, pDecF, decPub, MemRec.zero],
    by simp [nDecF, memoryMemRecKind, lblOf, pDecF, decPub, MemRec.zero]⟩
theorem halt2_specializes :
    MemoryTimestampSpecializesAt alphaA nHalt2.stamp (lblOf seedZ (pHalt2 seedZ alphaA)) :=
  ⟨rfl, rfl, by simp [nHalt2, memoryMemRecKind, lblOf, pHalt2, haltPub, MemRec.zero],
    by simp [nHalt2, memoryMemRecKind, lblOf, pHalt2, haltPub, MemRec.zero]⟩
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
theorem readS_specializes :
    MemoryTimestampSpecializesAt alphaA nReadS.stamp (lblOf seedZ (pReadSA seedZ alphaA)) :=
  ⟨rfl, rfl, by simp [nReadS, memoryMemRecKind, lblOf, pReadSA, readPub, recS],
    by simp [nReadS, memoryMemRecKind]⟩
theorem decSf1_specializes :
    MemoryTimestampSpecializesAt alphaA nDecSf1.stamp (lblOf seedZ (pDecSf1 seedZ alphaA)) :=
  ⟨rfl, rfl, by simp [nDecSf1, memoryMemRecKind, lblOf, pDecSf1, decPub, MemRec.zero],
    by simp [nDecSf1, memoryMemRecKind, lblOf, pDecSf1, decPub, MemRec.zero]⟩
theorem decS_specializes :
    MemoryTimestampSpecializesAt alphaA nDecS.stamp (lblOf seedZ (pDecS seedZ alphaA)) :=
  ⟨rfl, rfl, by simp [nDecS, memoryMemRecKind, lblOf, pDecS, decPub, MemRec.zero],
    by simp [nDecS, memoryMemRecKind, lblOf, pDecS, decPub, MemRec.zero]⟩
theorem halt0_specializes :
    MemoryTimestampSpecializesAt alphaA nHalt0.stamp (lblOf seedZ (pHalt0 seedZ alphaA)) :=
  ⟨rfl, rfl, by simp [nHalt0, memoryMemRecKind, lblOf, pHalt0, haltPub, MemRec.zero],
    by simp [nHalt0, memoryMemRecKind, lblOf, pHalt0, haltPub, MemRec.zero]⟩
theorem halt1s_specializes :
    MemoryTimestampSpecializesAt alphaA nHalt1s.stamp (lblOf seedZ (pHalt1s seedZ alphaA)) :=
  ⟨rfl, rfl, by simp [nHalt1s, memoryMemRecKind, lblOf, pHalt1s, haltPub, MemRec.zero],
    by simp [nHalt1s, memoryMemRecKind, lblOf, pHalt1s, haltPub, MemRec.zero]⟩
theorem haltS1_specializes :
    MemoryTimestampSpecializesAt alphaA nHaltS1.stamp (lblOf seedZ (pHaltS1 seedZ alphaA)) :=
  ⟨rfl, rfl, by simp [nHaltS1, memoryMemRecKind, lblOf, pHaltS1, haltPub, MemRec.zero],
    by simp [nHaltS1, memoryMemRecKind, lblOf, pHaltS1, haltPub, MemRec.zero]⟩
theorem verifyS_specializes :
    MemoryTimestampSpecializesAt alphaA nVerifyS.stamp (lblOf seedZ (pVerifySA seedZ alphaA)) :=
  ⟨rfl, rfl, by simp [nVerifyS, memoryMemRecKind, lblOf, pVerifySA, verifyPub, recS],
    by simp [nVerifyS, memoryMemRecKind]⟩
theorem halt5_specializes :
    MemoryTimestampSpecializesAt alphaA nHalt5.stamp (lblOf seedZ (pHalt5 seedZ)) :=
  ⟨rfl, rfl, by simp [nHalt5, memoryMemRecKind, lblOf, pHalt5, haltPub, MemRec.zero],
    by simp [nHalt5, memoryMemRecKind, lblOf, pHalt5, haltPub, MemRec.zero]⟩

/-! ## Local node validity -/

theorem op2ComputeTree_OK :
    ComputeNodesOK seedZ alphaA op2ComputeTree := by
  refine ComputeNodesOK.mk' ⟨?_, rfl, bind_parentRow, parent_specializes⟩ ?_
  · simp [parentNode, Op2Skeleton.parentRow, ComputeTable.fanoutComp]
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact ComputeNodesOK.mk' ⟨by simp [child1Node, Op2Skeleton.child1Row, Op2Skeleton.op1Row,
        ComputeTable.fanoutComp], rfl, bind_child1Row, child1_specializes⟩ (by simp)
    · exact ComputeNodesOK.mk' ⟨by simp [child2Node, Op2Skeleton.child2Row, Op2Skeleton.op1Row,
        ComputeTable.fanoutComp], rfl, bind_child2Row, child2_specializes⟩ (by simp)
    · exact ComputeNodesOK.mk' ⟨by simp [child3Node, Op2Skeleton.child3Row, Op2Skeleton.op1Row,
        ComputeTable.fanoutComp], rfl, bind_child3Row, child3_specializes⟩ (by simp)

theorem op2MemTree_OK :
    MemoryNodesOK seedZ alphaA op2MemTree := by
  refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_readF, readF_specializes⟩ ?_
  intro c hc; simp only [List.mem_cons, List.not_mem_nil, or_false] at hc; subst hc
  refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_decF, decF_specializes⟩ ?_
  intro d hd; simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl
  · exact MemoryNodesOK.mk' ⟨rfl, rfl, bind_halt2, halt2_specializes⟩ (by simp)
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
        refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_decSf1, decSf1_specializes⟩ ?_
        intro l hl; simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl
        · exact MemoryNodesOK.mk' ⟨rfl, rfl, bind_halt0, halt0_specializes⟩ (by simp)
        · exact MemoryNodesOK.mk' ⟨rfl, rfl, bind_halt1s, halt1s_specializes⟩ (by simp)
    · refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_readC, readC_specializes⟩ ?_
      intro h hh; simp only [List.mem_cons, List.not_mem_nil, or_false] at hh; subst hh
      refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_decC, decC_specializes⟩ ?_
      intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact MemoryNodesOK.mk' ⟨rfl, rfl, bind_haltC1, haltC1_specializes⟩ (by simp)
      · refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_verifyC, verifyC_specializes⟩ ?_
        intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; subst hj
        refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_readS, readS_specializes⟩ ?_
        intro k hk; simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; subst hk
        refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_decS, decS_specializes⟩ ?_
        intro l hl; simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl
        · exact MemoryNodesOK.mk' ⟨rfl, rfl, bind_haltS1, haltS1_specializes⟩ (by simp)
        · refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_verifyS, verifyS_specializes⟩ ?_
          intro m hm; simp only [List.mem_cons, List.not_mem_nil, or_false] at hm; subst hm
          exact MemoryNodesOK.mk' ⟨rfl, rfl, bind_halt5, halt5_specializes⟩ (by simp)

/-! ## The committed skeleton is exactly `Op2Skeleton.semanticSkeleton` -/

theorem skeletonOfNodes_eq :
    skeletonOfNodes op2ComputeTree [op2MemTree] = Op2Skeleton.semanticSkeleton := by
  simp [skeletonOfNodes, op2ComputeTree, op2MemTree, mapNTree, Op2Skeleton.semanticSkeleton,
    Op2Skeleton.computeTree, parentNode, child1Node, child2Node, child3Node,
    nReadF, nDecF, nHalt2, nVerifyF, nReadT, nDecT, nVerifyT, nReadC, nReadB, nDecC, nDecB,
    nHaltC1, nVerifyC, nHaltB1, nVerifyB, nReadS, nDecSf1, nDecS, nHalt0, nHalt1s, nHaltS1,
    nVerifyS, nHalt5, Op2Skeleton.readFTree, Op2Skeleton.tDecF, Op2Skeleton.tHalt2,
    Op2Skeleton.tVerifyF, Op2Skeleton.tReadT, Op2Skeleton.tDecT, Op2Skeleton.tVerifyT,
    Op2Skeleton.tReadC, Op2Skeleton.tReadB, Op2Skeleton.tDecC, Op2Skeleton.tDecB,
    Op2Skeleton.tHaltC1, Op2Skeleton.tVerifyC, Op2Skeleton.tHaltB1, Op2Skeleton.tVerifyB,
    Op2Skeleton.tReadS, Op2Skeleton.tDecSf1, Op2Skeleton.tDecS, Op2Skeleton.tHalt0,
    Op2Skeleton.tHalt1s, Op2Skeleton.tHaltS1, Op2Skeleton.tVerifyS, Op2Skeleton.tHalt5,
    Op2Skeleton.mLeaf, Op2Skeleton.mOne, Op2Skeleton.mTwo]

/-! ## The honest commitment -/

/-- The directly-built honest commitment of the OP2/K3 slice: the literal four-node
compute tree and twenty-three-node memory tree.  Census obligations are transported
from `Op2Skeleton`. -/
noncomputable def data
    (hfirst :
      ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.counts = 0 ∧
        ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.indicator = 0) :
    Data (Op2Execution hfirst) where
  computeNodes := op2ComputeTree
  memoryNodes := [op2MemTree]
  compute_rows := by
    show mapNTree ComputeNode.row op2ComputeTree = (exec seedZ alphaA).computeTree
    simp [op2ComputeTree, parentNode, child1Node, child2Node, child3Node, mapNTree, exec, execA,
      computeTree]
  memory_rows := by
    show [op2MemTree].map (mapNTree MemoryNode.row) = (execA seedZ alphaA).memoryForest
    simp [op2MemTree, nReadF, nDecF, nHalt2, nVerifyF, nReadT, nDecT, nVerifyT, nReadC,
      nReadB, nDecC, nDecB, nHaltC1, nVerifyC, nHaltB1, nVerifyB, nReadS, nDecSf1, nDecS,
      nHalt0, nHalt1s, nHaltS1, nVerifyS, nHalt5, mapNTree, exec, execA, rootTreeA, tDecFA, tHalt2,
      tVerifyFA, tReadTA, tDecTA, tVerifyTA, tReadCA, tReadBA, tDecCA, tDecBA, tHaltC1, tVerifyCA,
      tHaltB1, tVerifyBA, tReadSA, tDecSf1, tDecSA, tHalt0, tHalt1s, tHaltS1, tVerifySA, tHalt5,
      mLeaf, mOne, mTwo]
  computeOK := op2ComputeTree_OK
  memoryOK := by
    intro t ht
    simp only [List.mem_singleton] at ht
    subst ht
    exact op2MemTree_OK
  root_line_exponent := rfl
  root_line_origin := rfl
  nounSizeBound := 7
  Λ := 7
  slotSemantics := skeletonOfNodes_eq ▸ Op2Skeleton.slotSemantics
  recordEquations := skeletonOfNodes_eq ▸ Op2Skeleton.recordEquations
  census := skeletonOfNodes_eq ▸ Op2Skeleton.census
  sizeWindowBound := skeletonOfNodes_eq ▸ Op2Skeleton.sizeWindowBound
  q_eq_ringChar := by show (97 : ℕ) = ringChar K; exact ringChar_K3.symm
  skeletonBounded := skeletonOfNodes_eq ▸ Op2Skeleton.skeletonBounded
  combinedBounded := skeletonOfNodes_eq ▸ Op2Skeleton.combinedBounded

/-- The committed skeleton this commitment derives is exactly the OP2 committed skeleton. -/
theorem data_skeleton
    (hfirst :
      ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.counts = 0 ∧
        ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.indicator = 0) :
    (data hfirst).skeleton = Op2Skeleton.semanticSkeleton :=
  skeletonOfNodes_eq

end Nock.NockVMROM.Thm54.TraceGen.Op2ConfigK3

#print axioms Nock.NockVMROM.Thm54.TraceGen.Op2ConfigK3.Op2Execution
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op2ConfigK3.data
