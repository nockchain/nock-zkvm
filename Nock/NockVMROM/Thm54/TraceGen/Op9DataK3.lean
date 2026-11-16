/-
  Nock/NockVMROM/Thm54/TraceGen/Op9DataK3.lean

  Stage 3 of the OP9 Layer-2 CORE, over `K3`: the assembled
  `Op9Execution : BuildableNockExecution (ZMod 97) K3` — all fourteen fields —
  and the directly-built literal-node commitment `HonestCommitment.Data Op9Execution`
  for the fan-out-2 invoke program

      `*[[[1 7] [1 9]] [9 2 [1 [[1 7] [1 9]]]]] = 7`

  The two semantic-CORE fields come from `Op9LanguageK3` (`semanticData`, `memoryTraceFinal`);
  the twelve non-semantic fields from `Op9BuildablePartsK3`.  The six census
  obligations are transported from `Op9Skeleton` along `skeletonOfNodes_eq`.
  `Λ = 7` (the parent formula has seven atoms)
-/
import Nock.NockVMROM.Thm54.TraceGen.Op9LanguageK3
import Nock.NockVMROM.Thm54.TraceGen.Op9SkeletonK3
import Nock.NockVMROM.Thm54.HonestCommitment

namespace Nock.NockVMROM.Thm54.TraceGen.Op9ConfigK3

open Nock Nock.Walk Nock.ComputeTable Nock.MemoryTable
open Nock.NockVMROM.Thm54
open SemanticStrategy
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.TraceGen.Op9Skeleton
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
  (ComputeTimestampSpecializesAt MemoryTimestampSpecializesAt)

set_option linter.unusedSimpArgs false

/-! ## The assembled buildable execution -/

noncomputable def Op9Execution
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
  memoryTrace := memoryTraceFinal hfirst
  requestNodup := requestNodup
  recordCountBalance := recordCountBalance
  q_le_ringChar := q_le_ringChar
  two_ne_zero := two_ne_zero
  Ksz_lt_ringChar := Ksz_lt_ringChar
  programIOCapacity := programIOCapacity
  memoryIOCapacity := memoryIOCapacity

/-! ## Row-skeleton bindings of the concrete rows -/

theorem bind_parentRow :
    BindComputeRow seedZ Op9Skeleton.parentRow (parentRow seedZ alphaA) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro slot
    cases slot <;>
      simp [decActive, hasTailDecomposition, decFP, bindFP, fp,
        Op9Skeleton.parentRow, parentRow, parentDec, op9Head, Op9Skeleton.op9Head]
  · intro i
    fin_cases i
    · rw [dif_pos (by decide)]
      intro slot
      cases slot <;>
        simp [Op9Skeleton.parentRow, computeSubformulaFPs, ComputeTable.sfTriple,
          parentRow, parentPub, tripleFP, bindFP, fp]
    · rw [dif_pos (by decide)]
      intro slot
      cases slot <;>
        simp [Op9Skeleton.parentRow, computeSubformulaFPs, ComputeTable.sfTriple,
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
    BindComputeRow seedZ Op9Skeleton.child1Row (child1Row seedZ alphaA) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro slot
    cases slot <;>
      simp [decActive, hasTailDecomposition, decFP, bindFP, fp,
        Op9Skeleton.child1Row, Op9Skeleton.op1Row, child1Row, op1DecOf,
        op1Head, Op9Skeleton.op1Head]
  · intro i
    have hi : ¬ ((i : ℕ) < ComputeTable.fanoutComp Op9Skeleton.child1Row.state) := by
      simp [Op9Skeleton.child1Row, Op9Skeleton.op1Row, ComputeTable.fanoutComp]
    rw [dif_neg hi]
    fin_cases i <;>
      simp [computeSubformulaFPs, ComputeTable.sfTriple, child1Row, child1Pub, op1PubOf]
  · intro i
    fin_cases i
    · exact ⟨rfl, rfl, rfl⟩
    · rfl
    · rfl

theorem bind_child2Row :
    BindComputeRow seedZ Op9Skeleton.child2Row (child2Row seedZ alphaA) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro slot
    cases slot <;>
      simp [decActive, hasTailDecomposition, decFP, bindFP, fp,
        Op9Skeleton.child2Row, Op9Skeleton.op1Row, child2Row, op1DecOf,
        op1Head, Op9Skeleton.op1Head]
  · intro i
    have hi : ¬ ((i : ℕ) < ComputeTable.fanoutComp Op9Skeleton.child2Row.state) := by
      simp [Op9Skeleton.child2Row, Op9Skeleton.op1Row, ComputeTable.fanoutComp]
    rw [dif_neg hi]
    fin_cases i <;>
      simp [computeSubformulaFPs, ComputeTable.sfTriple, child2Row, child2Pub, op1PubOf]
  · intro i
    fin_cases i
    · exact ⟨rfl, rfl, rfl⟩
    · rfl
    · rfl

/-! ### Memory-row bindings (Root A: 19 nodes) -/

theorem bind_readF :
    BindMemoryRowA seedZ Op9Skeleton.skReadF (lblOf seedZ (pReadFA seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i
    · rfl
    · simp [Op9Skeleton.skReadF, Op9Skeleton.readRow, MemoryTable.fanoutMem,
        memoryChildCell, lblOf, pReadFA, readPub]
  · exact ⟨rfl, rfl, rfl⟩

theorem bind_decPF :
    BindMemoryRowA seedZ Op9Skeleton.skDecPF (lblOf seedZ (pDecPF seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i <;> rfl
  · rfl

theorem bind_halt9 :
    BindMemoryRowA seedZ Op9Skeleton.skHalt9 (lblOf seedZ (pHalt9 seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, rfl⟩
  · simp [Op9Skeleton.skHalt9, Op9Skeleton.haltRow, lblOf, pHalt9, haltPub, bindFP, fp]
  · intro i
    have hi : ¬ ((i : ℕ) < MemoryTable.fanoutMem Op9Skeleton.skHalt9.state) := by
      simp [Op9Skeleton.skHalt9, Op9Skeleton.haltRow, MemoryTable.fanoutMem]
    rw [dif_neg hi]
    fin_cases i <;> rfl
  · rfl

theorem bind_verifyF :
    BindMemoryRowA seedZ Op9Skeleton.skVerifyF (lblOf seedZ (pVerifyFA seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i
    · rfl
    · simp [Op9Skeleton.skVerifyF, Op9Skeleton.verifyRow, MemoryTable.fanoutMem,
        memoryChildCell, lblOf, pVerifyFA, verifyPub]
  · exact ⟨rfl, rfl, rfl⟩

theorem bind_readT :
    BindMemoryRowA seedZ Op9Skeleton.skReadT (lblOf seedZ (pReadTA seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i
    · rfl
    · simp [Op9Skeleton.skReadT, Op9Skeleton.readRow, MemoryTable.fanoutMem,
        memoryChildCell, lblOf, pReadTA, readPub]
  · exact ⟨rfl, rfl, rfl⟩

theorem bind_decPT :
    BindMemoryRowA seedZ Op9Skeleton.skDecPT (lblOf seedZ (pDecPT seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i <;> rfl
  · rfl

theorem bind_verifyT :
    BindMemoryRowA seedZ Op9Skeleton.skVerifyT (lblOf seedZ (pVerifyTA seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i
    · rfl
    · simp [Op9Skeleton.skVerifyT, Op9Skeleton.verifyRow, MemoryTable.fanoutMem,
        memoryChildCell, lblOf, pVerifyTA, verifyPub]
  · exact ⟨rfl, rfl, rfl⟩

theorem bind_haltA2 :
    BindMemoryRowA seedZ Op9Skeleton.skHaltA2 (lblOf seedZ (pHaltA2 seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, rfl⟩
  · simp [Op9Skeleton.skHaltA2, Op9Skeleton.haltRow, lblOf, pHaltA2, haltPub, bindFP, fp]
  · intro i
    have hi : ¬ ((i : ℕ) < MemoryTable.fanoutMem Op9Skeleton.skHaltA2.state) := by
      simp [Op9Skeleton.skHaltA2, Op9Skeleton.haltRow, MemoryTable.fanoutMem]
    rw [dif_neg hi]
    fin_cases i <;> rfl
  · rfl

theorem bind_readCoreF :
    BindMemoryRowA seedZ Op9Skeleton.skReadCoreF (lblOf seedZ (pReadCoreFA seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i
    · rfl
    · simp [Op9Skeleton.skReadCoreF, Op9Skeleton.readRow, MemoryTable.fanoutMem,
        memoryChildCell, lblOf, pReadCoreFA, readPub]
  · exact ⟨rfl, rfl, rfl⟩

theorem bind_decCF :
    BindMemoryRowA seedZ Op9Skeleton.skDecCF (lblOf seedZ (pDecCF seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i <;> rfl
  · rfl

theorem bind_haltH1a :
    BindMemoryRowA seedZ Op9Skeleton.skHaltH1a (lblOf seedZ (pHaltH1a seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, rfl⟩
  · simp [Op9Skeleton.skHaltH1a, Op9Skeleton.haltRow, lblOf, pHaltH1a, haltPub, bindFP, fp]
  · intro i
    have hi : ¬ ((i : ℕ) < MemoryTable.fanoutMem Op9Skeleton.skHaltH1a.state) := by
      simp [Op9Skeleton.skHaltH1a, Op9Skeleton.haltRow, MemoryTable.fanoutMem]
    rw [dif_neg hi]
    fin_cases i <;> rfl
  · rfl

theorem bind_verifyCoreF :
    BindMemoryRowA seedZ Op9Skeleton.skVerifyCoreF (lblOf seedZ (pVerifyCoreFA seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i
    · rfl
    · simp [Op9Skeleton.skVerifyCoreF, Op9Skeleton.verifyRow, MemoryTable.fanoutMem,
        memoryChildCell, lblOf, pVerifyCoreFA, verifyPub]
  · exact ⟨rfl, rfl, rfl⟩

theorem bind_decCN :
    BindMemoryRowA seedZ Op9Skeleton.skDecCN (lblOf seedZ (pDecCN seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i <;> rfl
  · rfl

theorem bind_decArmA :
    BindMemoryRowA seedZ Op9Skeleton.skDecArmA (lblOf seedZ (pDecArmA seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i <;> rfl
  · rfl

theorem bind_haltH1b :
    BindMemoryRowA seedZ Op9Skeleton.skHaltH1b (lblOf seedZ (pHaltH1b seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, rfl⟩
  · simp [Op9Skeleton.skHaltH1b, Op9Skeleton.haltRow, lblOf, pHaltH1b, haltPub, bindFP, fp]
  · intro i
    have hi : ¬ ((i : ℕ) < MemoryTable.fanoutMem Op9Skeleton.skHaltH1b.state) := by
      simp [Op9Skeleton.skHaltH1b, Op9Skeleton.haltRow, MemoryTable.fanoutMem]
    rw [dif_neg hi]
    fin_cases i <;> rfl
  · rfl

theorem bind_haltA7 :
    BindMemoryRowA seedZ Op9Skeleton.skHaltA7 (lblOf seedZ (pHaltA7 seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, rfl⟩
  · simp [Op9Skeleton.skHaltA7, Op9Skeleton.haltRow, lblOf, pHaltA7, haltPub, bindFP, fp]
  · intro i
    have hi : ¬ ((i : ℕ) < MemoryTable.fanoutMem Op9Skeleton.skHaltA7.state) := by
      simp [Op9Skeleton.skHaltA7, Op9Skeleton.haltRow, MemoryTable.fanoutMem]
    rw [dif_neg hi]
    fin_cases i <;> rfl
  · rfl

theorem bind_decCTA :
    BindMemoryRowA seedZ Op9Skeleton.skDecCTA (lblOf seedZ (pDecCTA seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i <;> rfl
  · rfl

theorem bind_haltH1c :
    BindMemoryRowA seedZ Op9Skeleton.skHaltH1c (lblOf seedZ (pHaltH1c seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, rfl⟩
  · simp [Op9Skeleton.skHaltH1c, Op9Skeleton.haltRow, lblOf, pHaltH1c, haltPub, bindFP, fp]
  · intro i
    have hi : ¬ ((i : ℕ) < MemoryTable.fanoutMem Op9Skeleton.skHaltH1c.state) := by
      simp [Op9Skeleton.skHaltH1c, Op9Skeleton.haltRow, MemoryTable.fanoutMem]
    rw [dif_neg hi]
    fin_cases i <;> rfl
  · rfl

theorem bind_haltA9 :
    BindMemoryRowA seedZ Op9Skeleton.skHaltA9 (lblOf seedZ (pHaltA9 seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, rfl⟩
  · simp [Op9Skeleton.skHaltA9, Op9Skeleton.haltRow, lblOf, pHaltA9, haltPub, bindFP, fp]
  · intro i
    have hi : ¬ ((i : ℕ) < MemoryTable.fanoutMem Op9Skeleton.skHaltA9.state) := by
      simp [Op9Skeleton.skHaltA9, Op9Skeleton.haltRow, MemoryTable.fanoutMem]
    rw [dif_neg hi]
    fin_cases i <;> rfl
  · rfl

/-! ### Memory-row bindings (Root B: 11 nodes) -/

theorem bind_readArm :
    BindMemoryRowA seedZ Op9Skeleton.skReadArm (lblOf seedZ (pReadArmA seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i
    · rfl
    · simp [Op9Skeleton.skReadArm, Op9Skeleton.readRow, MemoryTable.fanoutMem,
        memoryChildCell, lblOf, pReadArmA, readPub]
  · exact ⟨rfl, rfl, rfl⟩

theorem bind_decCN_B :
    BindMemoryRowA seedZ Op9Skeleton.skDecCN_B (lblOf seedZ (pDecCN_B seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i <;> rfl
  · rfl

theorem bind_verifyArm :
    BindMemoryRowA seedZ Op9Skeleton.skVerifyArm (lblOf seedZ (pVerifyArmA seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i
    · rfl
    · simp [Op9Skeleton.skVerifyArm, Op9Skeleton.verifyRow, MemoryTable.fanoutMem,
        memoryChildCell, lblOf, pVerifyArmA, verifyPub]
  · exact ⟨rfl, rfl, rfl⟩

theorem bind_readArmF :
    BindMemoryRowA seedZ Op9Skeleton.skReadArmF (lblOf seedZ (pReadArmFA seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i
    · rfl
    · simp [Op9Skeleton.skReadArmF, Op9Skeleton.readRow, MemoryTable.fanoutMem,
        memoryChildCell, lblOf, pReadArmFA, readPub]
  · exact ⟨rfl, rfl, rfl⟩

theorem bind_decArmB :
    BindMemoryRowA seedZ Op9Skeleton.skDecArmB (lblOf seedZ (pDecArmB seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i <;> rfl
  · rfl

theorem bind_haltH1_B1 :
    BindMemoryRowA seedZ Op9Skeleton.skHaltH1_B1 (lblOf seedZ (pHaltH1_B1 seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, rfl⟩
  · simp [Op9Skeleton.skHaltH1_B1, Op9Skeleton.haltRow, lblOf, pHaltH1_B1, haltPub, bindFP, fp]
  · intro i
    have hi : ¬ ((i : ℕ) < MemoryTable.fanoutMem Op9Skeleton.skHaltH1_B1.state) := by
      simp [Op9Skeleton.skHaltH1_B1, Op9Skeleton.haltRow, MemoryTable.fanoutMem]
    rw [dif_neg hi]
    fin_cases i <;> rfl
  · rfl

theorem bind_verifyArmF :
    BindMemoryRowA seedZ Op9Skeleton.skVerifyArmF (lblOf seedZ (pVerifyArmFA seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i
    · rfl
    · simp [Op9Skeleton.skVerifyArmF, Op9Skeleton.verifyRow, MemoryTable.fanoutMem,
        memoryChildCell, lblOf, pVerifyArmFA, verifyPub]
  · exact ⟨rfl, rfl, rfl⟩

theorem bind_haltA7_B :
    BindMemoryRowA seedZ Op9Skeleton.skHaltA7_B (lblOf seedZ (pHaltA7_B seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, rfl⟩
  · simp [Op9Skeleton.skHaltA7_B, Op9Skeleton.haltRow, lblOf, pHaltA7_B, haltPub, bindFP, fp]
  · intro i
    have hi : ¬ ((i : ℕ) < MemoryTable.fanoutMem Op9Skeleton.skHaltA7_B.state) := by
      simp [Op9Skeleton.skHaltA7_B, Op9Skeleton.haltRow, MemoryTable.fanoutMem]
    rw [dif_neg hi]
    fin_cases i <;> rfl
  · rfl

theorem bind_decCT_B :
    BindMemoryRowA seedZ Op9Skeleton.skDecCT_B (lblOf seedZ (pDecCT_B seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i <;> rfl
  · rfl

theorem bind_haltH1_B2 :
    BindMemoryRowA seedZ Op9Skeleton.skHaltH1_B2 (lblOf seedZ (pHaltH1_B2 seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, rfl⟩
  · simp [Op9Skeleton.skHaltH1_B2, Op9Skeleton.haltRow, lblOf, pHaltH1_B2, haltPub, bindFP, fp]
  · intro i
    have hi : ¬ ((i : ℕ) < MemoryTable.fanoutMem Op9Skeleton.skHaltH1_B2.state) := by
      simp [Op9Skeleton.skHaltH1_B2, Op9Skeleton.haltRow, MemoryTable.fanoutMem]
    rw [dif_neg hi]
    fin_cases i <;> rfl
  · rfl

theorem bind_haltA9_B :
    BindMemoryRowA seedZ Op9Skeleton.skHaltA9_B (lblOf seedZ (pHaltA9_B seedZ alphaA)) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, rfl⟩
  · simp [Op9Skeleton.skHaltA9_B, Op9Skeleton.haltRow, lblOf, pHaltA9_B, haltPub, bindFP, fp]
  · intro i
    have hi : ¬ ((i : ℕ) < MemoryTable.fanoutMem Op9Skeleton.skHaltA9_B.state) := by
      simp [Op9Skeleton.skHaltA9_B, Op9Skeleton.haltRow, MemoryTable.fanoutMem]
    rw [dif_neg hi]
    fin_cases i <;> rfl
  · rfl

/-! ## The literal committed node trees -/

noncomputable def parentNode : ComputeNode K where
  skel := Op9Skeleton.parentRow
  stamp :=
    { state := .s9
      lnPrevExponent := 0
      lnExponent := 3
      recordExponent := fun
        | 0 => 1
        | 1 => 2
        | 2 => 3
        | _ => 0 }
  row := parentRow seedZ alphaA

noncomputable def child1Node : ComputeNode K where
  skel := Op9Skeleton.child1Row
  stamp := { state := .s1, lnPrevExponent := 3, lnExponent := 4, recordExponent := fun _ => 4 }
  row := child1Row seedZ alphaA

noncomputable def child2Node : ComputeNode K where
  skel := Op9Skeleton.child2Row
  stamp := { state := .s1, lnPrevExponent := 4, lnExponent := 5, recordExponent := fun _ => 5 }
  row := child2Row seedZ alphaA

noncomputable def op9ComputeTree : NTree (ComputeNode K) :=
  .node parentNode [.node child1Node [], .node child2Node []]

/-! ### Memory nodes (Root A: 19 nodes) -/

noncomputable def nReadF : MemoryNode K where
  skel := Op9Skeleton.skReadF
  stamp := { state := .read_root, recordExponent := 1 }
  row := lblOf seedZ (pReadFA seedZ alphaA)
noncomputable def nDecPF : MemoryNode K where
  skel := Op9Skeleton.skDecPF
  stamp := { state := .decompose, recordExponent := 0 }
  row := lblOf seedZ (pDecPF seedZ alphaA)
noncomputable def nHalt9 : MemoryNode K where
  skel := Op9Skeleton.skHalt9
  stamp := { state := .halt, recordExponent := 0 }
  row := lblOf seedZ (pHalt9 seedZ alphaA)
noncomputable def nVerifyF : MemoryNode K where
  skel := Op9Skeleton.skVerifyF
  stamp := { state := .verify_child, recordExponent := 1 }
  row := lblOf seedZ (pVerifyFA seedZ alphaA)
noncomputable def nReadT : MemoryNode K where
  skel := Op9Skeleton.skReadT
  stamp := { state := .read_root, recordExponent := 2 }
  row := lblOf seedZ (pReadTA seedZ alphaA)
noncomputable def nDecPT : MemoryNode K where
  skel := Op9Skeleton.skDecPT
  stamp := { state := .decompose, recordExponent := 0 }
  row := lblOf seedZ (pDecPT seedZ alphaA)
noncomputable def nVerifyT : MemoryNode K where
  skel := Op9Skeleton.skVerifyT
  stamp := { state := .verify_child, recordExponent := 2 }
  row := lblOf seedZ (pVerifyTA seedZ alphaA)
noncomputable def nHaltA2 : MemoryNode K where
  skel := Op9Skeleton.skHaltA2
  stamp := { state := .halt, recordExponent := 0 }
  row := lblOf seedZ (pHaltA2 seedZ alphaA)
noncomputable def nReadCoreF : MemoryNode K where
  skel := Op9Skeleton.skReadCoreF
  stamp := { state := .read_root, recordExponent := 4 }
  row := lblOf seedZ (pReadCoreFA seedZ alphaA)
noncomputable def nDecCF : MemoryNode K where
  skel := Op9Skeleton.skDecCF
  stamp := { state := .decompose, recordExponent := 0 }
  row := lblOf seedZ (pDecCF seedZ alphaA)
noncomputable def nHaltH1a : MemoryNode K where
  skel := Op9Skeleton.skHaltH1a
  stamp := { state := .halt, recordExponent := 0 }
  row := lblOf seedZ (pHaltH1a seedZ alphaA)
noncomputable def nVerifyCoreF : MemoryNode K where
  skel := Op9Skeleton.skVerifyCoreF
  stamp := { state := .verify_child, recordExponent := 4 }
  row := lblOf seedZ (pVerifyCoreFA seedZ alphaA)
noncomputable def nDecCN : MemoryNode K where
  skel := Op9Skeleton.skDecCN
  stamp := { state := .decompose, recordExponent := 0 }
  row := lblOf seedZ (pDecCN seedZ alphaA)
noncomputable def nDecArmA : MemoryNode K where
  skel := Op9Skeleton.skDecArmA
  stamp := { state := .decompose, recordExponent := 0 }
  row := lblOf seedZ (pDecArmA seedZ alphaA)
noncomputable def nHaltH1b : MemoryNode K where
  skel := Op9Skeleton.skHaltH1b
  stamp := { state := .halt, recordExponent := 0 }
  row := lblOf seedZ (pHaltH1b seedZ alphaA)
noncomputable def nHaltA7 : MemoryNode K where
  skel := Op9Skeleton.skHaltA7
  stamp := { state := .halt, recordExponent := 0 }
  row := lblOf seedZ (pHaltA7 seedZ alphaA)
noncomputable def nDecCTA : MemoryNode K where
  skel := Op9Skeleton.skDecCTA
  stamp := { state := .decompose, recordExponent := 0 }
  row := lblOf seedZ (pDecCTA seedZ alphaA)
noncomputable def nHaltH1c : MemoryNode K where
  skel := Op9Skeleton.skHaltH1c
  stamp := { state := .halt, recordExponent := 0 }
  row := lblOf seedZ (pHaltH1c seedZ alphaA)
noncomputable def nHaltA9 : MemoryNode K where
  skel := Op9Skeleton.skHaltA9
  stamp := { state := .halt, recordExponent := 0 }
  row := lblOf seedZ (pHaltA9 seedZ alphaA)

/-! ### Memory nodes (Root B: 11 nodes) -/

noncomputable def nReadArm : MemoryNode K where
  skel := Op9Skeleton.skReadArm
  stamp := { state := .read_root, recordExponent := 3 }
  row := lblOf seedZ (pReadArmA seedZ alphaA)
noncomputable def nDecCN_B : MemoryNode K where
  skel := Op9Skeleton.skDecCN_B
  stamp := { state := .decompose, recordExponent := 0 }
  row := lblOf seedZ (pDecCN_B seedZ alphaA)
noncomputable def nVerifyArm : MemoryNode K where
  skel := Op9Skeleton.skVerifyArm
  stamp := { state := .verify_child, recordExponent := 3 }
  row := lblOf seedZ (pVerifyArmA seedZ alphaA)
noncomputable def nReadArmF : MemoryNode K where
  skel := Op9Skeleton.skReadArmF
  stamp := { state := .read_root, recordExponent := 5 }
  row := lblOf seedZ (pReadArmFA seedZ alphaA)
noncomputable def nDecArmB : MemoryNode K where
  skel := Op9Skeleton.skDecArmB
  stamp := { state := .decompose, recordExponent := 0 }
  row := lblOf seedZ (pDecArmB seedZ alphaA)
noncomputable def nHaltH1_B1 : MemoryNode K where
  skel := Op9Skeleton.skHaltH1_B1
  stamp := { state := .halt, recordExponent := 0 }
  row := lblOf seedZ (pHaltH1_B1 seedZ alphaA)
noncomputable def nVerifyArmF : MemoryNode K where
  skel := Op9Skeleton.skVerifyArmF
  stamp := { state := .verify_child, recordExponent := 5 }
  row := lblOf seedZ (pVerifyArmFA seedZ alphaA)
noncomputable def nHaltA7_B : MemoryNode K where
  skel := Op9Skeleton.skHaltA7_B
  stamp := { state := .halt, recordExponent := 0 }
  row := lblOf seedZ (pHaltA7_B seedZ alphaA)
noncomputable def nDecCT_B : MemoryNode K where
  skel := Op9Skeleton.skDecCT_B
  stamp := { state := .decompose, recordExponent := 0 }
  row := lblOf seedZ (pDecCT_B seedZ alphaA)
noncomputable def nHaltH1_B2 : MemoryNode K where
  skel := Op9Skeleton.skHaltH1_B2
  stamp := { state := .halt, recordExponent := 0 }
  row := lblOf seedZ (pHaltH1_B2 seedZ alphaA)
noncomputable def nHaltA9_B : MemoryNode K where
  skel := Op9Skeleton.skHaltA9_B
  stamp := { state := .halt, recordExponent := 0 }
  row := lblOf seedZ (pHaltA9_B seedZ alphaA)

/-! ### The committed memory node trees -/

noncomputable def op9MemTreeA : NTree (MemoryNode K) :=
  .node nReadF
    [.node nDecPF
      [.node nHalt9 [],
       .node nVerifyF
        [.node nReadT
          [.node nDecPT
            [.node nVerifyT [.node nHaltA2 []],
             .node nReadCoreF
              [.node nDecCF
                [.node nHaltH1a [],
                 .node nVerifyCoreF
                  [.node nDecCN
                    [.node nDecArmA [.node nHaltH1b [], .node nHaltA7 []],
                     .node nDecCTA [.node nHaltH1c [], .node nHaltA9 []]]]]]]]]]]

noncomputable def op9MemTreeB : NTree (MemoryNode K) :=
  .node nReadArm
    [.node nDecCN_B
      [.node nVerifyArm
        [.node nReadArmF
          [.node nDecArmB
            [.node nHaltH1_B1 [],
             .node nVerifyArmF [.node nHaltA7_B []]]]],
       .node nDecCT_B
        [.node nHaltH1_B2 [], .node nHaltA9_B []]]]

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
        parentRow, parentPub, recF, recT, recArm, MemRec.zero, pow_one]
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
    simp [child1Pub, op1PubOf, pow_succ, pow_two]
  · intro i
    fin_cases i <;>
      simp [child1Node, computeMemRec, computeMemRecKind, Nock.Framework.recordCount,
        child1Row, child1Pub, op1PubOf, recCoreF, MemRec.zero]
  · intro i hi
    fin_cases i <;>
      simp_all [child1Node, computeMemRec, computeMemRecKind, Nock.Framework.recordCount,
        child1Row, child1Pub, op1PubOf, MemRec.zero]

theorem child2_specializes :
    ComputeTimestampSpecializesAt alphaA child2Node.stamp (child2Row seedZ alphaA) := by
  refine ComputeTimestampSpecializesAt.of_absolute rfl rfl rfl ?_ ?_ ?_ ?_
    (by decide) (fun i => by fin_cases i <;> decide)
  · show (child2Pub seedZ alphaA).ln_prev = alphaA ^ 4
    simp [child2Pub, op1PubOf, pow_succ, pow_two]
  · show (child2Pub seedZ alphaA).ln = alphaA ^ 5
    simp [child2Pub, op1PubOf, pow_succ, pow_two]
  · intro i
    fin_cases i <;>
      simp [child2Node, computeMemRec, computeMemRecKind, Nock.Framework.recordCount,
        child2Row, child2Pub, op1PubOf, recArmF, MemRec.zero]
  · intro i hi
    fin_cases i <;>
      simp_all [child2Node, computeMemRec, computeMemRecKind, Nock.Framework.recordCount,
        child2Row, child2Pub, op1PubOf, MemRec.zero]

/-! ### Memory timestamp specializations (Root A) -/

theorem readF_specializes :
    MemoryTimestampSpecializesAt alphaA nReadF.stamp (lblOf seedZ (pReadFA seedZ alphaA)) :=
  ⟨rfl, rfl, by simp [nReadF, memoryMemRecKind, lblOf, pReadFA, readPub, recF, pow_one],
    by simp [nReadF, memoryMemRecKind]⟩
theorem decPF_specializes :
    MemoryTimestampSpecializesAt alphaA nDecPF.stamp (lblOf seedZ (pDecPF seedZ alphaA)) :=
  ⟨rfl, rfl, by simp [nDecPF, memoryMemRecKind, lblOf, pDecPF, decPub, MemRec.zero],
    by simp [nDecPF, memoryMemRecKind, lblOf, pDecPF, decPub, MemRec.zero]⟩
theorem halt9_specializes :
    MemoryTimestampSpecializesAt alphaA nHalt9.stamp (lblOf seedZ (pHalt9 seedZ alphaA)) :=
  ⟨rfl, rfl, by simp [nHalt9, memoryMemRecKind, lblOf, pHalt9, haltPub, MemRec.zero],
    by simp [nHalt9, memoryMemRecKind, lblOf, pHalt9, haltPub, MemRec.zero]⟩
theorem verifyF_specializes :
    MemoryTimestampSpecializesAt alphaA nVerifyF.stamp (lblOf seedZ (pVerifyFA seedZ alphaA)) :=
  ⟨rfl, rfl, by simp [nVerifyF, memoryMemRecKind, lblOf, pVerifyFA, verifyPub, recF, pow_one],
    by simp [nVerifyF, memoryMemRecKind]⟩
theorem readT_specializes :
    MemoryTimestampSpecializesAt alphaA nReadT.stamp (lblOf seedZ (pReadTA seedZ alphaA)) :=
  ⟨rfl, rfl, by simp [nReadT, memoryMemRecKind, lblOf, pReadTA, readPub, recT],
    by simp [nReadT, memoryMemRecKind]⟩
theorem decPT_specializes :
    MemoryTimestampSpecializesAt alphaA nDecPT.stamp (lblOf seedZ (pDecPT seedZ alphaA)) :=
  ⟨rfl, rfl, by simp [nDecPT, memoryMemRecKind, lblOf, pDecPT, decPub, MemRec.zero],
    by simp [nDecPT, memoryMemRecKind, lblOf, pDecPT, decPub, MemRec.zero]⟩
theorem verifyT_specializes :
    MemoryTimestampSpecializesAt alphaA nVerifyT.stamp (lblOf seedZ (pVerifyTA seedZ alphaA)) :=
  ⟨rfl, rfl, by simp [nVerifyT, memoryMemRecKind, lblOf, pVerifyTA, verifyPub, recT],
    by simp [nVerifyT, memoryMemRecKind]⟩
theorem haltA2_specializes :
    MemoryTimestampSpecializesAt alphaA nHaltA2.stamp (lblOf seedZ (pHaltA2 seedZ alphaA)) :=
  ⟨rfl, rfl, by simp [nHaltA2, memoryMemRecKind, lblOf, pHaltA2, haltPub, MemRec.zero],
    by simp [nHaltA2, memoryMemRecKind, lblOf, pHaltA2, haltPub, MemRec.zero]⟩
theorem readCoreF_specializes :
    MemoryTimestampSpecializesAt alphaA nReadCoreF.stamp
      (lblOf seedZ (pReadCoreFA seedZ alphaA)) :=
  ⟨rfl, rfl, by simp [nReadCoreF, memoryMemRecKind, lblOf, pReadCoreFA, readPub, recCoreF],
    by simp [nReadCoreF, memoryMemRecKind]⟩
theorem decCF_specializes :
    MemoryTimestampSpecializesAt alphaA nDecCF.stamp (lblOf seedZ (pDecCF seedZ alphaA)) :=
  ⟨rfl, rfl, by simp [nDecCF, memoryMemRecKind, lblOf, pDecCF, decPub, MemRec.zero],
    by simp [nDecCF, memoryMemRecKind, lblOf, pDecCF, decPub, MemRec.zero]⟩
theorem haltH1a_specializes :
    MemoryTimestampSpecializesAt alphaA nHaltH1a.stamp (lblOf seedZ (pHaltH1a seedZ alphaA)) :=
  ⟨rfl, rfl, by simp [nHaltH1a, memoryMemRecKind, lblOf, pHaltH1a, haltPub, MemRec.zero],
    by simp [nHaltH1a, memoryMemRecKind, lblOf, pHaltH1a, haltPub, MemRec.zero]⟩
theorem verifyCoreF_specializes :
    MemoryTimestampSpecializesAt alphaA nVerifyCoreF.stamp
      (lblOf seedZ (pVerifyCoreFA seedZ alphaA)) :=
  ⟨rfl, rfl,
    by simp [nVerifyCoreF, memoryMemRecKind, lblOf, pVerifyCoreFA, verifyPub, recCoreF],
    by simp [nVerifyCoreF, memoryMemRecKind]⟩
theorem decCN_specializes :
    MemoryTimestampSpecializesAt alphaA nDecCN.stamp (lblOf seedZ (pDecCN seedZ alphaA)) :=
  ⟨rfl, rfl, by simp [nDecCN, memoryMemRecKind, lblOf, pDecCN, decPub, MemRec.zero],
    by simp [nDecCN, memoryMemRecKind, lblOf, pDecCN, decPub, MemRec.zero]⟩
theorem decArmA_specializes :
    MemoryTimestampSpecializesAt alphaA nDecArmA.stamp (lblOf seedZ (pDecArmA seedZ alphaA)) :=
  ⟨rfl, rfl, by simp [nDecArmA, memoryMemRecKind, lblOf, pDecArmA, decPub, MemRec.zero],
    by simp [nDecArmA, memoryMemRecKind, lblOf, pDecArmA, decPub, MemRec.zero]⟩
theorem haltH1b_specializes :
    MemoryTimestampSpecializesAt alphaA nHaltH1b.stamp (lblOf seedZ (pHaltH1b seedZ alphaA)) :=
  ⟨rfl, rfl, by simp [nHaltH1b, memoryMemRecKind, lblOf, pHaltH1b, haltPub, MemRec.zero],
    by simp [nHaltH1b, memoryMemRecKind, lblOf, pHaltH1b, haltPub, MemRec.zero]⟩
theorem haltA7_specializes :
    MemoryTimestampSpecializesAt alphaA nHaltA7.stamp (lblOf seedZ (pHaltA7 seedZ alphaA)) :=
  ⟨rfl, rfl, by simp [nHaltA7, memoryMemRecKind, lblOf, pHaltA7, haltPub, MemRec.zero],
    by simp [nHaltA7, memoryMemRecKind, lblOf, pHaltA7, haltPub, MemRec.zero]⟩
theorem decCTA_specializes :
    MemoryTimestampSpecializesAt alphaA nDecCTA.stamp (lblOf seedZ (pDecCTA seedZ alphaA)) :=
  ⟨rfl, rfl, by simp [nDecCTA, memoryMemRecKind, lblOf, pDecCTA, decPub, MemRec.zero],
    by simp [nDecCTA, memoryMemRecKind, lblOf, pDecCTA, decPub, MemRec.zero]⟩
theorem haltH1c_specializes :
    MemoryTimestampSpecializesAt alphaA nHaltH1c.stamp (lblOf seedZ (pHaltH1c seedZ alphaA)) :=
  ⟨rfl, rfl, by simp [nHaltH1c, memoryMemRecKind, lblOf, pHaltH1c, haltPub, MemRec.zero],
    by simp [nHaltH1c, memoryMemRecKind, lblOf, pHaltH1c, haltPub, MemRec.zero]⟩
theorem haltA9_specializes :
    MemoryTimestampSpecializesAt alphaA nHaltA9.stamp (lblOf seedZ (pHaltA9 seedZ alphaA)) :=
  ⟨rfl, rfl, by simp [nHaltA9, memoryMemRecKind, lblOf, pHaltA9, haltPub, MemRec.zero],
    by simp [nHaltA9, memoryMemRecKind, lblOf, pHaltA9, haltPub, MemRec.zero]⟩

/-! ### Memory timestamp specializations (Root B) -/

theorem readArm_specializes :
    MemoryTimestampSpecializesAt alphaA nReadArm.stamp (lblOf seedZ (pReadArmA seedZ alphaA)) :=
  ⟨rfl, rfl, by simp [nReadArm, memoryMemRecKind, lblOf, pReadArmA, readPub, recArm],
    by simp [nReadArm, memoryMemRecKind]⟩
theorem decCN_B_specializes :
    MemoryTimestampSpecializesAt alphaA nDecCN_B.stamp (lblOf seedZ (pDecCN_B seedZ alphaA)) :=
  ⟨rfl, rfl, by simp [nDecCN_B, memoryMemRecKind, lblOf, pDecCN_B, decPub, MemRec.zero],
    by simp [nDecCN_B, memoryMemRecKind, lblOf, pDecCN_B, decPub, MemRec.zero]⟩
theorem verifyArm_specializes :
    MemoryTimestampSpecializesAt alphaA nVerifyArm.stamp
      (lblOf seedZ (pVerifyArmA seedZ alphaA)) :=
  ⟨rfl, rfl, by simp [nVerifyArm, memoryMemRecKind, lblOf, pVerifyArmA, verifyPub, recArm],
    by simp [nVerifyArm, memoryMemRecKind]⟩
theorem readArmF_specializes :
    MemoryTimestampSpecializesAt alphaA nReadArmF.stamp
      (lblOf seedZ (pReadArmFA seedZ alphaA)) :=
  ⟨rfl, rfl, by simp [nReadArmF, memoryMemRecKind, lblOf, pReadArmFA, readPub, recArmF],
    by simp [nReadArmF, memoryMemRecKind]⟩
theorem decArmB_specializes :
    MemoryTimestampSpecializesAt alphaA nDecArmB.stamp (lblOf seedZ (pDecArmB seedZ alphaA)) :=
  ⟨rfl, rfl, by simp [nDecArmB, memoryMemRecKind, lblOf, pDecArmB, decPub, MemRec.zero],
    by simp [nDecArmB, memoryMemRecKind, lblOf, pDecArmB, decPub, MemRec.zero]⟩
theorem haltH1_B1_specializes :
    MemoryTimestampSpecializesAt alphaA nHaltH1_B1.stamp
      (lblOf seedZ (pHaltH1_B1 seedZ alphaA)) :=
  ⟨rfl, rfl, by simp [nHaltH1_B1, memoryMemRecKind, lblOf, pHaltH1_B1, haltPub, MemRec.zero],
    by simp [nHaltH1_B1, memoryMemRecKind, lblOf, pHaltH1_B1, haltPub, MemRec.zero]⟩
theorem verifyArmF_specializes :
    MemoryTimestampSpecializesAt alphaA nVerifyArmF.stamp
      (lblOf seedZ (pVerifyArmFA seedZ alphaA)) :=
  ⟨rfl, rfl, by simp [nVerifyArmF, memoryMemRecKind, lblOf, pVerifyArmFA, verifyPub, recArmF],
    by simp [nVerifyArmF, memoryMemRecKind]⟩
theorem haltA7_B_specializes :
    MemoryTimestampSpecializesAt alphaA nHaltA7_B.stamp
      (lblOf seedZ (pHaltA7_B seedZ alphaA)) :=
  ⟨rfl, rfl, by simp [nHaltA7_B, memoryMemRecKind, lblOf, pHaltA7_B, haltPub, MemRec.zero],
    by simp [nHaltA7_B, memoryMemRecKind, lblOf, pHaltA7_B, haltPub, MemRec.zero]⟩
theorem decCT_B_specializes :
    MemoryTimestampSpecializesAt alphaA nDecCT_B.stamp (lblOf seedZ (pDecCT_B seedZ alphaA)) :=
  ⟨rfl, rfl, by simp [nDecCT_B, memoryMemRecKind, lblOf, pDecCT_B, decPub, MemRec.zero],
    by simp [nDecCT_B, memoryMemRecKind, lblOf, pDecCT_B, decPub, MemRec.zero]⟩
theorem haltH1_B2_specializes :
    MemoryTimestampSpecializesAt alphaA nHaltH1_B2.stamp
      (lblOf seedZ (pHaltH1_B2 seedZ alphaA)) :=
  ⟨rfl, rfl, by simp [nHaltH1_B2, memoryMemRecKind, lblOf, pHaltH1_B2, haltPub, MemRec.zero],
    by simp [nHaltH1_B2, memoryMemRecKind, lblOf, pHaltH1_B2, haltPub, MemRec.zero]⟩
theorem haltA9_B_specializes :
    MemoryTimestampSpecializesAt alphaA nHaltA9_B.stamp
      (lblOf seedZ (pHaltA9_B seedZ alphaA)) :=
  ⟨rfl, rfl, by simp [nHaltA9_B, memoryMemRecKind, lblOf, pHaltA9_B, haltPub, MemRec.zero],
    by simp [nHaltA9_B, memoryMemRecKind, lblOf, pHaltA9_B, haltPub, MemRec.zero]⟩

/-! ## Local node validity -/

theorem op9ComputeTree_OK :
    ComputeNodesOK seedZ alphaA op9ComputeTree := by
  refine ComputeNodesOK.mk' ⟨?_, rfl, bind_parentRow, parent_specializes⟩ ?_
  · simp [parentNode, Op9Skeleton.parentRow, ComputeTable.fanoutComp]
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ComputeNodesOK.mk' ⟨by simp [child1Node, Op9Skeleton.child1Row, Op9Skeleton.op1Row,
        ComputeTable.fanoutComp], rfl, bind_child1Row, child1_specializes⟩ (by simp)
    · exact ComputeNodesOK.mk' ⟨by simp [child2Node, Op9Skeleton.child2Row, Op9Skeleton.op1Row,
        ComputeTable.fanoutComp], rfl, bind_child2Row, child2_specializes⟩ (by simp)

theorem op9MemTreeA_OK :
    MemoryNodesOK seedZ alphaA op9MemTreeA := by
  refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_readF, readF_specializes⟩ ?_
  intro c hc; simp only [List.mem_cons, List.not_mem_nil, or_false] at hc; subst hc
  refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_decPF, decPF_specializes⟩ ?_
  intro d hd; simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl
  · exact MemoryNodesOK.mk' ⟨rfl, rfl, bind_halt9, halt9_specializes⟩ (by simp)
  · refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_verifyF, verifyF_specializes⟩ ?_
    intro e he; simp only [List.mem_cons, List.not_mem_nil, or_false] at he; subst he
    refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_readT, readT_specializes⟩ ?_
    intro f hf; simp only [List.mem_cons, List.not_mem_nil, or_false] at hf; subst hf
    refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_decPT, decPT_specializes⟩ ?_
    intro g hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_verifyT, verifyT_specializes⟩ ?_
      intro h hh; simp only [List.mem_cons, List.not_mem_nil, or_false] at hh; subst hh
      exact MemoryNodesOK.mk' ⟨rfl, rfl, bind_haltA2, haltA2_specializes⟩ (by simp)
    · refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_readCoreF, readCoreF_specializes⟩ ?_
      intro h hh; simp only [List.mem_cons, List.not_mem_nil, or_false] at hh; subst hh
      refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_decCF, decCF_specializes⟩ ?_
      intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact MemoryNodesOK.mk' ⟨rfl, rfl, bind_haltH1a, haltH1a_specializes⟩ (by simp)
      · refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_verifyCoreF, verifyCoreF_specializes⟩ ?_
        intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; subst hj
        refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_decCN, decCN_specializes⟩ ?_
        intro k hk; simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl
        · refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_decArmA, decArmA_specializes⟩ ?_
          intro l hl; simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
          rcases hl with rfl | rfl
          · exact MemoryNodesOK.mk' ⟨rfl, rfl, bind_haltH1b, haltH1b_specializes⟩ (by simp)
          · exact MemoryNodesOK.mk' ⟨rfl, rfl, bind_haltA7, haltA7_specializes⟩ (by simp)
        · refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_decCTA, decCTA_specializes⟩ ?_
          intro l hl; simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
          rcases hl with rfl | rfl
          · exact MemoryNodesOK.mk' ⟨rfl, rfl, bind_haltH1c, haltH1c_specializes⟩ (by simp)
          · exact MemoryNodesOK.mk' ⟨rfl, rfl, bind_haltA9, haltA9_specializes⟩ (by simp)

theorem op9MemTreeB_OK :
    MemoryNodesOK seedZ alphaA op9MemTreeB := by
  refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_readArm, readArm_specializes⟩ ?_
  intro c hc; simp only [List.mem_cons, List.not_mem_nil, or_false] at hc; subst hc
  refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_decCN_B, decCN_B_specializes⟩ ?_
  intro d hd; simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl
  · refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_verifyArm, verifyArm_specializes⟩ ?_
    intro e he; simp only [List.mem_cons, List.not_mem_nil, or_false] at he; subst he
    refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_readArmF, readArmF_specializes⟩ ?_
    intro f hf; simp only [List.mem_cons, List.not_mem_nil, or_false] at hf; subst hf
    refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_decArmB, decArmB_specializes⟩ ?_
    intro g hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact MemoryNodesOK.mk' ⟨rfl, rfl, bind_haltH1_B1, haltH1_B1_specializes⟩ (by simp)
    · refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_verifyArmF, verifyArmF_specializes⟩ ?_
      intro h hh; simp only [List.mem_cons, List.not_mem_nil, or_false] at hh; subst hh
      exact MemoryNodesOK.mk' ⟨rfl, rfl, bind_haltA7_B, haltA7_B_specializes⟩ (by simp)
  · refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_decCT_B, decCT_B_specializes⟩ ?_
    intro e he; simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact MemoryNodesOK.mk' ⟨rfl, rfl, bind_haltH1_B2, haltH1_B2_specializes⟩ (by simp)
    · exact MemoryNodesOK.mk' ⟨rfl, rfl, bind_haltA9_B, haltA9_B_specializes⟩ (by simp)

/-! ## The committed skeleton is exactly `Op9Skeleton.semanticSkeleton` -/

theorem skeletonOfNodes_eq :
    skeletonOfNodes op9ComputeTree [op9MemTreeA, op9MemTreeB] =
      Op9Skeleton.semanticSkeleton := by
  simp [skeletonOfNodes, op9ComputeTree, op9MemTreeA, op9MemTreeB, mapNTree,
    Op9Skeleton.semanticSkeleton, Op9Skeleton.computeTree,
    parentNode, child1Node, child2Node,
    nReadF, nDecPF, nHalt9, nVerifyF, nReadT, nDecPT, nVerifyT, nHaltA2,
    nReadCoreF, nDecCF, nHaltH1a, nVerifyCoreF, nDecCN, nDecArmA, nHaltH1b, nHaltA7,
    nDecCTA, nHaltH1c, nHaltA9,
    nReadArm, nDecCN_B, nVerifyArm, nReadArmF, nDecArmB, nHaltH1_B1, nVerifyArmF, nHaltA7_B,
    nDecCT_B, nHaltH1_B2, nHaltA9_B,
    Op9Skeleton.rootATree, Op9Skeleton.rootBTree,
    Op9Skeleton.mLeaf, Op9Skeleton.mOne, Op9Skeleton.mTwo]

/-! ## The honest commitment -/

noncomputable def data
    (hfirst :
      ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.counts = 0 ∧
        ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.indicator = 0) :
    Data (Op9Execution hfirst) where
  computeNodes := op9ComputeTree
  memoryNodes := [op9MemTreeA, op9MemTreeB]
  compute_rows := by
    show mapNTree ComputeNode.row op9ComputeTree = (exec seedZ alphaA).computeTree
    simp [op9ComputeTree, parentNode, child1Node, child2Node, mapNTree, exec, execA, computeTree]
  memory_rows := by
    show [op9MemTreeA, op9MemTreeB].map (mapNTree MemoryNode.row) =
      (execA seedZ alphaA).memoryForest
    simp [op9MemTreeA, op9MemTreeB, mapNTree, exec, execA,
      nReadF, nDecPF, nHalt9, nVerifyF, nReadT, nDecPT, nVerifyT, nHaltA2,
      nReadCoreF, nDecCF, nHaltH1a, nVerifyCoreF, nDecCN, nDecArmA, nHaltH1b, nHaltA7,
      nDecCTA, nHaltH1c, nHaltA9,
      nReadArm, nDecCN_B, nVerifyArm, nReadArmF, nDecArmB, nHaltH1_B1, nVerifyArmF, nHaltA7_B,
      nDecCT_B, nHaltH1_B2, nHaltA9_B,
      rootTreeAView, rootTreeBView, mLeaf, mOne, mTwo]
  computeOK := op9ComputeTree_OK
  memoryOK := by
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact op9MemTreeA_OK
    · exact op9MemTreeB_OK
  root_line_exponent := rfl
  root_line_origin := rfl
  nounSizeBound := 7
  Λ := 7
  slotSemantics := skeletonOfNodes_eq ▸ Op9Skeleton.slotSemantics
  recordEquations := skeletonOfNodes_eq ▸ Op9Skeleton.recordEquations
  census := skeletonOfNodes_eq ▸ Op9Skeleton.census
  sizeWindowBound := skeletonOfNodes_eq ▸ Op9Skeleton.sizeWindowBound
  q_eq_ringChar := by show (97 : ℕ) = ringChar K; exact ringChar_K3.symm
  skeletonBounded := skeletonOfNodes_eq ▸ Op9Skeleton.skeletonBounded
  combinedBounded := skeletonOfNodes_eq ▸ Op9Skeleton.combinedBounded

theorem data_skeleton
    (hfirst :
      ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.counts = 0 ∧
        ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.indicator = 0) :
    (data hfirst).skeleton = Op9Skeleton.semanticSkeleton :=
  skeletonOfNodes_eq

end Nock.NockVMROM.Thm54.TraceGen.Op9ConfigK3

#print axioms Nock.NockVMROM.Thm54.TraceGen.Op9ConfigK3.Op9Execution
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op9ConfigK3.data
