/-
  Nock/NockVMROM/Thm54/TraceGen/Op9RowWebK3.lean

  Stage 4c of the OP9 Layer-2 CORE, over `K3`: compute/memory genericity (`WF`),
  BFS chain, arity-2/3 topology of the fan-out-2 invoke program, LogUp poles,
  and per-row `Vmem` acceptance of all 30 memory rows.

      `*[0 [9 [2 [1 [[1 7] [1 9]]]]]] = 7`

  The `.s9` parent row has `sf1_e ≠ sf2_e` (core ≠ result fingerprint),
  and `sf2_s = op9CoreNoun` (the computed core feeds the second call).
-/
import Nock.NockVMROM.Thm54.TraceGen.Op9BuildablePartsK3
import Nock.NockVMROM.Thm54.ChainedLanguage
import Nock.NockVMROM.Thm54.ExactTraversal

namespace Nock.NockVMROM.Thm54.TraceGen.Op9ConfigK3

open Nock Nock.Walk Nock.MemoryTable Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen

noncomputable section

/-! ## BFS re-indexing of the canonical compute rows (pub projection) -/

theorem computePubAt_zero :
    (exec seedZ alphaA).computePubAt ⟨0, by norm_num [cfg]⟩ = parentPub seedZ alphaA := by
  norm_num [ExactExecution.computePubAt, ExactExecution.computeRowAt, computeRows_eq, cfg,
    parentRow]

theorem computePubAt_one :
    (exec seedZ alphaA).computePubAt ⟨1, by norm_num [cfg]⟩ = child1Pub seedZ alphaA := by
  norm_num [ExactExecution.computePubAt, ExactExecution.computeRowAt, computeRows_eq, cfg,
    child1Row, child1Pub]

theorem computePubAt_two :
    (exec seedZ alphaA).computePubAt ⟨2, by norm_num [cfg]⟩ = child2Pub seedZ alphaA := by
  norm_num [ExactExecution.computePubAt, ExactExecution.computeRowAt, computeRows_eq, cfg,
    child2Row, child2Pub]

/-! ## Compute genericity (`WF`) per row -/

theorem parent_wf : ComputeTable.WF (compInputs seedZ alphaA) (parentPub seedZ alphaA) where
  rlc5 := by
    intro hst
    simp [parentPub] at hst
  size8 := by simp [parentPub, fp, GlobalCarryRecognizer.enc_size]
  size11 := by simp [parentPub]

theorem child1_wf : ComputeTable.WF (compInputs seedZ alphaA) (child1Pub seedZ alphaA) where
  rlc5 := by simp [child1Pub, op1PubOf]
  size8 := by simp [child1Pub, op1PubOf]
  size11 := by simp [child1Pub, op1PubOf]

theorem child2_wf : ComputeTable.WF (compInputs seedZ alphaA) (child2Pub seedZ alphaA) where
  rlc5 := by simp [child2Pub, op1PubOf]
  size8 := by simp [child2Pub, op1PubOf]
  size11 := by simp [child2Pub, op1PubOf]

theorem compute_wf_all :
    ∀ i, ComputeTable.WF (cfg seedZ alphaA).challenges.computeInputs
      ((exec seedZ alphaA).computePubAt i) := by
  intro i
  fin_cases i
  · rw [computePubAt_zero]; exact parent_wf
  · rw [computePubAt_one]; exact child1_wf
  · rw [computePubAt_two]; exact child2_wf

theorem compute_chain :
    ∀ i : Fin (cfg seedZ alphaA).compRows,
      ∀ _ : (i : ℕ) + 1 < (cfg seedZ alphaA).compRows,
        ((exec seedZ alphaA).computePubAt i).ln =
          ((exec seedZ alphaA).computePubAt ⟨(i : ℕ) + 1, by omega⟩).ln_prev := by
  intro i hi
  fin_cases i
  · rw [computePubAt_zero, computePubAt_one]
    simp [parentPub, child1Pub, op1PubOf]
  · rw [computePubAt_one, computePubAt_two]
    simp [child1Pub, child2Pub, op1PubOf, pow_succ]
  · simp [cfg] at hi

/-! ## Arity-3 `Fcomp` topology on the fan-out-2 compute tree -/

theorem child1Row_fcomp :
    ComputeTable.Fcomp (child1Row seedZ alphaA) (fun _ => none) := by
  refine ⟨rfl, child1_accepts, ?_, ?_⟩
  · intro i; fin_cases i <;> simp [child1Row, ComputeTable.fanoutComp]
  · intro i hi; simp [child1Row, ComputeTable.fanoutComp] at hi

theorem child2Row_fcomp :
    ComputeTable.Fcomp (child2Row seedZ alphaA) (fun _ => none) := by
  refine ⟨rfl, child2_accepts, ?_, ?_⟩
  · intro i; fin_cases i <;> simp [child2Row, ComputeTable.fanoutComp]
  · intro i hi; simp [child2Row, ComputeTable.fanoutComp] at hi

theorem child1Tree_rvt :
    RVT (ComputeTable.Fcomp (K := K)) (.node (child1Row seedZ alphaA) []) := by
  unfold RVT
  refine ⟨?_, by simp, ?_⟩
  · rw [show (fun i : Fin 3 =>
        (NTree.node (child1Row seedZ alphaA) ([] : List (NTree _))).childLabel i)
        = (fun _ => none) by funext i; fin_cases i <;> rfl]
    exact child1Row_fcomp
  · exact ⟨fun _ => child1Row_fcomp, fun _ => rfl⟩

theorem child2Tree_rvt :
    RVT (ComputeTable.Fcomp (K := K)) (.node (child2Row seedZ alphaA) []) := by
  unfold RVT
  refine ⟨?_, by simp, ?_⟩
  · rw [show (fun i : Fin 3 =>
        (NTree.node (child2Row seedZ alphaA) ([] : List (NTree _))).childLabel i)
        = (fun _ => none) by funext i; fin_cases i <;> rfl]
    exact child2Row_fcomp
  · exact ⟨fun _ => child2Row_fcomp, fun _ => rfl⟩

theorem computeTree_rvt :
    RVT (ComputeTable.Fcomp (K := K)) (computeTree seedZ alphaA) := by
  unfold computeTree RVT
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨rfl, parent_accepts, ?_, ?_⟩
    · intro i
      fin_cases i <;>
        simp [parentRow, ComputeTable.fanoutComp, NTree.childLabel, NTree.childOpt]
    · intro i hi
      fin_cases i
      · simp [parentRow, child1Row, child1Pub, op1PubOf, parentPub, ComputeTable.sfTriple,
          NTree.childLabel, NTree.childOpt, NTree.label]
      · simp [parentRow, child2Row, child2Pub, op1PubOf, parentPub, ComputeTable.sfTriple,
          NTree.childLabel, NTree.childOpt, NTree.label]
      · simp [parentRow, ComputeTable.fanoutComp] at hi
  · intro s hs
    simp [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact child1Tree_rvt
    · exact child2Tree_rvt
  · refine ⟨fun h => absurd h (by simp [NTree.isLeaf]), fun h => ?_⟩
    exfalso
    have h0 := h.2.2.1 ⟨0, by norm_num⟩
    simp [ComputeTable.fanoutComp, parentRow] at h0

theorem compute_topology : ComputeExactTopology (exec seedZ alphaA) := by
  refine ⟨?_, ?_⟩
  · show RVT (ComputeTable.Fcomp (K := K)) (exec seedZ alphaA).computeTree
    exact computeTree_rvt
  · show ProperArity 3 (exec seedZ alphaA).computeTree
    simp [exec, computeTree]

/-! ## The LogUp pole is the record root's fingerprint size -/

theorem pole_eq (r : MemRec K) : pole (memInputs seedZ) r 1 = r.root.size := by
  simp [pole, memInputs, recRLC]

theorem pole_row_eq (r : MemRec K) :
    pole (memInputs seedZ) (NockVM.formRRow r MemoryTable.formRDefault)
      (NockVM.formRCprime r MemoryTable.formRDefault) = pole (memInputs seedZ) r 1 := by
  simp [pole, memInputs, recRLC, NockVM.formRRow]

theorem poleF_ne : pole (memInputs seedZ) (recF seedZ alphaA) 1 ≠ 0 := by
  rw [pole_eq]
  show (fp seedZ op9ParentFormula).size ≠ 0
  simp [fp, GlobalCarryRecognizer.enc_size]
  exact fun h => (seedZ_ne_zero h).elim

theorem poleT_ne : pole (memInputs seedZ) (recT seedZ alphaA) 1 ≠ 0 := by
  rw [pole_eq]
  show (fp seedZ op9ParentTail).size ≠ 0
  simp [fp, GlobalCarryRecognizer.enc_size]
  exact fun h => (seedZ_ne_zero h).elim

theorem poleArm_ne : pole (memInputs seedZ) (recArm seedZ alphaA) 1 ≠ 0 := by
  rw [pole_eq]
  show (fp seedZ op9CoreNoun).size ≠ 0
  simp [fp, GlobalCarryRecognizer.enc_size]
  exact fun h => (seedZ_ne_zero h).elim

theorem poleCoreF_ne : pole (memInputs seedZ) (recCoreF seedZ alphaA) 1 ≠ 0 := by
  rw [pole_eq]
  show (fp seedZ op9CoreFormula).size ≠ 0
  simp [fp, GlobalCarryRecognizer.enc_size]
  exact fun h => (seedZ_ne_zero h).elim

theorem poleArmF_ne : pole (memInputs seedZ) (recArmF seedZ alphaA) 1 ≠ 0 := by
  rw [pole_eq]
  show (fp seedZ op9Arm).size ≠ 0
  simp [fp, GlobalCarryRecognizer.enc_size]
  exact fun h => (seedZ_ne_zero h).elim

/-! ## The thirty memory rows are accepted by `V_mem` -/

-- Root A rows
theorem pReadF_accepts : Vmem (memInputs seedZ) (pReadF seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨rfl, rfl, ?_, ?_, rfl, rfl⟩, ?_⟩
  · simp [NockVM.formRRow, NockVM.formRCprime, pReadF, readPub, cReadF, cDecPF, recF, Pub.lambda,
  Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · simp [NockVM.formRRow, NockVM.formRCprime, pReadF, readPub, cReadF, cDecPF, recF, Pub.lambda,
  Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · show (pReadF seedZ alphaA).icur - (pReadF seedZ alphaA).ipre =
      (pole (memInputs seedZ) (pReadF seedZ alphaA).mem (pReadF seedZ alphaA).cprime)⁻¹
    simp [pole_row_eq, pReadF, readPub, qF, Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow,
      cellRead, cellDec, cellVerify]
      <;> first | ring | skip

theorem pDecPF_accepts : Vmem (memInputs seedZ) (pDecPF seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨?_, ?_, ?_, rfl⟩, ?_⟩
  · exact GlobalCarryRecognizer.enc_cons seedZ_ne_zero op9Head op9ParentTail
  · simp [pDecPF, decPub, cDecPF, cHead9, cVerifyF, Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · simp [pDecPF, decPub, cDecPF, cHead9, cVerifyF, Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · show (pDecPF seedZ alphaA).icur = (pDecPF seedZ alphaA).ipre; rfl

theorem pHalt9_accepts : Vmem (memInputs seedZ) (pHalt9 seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
  · simp [haltPub, pHalt9, fp, GlobalCarryRecognizer.enc_atom, memInputs]
  · simp [haltPub, pHalt9, fp, GlobalCarryRecognizer.enc_atom]

theorem pVerifyF_accepts : Vmem (memInputs seedZ) (pVerifyF seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨rfl, rfl, ?_, ?_, rfl, rfl⟩, ?_⟩
  · simp [NockVM.formRRow, NockVM.formRCprime, pVerifyF, verifyPub, cVerifyF, cReadT, recF,
  Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · simp [NockVM.formRRow, NockVM.formRCprime, pVerifyF, verifyPub, cVerifyF, cReadT, recF,
  Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · show (pVerifyF seedZ alphaA).ipre - (pVerifyF seedZ alphaA).icur =
      (pole (memInputs seedZ) (pVerifyF seedZ alphaA).mem (pVerifyF seedZ alphaA).cprime)⁻¹
    simp [pole_row_eq, pVerifyF, verifyPub, qF, Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp,
      one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip

theorem pReadT_accepts : Vmem (memInputs seedZ) (pReadT seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨rfl, rfl, ?_, ?_, rfl, rfl⟩, ?_⟩
  · simp [NockVM.formRRow, NockVM.formRCprime, pReadT, readPub, cReadT, cDecPT, recT, Pub.lambda,
  Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · simp [NockVM.formRRow, NockVM.formRCprime, pReadT, readPub, cReadT, cDecPT, recT, Pub.lambda,
  Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · show (pReadT seedZ alphaA).icur - (pReadT seedZ alphaA).ipre =
      (pole (memInputs seedZ) (pReadT seedZ alphaA).mem (pReadT seedZ alphaA).cprime)⁻¹
    simp [pole_row_eq, pReadT, readPub, qT, Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow,
      cellRead, cellDec, cellVerify]
      <;> first | ring | skip

theorem pDecPT_accepts : Vmem (memInputs seedZ) (pDecPT seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨?_, ?_, ?_, rfl⟩, ?_⟩
  · exact GlobalCarryRecognizer.enc_cons seedZ_ne_zero op9AxisAtom op9CoreFormula
  · simp [pDecPT, decPub, cDecPT, cVerifyT, cReadCoreF, Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · simp [pDecPT, decPub, cDecPT, cVerifyT, cReadCoreF, Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · show (pDecPT seedZ alphaA).icur = (pDecPT seedZ alphaA).ipre; rfl

theorem pVerifyT_accepts : Vmem (memInputs seedZ) (pVerifyT seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨rfl, rfl, ?_, ?_, rfl, rfl⟩, ?_⟩
  · simp [NockVM.formRRow, NockVM.formRCprime, pVerifyT, verifyPub, cVerifyT, cAxisAtom, recT,
  Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · simp [NockVM.formRRow, NockVM.formRCprime, pVerifyT, verifyPub, cVerifyT, cAxisAtom, recT,
  Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · show (pVerifyT seedZ alphaA).ipre - (pVerifyT seedZ alphaA).icur =
      (pole (memInputs seedZ) (pVerifyT seedZ alphaA).mem (pVerifyT seedZ alphaA).cprime)⁻¹
    simp [pole_row_eq, pVerifyT, verifyPub, qT, Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp,
      one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip

theorem pHaltA2_accepts : Vmem (memInputs seedZ) (pHaltA2 seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
  · simp [haltPub, pHaltA2, fp, GlobalCarryRecognizer.enc_atom, memInputs]
  · simp [haltPub, pHaltA2, fp, GlobalCarryRecognizer.enc_atom]

theorem pReadCoreF_accepts : Vmem (memInputs seedZ) (pReadCoreF seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨rfl, rfl, ?_, ?_, rfl, rfl⟩, ?_⟩
  · simp [NockVM.formRRow, NockVM.formRCprime, pReadCoreF, readPub, cReadCoreF, cDecCF, recCoreF,
  Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · simp [NockVM.formRRow, NockVM.formRCprime, pReadCoreF, readPub, cReadCoreF, cDecCF, recCoreF,
  Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · show (pReadCoreF seedZ alphaA).icur - (pReadCoreF seedZ alphaA).ipre =
      (pole (memInputs seedZ) (pReadCoreF seedZ alphaA).mem (pReadCoreF seedZ alphaA).cprime)⁻¹
    simp [pole_row_eq, pReadCoreF, readPub, qCoreF, Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp,
      one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip

theorem pDecCF_accepts : Vmem (memInputs seedZ) (pDecCF seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨?_, ?_, ?_, rfl⟩, ?_⟩
  · exact GlobalCarryRecognizer.enc_cons seedZ_ne_zero op1Head op9CoreNoun
  · simp [pDecCF, decPub, cDecCF, cHead1, cVerifyCoreF, Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · simp [pDecCF, decPub, cDecCF, cHead1, cVerifyCoreF, Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · show (pDecCF seedZ alphaA).icur = (pDecCF seedZ alphaA).ipre; rfl

theorem pHaltH1a_accepts : Vmem (memInputs seedZ) (pHaltH1a seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
  · simp [haltPub, pHaltH1a, fp, GlobalCarryRecognizer.enc_atom, memInputs]
  · simp [haltPub, pHaltH1a, fp, GlobalCarryRecognizer.enc_atom]

theorem pVerifyCoreF_accepts : Vmem (memInputs seedZ) (pVerifyCoreF seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨rfl, rfl, ?_, ?_, rfl, rfl⟩, ?_⟩
  · simp [NockVM.formRRow, NockVM.formRCprime, pVerifyCoreF, verifyPub, cVerifyCoreF, cDecCN,
  recCoreF, Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · simp [NockVM.formRRow, NockVM.formRCprime, pVerifyCoreF, verifyPub, cVerifyCoreF, cDecCN,
  recCoreF, Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · show (pVerifyCoreF seedZ alphaA).ipre - (pVerifyCoreF seedZ alphaA).icur =
      (pole (memInputs seedZ) (pVerifyCoreF seedZ alphaA).mem (pVerifyCoreF seedZ alphaA).cprime)⁻¹
    simp [pole_row_eq, pVerifyCoreF, verifyPub, qCoreF, Pub.lambda, Pub.cprime,
      MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip

theorem pDecCN_accepts : Vmem (memInputs seedZ) (pDecCN seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨?_, ?_, ?_, rfl⟩, ?_⟩
  · exact GlobalCarryRecognizer.enc_cons seedZ_ne_zero op9Arm op9CoreTail
  · simp [pDecCN, decPub, cDecCN, cDecArmA, cDecCTA, Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · simp [pDecCN, decPub, cDecCN, cDecArmA, cDecCTA, Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · show (pDecCN seedZ alphaA).icur = (pDecCN seedZ alphaA).ipre; rfl

theorem pDecArmA_accepts : Vmem (memInputs seedZ) (pDecArmA seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨?_, ?_, ?_, rfl⟩, ?_⟩
  · exact GlobalCarryRecognizer.enc_cons seedZ_ne_zero (.atom 1) (.atom 7)
  · simp [pDecArmA, decPub, cDecArmA, cHead1, cResult, Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · simp [pDecArmA, decPub, cDecArmA, cHead1, cResult, Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · show (pDecArmA seedZ alphaA).icur = (pDecArmA seedZ alphaA).ipre; rfl

theorem pHaltH1b_accepts : Vmem (memInputs seedZ) (pHaltH1b seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
  · simp [haltPub, pHaltH1b, fp, GlobalCarryRecognizer.enc_atom, memInputs]
  · simp [haltPub, pHaltH1b, fp, GlobalCarryRecognizer.enc_atom]

theorem pHaltA7_accepts : Vmem (memInputs seedZ) (pHaltA7 seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
  · simp [haltPub, pHaltA7, fp, GlobalCarryRecognizer.enc_atom, memInputs]
  · simp [haltPub, pHaltA7, fp, GlobalCarryRecognizer.enc_atom]

theorem pDecCTA_accepts : Vmem (memInputs seedZ) (pDecCTA seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨?_, ?_, ?_, rfl⟩, ?_⟩
  · exact GlobalCarryRecognizer.enc_cons seedZ_ne_zero (.atom 1) (.atom 9)
  · simp [pDecCTA, decPub, cDecCTA, cHead1, cHead9, Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · simp [pDecCTA, decPub, cDecCTA, cHead1, cHead9, Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · show (pDecCTA seedZ alphaA).icur = (pDecCTA seedZ alphaA).ipre; rfl

theorem pHaltH1c_accepts : Vmem (memInputs seedZ) (pHaltH1c seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
  · simp [haltPub, pHaltH1c, fp, GlobalCarryRecognizer.enc_atom, memInputs]
  · simp [haltPub, pHaltH1c, fp, GlobalCarryRecognizer.enc_atom]

theorem pHaltA9_accepts : Vmem (memInputs seedZ) (pHaltA9 seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
  · simp [haltPub, pHaltA9, fp, GlobalCarryRecognizer.enc_atom, memInputs]
  · simp [haltPub, pHaltA9, fp, GlobalCarryRecognizer.enc_atom]

-- Root B rows
theorem pReadArm_accepts : Vmem (memInputs seedZ) (pReadArm seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨rfl, rfl, ?_, ?_, rfl, rfl⟩, ?_⟩
  · simp [NockVM.formRRow, NockVM.formRCprime, pReadArm, readPub, cReadArm, cDecCN_B, recArm,
  Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · simp [NockVM.formRRow, NockVM.formRCprime, pReadArm, readPub, cReadArm, cDecCN_B, recArm,
  Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · show (pReadArm seedZ alphaA).icur - (pReadArm seedZ alphaA).ipre =
      (pole (memInputs seedZ) (pReadArm seedZ alphaA).mem (pReadArm seedZ alphaA).cprime)⁻¹
    simp [pole_row_eq, pReadArm, readPub, qArm, Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp,
      one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip

theorem pDecCN_B_accepts : Vmem (memInputs seedZ) (pDecCN_B seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨?_, ?_, ?_, rfl⟩, ?_⟩
  · exact GlobalCarryRecognizer.enc_cons seedZ_ne_zero op9Arm op9CoreTail
  · simp [pDecCN_B, decPub, cDecCN_B, cVerifyArm, cDecCT_B, Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · simp [pDecCN_B, decPub, cDecCN_B, cVerifyArm, cDecCT_B, Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · show (pDecCN_B seedZ alphaA).icur = (pDecCN_B seedZ alphaA).ipre; rfl

theorem pVerifyArm_accepts : Vmem (memInputs seedZ) (pVerifyArm seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨rfl, rfl, ?_, ?_, rfl, rfl⟩, ?_⟩
  · simp [NockVM.formRRow, NockVM.formRCprime, pVerifyArm, verifyPub, cVerifyArm, cReadArmF, recArm,
  Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · simp [NockVM.formRRow, NockVM.formRCprime, pVerifyArm, verifyPub, cVerifyArm, cReadArmF, recArm,
  Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · show (pVerifyArm seedZ alphaA).ipre - (pVerifyArm seedZ alphaA).icur =
      (pole (memInputs seedZ) (pVerifyArm seedZ alphaA).mem (pVerifyArm seedZ alphaA).cprime)⁻¹
    simp [pole_row_eq, pVerifyArm, verifyPub, qArm, Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp,
      one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip

theorem pReadArmF_accepts : Vmem (memInputs seedZ) (pReadArmF seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨rfl, rfl, ?_, ?_, rfl, rfl⟩, ?_⟩
  · simp [NockVM.formRRow, NockVM.formRCprime, pReadArmF, readPub, cReadArmF, cDecArmB, recArmF,
  Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · simp [NockVM.formRRow, NockVM.formRCprime, pReadArmF, readPub, cReadArmF, cDecArmB, recArmF,
  Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · show (pReadArmF seedZ alphaA).icur - (pReadArmF seedZ alphaA).ipre =
      (pole (memInputs seedZ) (pReadArmF seedZ alphaA).mem (pReadArmF seedZ alphaA).cprime)⁻¹
    simp [pole_row_eq, pReadArmF, readPub, qArmF, Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp,
      one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip

theorem pDecArmB_accepts : Vmem (memInputs seedZ) (pDecArmB seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨?_, ?_, ?_, rfl⟩, ?_⟩
  · exact GlobalCarryRecognizer.enc_cons seedZ_ne_zero (.atom 1) (.atom 7)
  · simp [pDecArmB, decPub, cDecArmB, cHead1, cVerifyArmF, Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · simp [pDecArmB, decPub, cDecArmB, cHead1, cVerifyArmF, Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · show (pDecArmB seedZ alphaA).icur = (pDecArmB seedZ alphaA).ipre; rfl

theorem pHaltH1_B1_accepts : Vmem (memInputs seedZ) (pHaltH1_B1 seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
  · simp [haltPub, pHaltH1_B1, fp, GlobalCarryRecognizer.enc_atom, memInputs]
  · simp [haltPub, pHaltH1_B1, fp, GlobalCarryRecognizer.enc_atom]

theorem pVerifyArmF_accepts : Vmem (memInputs seedZ) (pVerifyArmF seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨rfl, rfl, ?_, ?_, rfl, rfl⟩, ?_⟩
  · simp [NockVM.formRRow, NockVM.formRCprime, pVerifyArmF, verifyPub, cVerifyArmF, cResult,
      recArmF,
  Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · simp [NockVM.formRRow, NockVM.formRCprime, pVerifyArmF, verifyPub, cVerifyArmF, cResult,
      recArmF,
  Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · show (pVerifyArmF seedZ alphaA).ipre - (pVerifyArmF seedZ alphaA).icur =
      (pole (memInputs seedZ) (pVerifyArmF seedZ alphaA).mem (pVerifyArmF seedZ alphaA).cprime)⁻¹
    simp [pole_row_eq, pVerifyArmF, verifyPub, qArmF, Pub.lambda, Pub.cprime,
        MemoryTable.pwScaleExp,
      one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip

theorem pHaltA7_B_accepts : Vmem (memInputs seedZ) (pHaltA7_B seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
  · simp [haltPub, pHaltA7_B, fp, GlobalCarryRecognizer.enc_atom, memInputs]
  · simp [haltPub, pHaltA7_B, fp, GlobalCarryRecognizer.enc_atom]

theorem pDecCT_B_accepts : Vmem (memInputs seedZ) (pDecCT_B seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨?_, ?_, ?_, rfl⟩, ?_⟩
  · exact GlobalCarryRecognizer.enc_cons seedZ_ne_zero (.atom 1) (.atom 9)
  · simp [pDecCT_B, decPub, cDecCT_B, cHead1, cHead9, Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · simp [pDecCT_B, decPub, cDecCT_B, cHead1, cHead9, Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · show (pDecCT_B seedZ alphaA).icur = (pDecCT_B seedZ alphaA).ipre; rfl

theorem pHaltH1_B2_accepts : Vmem (memInputs seedZ) (pHaltH1_B2 seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
  · simp [haltPub, pHaltH1_B2, fp, GlobalCarryRecognizer.enc_atom, memInputs]
  · simp [haltPub, pHaltH1_B2, fp, GlobalCarryRecognizer.enc_atom]

theorem pHaltA9_B_accepts : Vmem (memInputs seedZ) (pHaltA9_B seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
  · simp [haltPub, pHaltA9_B, fp, GlobalCarryRecognizer.enc_atom, memInputs]
  · simp [haltPub, pHaltA9_B, fp, GlobalCarryRecognizer.enc_atom]

/-! ## Memory row acceptance -/

theorem memoryRowsAccepted : (exec seedZ alphaA).MemoryRowsAccepted := by
  rw [ExactExecution.memoryRowsAccepted_iff, memoryRows_eq]
  intro row hrow
  simp [List.mem_cons, List.not_mem_nil, or_false] at hrow
  rcases hrow with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl
  -- BFS order: readF, readArm, decPF, decCN_B, halt9, verifyF, verifyArm, decCT_B,
  -- readT, readArmF, haltH1_B2, haltA9_B, decPT, decArmB, verifyT, readCoreF,
  -- haltH1_B1, verifyArmF, haltA2, decCF, haltA7_B, haltH1a, verifyCoreF,
  -- decCN, decArmA, decCTA, haltH1b, haltA7, haltH1c, haltA9
  · exact ⟨rfl, rfl, pReadF_accepts, rfl⟩
  · exact ⟨rfl, rfl, pReadArm_accepts, rfl⟩
  · exact ⟨rfl, rfl, pDecPF_accepts, rfl⟩
  · exact ⟨rfl, rfl, pDecCN_B_accepts, rfl⟩
  · exact ⟨rfl, rfl, pHalt9_accepts, rfl⟩
  · exact ⟨rfl, rfl, pVerifyF_accepts, rfl⟩
  · exact ⟨rfl, rfl, pVerifyArm_accepts, rfl⟩
  · exact ⟨rfl, rfl, pDecCT_B_accepts, rfl⟩
  · exact ⟨rfl, rfl, pReadT_accepts, rfl⟩
  · exact ⟨rfl, rfl, pReadArmF_accepts, rfl⟩
  · exact ⟨rfl, rfl, pHaltH1_B2_accepts, rfl⟩
  · exact ⟨rfl, rfl, pHaltA9_B_accepts, rfl⟩
  · exact ⟨rfl, rfl, pDecPT_accepts, rfl⟩
  · exact ⟨rfl, rfl, pDecArmB_accepts, rfl⟩
  · exact ⟨rfl, rfl, pVerifyT_accepts, rfl⟩
  · exact ⟨rfl, rfl, pReadCoreF_accepts, rfl⟩
  · exact ⟨rfl, rfl, pHaltH1_B1_accepts, rfl⟩
  · exact ⟨rfl, rfl, pVerifyArmF_accepts, rfl⟩
  · exact ⟨rfl, rfl, pHaltA2_accepts, rfl⟩
  · exact ⟨rfl, rfl, pDecCF_accepts, rfl⟩
  · exact ⟨rfl, rfl, pHaltA7_B_accepts, rfl⟩
  · exact ⟨rfl, rfl, pHaltH1a_accepts, rfl⟩
  · exact ⟨rfl, rfl, pVerifyCoreF_accepts, rfl⟩
  · exact ⟨rfl, rfl, pDecCN_accepts, rfl⟩
  · exact ⟨rfl, rfl, pDecArmA_accepts, rfl⟩
  · exact ⟨rfl, rfl, pDecCTA_accepts, rfl⟩
  · exact ⟨rfl, rfl, pHaltH1b_accepts, rfl⟩
  · exact ⟨rfl, rfl, pHaltA7_accepts, rfl⟩
  · exact ⟨rfl, rfl, pHaltH1c_accepts, rfl⟩
  · exact ⟨rfl, rfl, pHaltA9_accepts, rfl⟩

/-! ## Memory genericity (`WF`) -/

theorem pReadF_wf : MemoryTable.WF (memInputs seedZ) (pReadF seedZ alphaA) where
  pole_ne _ := by
    simpa [pole_row_eq, pReadF, readPub, Pub.cprime, Option.getD] using poleF_ne
theorem pVerifyF_wf : MemoryTable.WF (memInputs seedZ) (pVerifyF seedZ alphaA) where
  pole_ne _ := by
    simpa [pole_row_eq, pVerifyF, verifyPub, Pub.cprime, Option.getD] using poleF_ne
theorem pReadT_wf : MemoryTable.WF (memInputs seedZ) (pReadT seedZ alphaA) where
  pole_ne _ := by
    simpa [pole_row_eq, pReadT, readPub, Pub.cprime, Option.getD] using poleT_ne
theorem pVerifyT_wf : MemoryTable.WF (memInputs seedZ) (pVerifyT seedZ alphaA) where
  pole_ne _ := by
    simpa [pole_row_eq, pVerifyT, verifyPub, Pub.cprime, Option.getD] using poleT_ne
theorem pReadArm_wf : MemoryTable.WF (memInputs seedZ) (pReadArm seedZ alphaA) where
  pole_ne _ := by
    simpa [pole_row_eq, pReadArm, readPub, Pub.cprime, Option.getD] using poleArm_ne
theorem pVerifyArm_wf : MemoryTable.WF (memInputs seedZ) (pVerifyArm seedZ alphaA) where
  pole_ne _ := by
    simpa [pole_row_eq, pVerifyArm, verifyPub, Pub.cprime, Option.getD] using poleArm_ne
theorem pReadCoreF_wf : MemoryTable.WF (memInputs seedZ) (pReadCoreF seedZ alphaA) where
  pole_ne _ := by
    simpa [pole_row_eq, pReadCoreF, readPub, Pub.cprime, Option.getD] using poleCoreF_ne
theorem pVerifyCoreF_wf : MemoryTable.WF (memInputs seedZ) (pVerifyCoreF seedZ alphaA) where
  pole_ne _ := by
    simpa [pole_row_eq, pVerifyCoreF, verifyPub, Pub.cprime, Option.getD] using poleCoreF_ne
theorem pReadArmF_wf : MemoryTable.WF (memInputs seedZ) (pReadArmF seedZ alphaA) where
  pole_ne _ := by
    simpa [pole_row_eq, pReadArmF, readPub, Pub.cprime, Option.getD] using poleArmF_ne
theorem pVerifyArmF_wf : MemoryTable.WF (memInputs seedZ) (pVerifyArmF seedZ alphaA) where
  pole_ne _ := by
    simpa [pole_row_eq, pVerifyArmF, verifyPub, Pub.cprime, Option.getD] using poleArmF_ne

theorem halt_wf (k : ℕ) (acc : K) :
    MemoryTable.WF (memInputs seedZ) (haltPub seedZ k acc) where
  pole_ne h := by simp [haltPub] at h

theorem dec_wf (pt lc rc : MemoryTable.Cell K) (lcSt rcSt : MemoryTable.MState) (acc : K) :
    MemoryTable.WF (memInputs seedZ) (decPub seedZ pt lc rc lcSt rcSt acc) where
  pole_ne h := by simp [decPub] at h

/-! ## BFS re-indexing of the canonical memory rows (pub projection) -/

theorem memoryPubAt_0 :
    (exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩ = pReadF seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_1 :
    (exec seedZ alphaA).memoryPubAt ⟨1, by norm_num [cfg]⟩ = pReadArm seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_2 :
    (exec seedZ alphaA).memoryPubAt ⟨2, by norm_num [cfg]⟩ = pDecPF seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_3 :
    (exec seedZ alphaA).memoryPubAt ⟨3, by norm_num [cfg]⟩ = pDecCN_B seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_4 :
    (exec seedZ alphaA).memoryPubAt ⟨4, by norm_num [cfg]⟩ = pHalt9 seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_5 :
    (exec seedZ alphaA).memoryPubAt ⟨5, by norm_num [cfg]⟩ = pVerifyF seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_6 :
    (exec seedZ alphaA).memoryPubAt ⟨6, by norm_num [cfg]⟩ = pVerifyArm seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_7 :
    (exec seedZ alphaA).memoryPubAt ⟨7, by norm_num [cfg]⟩ = pDecCT_B seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_8 :
    (exec seedZ alphaA).memoryPubAt ⟨8, by norm_num [cfg]⟩ = pReadT seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_9 :
    (exec seedZ alphaA).memoryPubAt ⟨9, by norm_num [cfg]⟩ = pReadArmF seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_10 :
    (exec seedZ alphaA).memoryPubAt ⟨10, by norm_num [cfg]⟩ = pHaltH1_B2 seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_11 :
    (exec seedZ alphaA).memoryPubAt ⟨11, by norm_num [cfg]⟩ = pHaltA9_B seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_12 :
    (exec seedZ alphaA).memoryPubAt ⟨12, by norm_num [cfg]⟩ = pDecPT seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_13 :
    (exec seedZ alphaA).memoryPubAt ⟨13, by norm_num [cfg]⟩ = pDecArmB seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_14 :
    (exec seedZ alphaA).memoryPubAt ⟨14, by norm_num [cfg]⟩ = pVerifyT seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_15 :
    (exec seedZ alphaA).memoryPubAt ⟨15, by norm_num [cfg]⟩ = pReadCoreF seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_16 :
    (exec seedZ alphaA).memoryPubAt ⟨16, by norm_num [cfg]⟩ = pHaltH1_B1 seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_17 :
    (exec seedZ alphaA).memoryPubAt ⟨17, by norm_num [cfg]⟩ = pVerifyArmF seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_18 :
    (exec seedZ alphaA).memoryPubAt ⟨18, by norm_num [cfg]⟩ = pHaltA2 seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_19 :
    (exec seedZ alphaA).memoryPubAt ⟨19, by norm_num [cfg]⟩ = pDecCF seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_20 :
    (exec seedZ alphaA).memoryPubAt ⟨20, by norm_num [cfg]⟩ = pHaltA7_B seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_21 :
    (exec seedZ alphaA).memoryPubAt ⟨21, by norm_num [cfg]⟩ = pHaltH1a seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_22 :
    (exec seedZ alphaA).memoryPubAt ⟨22, by norm_num [cfg]⟩ = pVerifyCoreF seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_23 :
    (exec seedZ alphaA).memoryPubAt ⟨23, by norm_num [cfg]⟩ = pDecCN seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_24 :
    (exec seedZ alphaA).memoryPubAt ⟨24, by norm_num [cfg]⟩ = pDecArmA seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_25 :
    (exec seedZ alphaA).memoryPubAt ⟨25, by norm_num [cfg]⟩ = pDecCTA seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_26 :
    (exec seedZ alphaA).memoryPubAt ⟨26, by norm_num [cfg]⟩ = pHaltH1b seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_27 :
    (exec seedZ alphaA).memoryPubAt ⟨27, by norm_num [cfg]⟩ = pHaltA7 seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_28 :
    (exec seedZ alphaA).memoryPubAt ⟨28, by norm_num [cfg]⟩ = pHaltH1c seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_29 :
    (exec seedZ alphaA).memoryPubAt ⟨29, by norm_num [cfg]⟩ = pHaltA9 seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]

theorem memory_wf_all :
    ∀ i, MemoryTable.WF (cfg seedZ alphaA).challenges.memoryInputs
      ((exec seedZ alphaA).memoryPubAt i) := by
  intro i
  fin_cases i <;> first
    | (rw [memoryPubAt_0]; exact pReadF_wf)
    | (rw [memoryPubAt_1]; exact pReadArm_wf)
    | (rw [memoryPubAt_2]; exact dec_wf _ _ _ _ _ _)
    | (rw [memoryPubAt_3]; exact dec_wf _ _ _ _ _ _)
    | (rw [memoryPubAt_4]; exact halt_wf _ _)
    | (rw [memoryPubAt_5]; exact pVerifyF_wf)
    | (rw [memoryPubAt_6]; exact pVerifyArm_wf)
    | (rw [memoryPubAt_7]; exact dec_wf _ _ _ _ _ _)
    | (rw [memoryPubAt_8]; exact pReadT_wf)
    | (rw [memoryPubAt_9]; exact pReadArmF_wf)
    | (rw [memoryPubAt_10]; exact halt_wf _ _)
    | (rw [memoryPubAt_11]; exact halt_wf _ _)
    | (rw [memoryPubAt_12]; exact dec_wf _ _ _ _ _ _)
    | (rw [memoryPubAt_13]; exact dec_wf _ _ _ _ _ _)
    | (rw [memoryPubAt_14]; exact pVerifyT_wf)
    | (rw [memoryPubAt_15]; exact pReadCoreF_wf)
    | (rw [memoryPubAt_16]; exact halt_wf _ _)
    | (rw [memoryPubAt_17]; exact pVerifyArmF_wf)
    | (rw [memoryPubAt_18]; exact halt_wf _ _)
    | (rw [memoryPubAt_19]; exact dec_wf _ _ _ _ _ _)
    | (rw [memoryPubAt_20]; exact halt_wf _ _)
    | (rw [memoryPubAt_21]; exact halt_wf _ _)
    | (rw [memoryPubAt_22]; exact pVerifyCoreF_wf)
    | (rw [memoryPubAt_23]; exact dec_wf _ _ _ _ _ _)
    | (rw [memoryPubAt_24]; exact dec_wf _ _ _ _ _ _)
    | (rw [memoryPubAt_25]; exact dec_wf _ _ _ _ _ _)
    | (rw [memoryPubAt_26]; exact halt_wf _ _)
    | (rw [memoryPubAt_27]; exact halt_wf _ _)
    | (rw [memoryPubAt_28]; exact halt_wf _ _)
    | (rw [memoryPubAt_29]; exact halt_wf _ _)

theorem memory_chain :
    ∀ i : Fin (cfg seedZ alphaA).memRows,
      ∀ _ : (i : ℕ) + 1 < (cfg seedZ alphaA).memRows,
        ((exec seedZ alphaA).memoryPubAt i).icur =
          ((exec seedZ alphaA).memoryPubAt ⟨(i : ℕ) + 1, by omega⟩).ipre := by
  intro i hi
  fin_cases i
  · rw [memoryPubAt_0, memoryPubAt_1]; rfl
  · rw [memoryPubAt_1, memoryPubAt_2]; rfl
  · rw [memoryPubAt_2, memoryPubAt_3]; rfl
  · rw [memoryPubAt_3, memoryPubAt_4]; rfl
  · rw [memoryPubAt_4, memoryPubAt_5]; rfl
  · rw [memoryPubAt_5, memoryPubAt_6]; rfl
  · rw [memoryPubAt_6, memoryPubAt_7]; rfl
  · rw [memoryPubAt_7, memoryPubAt_8]; rfl
  · rw [memoryPubAt_8, memoryPubAt_9]; rfl
  · rw [memoryPubAt_9, memoryPubAt_10]; rfl
  · rw [memoryPubAt_10, memoryPubAt_11]; rfl
  · rw [memoryPubAt_11, memoryPubAt_12]; rfl
  · rw [memoryPubAt_12, memoryPubAt_13]; rfl
  · rw [memoryPubAt_13, memoryPubAt_14]; rfl
  · rw [memoryPubAt_14, memoryPubAt_15]; rfl
  · rw [memoryPubAt_15, memoryPubAt_16]; rfl
  · rw [memoryPubAt_16, memoryPubAt_17]; rfl
  · rw [memoryPubAt_17, memoryPubAt_18]; rfl
  · rw [memoryPubAt_18, memoryPubAt_19]; rfl
  · rw [memoryPubAt_19, memoryPubAt_20]; rfl
  · rw [memoryPubAt_20, memoryPubAt_21]; rfl
  · rw [memoryPubAt_21, memoryPubAt_22]; rfl
  · rw [memoryPubAt_22, memoryPubAt_23]; rfl
  · rw [memoryPubAt_23, memoryPubAt_24]; rfl
  · rw [memoryPubAt_24, memoryPubAt_25]; rfl
  · rw [memoryPubAt_25, memoryPubAt_26]; rfl
  · rw [memoryPubAt_26, memoryPubAt_27]; rfl
  · rw [memoryPubAt_27, memoryPubAt_28]; rfl
  · rw [memoryPubAt_28, memoryPubAt_29]; rfl
  · simp [cfg] at hi

/-! ## Memory tree topology -/

theorem fmem_leaf {pub : MemoryTable.Pub K} (hv : Vmem (memInputs seedZ) pub)
    (hf : MemoryTable.fanoutMem pub.st = 0) :
    MemoryTable.Fmem (lblOf seedZ pub) (fun _ => none) := by
  refine ⟨rfl, hv, ?_, ?_⟩
  · intro i
    refine ⟨fun h => ?_, fun h => absurd rfl h⟩
    rw [show (lblOf seedZ pub).1 = pub.st from rfl, hf] at h
    omega
  · intro i hi
    rw [show (lblOf seedZ pub).1 = pub.st from rfl, hf] at hi
    omega

theorem rvt_one {pub : MemoryTable.Pub K} {ct : NTree MLbl}
    (hv : Vmem (memInputs seedZ) pub) (hf : MemoryTable.fanoutMem pub.st = 1)
    (hpt : ct.label.2.2.pt = pub.lc) (hct : RVT (MemoryTable.Fmem (K := K)) ct) :
    RVT (MemoryTable.Fmem (K := K)) (mOne seedZ pub ct) := by
  unfold mOne RVT
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨rfl, hv, ?_, ?_⟩
    · intro i
      fin_cases i <;> simp [NTree.childLabel, NTree.childOpt, lblOf, hf]
    · intro i hi
      fin_cases i
      · simpa [NTree.childLabel, NTree.childOpt, MemoryTable.memCell, lblOf, NTree.label]
          using hpt
      · exact absurd hi (by rw [show (lblOf seedZ pub).1 = pub.st from rfl, hf]; decide)
  · intro s hs
    simp [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl
    exact hct
  · refine ⟨fun h => absurd h (by simp [NTree.isLeaf]), fun h => ?_⟩
    exfalso
    have h0 := h.2.2.1 ⟨0, by norm_num⟩
    rw [show (lblOf seedZ pub).1 = pub.st from rfl, hf] at h0
    simp at h0

theorem rvt_two {pub : MemoryTable.Pub K} {lt rt : NTree MLbl}
    (hv : Vmem (memInputs seedZ) pub) (hf : MemoryTable.fanoutMem pub.st = 2)
    (hl : lt.label.2.2.pt = pub.lc) (hr : rt.label.2.2.pt = pub.rc)
    (hlt : RVT (MemoryTable.Fmem (K := K)) lt)
    (hrt : RVT (MemoryTable.Fmem (K := K)) rt) :
    RVT (MemoryTable.Fmem (K := K)) (mTwo seedZ pub lt rt) := by
  unfold mTwo RVT
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨rfl, hv, ?_, ?_⟩
    · intro i
      fin_cases i <;> simp [NTree.childLabel, NTree.childOpt, lblOf, hf]
    · intro i hi
      fin_cases i
      · simpa [NTree.childLabel, NTree.childOpt, MemoryTable.memCell, lblOf, NTree.label]
          using hl
      · simpa [NTree.childLabel, NTree.childOpt, MemoryTable.memCell, lblOf, NTree.label]
          using hr
  · intro s hs
    simp [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact hlt
    · exact hrt
  · refine ⟨fun h => absurd h (by simp [NTree.isLeaf]), fun h => ?_⟩
    exfalso
    have h0 := h.2.2.1 ⟨0, by norm_num⟩
    rw [show (lblOf seedZ pub).1 = pub.st from rfl, hf] at h0
    simp at h0

theorem halt_tree_rvt {k : ℕ} {acc : K}
    (hv : Vmem (memInputs seedZ) (haltPub seedZ k acc)) :
    RVT (MemoryTable.Fmem (K := K)) (mLeaf seedZ (haltPub seedZ k acc)) := by
  unfold mLeaf RVT
  exact ⟨fmem_leaf hv rfl, by simp,
    ⟨fun _ => fmem_leaf hv rfl, fun _ => rfl⟩⟩

-- Root A: build RVT bottom-up (19 nodes)
theorem tHalt9_rvt : RVT (MemoryTable.Fmem (K := K)) (mLeaf seedZ (pHalt9 seedZ alphaA)) :=
  halt_tree_rvt pHalt9_accepts
theorem tHaltA2_rvt : RVT (MemoryTable.Fmem (K := K)) (mLeaf seedZ (pHaltA2 seedZ alphaA)) :=
  halt_tree_rvt pHaltA2_accepts
theorem tHaltH1a_rvt : RVT (MemoryTable.Fmem (K := K)) (mLeaf seedZ (pHaltH1a seedZ alphaA)) :=
  halt_tree_rvt pHaltH1a_accepts
theorem tHaltH1b_rvt : RVT (MemoryTable.Fmem (K := K)) (mLeaf seedZ (pHaltH1b seedZ alphaA)) :=
  halt_tree_rvt pHaltH1b_accepts
theorem tHaltA7_rvt : RVT (MemoryTable.Fmem (K := K)) (mLeaf seedZ (pHaltA7 seedZ alphaA)) :=
  halt_tree_rvt pHaltA7_accepts
theorem tHaltH1c_rvt : RVT (MemoryTable.Fmem (K := K)) (mLeaf seedZ (pHaltH1c seedZ alphaA)) :=
  halt_tree_rvt pHaltH1c_accepts
theorem tHaltA9_rvt : RVT (MemoryTable.Fmem (K := K)) (mLeaf seedZ (pHaltA9 seedZ alphaA)) :=
  halt_tree_rvt pHaltA9_accepts

theorem tVerifyT_rvt : RVT (MemoryTable.Fmem (K := K))
    (mOne seedZ (pVerifyT seedZ alphaA) (mLeaf seedZ (pHaltA2 seedZ alphaA))) :=
  rvt_one pVerifyT_accepts rfl rfl tHaltA2_rvt
theorem tDecArmA_rvt : RVT (MemoryTable.Fmem (K := K))
    (mTwo seedZ (pDecArmA seedZ alphaA)
      (mLeaf seedZ (pHaltH1b seedZ alphaA)) (mLeaf seedZ (pHaltA7 seedZ alphaA))) :=
  rvt_two pDecArmA_accepts rfl rfl rfl tHaltH1b_rvt tHaltA7_rvt
theorem tDecCTA_rvt : RVT (MemoryTable.Fmem (K := K))
    (mTwo seedZ (pDecCTA seedZ alphaA)
      (mLeaf seedZ (pHaltH1c seedZ alphaA)) (mLeaf seedZ (pHaltA9 seedZ alphaA))) :=
  rvt_two pDecCTA_accepts rfl rfl rfl tHaltH1c_rvt tHaltA9_rvt
theorem tDecCN_rvt : RVT (MemoryTable.Fmem (K := K))
    (mTwo seedZ (pDecCN seedZ alphaA)
      (mTwo seedZ (pDecArmA seedZ alphaA)
        (mLeaf seedZ (pHaltH1b seedZ alphaA)) (mLeaf seedZ (pHaltA7 seedZ alphaA)))
      (mTwo seedZ (pDecCTA seedZ alphaA)
        (mLeaf seedZ (pHaltH1c seedZ alphaA)) (mLeaf seedZ (pHaltA9 seedZ alphaA)))) :=
  rvt_two pDecCN_accepts rfl rfl rfl tDecArmA_rvt tDecCTA_rvt
theorem tVerifyCoreF_rvt : RVT (MemoryTable.Fmem (K := K))
    (mOne seedZ (pVerifyCoreF seedZ alphaA)
      (mTwo seedZ (pDecCN seedZ alphaA)
        (mTwo seedZ (pDecArmA seedZ alphaA)
          (mLeaf seedZ (pHaltH1b seedZ alphaA)) (mLeaf seedZ (pHaltA7 seedZ alphaA)))
        (mTwo seedZ (pDecCTA seedZ alphaA)
          (mLeaf seedZ (pHaltH1c seedZ alphaA)) (mLeaf seedZ (pHaltA9 seedZ alphaA))))) :=
  rvt_one pVerifyCoreF_accepts rfl rfl tDecCN_rvt
theorem tDecCF_rvt : RVT (MemoryTable.Fmem (K := K))
    (mTwo seedZ (pDecCF seedZ alphaA)
      (mLeaf seedZ (pHaltH1a seedZ alphaA))
      (mOne seedZ (pVerifyCoreF seedZ alphaA)
        (mTwo seedZ (pDecCN seedZ alphaA)
          (mTwo seedZ (pDecArmA seedZ alphaA)
            (mLeaf seedZ (pHaltH1b seedZ alphaA)) (mLeaf seedZ (pHaltA7 seedZ alphaA)))
          (mTwo seedZ (pDecCTA seedZ alphaA)
            (mLeaf seedZ (pHaltH1c seedZ alphaA)) (mLeaf seedZ (pHaltA9 seedZ alphaA)))))) :=
  rvt_two pDecCF_accepts rfl rfl rfl tHaltH1a_rvt tVerifyCoreF_rvt
theorem tReadCoreF_rvt : RVT (MemoryTable.Fmem (K := K))
    (mOne seedZ (pReadCoreF seedZ alphaA)
      (mTwo seedZ (pDecCF seedZ alphaA)
        (mLeaf seedZ (pHaltH1a seedZ alphaA))
        (mOne seedZ (pVerifyCoreF seedZ alphaA)
          (mTwo seedZ (pDecCN seedZ alphaA)
            (mTwo seedZ (pDecArmA seedZ alphaA)
              (mLeaf seedZ (pHaltH1b seedZ alphaA)) (mLeaf seedZ (pHaltA7 seedZ alphaA)))
            (mTwo seedZ (pDecCTA seedZ alphaA)
              (mLeaf seedZ (pHaltH1c seedZ alphaA)) (mLeaf seedZ (pHaltA9 seedZ alphaA))))))) :=
  rvt_one pReadCoreF_accepts rfl rfl tDecCF_rvt
theorem tDecPT_rvt : RVT (MemoryTable.Fmem (K := K))
    (mTwo seedZ (pDecPT seedZ alphaA)
      (mOne seedZ (pVerifyT seedZ alphaA) (mLeaf seedZ (pHaltA2 seedZ alphaA)))
      (mOne seedZ (pReadCoreF seedZ alphaA)
        (mTwo seedZ (pDecCF seedZ alphaA)
          (mLeaf seedZ (pHaltH1a seedZ alphaA))
          (mOne seedZ (pVerifyCoreF seedZ alphaA)
            (mTwo seedZ (pDecCN seedZ alphaA)
              (mTwo seedZ (pDecArmA seedZ alphaA)
                (mLeaf seedZ (pHaltH1b seedZ alphaA)) (mLeaf seedZ (pHaltA7 seedZ alphaA)))
              (mTwo seedZ (pDecCTA seedZ alphaA)
                (mLeaf seedZ (pHaltH1c seedZ alphaA))
                (mLeaf seedZ (pHaltA9 seedZ alphaA)))))))) :=
  rvt_two pDecPT_accepts rfl rfl rfl tVerifyT_rvt tReadCoreF_rvt
theorem tReadT_rvt : RVT (MemoryTable.Fmem (K := K))
    (mOne seedZ (pReadT seedZ alphaA)
      (mTwo seedZ (pDecPT seedZ alphaA)
        (mOne seedZ (pVerifyT seedZ alphaA) (mLeaf seedZ (pHaltA2 seedZ alphaA)))
        (mOne seedZ (pReadCoreF seedZ alphaA)
          (mTwo seedZ (pDecCF seedZ alphaA)
            (mLeaf seedZ (pHaltH1a seedZ alphaA))
            (mOne seedZ (pVerifyCoreF seedZ alphaA)
              (mTwo seedZ (pDecCN seedZ alphaA)
                (mTwo seedZ (pDecArmA seedZ alphaA)
                  (mLeaf seedZ (pHaltH1b seedZ alphaA)) (mLeaf seedZ (pHaltA7 seedZ alphaA)))
                (mTwo seedZ (pDecCTA seedZ alphaA)
                  (mLeaf seedZ (pHaltH1c seedZ alphaA))
                  (mLeaf seedZ (pHaltA9 seedZ alphaA))))))))) :=
  rvt_one pReadT_accepts rfl rfl tDecPT_rvt
theorem tVerifyF_rvt : RVT (MemoryTable.Fmem (K := K))
    (mOne seedZ (pVerifyF seedZ alphaA)
      (mOne seedZ (pReadT seedZ alphaA)
        (mTwo seedZ (pDecPT seedZ alphaA)
          (mOne seedZ (pVerifyT seedZ alphaA) (mLeaf seedZ (pHaltA2 seedZ alphaA)))
          (mOne seedZ (pReadCoreF seedZ alphaA)
            (mTwo seedZ (pDecCF seedZ alphaA)
              (mLeaf seedZ (pHaltH1a seedZ alphaA))
              (mOne seedZ (pVerifyCoreF seedZ alphaA)
                (mTwo seedZ (pDecCN seedZ alphaA)
                  (mTwo seedZ (pDecArmA seedZ alphaA)
                    (mLeaf seedZ (pHaltH1b seedZ alphaA)) (mLeaf seedZ (pHaltA7 seedZ alphaA)))
                  (mTwo seedZ (pDecCTA seedZ alphaA)
                    (mLeaf seedZ (pHaltH1c seedZ alphaA))
                    (mLeaf seedZ (pHaltA9 seedZ alphaA)))))))))) :=
  rvt_one pVerifyF_accepts rfl rfl tReadT_rvt
theorem tDecPF_rvt : RVT (MemoryTable.Fmem (K := K))
    (mTwo seedZ (pDecPF seedZ alphaA)
      (mLeaf seedZ (pHalt9 seedZ alphaA))
      (mOne seedZ (pVerifyF seedZ alphaA)
        (mOne seedZ (pReadT seedZ alphaA)
          (mTwo seedZ (pDecPT seedZ alphaA)
            (mOne seedZ (pVerifyT seedZ alphaA) (mLeaf seedZ (pHaltA2 seedZ alphaA)))
            (mOne seedZ (pReadCoreF seedZ alphaA)
              (mTwo seedZ (pDecCF seedZ alphaA)
                (mLeaf seedZ (pHaltH1a seedZ alphaA))
                (mOne seedZ (pVerifyCoreF seedZ alphaA)
                  (mTwo seedZ (pDecCN seedZ alphaA)
                    (mTwo seedZ (pDecArmA seedZ alphaA)
                      (mLeaf seedZ (pHaltH1b seedZ alphaA))
                      (mLeaf seedZ (pHaltA7 seedZ alphaA)))
                    (mTwo seedZ (pDecCTA seedZ alphaA)
                      (mLeaf seedZ (pHaltH1c seedZ alphaA))
                      (mLeaf seedZ (pHaltA9 seedZ alphaA))))))))))) :=
  rvt_two pDecPF_accepts rfl rfl rfl tHalt9_rvt tVerifyF_rvt
theorem rootTreeA_rvt : RVT (MemoryTable.Fmem (K := K)) (rootTreeA seedZ alphaA) := by
  show RVT _ (mOne seedZ (pReadF seedZ alphaA) _)
  exact rvt_one pReadF_accepts rfl rfl tDecPF_rvt

-- Root B: build RVT bottom-up (11 nodes)
theorem tHaltH1_B1_rvt : RVT (MemoryTable.Fmem (K := K))
    (mLeaf seedZ (pHaltH1_B1 seedZ alphaA)) :=
  halt_tree_rvt pHaltH1_B1_accepts
theorem tHaltA7_B_rvt : RVT (MemoryTable.Fmem (K := K))
    (mLeaf seedZ (pHaltA7_B seedZ alphaA)) :=
  halt_tree_rvt pHaltA7_B_accepts
theorem tHaltH1_B2_rvt : RVT (MemoryTable.Fmem (K := K))
    (mLeaf seedZ (pHaltH1_B2 seedZ alphaA)) :=
  halt_tree_rvt pHaltH1_B2_accepts
theorem tHaltA9_B_rvt : RVT (MemoryTable.Fmem (K := K))
    (mLeaf seedZ (pHaltA9_B seedZ alphaA)) :=
  halt_tree_rvt pHaltA9_B_accepts
theorem tVerifyArmF_rvt : RVT (MemoryTable.Fmem (K := K))
    (mOne seedZ (pVerifyArmF seedZ alphaA) (mLeaf seedZ (pHaltA7_B seedZ alphaA))) :=
  rvt_one pVerifyArmF_accepts rfl rfl tHaltA7_B_rvt
theorem tDecArmB_rvt : RVT (MemoryTable.Fmem (K := K))
    (mTwo seedZ (pDecArmB seedZ alphaA)
      (mLeaf seedZ (pHaltH1_B1 seedZ alphaA))
      (mOne seedZ (pVerifyArmF seedZ alphaA) (mLeaf seedZ (pHaltA7_B seedZ alphaA)))) :=
  rvt_two pDecArmB_accepts rfl rfl rfl tHaltH1_B1_rvt tVerifyArmF_rvt
theorem tReadArmF_rvt : RVT (MemoryTable.Fmem (K := K))
    (mOne seedZ (pReadArmF seedZ alphaA)
      (mTwo seedZ (pDecArmB seedZ alphaA)
        (mLeaf seedZ (pHaltH1_B1 seedZ alphaA))
        (mOne seedZ (pVerifyArmF seedZ alphaA) (mLeaf seedZ (pHaltA7_B seedZ alphaA))))) :=
  rvt_one pReadArmF_accepts rfl rfl tDecArmB_rvt
theorem tVerifyArm_rvt : RVT (MemoryTable.Fmem (K := K))
    (mOne seedZ (pVerifyArm seedZ alphaA)
      (mOne seedZ (pReadArmF seedZ alphaA)
        (mTwo seedZ (pDecArmB seedZ alphaA)
          (mLeaf seedZ (pHaltH1_B1 seedZ alphaA))
          (mOne seedZ (pVerifyArmF seedZ alphaA)
            (mLeaf seedZ (pHaltA7_B seedZ alphaA)))))) :=
  rvt_one pVerifyArm_accepts rfl rfl tReadArmF_rvt
theorem tDecCT_B_rvt : RVT (MemoryTable.Fmem (K := K))
    (mTwo seedZ (pDecCT_B seedZ alphaA)
      (mLeaf seedZ (pHaltH1_B2 seedZ alphaA)) (mLeaf seedZ (pHaltA9_B seedZ alphaA))) :=
  rvt_two pDecCT_B_accepts rfl rfl rfl tHaltH1_B2_rvt tHaltA9_B_rvt
theorem tDecCN_B_rvt : RVT (MemoryTable.Fmem (K := K))
    (mTwo seedZ (pDecCN_B seedZ alphaA)
      (mOne seedZ (pVerifyArm seedZ alphaA)
        (mOne seedZ (pReadArmF seedZ alphaA)
          (mTwo seedZ (pDecArmB seedZ alphaA)
            (mLeaf seedZ (pHaltH1_B1 seedZ alphaA))
            (mOne seedZ (pVerifyArmF seedZ alphaA)
              (mLeaf seedZ (pHaltA7_B seedZ alphaA))))))
      (mTwo seedZ (pDecCT_B seedZ alphaA)
        (mLeaf seedZ (pHaltH1_B2 seedZ alphaA)) (mLeaf seedZ (pHaltA9_B seedZ alphaA)))) :=
  rvt_two pDecCN_B_accepts rfl rfl rfl tVerifyArm_rvt tDecCT_B_rvt
theorem rootTreeB_rvt : RVT (MemoryTable.Fmem (K := K)) (rootTreeB seedZ alphaA) := by
  show RVT _ (mOne seedZ (pReadArm seedZ alphaA) _)
  exact rvt_one pReadArm_accepts rfl rfl tDecCN_B_rvt

theorem memory_topology : MemoryExactTopology (exec seedZ alphaA) := by
  intro t ht
  simp [exec, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · exact ⟨rootTreeA_rvt, by
      simp [rootTreeA, mOne, mTwo, mLeaf, properArity_node_iff]⟩
  · exact ⟨rootTreeB_rvt, by
      simp [rootTreeB, mOne, mTwo, mLeaf, properArity_node_iff]⟩

end

end Nock.NockVMROM.Thm54.TraceGen.Op9ConfigK3

#print axioms Nock.NockVMROM.Thm54.TraceGen.Op9ConfigK3.memoryRowsAccepted
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op9ConfigK3.compute_topology
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op9ConfigK3.memory_topology
