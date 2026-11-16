/-
  Nock/NockVMROM/Thm54/TraceGen/Op6RowWebK3.lean

  Stage 4c of the OP6 Layer-2 CORE, over `K3`: compute/memory genericity (`WF`),
  BFS chain, and arity-2/3 topology of the fan-out-2 branch (if) program

      `*[0 [6 [[1 0] [[1 5] [1 6]]]]] = 5`

  The `.s6` parent row has `sf1_e ≠ sf2_e` (atoms 5 vs 0, taken result ≠ condition),
  and the condition value is 0 (selecting branch c).  With `c = 1` in `compInputs`,
  the RLC is `0*0 + 0*0 + 1*(5-0) = 5 ≠ 0` in K3 (char 97).
-/
import Nock.NockVMROM.Thm54.TraceGen.Op6BuildablePartsK3
import Nock.NockVMROM.Thm54.ChainedLanguage
import Nock.NockVMROM.Thm54.ExactTraversal

namespace Nock.NockVMROM.Thm54.TraceGen.Op6ConfigK3

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
    intro _hst hne
    simp [compInputs, parentPub, fp, seedZ, op6Result, op6CondResult,
      GlobalCarryRecognizer.enc_atom, ComputeTable.FP.atomFP]
    decide
  size8 := by simp [parentPub]
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
  show (fp seedZ op6ParentFormula).size ≠ 0
  simp [fp, GlobalCarryRecognizer.enc_size]
  exact fun h => (seedZ_ne_zero h).elim

theorem poleT_ne : pole (memInputs seedZ) (recT seedZ alphaA) 1 ≠ 0 := by
  rw [pole_eq]
  show (fp seedZ op6ParentTail).size ≠ 0
  simp [fp, GlobalCarryRecognizer.enc_size]
  exact fun h => (seedZ_ne_zero h).elim

theorem poleP_ne : pole (memInputs seedZ) (recP seedZ alphaA) 1 ≠ 0 := by
  rw [pole_eq]
  show (fp seedZ op6BranchPair).size ≠ 0
  simp [fp, GlobalCarryRecognizer.enc_size]
  exact fun h => (seedZ_ne_zero h).elim

theorem poleC1_ne : pole (memInputs seedZ) (recC1 seedZ alphaA) 1 ≠ 0 := by
  rw [pole_eq]
  show (fp seedZ op6BranchC).size ≠ 0
  simp [fp, GlobalCarryRecognizer.enc_size]
  exact fun h => (seedZ_ne_zero h).elim

theorem poleC2_ne : pole (memInputs seedZ) (recC2 seedZ alphaA) 1 ≠ 0 := by
  rw [pole_eq]
  show (fp seedZ op6CondFormula).size ≠ 0
  simp [fp, GlobalCarryRecognizer.enc_size]
  exact fun h => (seedZ_ne_zero h).elim

/-! ## The twenty-three memory rows are accepted by `V_mem` -/

theorem pReadF_accepts : Vmem (memInputs seedZ) (pReadF seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨rfl, rfl, ?_, ?_, rfl, rfl⟩, ?_⟩
  · simp [NockVM.formRRow, NockVM.formRCprime, pReadF, readPub, cReadF, cDecF, recF, Pub.lambda,
  Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · simp [NockVM.formRRow, NockVM.formRCprime, pReadF, readPub, cReadF, cDecF, recF, Pub.lambda,
  Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · show (pReadF seedZ alphaA).icur - (pReadF seedZ alphaA).ipre =
      (pole (memInputs seedZ) (pReadF seedZ alphaA).mem (pReadF seedZ alphaA).cprime)⁻¹
    simp [pole_row_eq, pReadF, readPub, qF, Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow,
      cellRead, cellDec, cellVerify]
      <;> first | ring | skip

theorem pDecF_accepts : Vmem (memInputs seedZ) (pDecF seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨?_, ?_, ?_, rfl⟩, ?_⟩
  · exact GlobalCarryRecognizer.enc_cons seedZ_ne_zero op6Head op6ParentTail
  · simp [pDecF, decPub, cDecF, cHalt6, cVerifyF, Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · simp [pDecF, decPub, cDecF, cHalt6, cVerifyF, Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · show (pDecF seedZ alphaA).icur = (pDecF seedZ alphaA).ipre; rfl

theorem pHalt6_accepts : Vmem (memInputs seedZ) (pHalt6 seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
  · simp [haltPub, pHalt6, fp, GlobalCarryRecognizer.enc_atom, memInputs]
  · simp [haltPub, pHalt6, fp, GlobalCarryRecognizer.enc_atom]

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
  · simp [NockVM.formRRow, NockVM.formRCprime, pReadT, readPub, cReadT, cDecT, recT, Pub.lambda,
  Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · simp [NockVM.formRRow, NockVM.formRCprime, pReadT, readPub, cReadT, cDecT, recT, Pub.lambda,
  Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · show (pReadT seedZ alphaA).icur - (pReadT seedZ alphaA).ipre =
      (pole (memInputs seedZ) (pReadT seedZ alphaA).mem (pReadT seedZ alphaA).cprime)⁻¹
    simp [pole_row_eq, pReadT, readPub, qT, Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow,
      cellRead, cellDec, cellVerify]
      <;> first | ring | skip

theorem pDecT_accepts : Vmem (memInputs seedZ) (pDecT seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨?_, ?_, ?_, rfl⟩, ?_⟩
  · exact GlobalCarryRecognizer.enc_cons seedZ_ne_zero op6CondFormula op6BranchPair
  · simp [pDecT, decPub, cDecT, cVerifyT, cReadP, Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · simp [pDecT, decPub, cDecT, cVerifyT, cReadP, Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · show (pDecT seedZ alphaA).icur = (pDecT seedZ alphaA).ipre; rfl

theorem pVerifyT_accepts : Vmem (memInputs seedZ) (pVerifyT seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨rfl, rfl, ?_, ?_, rfl, rfl⟩, ?_⟩
  · simp [NockVM.formRRow, NockVM.formRCprime, pVerifyT, verifyPub, cVerifyT, cReadC2, recT,
  Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · simp [NockVM.formRRow, NockVM.formRCprime, pVerifyT, verifyPub, cVerifyT, cReadC2, recT,
  Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · show (pVerifyT seedZ alphaA).ipre - (pVerifyT seedZ alphaA).icur =
      (pole (memInputs seedZ) (pVerifyT seedZ alphaA).mem (pVerifyT seedZ alphaA).cprime)⁻¹
    simp [pole_row_eq, pVerifyT, verifyPub, qT, Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp,
      one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip

theorem pReadP_accepts : Vmem (memInputs seedZ) (pReadP seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨rfl, rfl, ?_, ?_, rfl, rfl⟩, ?_⟩
  · simp [NockVM.formRRow, NockVM.formRCprime, pReadP, readPub, cReadP, cDecP, recP, Pub.lambda,
  Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · simp [NockVM.formRRow, NockVM.formRCprime, pReadP, readPub, cReadP, cDecP, recP, Pub.lambda,
  Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · show (pReadP seedZ alphaA).icur - (pReadP seedZ alphaA).ipre =
      (pole (memInputs seedZ) (pReadP seedZ alphaA).mem (pReadP seedZ alphaA).cprime)⁻¹
    simp [pole_row_eq, pReadP, readPub, qP, Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow,
      cellRead, cellDec, cellVerify]
      <;> first | ring | skip

theorem pHalt5_accepts : Vmem (memInputs seedZ) (pHalt5 seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
  · simp [haltPub, pHalt5, fp, GlobalCarryRecognizer.enc_atom, memInputs]
  · simp [haltPub, pHalt5, fp, GlobalCarryRecognizer.enc_atom]

theorem pDecP_accepts : Vmem (memInputs seedZ) (pDecP seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨?_, ?_, ?_, rfl⟩, ?_⟩
  · exact GlobalCarryRecognizer.enc_cons seedZ_ne_zero op6BranchC op6BranchD
  · simp [pDecP, decPub, cDecP, cVerifyP, cDecBranchD, Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · simp [pDecP, decPub, cDecP, cVerifyP, cDecBranchD, Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · show (pDecP seedZ alphaA).icur = (pDecP seedZ alphaA).ipre; rfl

theorem pVerifyP_accepts : Vmem (memInputs seedZ) (pVerifyP seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨rfl, rfl, ?_, ?_, rfl, rfl⟩, ?_⟩
  · simp [NockVM.formRRow, NockVM.formRCprime, pVerifyP, verifyPub, cVerifyP, cReadC1, recP,
  Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · simp [NockVM.formRRow, NockVM.formRCprime, pVerifyP, verifyPub, cVerifyP, cReadC1, recP,
  Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · show (pVerifyP seedZ alphaA).ipre - (pVerifyP seedZ alphaA).icur =
      (pole (memInputs seedZ) (pVerifyP seedZ alphaA).mem (pVerifyP seedZ alphaA).cprime)⁻¹
    simp [pole_row_eq, pVerifyP, verifyPub, qP, Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp,
      one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip

theorem pDecBranchD_accepts : Vmem (memInputs seedZ) (pDecBranchD seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨?_, ?_, ?_, rfl⟩, ?_⟩
  · exact GlobalCarryRecognizer.enc_cons seedZ_ne_zero (.atom 1) (.atom 6)
  · simp [pDecBranchD, decPub, cDecBranchD, cHalt1_d, cHalt6_d, Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · simp [pDecBranchD, decPub, cDecBranchD, cHalt1_d, cHalt6_d, Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · show (pDecBranchD seedZ alphaA).icur = (pDecBranchD seedZ alphaA).ipre; rfl

theorem pReadC1_accepts : Vmem (memInputs seedZ) (pReadC1 seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨rfl, rfl, ?_, ?_, rfl, rfl⟩, ?_⟩
  · simp [NockVM.formRRow, NockVM.formRCprime, pReadC1, readPub, cReadC1, cDecC1, recC1, Pub.lambda,
  Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · simp [NockVM.formRRow, NockVM.formRCprime, pReadC1, readPub, cReadC1, cDecC1, recC1, Pub.lambda,
  Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · show (pReadC1 seedZ alphaA).icur - (pReadC1 seedZ alphaA).ipre =
      (pole (memInputs seedZ) (pReadC1 seedZ alphaA).mem (pReadC1 seedZ alphaA).cprime)⁻¹
    simp [pole_row_eq, pReadC1, readPub, qC1, Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp,
      one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip

theorem pHalt1_d_accepts : Vmem (memInputs seedZ) (pHalt1_d seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
  · simp [haltPub, pHalt1_d, fp, GlobalCarryRecognizer.enc_atom, memInputs]
  · simp [haltPub, pHalt1_d, fp, GlobalCarryRecognizer.enc_atom]

theorem pHalt6_d_accepts : Vmem (memInputs seedZ) (pHalt6_d seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
  · simp [haltPub, pHalt6_d, fp, GlobalCarryRecognizer.enc_atom, memInputs]
  · simp [haltPub, pHalt6_d, fp, GlobalCarryRecognizer.enc_atom]

theorem pDecC1_accepts : Vmem (memInputs seedZ) (pDecC1 seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨?_, ?_, ?_, rfl⟩, ?_⟩
  · exact GlobalCarryRecognizer.enc_cons seedZ_ne_zero (.atom 1) op6Result
  · simp [pDecC1, decPub, cDecC1, cHalt1_c1, cVerifyC1, Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · simp [pDecC1, decPub, cDecC1, cHalt1_c1, cVerifyC1, Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · show (pDecC1 seedZ alphaA).icur = (pDecC1 seedZ alphaA).ipre; rfl

theorem pHalt1_c1_accepts : Vmem (memInputs seedZ) (pHalt1_c1 seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
  · simp [haltPub, pHalt1_c1, fp, GlobalCarryRecognizer.enc_atom, memInputs]
  · simp [haltPub, pHalt1_c1, fp, GlobalCarryRecognizer.enc_atom]

theorem pVerifyC1_accepts : Vmem (memInputs seedZ) (pVerifyC1 seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨rfl, rfl, ?_, ?_, rfl, rfl⟩, ?_⟩
  · simp [NockVM.formRRow, NockVM.formRCprime, pVerifyC1, verifyPub, cVerifyC1, cHalt5, recC1,
  Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · simp [NockVM.formRRow, NockVM.formRCprime, pVerifyC1, verifyPub, cVerifyC1, cHalt5, recC1,
  Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · show (pVerifyC1 seedZ alphaA).ipre - (pVerifyC1 seedZ alphaA).icur =
      (pole (memInputs seedZ) (pVerifyC1 seedZ alphaA).mem (pVerifyC1 seedZ alphaA).cprime)⁻¹
    simp [pole_row_eq, pVerifyC1, verifyPub, qC1, Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp,
      one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip

theorem pReadC2_accepts : Vmem (memInputs seedZ) (pReadC2 seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨rfl, rfl, ?_, ?_, rfl, rfl⟩, ?_⟩
  · simp [NockVM.formRRow, NockVM.formRCprime, pReadC2, readPub, cReadC2, cDecC2, recC2, Pub.lambda,
  Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · simp [NockVM.formRRow, NockVM.formRCprime, pReadC2, readPub, cReadC2, cDecC2, recC2, Pub.lambda,
  Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · show (pReadC2 seedZ alphaA).icur - (pReadC2 seedZ alphaA).ipre =
      (pole (memInputs seedZ) (pReadC2 seedZ alphaA).mem (pReadC2 seedZ alphaA).cprime)⁻¹
    simp [pole_row_eq, pReadC2, readPub, qC2, Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp,
      one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip

theorem pDecC2_accepts : Vmem (memInputs seedZ) (pDecC2 seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨?_, ?_, ?_, rfl⟩, ?_⟩
  · exact GlobalCarryRecognizer.enc_cons seedZ_ne_zero (.atom 1) op6CondResult
  · simp [pDecC2, decPub, cDecC2, cHalt1_c2, cVerifyC2, Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · simp [pDecC2, decPub, cDecC2, cHalt1_c2, cVerifyC2, Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · show (pDecC2 seedZ alphaA).icur = (pDecC2 seedZ alphaA).ipre; rfl

theorem pHalt1_c2_accepts : Vmem (memInputs seedZ) (pHalt1_c2 seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
  · simp [haltPub, pHalt1_c2, fp, GlobalCarryRecognizer.enc_atom, memInputs]
  · simp [haltPub, pHalt1_c2, fp, GlobalCarryRecognizer.enc_atom]

theorem pVerifyC2_accepts : Vmem (memInputs seedZ) (pVerifyC2 seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨rfl, rfl, ?_, ?_, rfl, rfl⟩, ?_⟩
  · simp [NockVM.formRRow, NockVM.formRCprime, pVerifyC2, verifyPub, cVerifyC2, cHalt0, recC2,
  Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · simp [NockVM.formRRow, NockVM.formRCprime, pVerifyC2, verifyPub, cVerifyC2, cHalt0, recC2,
  Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · show (pVerifyC2 seedZ alphaA).ipre - (pVerifyC2 seedZ alphaA).icur =
      (pole (memInputs seedZ) (pVerifyC2 seedZ alphaA).mem (pVerifyC2 seedZ alphaA).cprime)⁻¹
    simp [pole_row_eq, pVerifyC2, verifyPub, qC2, Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp,
      one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip

theorem pHalt0_accepts : Vmem (memInputs seedZ) (pHalt0 seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
  · simp [haltPub, pHalt0, fp, GlobalCarryRecognizer.enc_atom, memInputs]
  · simp [haltPub, pHalt0, fp, GlobalCarryRecognizer.enc_atom]

/-! ## Memory row acceptance -/

theorem memoryRowsAccepted : (exec seedZ alphaA).MemoryRowsAccepted := by
  rw [ExactExecution.memoryRowsAccepted_iff, memoryRows_eq]
  intro row hrow
  simp [List.mem_cons, List.not_mem_nil, or_false] at hrow
  rcases hrow with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨rfl, rfl, pReadF_accepts, rfl⟩
  · exact ⟨rfl, rfl, pDecF_accepts, rfl⟩
  · exact ⟨rfl, rfl, pHalt6_accepts, rfl⟩
  · exact ⟨rfl, rfl, pVerifyF_accepts, rfl⟩
  · exact ⟨rfl, rfl, pReadT_accepts, rfl⟩
  · exact ⟨rfl, rfl, pDecT_accepts, rfl⟩
  · exact ⟨rfl, rfl, pVerifyT_accepts, rfl⟩
  · exact ⟨rfl, rfl, pReadP_accepts, rfl⟩
  · exact ⟨rfl, rfl, pReadC2_accepts, rfl⟩
  · exact ⟨rfl, rfl, pDecP_accepts, rfl⟩
  · exact ⟨rfl, rfl, pDecC2_accepts, rfl⟩
  · exact ⟨rfl, rfl, pVerifyP_accepts, rfl⟩
  · exact ⟨rfl, rfl, pDecBranchD_accepts, rfl⟩
  · exact ⟨rfl, rfl, pHalt1_c2_accepts, rfl⟩
  · exact ⟨rfl, rfl, pVerifyC2_accepts, rfl⟩
  · exact ⟨rfl, rfl, pReadC1_accepts, rfl⟩
  · exact ⟨rfl, rfl, pHalt1_d_accepts, rfl⟩
  · exact ⟨rfl, rfl, pHalt6_d_accepts, rfl⟩
  · exact ⟨rfl, rfl, pHalt0_accepts, rfl⟩
  · exact ⟨rfl, rfl, pDecC1_accepts, rfl⟩
  · exact ⟨rfl, rfl, pHalt1_c1_accepts, rfl⟩
  · exact ⟨rfl, rfl, pVerifyC1_accepts, rfl⟩
  · exact ⟨rfl, rfl, pHalt5_accepts, rfl⟩

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
theorem pReadP_wf : MemoryTable.WF (memInputs seedZ) (pReadP seedZ alphaA) where
  pole_ne _ := by
    simpa [pole_row_eq, pReadP, readPub, Pub.cprime, Option.getD] using poleP_ne
theorem pVerifyP_wf : MemoryTable.WF (memInputs seedZ) (pVerifyP seedZ alphaA) where
  pole_ne _ := by
    simpa [pole_row_eq, pVerifyP, verifyPub, Pub.cprime, Option.getD] using poleP_ne
theorem pReadC1_wf : MemoryTable.WF (memInputs seedZ) (pReadC1 seedZ alphaA) where
  pole_ne _ := by
    simpa [pole_row_eq, pReadC1, readPub, Pub.cprime, Option.getD] using poleC1_ne
theorem pVerifyC1_wf : MemoryTable.WF (memInputs seedZ) (pVerifyC1 seedZ alphaA) where
  pole_ne _ := by
    simpa [pole_row_eq, pVerifyC1, verifyPub, Pub.cprime, Option.getD] using poleC1_ne
theorem pReadC2_wf : MemoryTable.WF (memInputs seedZ) (pReadC2 seedZ alphaA) where
  pole_ne _ := by
    simpa [pole_row_eq, pReadC2, readPub, Pub.cprime, Option.getD] using poleC2_ne
theorem pVerifyC2_wf : MemoryTable.WF (memInputs seedZ) (pVerifyC2 seedZ alphaA) where
  pole_ne _ := by
    simpa [pole_row_eq, pVerifyC2, verifyPub, Pub.cprime, Option.getD] using poleC2_ne

theorem halt_wf (k : ℕ) (acc : K) :
    MemoryTable.WF (memInputs seedZ) (haltPub seedZ k acc) where
  pole_ne h := by simp [haltPub] at h

theorem dec_wf (pt lc rc : MemoryTable.Cell K) (lcSt rcSt : MemoryTable.MState) (acc : K) :
    MemoryTable.WF (memInputs seedZ) (decPub seedZ pt lc rc lcSt rcSt acc) where
  pole_ne h := by simp [decPub] at h

/-! ## BFS re-indexing of the canonical memory rows -/

theorem memoryPubAt_0 :
    (exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩ = pReadF seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_1 :
    (exec seedZ alphaA).memoryPubAt ⟨1, by norm_num [cfg]⟩ = pDecF seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_2 :
    (exec seedZ alphaA).memoryPubAt ⟨2, by norm_num [cfg]⟩ = pHalt6 seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_3 :
    (exec seedZ alphaA).memoryPubAt ⟨3, by norm_num [cfg]⟩ = pVerifyF seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_4 :
    (exec seedZ alphaA).memoryPubAt ⟨4, by norm_num [cfg]⟩ = pReadT seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_5 :
    (exec seedZ alphaA).memoryPubAt ⟨5, by norm_num [cfg]⟩ = pDecT seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_6 :
    (exec seedZ alphaA).memoryPubAt ⟨6, by norm_num [cfg]⟩ = pVerifyT seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_7 :
    (exec seedZ alphaA).memoryPubAt ⟨7, by norm_num [cfg]⟩ = pReadP seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_8 :
    (exec seedZ alphaA).memoryPubAt ⟨8, by norm_num [cfg]⟩ = pReadC2 seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_9 :
    (exec seedZ alphaA).memoryPubAt ⟨9, by norm_num [cfg]⟩ = pDecP seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_10 :
    (exec seedZ alphaA).memoryPubAt ⟨10, by norm_num [cfg]⟩ = pDecC2 seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_11 :
    (exec seedZ alphaA).memoryPubAt ⟨11, by norm_num [cfg]⟩ = pVerifyP seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_12 :
    (exec seedZ alphaA).memoryPubAt ⟨12, by norm_num [cfg]⟩ = pDecBranchD seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_13 :
    (exec seedZ alphaA).memoryPubAt ⟨13, by norm_num [cfg]⟩ = pHalt1_c2 seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_14 :
    (exec seedZ alphaA).memoryPubAt ⟨14, by norm_num [cfg]⟩ = pVerifyC2 seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_15 :
    (exec seedZ alphaA).memoryPubAt ⟨15, by norm_num [cfg]⟩ = pReadC1 seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_16 :
    (exec seedZ alphaA).memoryPubAt ⟨16, by norm_num [cfg]⟩ = pHalt1_d seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_17 :
    (exec seedZ alphaA).memoryPubAt ⟨17, by norm_num [cfg]⟩ = pHalt6_d seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_18 :
    (exec seedZ alphaA).memoryPubAt ⟨18, by norm_num [cfg]⟩ = pHalt0 seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_19 :
    (exec seedZ alphaA).memoryPubAt ⟨19, by norm_num [cfg]⟩ = pDecC1 seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_20 :
    (exec seedZ alphaA).memoryPubAt ⟨20, by norm_num [cfg]⟩ = pHalt1_c1 seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_21 :
    (exec seedZ alphaA).memoryPubAt ⟨21, by norm_num [cfg]⟩ = pVerifyC1 seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_22 :
    (exec seedZ alphaA).memoryPubAt ⟨22, by norm_num [cfg]⟩ = pHalt5 seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]

theorem memory_wf_all :
    ∀ i, MemoryTable.WF (cfg seedZ alphaA).challenges.memoryInputs
      ((exec seedZ alphaA).memoryPubAt i) := by
  intro i
  fin_cases i
  · rw [memoryPubAt_0]; exact pReadF_wf
  · rw [memoryPubAt_1]; exact dec_wf _ _ _ _ _ _
  · rw [memoryPubAt_2]; exact halt_wf _ _
  · rw [memoryPubAt_3]; exact pVerifyF_wf
  · rw [memoryPubAt_4]; exact pReadT_wf
  · rw [memoryPubAt_5]; exact dec_wf _ _ _ _ _ _
  · rw [memoryPubAt_6]; exact pVerifyT_wf
  · rw [memoryPubAt_7]; exact pReadP_wf
  · rw [memoryPubAt_8]; exact pReadC2_wf
  · rw [memoryPubAt_9]; exact dec_wf _ _ _ _ _ _
  · rw [memoryPubAt_10]; exact dec_wf _ _ _ _ _ _
  · rw [memoryPubAt_11]; exact pVerifyP_wf
  · rw [memoryPubAt_12]; exact dec_wf _ _ _ _ _ _
  · rw [memoryPubAt_13]; exact halt_wf _ _
  · rw [memoryPubAt_14]; exact pVerifyC2_wf
  · rw [memoryPubAt_15]; exact pReadC1_wf
  · rw [memoryPubAt_16]; exact halt_wf _ _
  · rw [memoryPubAt_17]; exact halt_wf _ _
  · rw [memoryPubAt_18]; exact halt_wf _ _
  · rw [memoryPubAt_19]; exact dec_wf _ _ _ _ _ _
  · rw [memoryPubAt_20]; exact halt_wf _ _
  · rw [memoryPubAt_21]; exact pVerifyC1_wf
  · rw [memoryPubAt_22]; exact halt_wf _ _

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
  · simp [cfg] at hi

/-! ## Arity-2 `Fmem` topology on the twenty-three-row forest -/

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

theorem tHalt6_rvt : RVT (MemoryTable.Fmem (K := K)) (tHalt6 seedZ alphaA) :=
  halt_tree_rvt pHalt6_accepts
theorem tHalt5_rvt : RVT (MemoryTable.Fmem (K := K)) (tHalt5 seedZ alphaA) :=
  halt_tree_rvt pHalt5_accepts
theorem tHalt0_rvt : RVT (MemoryTable.Fmem (K := K)) (tHalt0 seedZ alphaA) :=
  halt_tree_rvt pHalt0_accepts
theorem tHalt1_c1_rvt : RVT (MemoryTable.Fmem (K := K)) (tHalt1_c1 seedZ alphaA) :=
  halt_tree_rvt pHalt1_c1_accepts
theorem tHalt1_c2_rvt : RVT (MemoryTable.Fmem (K := K)) (tHalt1_c2 seedZ alphaA) :=
  halt_tree_rvt pHalt1_c2_accepts
theorem tHalt1_d_rvt : RVT (MemoryTable.Fmem (K := K)) (tHalt1_d seedZ alphaA) :=
  halt_tree_rvt pHalt1_d_accepts
theorem tHalt6_d_rvt : RVT (MemoryTable.Fmem (K := K)) (tHalt6_d seedZ alphaA) :=
  halt_tree_rvt pHalt6_d_accepts

theorem tVerifyC2_rvt : RVT (MemoryTable.Fmem (K := K)) (tVerifyC2 seedZ alphaA) :=
  rvt_one pVerifyC2_accepts rfl rfl tHalt0_rvt
theorem tDecC2_rvt : RVT (MemoryTable.Fmem (K := K)) (tDecC2 seedZ alphaA) :=
  rvt_two pDecC2_accepts rfl rfl rfl tHalt1_c2_rvt tVerifyC2_rvt
theorem tReadC2_rvt : RVT (MemoryTable.Fmem (K := K)) (tReadC2 seedZ alphaA) :=
  rvt_one pReadC2_accepts rfl rfl tDecC2_rvt
theorem tVerifyC1_rvt : RVT (MemoryTable.Fmem (K := K)) (tVerifyC1 seedZ alphaA) :=
  rvt_one pVerifyC1_accepts rfl rfl tHalt5_rvt
theorem tDecC1_rvt : RVT (MemoryTable.Fmem (K := K)) (tDecC1 seedZ alphaA) :=
  rvt_two pDecC1_accepts rfl rfl rfl tHalt1_c1_rvt tVerifyC1_rvt
theorem tReadC1_rvt : RVT (MemoryTable.Fmem (K := K)) (tReadC1 seedZ alphaA) :=
  rvt_one pReadC1_accepts rfl rfl tDecC1_rvt
theorem tVerifyP_rvt : RVT (MemoryTable.Fmem (K := K)) (tVerifyP seedZ alphaA) :=
  rvt_one pVerifyP_accepts rfl rfl tReadC1_rvt
theorem tDecBranchD_rvt : RVT (MemoryTable.Fmem (K := K)) (tDecBranchD seedZ alphaA) :=
  rvt_two pDecBranchD_accepts rfl rfl rfl tHalt1_d_rvt tHalt6_d_rvt
theorem tDecP_rvt : RVT (MemoryTable.Fmem (K := K)) (tDecP seedZ alphaA) :=
  rvt_two pDecP_accepts rfl rfl rfl tVerifyP_rvt tDecBranchD_rvt
theorem tReadP_rvt : RVT (MemoryTable.Fmem (K := K)) (tReadP seedZ alphaA) :=
  rvt_one pReadP_accepts rfl rfl tDecP_rvt
theorem tVerifyT_rvt : RVT (MemoryTable.Fmem (K := K)) (tVerifyT seedZ alphaA) :=
  rvt_one pVerifyT_accepts rfl rfl tReadC2_rvt
theorem tDecT_rvt : RVT (MemoryTable.Fmem (K := K)) (tDecT seedZ alphaA) :=
  rvt_two pDecT_accepts rfl rfl rfl tVerifyT_rvt tReadP_rvt
theorem tReadT_rvt : RVT (MemoryTable.Fmem (K := K)) (tReadT seedZ alphaA) :=
  rvt_one pReadT_accepts rfl rfl tDecT_rvt
theorem tVerifyF_rvt : RVT (MemoryTable.Fmem (K := K)) (tVerifyF seedZ alphaA) :=
  rvt_one pVerifyF_accepts rfl rfl tReadT_rvt
theorem tDecF_rvt : RVT (MemoryTable.Fmem (K := K)) (tDecF seedZ alphaA) :=
  rvt_two pDecF_accepts rfl rfl rfl tHalt6_rvt tVerifyF_rvt
theorem rootTree_rvt : RVT (MemoryTable.Fmem (K := K)) (rootTree seedZ alphaA) :=
  rvt_one pReadF_accepts rfl rfl tDecF_rvt

theorem memory_topology : MemoryExactTopology (exec seedZ alphaA) := by
  intro t ht
  simp [exec, List.mem_cons, List.not_mem_nil, or_false] at ht
  subst ht
  refine ⟨rootTree_rvt, ?_⟩
  show ProperArity 2 (rootTree seedZ alphaA)
  simp [rootTree, tDecF, tHalt6, tVerifyF, tReadT, tDecT, tVerifyT, tHalt5,
    tReadP, tDecP, tVerifyP, tReadC1, tDecC1, tHalt1_c1, tVerifyC1,
    tReadC2, tDecC2, tHalt1_c2, tVerifyC2, tHalt0,
    tDecBranchD, tHalt1_d, tHalt6_d, mLeaf, mOne, mTwo]

end

end Nock.NockVMROM.Thm54.TraceGen.Op6ConfigK3

#print axioms Nock.NockVMROM.Thm54.TraceGen.Op6ConfigK3.compute_wf_all
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op6ConfigK3.compute_chain
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op6ConfigK3.compute_topology
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op6ConfigK3.memory_wf_all
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op6ConfigK3.memory_chain
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op6ConfigK3.memory_topology
