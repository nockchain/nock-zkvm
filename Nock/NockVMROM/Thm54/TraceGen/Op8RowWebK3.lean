/-
  Nock/NockVMROM/Thm54/TraceGen/Op8RowWebK3.lean

  Stage 4c of the OP8 Layer-2 CORE, over `K3`: compute/memory genericity (`WF`),
  BFS chain, and arity-2/3 topology of the fan-out-2 push program

      `*[0 [8 [1 3] [1 5]]] = 5`

  The `.s8` parent row has `sf1_e ≠ sf2_e` (atoms 5 vs 3, consumer result ≠
  intermediate), and `sf1_s = op8PushedSubject` (autocons threading).  With `c = 1` in
  `compInputs`, the RLC is `0*0 + 0*0 + 1*(5-3) = 2 ≠ 0` in K3 (char 97).
-/
import Nock.NockVMROM.Thm54.TraceGen.Op8BuildablePartsK3
import Nock.NockVMROM.Thm54.ChainedLanguage
import Nock.NockVMROM.Thm54.ExactTraversal

namespace Nock.NockVMROM.Thm54.TraceGen.Op8ConfigK3

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
    (exec seedZ alphaA).computePubAt ⟨1, by norm_num [cfg]⟩ = child2Pub seedZ alphaA := by
  norm_num [ExactExecution.computePubAt, ExactExecution.computeRowAt, computeRows_eq, cfg,
    child2Row, child2Pub]

theorem computePubAt_two :
    (exec seedZ alphaA).computePubAt ⟨2, by norm_num [cfg]⟩ = child1Pub seedZ alphaA := by
  norm_num [ExactExecution.computePubAt, ExactExecution.computeRowAt, computeRows_eq, cfg,
    child1Row, child1Pub]

/-! ## Compute genericity (`WF`) per row -/

theorem parent_wf : ComputeTable.WF (compInputs seedZ alphaA) (parentPub seedZ alphaA) where
  rlc5 := by
    intro _hst hne
    simp [compInputs, parentPub, fp, seedZ, op8Result, op8Sb,
      GlobalCarryRecognizer.enc_atom, ComputeTable.FP.atomFP]
    decide
  size8 := by
    simp [parentPub, fp, GlobalCarryRecognizer.enc_size]
    exact ⟨fun h => (seedZ_ne_zero h).elim, fun h => (seedZ_ne_zero h).elim⟩
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
  · rw [computePubAt_one]; exact child2_wf
  · rw [computePubAt_two]; exact child1_wf

theorem compute_chain :
    ∀ i : Fin (cfg seedZ alphaA).compRows,
      ∀ _ : (i : ℕ) + 1 < (cfg seedZ alphaA).compRows,
        ((exec seedZ alphaA).computePubAt i).ln =
          ((exec seedZ alphaA).computePubAt ⟨(i : ℕ) + 1, by omega⟩).ln_prev := by
  intro i hi
  fin_cases i
  · rw [computePubAt_zero, computePubAt_one]
    simp [parentPub, child2Pub, op1PubOf]
  · rw [computePubAt_one, computePubAt_two]
    simp [child2Pub, child1Pub, op1PubOf, pow_succ]
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
      · simp [parentRow, child2Row, child2Pub, op1PubOf, parentPub, ComputeTable.sfTriple,
          NTree.childLabel, NTree.childOpt, NTree.label]
      · simp [parentRow, child1Row, child1Pub, op1PubOf, parentPub, ComputeTable.sfTriple,
          NTree.childLabel, NTree.childOpt, NTree.label]
      · simp [parentRow, ComputeTable.fanoutComp] at hi
  · intro s hs
    simp [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact child2Tree_rvt
    · exact child1Tree_rvt
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
  show (fp seedZ op8ParentFormula).size ≠ 0
  simp [fp, GlobalCarryRecognizer.enc_size]
  exact fun h => (seedZ_ne_zero h).elim

theorem poleT_ne : pole (memInputs seedZ) (recT seedZ alphaA) 1 ≠ 0 := by
  rw [pole_eq]
  show (fp seedZ op8ParentTail).size ≠ 0
  simp [fp, GlobalCarryRecognizer.enc_size]
  exact fun h => (seedZ_ne_zero h).elim

theorem poleB_ne : pole (memInputs seedZ) (recB seedZ alphaA) 1 ≠ 0 := by
  rw [pole_eq]
  show (fp seedZ op8ChildFormulaB).size ≠ 0
  simp [fp, GlobalCarryRecognizer.enc_size]
  exact fun h => (seedZ_ne_zero h).elim

theorem poleC_ne : pole (memInputs seedZ) (recC seedZ alphaA) 1 ≠ 0 := by
  rw [pole_eq]
  show (fp seedZ op8ChildFormulaC).size ≠ 0
  simp [fp, GlobalCarryRecognizer.enc_size]
  exact fun h => (seedZ_ne_zero h).elim

/-! ## The seventeen memory rows are accepted by `V_mem` -/

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
  · exact GlobalCarryRecognizer.enc_cons seedZ_ne_zero op8Head op8ParentTail
  · simp [pDecF, decPub, cDecF, cHalt8, cVerifyF, Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · simp [pDecF, decPub, cDecF, cHalt8, cVerifyF, Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · show (pDecF seedZ alphaA).icur = (pDecF seedZ alphaA).ipre; rfl

theorem pHalt8_accepts : Vmem (memInputs seedZ) (pHalt8 seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
  · simp [haltPub, pHalt8, fp, GlobalCarryRecognizer.enc_atom, memInputs]
  · simp [haltPub, pHalt8, fp, GlobalCarryRecognizer.enc_atom]

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
  · exact GlobalCarryRecognizer.enc_cons seedZ_ne_zero op8ChildFormulaB op8ChildFormulaC
  · simp [pDecT, decPub, cDecT, cVerifyT, cReadC, Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · simp [pDecT, decPub, cDecT, cVerifyT, cReadC, Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · show (pDecT seedZ alphaA).icur = (pDecT seedZ alphaA).ipre; rfl

theorem pVerifyT_accepts : Vmem (memInputs seedZ) (pVerifyT seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨rfl, rfl, ?_, ?_, rfl, rfl⟩, ?_⟩
  · simp [NockVM.formRRow, NockVM.formRCprime, pVerifyT, verifyPub, cVerifyT, cReadB, recT,
  Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · simp [NockVM.formRRow, NockVM.formRCprime, pVerifyT, verifyPub, cVerifyT, cReadB, recT,
  Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · show (pVerifyT seedZ alphaA).ipre - (pVerifyT seedZ alphaA).icur =
      (pole (memInputs seedZ) (pVerifyT seedZ alphaA).mem (pVerifyT seedZ alphaA).cprime)⁻¹
    simp [pole_row_eq, pVerifyT, verifyPub, qT, Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp,
      one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip

theorem pReadC_accepts : Vmem (memInputs seedZ) (pReadC seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨rfl, rfl, ?_, ?_, rfl, rfl⟩, ?_⟩
  · simp [NockVM.formRRow, NockVM.formRCprime, pReadC, readPub, cReadC, cDecC, recC, Pub.lambda,
  Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · simp [NockVM.formRRow, NockVM.formRCprime, pReadC, readPub, cReadC, cDecC, recC, Pub.lambda,
  Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · show (pReadC seedZ alphaA).icur - (pReadC seedZ alphaA).ipre =
      (pole (memInputs seedZ) (pReadC seedZ alphaA).mem (pReadC seedZ alphaA).cprime)⁻¹
    simp [pole_row_eq, pReadC, readPub, qC, Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow,
      cellRead, cellDec, cellVerify]
      <;> first | ring | skip

theorem pReadB_accepts : Vmem (memInputs seedZ) (pReadB seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨rfl, rfl, ?_, ?_, rfl, rfl⟩, ?_⟩
  · simp [NockVM.formRRow, NockVM.formRCprime, pReadB, readPub, cReadB, cDecB, recB, Pub.lambda,
  Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · simp [NockVM.formRRow, NockVM.formRCprime, pReadB, readPub, cReadB, cDecB, recB, Pub.lambda,
  Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · show (pReadB seedZ alphaA).icur - (pReadB seedZ alphaA).ipre =
      (pole (memInputs seedZ) (pReadB seedZ alphaA).mem (pReadB seedZ alphaA).cprime)⁻¹
    simp [pole_row_eq, pReadB, readPub, qC, qB, Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp,
      one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip

theorem pDecC_accepts : Vmem (memInputs seedZ) (pDecC seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨?_, ?_, ?_, rfl⟩, ?_⟩
  · exact GlobalCarryRecognizer.enc_cons seedZ_ne_zero (.atom 1) op8Result
  · simp [pDecC, decPub, cDecC, cHaltC1, cVerifyC, Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · simp [pDecC, decPub, cDecC, cHaltC1, cVerifyC, Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · show (pDecC seedZ alphaA).icur = (pDecC seedZ alphaA).ipre; rfl

theorem pDecB_accepts : Vmem (memInputs seedZ) (pDecB seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨?_, ?_, ?_, rfl⟩, ?_⟩
  · exact GlobalCarryRecognizer.enc_cons seedZ_ne_zero (.atom 1) op8Sb
  · simp [pDecB, decPub, cDecB, cHaltB1, cVerifyB, Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · simp [pDecB, decPub, cDecB, cHaltB1, cVerifyB, Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · show (pDecB seedZ alphaA).icur = (pDecB seedZ alphaA).ipre; rfl

theorem pHaltC1_accepts : Vmem (memInputs seedZ) (pHaltC1 seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
  · simp [haltPub, pHaltC1, fp, GlobalCarryRecognizer.enc_atom, memInputs]
  · simp [haltPub, pHaltC1, fp, GlobalCarryRecognizer.enc_atom]

theorem pVerifyC_accepts : Vmem (memInputs seedZ) (pVerifyC seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨rfl, rfl, ?_, ?_, rfl, rfl⟩, ?_⟩
  · simp [NockVM.formRRow, NockVM.formRCprime, pVerifyC, verifyPub, cVerifyC, cHalt5, recC,
  Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · simp [NockVM.formRRow, NockVM.formRCprime, pVerifyC, verifyPub, cVerifyC, cHalt5, recC,
  Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · show (pVerifyC seedZ alphaA).ipre - (pVerifyC seedZ alphaA).icur =
      (pole (memInputs seedZ) (pVerifyC seedZ alphaA).mem (pVerifyC seedZ alphaA).cprime)⁻¹
    simp [pole_row_eq, pVerifyC, verifyPub, qC, qB, Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp,
      one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip

theorem pHaltB1_accepts : Vmem (memInputs seedZ) (pHaltB1 seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
  · simp [haltPub, pHaltB1, fp, GlobalCarryRecognizer.enc_atom, memInputs]
  · simp [haltPub, pHaltB1, fp, GlobalCarryRecognizer.enc_atom]

theorem pVerifyB_accepts : Vmem (memInputs seedZ) (pVerifyB seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨rfl, rfl, ?_, ?_, rfl, rfl⟩, ?_⟩
  · simp [NockVM.formRRow, NockVM.formRCprime, pVerifyB, verifyPub, cVerifyB, cHalt3, recB,
  Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · simp [NockVM.formRRow, NockVM.formRCprime, pVerifyB, verifyPub, cVerifyB, cHalt3, recB,
  Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip
  · show (pVerifyB seedZ alphaA).ipre - (pVerifyB seedZ alphaA).icur =
      (pole (memInputs seedZ) (pVerifyB seedZ alphaA).mem (pVerifyB seedZ alphaA).cprime)⁻¹
    simp [pole_row_eq, pVerifyB, verifyPub, qB, Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp,
      one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip

theorem pHalt5_accepts : Vmem (memInputs seedZ) (pHalt5 seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
  · simp [haltPub, pHalt5, fp, GlobalCarryRecognizer.enc_atom, memInputs]
  · simp [haltPub, pHalt5, fp, GlobalCarryRecognizer.enc_atom]

theorem pHalt3_accepts : Vmem (memInputs seedZ) (pHalt3 seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
  · simp [haltPub, pHalt3, fp, GlobalCarryRecognizer.enc_atom, memInputs]
  · simp [haltPub, pHalt3, fp, GlobalCarryRecognizer.enc_atom]

/-! ## Memory row acceptance -/

theorem memoryRowsAccepted : (exec seedZ alphaA).MemoryRowsAccepted := by
  rw [ExactExecution.memoryRowsAccepted_iff, memoryRows_eq]
  intro row hrow
  simp [List.mem_cons, List.not_mem_nil, or_false] at hrow
  rcases hrow with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl
  · exact ⟨rfl, rfl, pReadF_accepts, rfl⟩
  · exact ⟨rfl, rfl, pDecF_accepts, rfl⟩
  · exact ⟨rfl, rfl, pHalt8_accepts, rfl⟩
  · exact ⟨rfl, rfl, pVerifyF_accepts, rfl⟩
  · exact ⟨rfl, rfl, pReadT_accepts, rfl⟩
  · exact ⟨rfl, rfl, pDecT_accepts, rfl⟩
  · exact ⟨rfl, rfl, pVerifyT_accepts, rfl⟩
  · exact ⟨rfl, rfl, pReadC_accepts, rfl⟩
  · exact ⟨rfl, rfl, pReadB_accepts, rfl⟩
  · exact ⟨rfl, rfl, pDecC_accepts, rfl⟩
  · exact ⟨rfl, rfl, pDecB_accepts, rfl⟩
  · exact ⟨rfl, rfl, pHaltC1_accepts, rfl⟩
  · exact ⟨rfl, rfl, pVerifyC_accepts, rfl⟩
  · exact ⟨rfl, rfl, pHaltB1_accepts, rfl⟩
  · exact ⟨rfl, rfl, pVerifyB_accepts, rfl⟩
  · exact ⟨rfl, rfl, pHalt5_accepts, rfl⟩
  · exact ⟨rfl, rfl, pHalt3_accepts, rfl⟩

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
theorem pReadC_wf : MemoryTable.WF (memInputs seedZ) (pReadC seedZ alphaA) where
  pole_ne _ := by
    simpa [pole_row_eq, pReadC, readPub, Pub.cprime, Option.getD] using poleC_ne
theorem pVerifyC_wf : MemoryTable.WF (memInputs seedZ) (pVerifyC seedZ alphaA) where
  pole_ne _ := by
    simpa [pole_row_eq, pVerifyC, verifyPub, Pub.cprime, Option.getD] using poleC_ne
theorem pReadB_wf : MemoryTable.WF (memInputs seedZ) (pReadB seedZ alphaA) where
  pole_ne _ := by
    simpa [pole_row_eq, pReadB, readPub, Pub.cprime, Option.getD] using poleB_ne
theorem pVerifyB_wf : MemoryTable.WF (memInputs seedZ) (pVerifyB seedZ alphaA) where
  pole_ne _ := by
    simpa [pole_row_eq, pVerifyB, verifyPub, Pub.cprime, Option.getD] using poleB_ne

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
    (exec seedZ alphaA).memoryPubAt ⟨2, by norm_num [cfg]⟩ = pHalt8 seedZ alphaA := by
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
    (exec seedZ alphaA).memoryPubAt ⟨7, by norm_num [cfg]⟩ = pReadC seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_8 :
    (exec seedZ alphaA).memoryPubAt ⟨8, by norm_num [cfg]⟩ = pReadB seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_9 :
    (exec seedZ alphaA).memoryPubAt ⟨9, by norm_num [cfg]⟩ = pDecC seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_10 :
    (exec seedZ alphaA).memoryPubAt ⟨10, by norm_num [cfg]⟩ = pDecB seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_11 :
    (exec seedZ alphaA).memoryPubAt ⟨11, by norm_num [cfg]⟩ = pHaltC1 seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_12 :
    (exec seedZ alphaA).memoryPubAt ⟨12, by norm_num [cfg]⟩ = pVerifyC seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_13 :
    (exec seedZ alphaA).memoryPubAt ⟨13, by norm_num [cfg]⟩ = pHaltB1 seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_14 :
    (exec seedZ alphaA).memoryPubAt ⟨14, by norm_num [cfg]⟩ = pVerifyB seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_15 :
    (exec seedZ alphaA).memoryPubAt ⟨15, by norm_num [cfg]⟩ = pHalt5 seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_16 :
    (exec seedZ alphaA).memoryPubAt ⟨16, by norm_num [cfg]⟩ = pHalt3 seedZ alphaA := by
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
  · rw [memoryPubAt_7]; exact pReadC_wf
  · rw [memoryPubAt_8]; exact pReadB_wf
  · rw [memoryPubAt_9]; exact dec_wf _ _ _ _ _ _
  · rw [memoryPubAt_10]; exact dec_wf _ _ _ _ _ _
  · rw [memoryPubAt_11]; exact halt_wf _ _
  · rw [memoryPubAt_12]; exact pVerifyC_wf
  · rw [memoryPubAt_13]; exact halt_wf _ _
  · rw [memoryPubAt_14]; exact pVerifyB_wf
  · rw [memoryPubAt_15]; exact halt_wf _ _
  · rw [memoryPubAt_16]; exact halt_wf _ _

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
  · simp [cfg] at hi

/-! ## Arity-2 `Fmem` topology on the seventeen-row forest -/

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

theorem tHalt8_rvt : RVT (MemoryTable.Fmem (K := K)) (tHalt8 seedZ alphaA) :=
  halt_tree_rvt pHalt8_accepts
theorem tHalt5_rvt : RVT (MemoryTable.Fmem (K := K)) (tHalt5 seedZ alphaA) :=
  halt_tree_rvt pHalt5_accepts
theorem tHalt3_rvt : RVT (MemoryTable.Fmem (K := K)) (tHalt3 seedZ alphaA) :=
  halt_tree_rvt pHalt3_accepts
theorem tHaltB1_rvt : RVT (MemoryTable.Fmem (K := K)) (tHaltB1 seedZ alphaA) :=
  halt_tree_rvt pHaltB1_accepts
theorem tHaltC1_rvt : RVT (MemoryTable.Fmem (K := K)) (tHaltC1 seedZ alphaA) :=
  halt_tree_rvt pHaltC1_accepts

theorem tVerifyB_rvt : RVT (MemoryTable.Fmem (K := K)) (tVerifyB seedZ alphaA) :=
  rvt_one pVerifyB_accepts rfl rfl tHalt3_rvt
theorem tDecB_rvt : RVT (MemoryTable.Fmem (K := K)) (tDecB seedZ alphaA) :=
  rvt_two pDecB_accepts rfl rfl rfl tHaltB1_rvt tVerifyB_rvt
theorem tReadB_rvt : RVT (MemoryTable.Fmem (K := K)) (tReadB seedZ alphaA) :=
  rvt_one pReadB_accepts rfl rfl tDecB_rvt
theorem tVerifyC_rvt : RVT (MemoryTable.Fmem (K := K)) (tVerifyC seedZ alphaA) :=
  rvt_one pVerifyC_accepts rfl rfl tHalt5_rvt
theorem tDecC_rvt : RVT (MemoryTable.Fmem (K := K)) (tDecC seedZ alphaA) :=
  rvt_two pDecC_accepts rfl rfl rfl tHaltC1_rvt tVerifyC_rvt
theorem tReadC_rvt : RVT (MemoryTable.Fmem (K := K)) (tReadC seedZ alphaA) :=
  rvt_one pReadC_accepts rfl rfl tDecC_rvt
theorem tVerifyT_rvt : RVT (MemoryTable.Fmem (K := K)) (tVerifyT seedZ alphaA) :=
  rvt_one pVerifyT_accepts rfl rfl tReadB_rvt
theorem tDecT_rvt : RVT (MemoryTable.Fmem (K := K)) (tDecT seedZ alphaA) :=
  rvt_two pDecT_accepts rfl rfl rfl tVerifyT_rvt tReadC_rvt
theorem tReadT_rvt : RVT (MemoryTable.Fmem (K := K)) (tReadT seedZ alphaA) :=
  rvt_one pReadT_accepts rfl rfl tDecT_rvt
theorem tVerifyF_rvt : RVT (MemoryTable.Fmem (K := K)) (tVerifyF seedZ alphaA) :=
  rvt_one pVerifyF_accepts rfl rfl tReadT_rvt
theorem tDecF_rvt : RVT (MemoryTable.Fmem (K := K)) (tDecF seedZ alphaA) :=
  rvt_two pDecF_accepts rfl rfl rfl tHalt8_rvt tVerifyF_rvt
theorem rootTree_rvt : RVT (MemoryTable.Fmem (K := K)) (rootTree seedZ alphaA) :=
  rvt_one pReadF_accepts rfl rfl tDecF_rvt

theorem memory_topology : MemoryExactTopology (exec seedZ alphaA) := by
  intro t ht
  simp [exec, List.mem_cons, List.not_mem_nil, or_false] at ht
  subst ht
  refine ⟨rootTree_rvt, ?_⟩
  show ProperArity 2 (rootTree seedZ alphaA)
  simp [rootTree, tDecF, tHalt8, tVerifyF, tReadT, tDecT, tVerifyT, tReadC, tReadB,
    tDecC, tDecB, tHaltC1, tVerifyC, tHaltB1, tVerifyB, tHalt5, tHalt3, mLeaf, mOne, mTwo]

end

end Nock.NockVMROM.Thm54.TraceGen.Op8ConfigK3

#print axioms Nock.NockVMROM.Thm54.TraceGen.Op8ConfigK3.compute_wf_all
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op8ConfigK3.compute_chain
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op8ConfigK3.compute_topology
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op8ConfigK3.memory_wf_all
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op8ConfigK3.memory_chain
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op8ConfigK3.memory_topology
