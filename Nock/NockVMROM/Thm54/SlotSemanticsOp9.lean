/-
  Nock/NockVMROM/Thm54/SlotSemanticsOp9.lean

  Named `CensusRecordPremises.slotSemantics` at an OP9 reconstruction.

  Scope (in force for this module; nothing wider is claimed).
  * Execution: `(Op9Execution hfirst)`, the already-compiled `BuildableNockExecution` over
    `K3` for `*[0 [9 [2 [1 [[1 7] [1 9]]]]]] = 7`.
    Parent compute row is `.s9`. `Λ = 7`. This is strictly off the earlier state
    gate (`slotSemantics_of_no_lookup_states`), whose hypothesis fails here.
  * Reconstruction: `computeNodesOf` / `memoryNodesOf`. Subformula slots are
    `subformulaNounOf` (prefer the row's `CallRealization` when that noun is a
    `NockProgram^Λ` realizer of the committed fingerprint). Pins the arm-fetch
    to `op9CoreNoun` / `op9Arm` without a uniqueness field (as before).
  * Join: `Noun.slot 2 op9CoreNoun = some op9Arm` (`op9_slot`) on the reconstructed
    parent; children are `.s1` so both `SkeletonSlotSemantics` clauses are vacuous.
    Not `needs.served` length, not `axisNat`. C5
    (`ExactExecutionLocalCertificates`) is inhabited at this execution in
    `AxisAtomsOp9`, not here.
  * Inhabitation: `ResidualPremises` and `MemoryRecordPremises` at this execution
    are compiled, so the named type is not a `∀` over an empty type.
    * Not done: no C2 field; capstone untouched; `Gen.lean` /
    `BFSAssign.lean` not touched.

  Paper: the paper.
-/
import Nock.NockVMROM.Thm54.CensusExtraClosure
import Nock.NockVMROM.Thm54.TraceGen.Op9DataK3

namespace Nock.NockVMROM.Thm54.SlotSemanticsOp9

open scoped Classical
open Nock Nock.Walk Nock.ComputeTable Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.GenericHonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestData
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.ServedLookupBridge
open Nock.NockVMROM.Thm54.CensusExtraClosure
open Nock.NockVMROM.Thm54.TraceGen
  (op9Subject op9ParentFormula op9Result op9AxisAtom op9CoreNoun op9Arm op9_slot)
open Nock.NockVMROM.Thm54.TraceGen.Op9ConfigK3

noncomputable section

variable (hfirst :
  ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.counts = 0 ∧
    ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.indicator = 0)

omit hfirst in private theorem zero_lt_comp : (0 : ℕ) < (cfg seedZ alphaA).compRows := by decide
omit hfirst in private theorem one_lt_comp : (1 : ℕ) < (cfg seedZ alphaA).compRows := by decide
omit hfirst in private theorem two_lt_comp : (2 : ℕ) < (cfg seedZ alphaA).compRows := by decide

private theorem op9_one : (1 : ℕ) < (Op9Execution hfirst).cfg.compRows := by
  change (1 : ℕ) < (cfg seedZ alphaA).compRows
  exact one_lt_comp

private theorem op9_two : (2 : ℕ) < (Op9Execution hfirst).cfg.compRows := by
  change (2 : ℕ) < (cfg seedZ alphaA).compRows
  exact two_lt_comp

theorem computeRowAt_zero :
    (exec seedZ alphaA).computeRowAt ⟨0, zero_lt_comp⟩ = parentRow seedZ alphaA :=
  Nock.NockVMROM.Thm54.TraceGen.Op9ConfigK3.computeRowAt_zero

theorem op9_computeRowAt_zero :
    (Op9Execution hfirst).exec.computeRowAt ⟨0, (Op9Execution hfirst).cfg.compRows_pos⟩ =
      parentRow seedZ alphaA := by
  exact computeRowAt_zero

theorem op9_computeRowAt_one :
    (Op9Execution hfirst).exec.computeRowAt ⟨1, one_lt_comp⟩ = child1Row seedZ alphaA := by
  exact Nock.NockVMROM.Thm54.TraceGen.Op9ConfigK3.computeRowAt_one

theorem op9_computeRowAt_two :
    (Op9Execution hfirst).exec.computeRowAt ⟨2, two_lt_comp⟩ = child2Row seedZ alphaA := by
  exact Nock.NockVMROM.Thm54.TraceGen.Op9ConfigK3.computeRowAt_two

/-- Parent row is `.s9`. This is the load-bearing witness that the lookup
state gate does not apply. -- the paper -/
theorem parent_is_s9 :
    ((Op9Execution hfirst).exec.computeRowAt ⟨0, (Op9Execution hfirst).cfg.compRows_pos⟩).1 = .s9 := by
  rw [op9_computeRowAt_zero]; rfl

/-- The earlier gate hypothesis is false at this execution. -/

theorem lookup_state_gate_fails :
    ¬ ∀ i : Fin (Op9Execution hfirst).cfg.compRows,
      ((Op9Execution hfirst).exec.computeRowAt i).1 ≠ .s0 ∧
        ((Op9Execution hfirst).exec.computeRowAt i).1 ≠ .s9 := by
  intro h
  exact (h ⟨0, (Op9Execution hfirst).cfg.compRows_pos⟩).2 (parent_is_s9 hfirst)

private theorem fin_val_le_two (i : Fin (Op9Execution hfirst).cfg.compRows) :
    (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 := by
  have hrows : (Op9Execution hfirst).cfg.compRows = 3 := rfl
  have hi : (i : ℕ) < 3 := by
    rw [← hrows]
    exact i.isLt
  omega

theorem row_states (i : Fin (Op9Execution hfirst).cfg.compRows) :
    ((Op9Execution hfirst).exec.computeRowAt i).1 = .s9 ∨
      ((Op9Execution hfirst).exec.computeRowAt i).1 = .s1 := by
  rcases fin_val_le_two hfirst i with h | h | h
  · have : i = ⟨0, (Op9Execution hfirst).cfg.compRows_pos⟩ := Fin.ext h
    subst this
    exact Or.inl (parent_is_s9 hfirst)
  · have : i = ⟨1, one_lt_comp⟩ := Fin.ext h
    subst this
    refine Or.inr ?_
    have hs : ((exec seedZ alphaA).computeRowAt ⟨1, one_lt_comp⟩).1 = .s1 := by
      rw [Nock.NockVMROM.Thm54.TraceGen.Op9ConfigK3.computeRowAt_one]; rfl
    exact hs
  · have : i = ⟨2, two_lt_comp⟩ := Fin.ext h
    subst this
    refine Or.inr ?_
    have hs : ((exec seedZ alphaA).computeRowAt ⟨2, two_lt_comp⟩).1 = .s1 := by
      rw [Nock.NockVMROM.Thm54.TraceGen.Op9ConfigK3.computeRowAt_two]; rfl
    exact hs

theorem parent_decomp_f_th : decompNoun parentRowData .f_th = op9AxisAtom := by
  simp [decompNoun, parentRowData, parentTailR] <;> rfl

theorem castRowData_decompNoun
    {row₁ row₂ : ComputeTable.State × ComputeTable.DTcomp K}
    (heq : row₁ = row₂) (d : SemanticTrace.ComputeRowSemanticData 97 7 row₂)
    (slot : DecSlot) :
    decompNoun (castRowData heq d) slot = decompNoun d slot := by
  cases heq
  rfl

theorem castRowData_subformulaNounOf
    {row₁ row₂ : ComputeTable.State × ComputeTable.DTcomp K}
    (heq : row₁ = row₂) (d : SemanticTrace.ComputeRowSemanticData 97 7 row₂)
    (pubR : ComputePublicRowNounRealization 97 (computePublicLabel row₁))
    (i : Fin 3) (hi : (i : ℕ) < ComputeTable.fanoutComp row₁.1)
    (slot : TripleSlot) :
    subformulaNounOf (castRowData heq d) pubR i hi slot =
      subformulaNounOf d (heq ▸ pubR) i (heq ▸ hi) slot := by
  cases heq
  rfl

theorem rows_zero :
    (Op9Execution hfirst).semanticData.rows ⟨0, (Op9Execution hfirst).cfg.compRows_pos⟩ =
      castRowData
        Nock.NockVMROM.Thm54.TraceGen.Op9ConfigK3.computeRowAt_zero
        parentRowData :=
  rfl

theorem rows_one :
    (Op9Execution hfirst).semanticData.rows ⟨1, one_lt_comp⟩ =
      castRowData
        Nock.NockVMROM.Thm54.TraceGen.Op9ConfigK3.computeRowAt_one
        child1RowData :=
  rfl

theorem rows_two :
    (Op9Execution hfirst).semanticData.rows ⟨2, two_lt_comp⟩ =
      castRowData
        Nock.NockVMROM.Thm54.TraceGen.Op9ConfigK3.computeRowAt_two
        child2RowData :=
  rfl

theorem rows_zero_decomp_f_th :
    decompNoun ((Op9Execution hfirst).semanticData.rows ⟨0, (Op9Execution hfirst).cfg.compRows_pos⟩)
      .f_th = op9AxisAtom := by
  simp only [rows_zero]
  exact (castRowData_decompNoun
      Nock.NockVMROM.Thm54.TraceGen.Op9ConfigK3.computeRowAt_zero
      parentRowData .f_th).trans parent_decomp_f_th

def residualPremises : ResidualPremises (Op9Execution hfirst) where
  inactiveDec := trivial
  axisAtoms := by
    intro i
    rcases fin_val_le_two hfirst i with h | h | h
    · have : i = ⟨0, (Op9Execution hfirst).cfg.compRows_pos⟩ := Fin.ext h
      subst this
      refine ⟨?_, ?_⟩
      · intro hs
        rw [parent_is_s9] at hs
        exact absurd hs (by decide)
      · intro
        exact ⟨2, rows_zero_decomp_f_th hfirst⟩
    · have : i = ⟨1, one_lt_comp⟩ := Fin.ext h
      subst this
      refine ⟨?_, ?_⟩ <;> intro hs <;>
        (have hst : ((Op9Execution hfirst).exec.computeRowAt ⟨1, one_lt_comp⟩).1 = .s1 := by
          rw [op9_computeRowAt_one]; rfl
         rw [hst] at hs
         exact absurd hs (by decide))
    · have : i = ⟨2, two_lt_comp⟩ := Fin.ext h
      subst this
      refine ⟨?_, ?_⟩ <;> intro hs <;>
        (have hst : ((Op9Execution hfirst).exec.computeRowAt ⟨2, two_lt_comp⟩).1 = .s1 := by
          rw [op9_computeRowAt_two]; rfl
         rw [hst] at hs
         exact absurd hs (by decide))
  q_eq_ringChar := by
    change (97 : ℕ) = ringChar TraceGen.Op9ConfigK3.K
    exact ringChar_K3.symm


theorem timestampClosed :
    ∀ i : Fin (Op9Execution hfirst).cfg.memRows,
      memoryMemRecKind ((Op9Execution hfirst).exec.memoryRowAt i).1 = .active →
        MemoryTimestampClosedAt (Op9Execution hfirst).cfg.challenges.α
          ((Op9Execution hfirst).exec.memoryRowAt i).2.2.mem.ts := by
  intro i hact
  have hmem : (Op9Execution hfirst).exec.memoryRowAt i ∈ (exec seedZ alphaA).memoryRows := by
    exact ExactExecution.memoryRowAt_mem (exec seedZ alphaA) i
  rw [Nock.NockVMROM.Thm54.TraceGen.Op9ConfigK3.memoryRows_eq] at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with
      h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
      h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · rw [h]; exact ⟨1, by simp [Op9Execution, lblOf, pReadF, readPub, recF, cfg]⟩
  · rw [h]; exact ⟨3, by simp [Op9Execution, lblOf, pReadArm, readPub, recArm, cfg]⟩
  · rw [h] at hact; exact absurd hact (by decide)
  · rw [h] at hact; exact absurd hact (by decide)
  · rw [h] at hact; exact absurd hact (by decide)
  · rw [h]; exact ⟨1, by simp [Op9Execution, lblOf, pVerifyF, verifyPub, recF, cfg]⟩
  · rw [h]; exact ⟨3, by simp [Op9Execution, lblOf, pVerifyArm, verifyPub, recArm, cfg]⟩
  · rw [h] at hact; exact absurd hact (by decide)
  · rw [h]; exact ⟨2, by simp [Op9Execution, lblOf, pReadT, readPub, recT, cfg]⟩
  · rw [h]; exact ⟨5, by simp [Op9Execution, lblOf, pReadArmF, readPub, recArmF, cfg]⟩
  · rw [h] at hact; exact absurd hact (by decide)
  · rw [h] at hact; exact absurd hact (by decide)
  · rw [h] at hact; exact absurd hact (by decide)
  · rw [h] at hact; exact absurd hact (by decide)
  · rw [h]; exact ⟨2, by simp [Op9Execution, lblOf, pVerifyT, verifyPub, recT, cfg]⟩
  · rw [h]; exact ⟨4, by simp [Op9Execution, lblOf, pReadCoreF, readPub, recCoreF, cfg]⟩
  · rw [h] at hact; exact absurd hact (by decide)
  · rw [h]; exact ⟨5, by simp [Op9Execution, lblOf, pVerifyArmF, verifyPub, recArmF, cfg]⟩
  · rw [h] at hact; exact absurd hact (by decide)
  · rw [h] at hact; exact absurd hact (by decide)
  · rw [h] at hact; exact absurd hact (by decide)
  · rw [h] at hact; exact absurd hact (by decide)
  · rw [h]; exact ⟨4, by simp [Op9Execution, lblOf, pVerifyCoreF, verifyPub, recCoreF, cfg]⟩
  · rw [h] at hact; exact absurd hact (by decide)
  · rw [h] at hact; exact absurd hact (by decide)
  · rw [h] at hact; exact absurd hact (by decide)
  · rw [h] at hact; exact absurd hact (by decide)
  · rw [h] at hact; exact absurd hact (by decide)
  · rw [h] at hact; exact absurd hact (by decide)
  · rw [h] at hact; exact absurd hact (by decide)

def memoryRecordPremises : MemoryRecordPremises (Op9Execution hfirst) :=
  memoryRecordPremises_of_timestampClosed (Op9Execution hfirst) (timestampClosed hfirst) honestVer

theorem reconstructed_parent_state (P : ResidualPremises (Op9Execution hfirst)) :
    ((computeNodeAt (Op9Execution hfirst) P ⟨0, (Op9Execution hfirst).cfg.compRows_pos⟩).skel).state = .s9 := by
  rw [reconstructed_row_state, parent_is_s9]

theorem reconstructed_child1_state (P : ResidualPremises (Op9Execution hfirst)) :
    ((computeNodeAt (Op9Execution hfirst) P ⟨1, one_lt_comp⟩).skel).state = .s1 := by
  rw [reconstructed_row_state]
  have hs : ((exec seedZ alphaA).computeRowAt ⟨1, one_lt_comp⟩).1 = .s1 := by
    rw [Nock.NockVMROM.Thm54.TraceGen.Op9ConfigK3.computeRowAt_one]; rfl
  exact hs

theorem reconstructed_child2_state (P : ResidualPremises (Op9Execution hfirst)) :
    ((computeNodeAt (Op9Execution hfirst) P ⟨2, two_lt_comp⟩).skel).state = .s1 := by
  rw [reconstructed_row_state]
  have hs : ((exec seedZ alphaA).computeRowAt ⟨2, two_lt_comp⟩).1 = .s1 := by
    rw [Nock.NockVMROM.Thm54.TraceGen.Op9ConfigK3.computeRowAt_two]; rfl
  exact hs

theorem parent_sf0_result_windowed
    (pubR : ComputePublicRowNounRealization 97
      (computePublicLabel (parentRow seedZ alphaA))) :
    subformulaNounOf parentRowData pubR ⟨0, by decide⟩
      (by simp [parentRow, ComputeTable.fanoutComp]) .result = op9CoreNoun := by
  have hlen : (0 : ℕ) < parentRowData.calls.length := by simp [parentRowData]
  have hw :
      FieldEmbedding.BoundedBy 97
          (callSlotNoun (parentRowData.calls.get ⟨0, hlen⟩) .result) ∧
        (callSlotNoun (parentRowData.calls.get ⟨0, hlen⟩) .result).leaves ≤ 7 ∧
          GlobalCarryRecognizer.enc (parentRow seedZ alphaA).2.1.z
            (callSlotNoun (parentRowData.calls.get ⟨0, hlen⟩) .result) =
            tripleFP (computeSubformulaFPs (parentRow seedZ alphaA).2.2.1 0) .result := by
    refine ⟨?_, ?_, ?_⟩
    · simp [parentRowData, parentCall1, callSlotNoun, op9CoreNoun,
        FieldEmbedding.BoundedBy]
    · simp [parentRowData, parentCall1, callSlotNoun, op9CoreNoun, Noun.leaves]
    · simp [parentRowData, parentCall1, callSlotNoun, parentRow, parentPub,
        SemanticStrategy.tripleFP, computeSubformulaFPs, ComputeTable.sfTriple, fp,
        compInputs]
  simpa [parentRowData, parentCall1, callSlotNoun] using
    subformulaNounOf_leaves_of_call parentRowData pubR ⟨0, by decide⟩
      (by simp [parentRow, ComputeTable.fanoutComp]) TripleSlot.result hlen hw

theorem parent_sf1_formula_windowed
    (pubR : ComputePublicRowNounRealization 97
      (computePublicLabel (parentRow seedZ alphaA))) :
    subformulaNounOf parentRowData pubR ⟨1, by decide⟩
      (by simp [parentRow, ComputeTable.fanoutComp]) .formula = op9Arm := by
  have hlen : (1 : ℕ) < parentRowData.calls.length := by simp [parentRowData]
  have hw :
      FieldEmbedding.BoundedBy 97
          (callSlotNoun (parentRowData.calls.get ⟨1, hlen⟩) .formula) ∧
        (callSlotNoun (parentRowData.calls.get ⟨1, hlen⟩) .formula).leaves ≤ 7 ∧
          GlobalCarryRecognizer.enc (parentRow seedZ alphaA).2.1.z
            (callSlotNoun (parentRowData.calls.get ⟨1, hlen⟩) .formula) =
            tripleFP (computeSubformulaFPs (parentRow seedZ alphaA).2.2.1 1) .formula := by
    refine ⟨?_, ?_, ?_⟩
    · simp [parentRowData, parentCall2, callSlotNoun, op9Arm, FieldEmbedding.BoundedBy]
    · simp [parentRowData, parentCall2, callSlotNoun, op9Arm, Noun.leaves]
    · simp [parentRowData, parentCall2, callSlotNoun, parentRow, parentPub,
        SemanticStrategy.tripleFP, computeSubformulaFPs, ComputeTable.sfTriple, fp,
        compInputs]
  simpa [parentRowData, parentCall2, callSlotNoun] using
    subformulaNounOf_leaves_of_call parentRowData pubR ⟨1, by decide⟩
      (by simp [parentRow, ComputeTable.fanoutComp]) TripleSlot.formula hlen hw

theorem rows_zero_sf0_result
    (pubR : ComputePublicRowNounRealization 97
      (computePublicLabel
        ((Op9Execution hfirst).exec.computeRowAt ⟨0, (Op9Execution hfirst).cfg.compRows_pos⟩)))
    (hi : (0 : ℕ) < ComputeTable.fanoutComp
      ((Op9Execution hfirst).exec.computeRowAt ⟨0, (Op9Execution hfirst).cfg.compRows_pos⟩).1) :
    subformulaNounOf ((Op9Execution hfirst).semanticData.rows ⟨0, (Op9Execution hfirst).cfg.compRows_pos⟩)
      pubR ⟨0, by decide⟩ hi .result = op9CoreNoun := by
  simp only [rows_zero]
  exact (castRowData_subformulaNounOf
      Nock.NockVMROM.Thm54.TraceGen.Op9ConfigK3.computeRowAt_zero
      parentRowData pubR ⟨0, by decide⟩ hi TripleSlot.result).trans
    (parent_sf0_result_windowed _)

theorem rows_zero_sf1_formula
    (pubR : ComputePublicRowNounRealization 97
      (computePublicLabel
        ((Op9Execution hfirst).exec.computeRowAt ⟨0, (Op9Execution hfirst).cfg.compRows_pos⟩)))
    (hi : (1 : ℕ) < ComputeTable.fanoutComp
      ((Op9Execution hfirst).exec.computeRowAt ⟨0, (Op9Execution hfirst).cfg.compRows_pos⟩).1) :
    subformulaNounOf ((Op9Execution hfirst).semanticData.rows ⟨0, (Op9Execution hfirst).cfg.compRows_pos⟩)
      pubR ⟨1, by decide⟩ hi .formula = op9Arm := by
  simp only [rows_zero]
  exact (castRowData_subformulaNounOf
      Nock.NockVMROM.Thm54.TraceGen.Op9ConfigK3.computeRowAt_zero
      parentRowData pubR ⟨1, by decide⟩ hi TripleSlot.formula).trans
    (parent_sf1_formula_windowed _)

theorem reconstructed_sf0_result (P : ResidualPremises (Op9Execution hfirst)) :
    P8Census.skeletonSubformula
        (computeNodeAt (Op9Execution hfirst) P ⟨0, (Op9Execution hfirst).cfg.compRows_pos⟩).skel
        0 .result = op9CoreNoun := by
  have hlt : ↑(0 : Fin 3) < ComputeTable.fanoutComp
      (computeNodeAt (Op9Execution hfirst) P ⟨0, (Op9Execution hfirst).cfg.compRows_pos⟩).skel.state := by
    rw [reconstructed_parent_state hfirst P]
    decide
  have hi : (0 : ℕ) < ComputeTable.fanoutComp
      ((Op9Execution hfirst).exec.computeRowAt ⟨0, (Op9Execution hfirst).cfg.compRows_pos⟩).1 := by
    rw [parent_is_s9]
    decide
  have hsf :
      P8Census.skeletonSubformula
          (computeNodeAt (Op9Execution hfirst) P ⟨0, (Op9Execution hfirst).cfg.compRows_pos⟩).skel
          0 .result =
        subformulaNounOf ((Op9Execution hfirst).semanticData.rows ⟨0, (Op9Execution hfirst).cfg.compRows_pos⟩)
          (publicRowNoun_of_execution (Op9Execution hfirst) ⟨0, (Op9Execution hfirst).cfg.compRows_pos⟩)
          ⟨0, by decide⟩ hi .result := by
    unfold P8Census.skeletonSubformula
    rw [dif_pos hlt]
    rfl
  rw [hsf]
  exact rows_zero_sf0_result hfirst _ hi

theorem reconstructed_sf1_formula (P : ResidualPremises (Op9Execution hfirst)) :
    P8Census.skeletonSubformula
        (computeNodeAt (Op9Execution hfirst) P ⟨0, (Op9Execution hfirst).cfg.compRows_pos⟩).skel
        1 .formula = op9Arm := by
  have hlt : ↑(1 : Fin 3) < ComputeTable.fanoutComp
      (computeNodeAt (Op9Execution hfirst) P ⟨0, (Op9Execution hfirst).cfg.compRows_pos⟩).skel.state := by
    rw [reconstructed_parent_state hfirst P]
    decide
  have hi : (1 : ℕ) < ComputeTable.fanoutComp
      ((Op9Execution hfirst).exec.computeRowAt ⟨0, (Op9Execution hfirst).cfg.compRows_pos⟩).1 := by
    rw [parent_is_s9]
    decide
  have hsf :
      P8Census.skeletonSubformula
          (computeNodeAt (Op9Execution hfirst) P ⟨0, (Op9Execution hfirst).cfg.compRows_pos⟩).skel
          1 .formula =
        subformulaNounOf ((Op9Execution hfirst).semanticData.rows ⟨0, (Op9Execution hfirst).cfg.compRows_pos⟩)
          (publicRowNoun_of_execution (Op9Execution hfirst) ⟨0, (Op9Execution hfirst).cfg.compRows_pos⟩)
          ⟨1, by decide⟩ hi .formula := by
    unfold P8Census.skeletonSubformula
    rw [dif_pos hlt]
    rfl
  rw [hsf]
  exact rows_zero_sf1_formula hfirst _ hi

theorem reconstructed_mr3_axis (P : ResidualPremises (Op9Execution hfirst)) :
    P8Census.skeletonMemoryAxis
        (computeNodeAt (Op9Execution hfirst) P ⟨0, (Op9Execution hfirst).cfg.compRows_pos⟩).skel 2 = 2 := by
  have hlt : ↑(2 : Fin 3) < Nock.Framework.recordCount
      (computeNodeAt (Op9Execution hfirst) P ⟨0, (Op9Execution hfirst).cfg.compRows_pos⟩).skel.state := by
    rw [reconstructed_parent_state hfirst P]
    decide
  have hi : (2 : ℕ) < Nock.Framework.recordCount
      ((Op9Execution hfirst).exec.computeRowAt ⟨0, (Op9Execution hfirst).cfg.compRows_pos⟩).1 := by
    rw [parent_is_s9]
    decide
  have hsf :
      P8Census.skeletonMemoryAxis
          (computeNodeAt (Op9Execution hfirst) P ⟨0, (Op9Execution hfirst).cfg.compRows_pos⟩).skel 2 =
        (memRecSkelOf ((Op9Execution hfirst).semanticData.rows ⟨0, (Op9Execution hfirst).cfg.compRows_pos⟩)
          (publicRowNoun_of_execution (Op9Execution hfirst) ⟨0, (Op9Execution hfirst).cfg.compRows_pos⟩)
          ⟨2, by decide⟩ hi).axis := by
    unfold P8Census.skeletonMemoryAxis
    rw [dif_pos hlt]
    rfl
  rw [hsf]
  simp [memRecSkelOf, parent_is_s9, atomVal, rows_zero_decomp_f_th, op9AxisAtom]

/-- Named `CensusRecordPremises.slotSemantics` at this OP9 reconstruction.
Written scope: `(Op9Execution hfirst)` over `K3`, parent `.s9`, `Λ = 7`. The reconstructed
arm-fetch is the honest slot `op9_slot`. Not C5; C2 is not a field.
-- -/
theorem named_slotSemantics
    (P : ResidualPremises (Op9Execution hfirst)) (M : MemoryRecordPremises (Op9Execution hfirst)) :
    ∀ s ∈ computeSkeletonRows
        (skeletonOfNodes (computeNodesOf (Op9Execution hfirst) P)
          (memoryNodesOf (Op9Execution hfirst) M)),
      SkeletonSlotSemantics s := by
  intro s hs
  obtain ⟨i, rfl⟩ := reconstructed_rows_are_nodes (Op9Execution hfirst) P M hs
  rcases fin_val_le_two hfirst i with h | h | h
  · have : i = ⟨0, (Op9Execution hfirst).cfg.compRows_pos⟩ := Fin.ext h
    subst this
    refine
      { s0_slot := fun hs0 => by
          rw [reconstructed_parent_state hfirst P] at hs0
          exact absurd hs0 (by decide)
        s9_slot := fun _ => ?_ }
    rw [reconstructed_sf0_result hfirst P, reconstructed_sf1_formula hfirst P, reconstructed_mr3_axis hfirst P]
    exact op9_slot
  · have : i = ⟨1, one_lt_comp⟩ := Fin.ext h
    subst this
    refine
      { s0_slot := fun hs0 => by
          rw [reconstructed_child1_state hfirst P] at hs0
          exact absurd hs0 (by decide)
        s9_slot := fun hs9 => by
          rw [reconstructed_child1_state hfirst P] at hs9
          exact absurd hs9 (by decide) }
  · have : i = ⟨2, two_lt_comp⟩ := Fin.ext h
    subst this
    refine
      { s0_slot := fun hs0 => by
          rw [reconstructed_child2_state hfirst P] at hs0
          exact absurd hs0 (by decide)
        s9_slot := fun hs9 => by
          rw [reconstructed_child2_state hfirst P] at hs9
          exact absurd hs9 (by decide) }

end

end Nock.NockVMROM.Thm54.SlotSemanticsOp9

#print axioms Nock.NockVMROM.Thm54.SlotSemanticsOp9.parent_is_s9
#print axioms Nock.NockVMROM.Thm54.SlotSemanticsOp9.lookup_state_gate_fails
#print axioms Nock.NockVMROM.Thm54.SlotSemanticsOp9.residualPremises
#print axioms Nock.NockVMROM.Thm54.SlotSemanticsOp9.memoryRecordPremises
#print axioms Nock.NockVMROM.Thm54.SlotSemanticsOp9.reconstructed_sf0_result
#print axioms Nock.NockVMROM.Thm54.SlotSemanticsOp9.reconstructed_sf1_formula
#print axioms Nock.NockVMROM.Thm54.SlotSemanticsOp9.reconstructed_mr3_axis
#print axioms Nock.NockVMROM.Thm54.SlotSemanticsOp9.named_slotSemantics
