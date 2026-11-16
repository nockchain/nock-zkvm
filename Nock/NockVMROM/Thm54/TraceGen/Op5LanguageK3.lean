/-
  Nock/NockVMROM/Thm54/TraceGen/Op5LanguageK3.lean

  Stage 4d of the OP5 Layer-2 CORE, over `K3`: the per-row `ComputeRowSemanticData`,
  memory trace, semantic IO preimage, chained/traversable language, noun realization,
  and the assembled `ExactExecutionSemanticData 97 5` for the fan-out-2 equality program

      `*[0 [5 [1 3] [1 4]]] = 1`

  Four committed records: parent formula@3 (`α¹`), parent formula-tail@2 (`α²`, the
  axis-2 NMR descent), and two child formula@3 records (`α³,α⁴`).  The `.s5` parent is
  the genuinely-new row with nine comparison roles including `equalityOperand`.  The
  two `.s1` children reuse the OP1 three-entry census, adapted to `Λ = 5`.
  -- the paper
-/
import Nock.NockVMROM.Thm54.TraceGen.Op5RowWebK3
import Nock.NockVMROM.Thm54.ServedMemoryTrace
import Nock.NockVMROM.Thm54.AxisSoundness
import Nock.NockVMROM.Thm54.Language
import Nock.NockVMROM.Thm54.NounRealization
import Nock.NockVMROM.Thm54.SemanticTrace
import Mathlib.Tactic.IntervalCases

namespace Nock.NockVMROM.Thm54.TraceGen.Op5ConfigK3

open Nock Nock.Walk Nock.NockVM Nock.MemoryTable Nock.ComputeTable
open Nock.AxisBatching Nock.AxisBatching.MTree
open Nock.AxisBridge
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticTrace
open Nock.NockVMROM.Thm54.ServedMemoryTrace
open Nock.NockVMROM.Thm54.TraceGen

/-! ## A. Diagonal pair-faithfulness and noun bounds -/

theorem pairFaithful_self (n : Noun) (h : FieldEmbedding.BoundedBy 97 n) :
    OpcodeSemantics.PairFaithful seedZ 97 n n where
  separates := fun hne => absurd rfl hne
  left_bounded := h
  right_bounded := h

theorem bounded_atom (k : ℕ) (hk : k < 97) : FieldEmbedding.BoundedBy 97 (.atom k) := by
  simp [FieldEmbedding.BoundedBy]; exact hk

theorem bounded_subject : FieldEmbedding.BoundedBy 97 op5Subject :=
  bounded_atom 0 (by norm_num)
theorem bounded_op5Head : FieldEmbedding.BoundedBy 97 op5Head :=
  bounded_atom 5 (by norm_num)
theorem bounded_op1Head : FieldEmbedding.BoundedBy 97 op1Head :=
  bounded_atom 1 (by norm_num)
theorem bounded_result : FieldEmbedding.BoundedBy 97 op5Result :=
  bounded_atom 1 (by norm_num)
theorem bounded_sf1 : FieldEmbedding.BoundedBy 97 op5Sf1 :=
  bounded_atom 3 (by norm_num)
theorem bounded_sf2 : FieldEmbedding.BoundedBy 97 op5Sf2 :=
  bounded_atom 4 (by norm_num)
theorem bounded_childB : FieldEmbedding.BoundedBy 97 op5ChildFormulaB :=
  ⟨bounded_op1Head, bounded_sf1⟩
theorem bounded_childC : FieldEmbedding.BoundedBy 97 op5ChildFormulaC :=
  ⟨bounded_op1Head, bounded_sf2⟩
theorem bounded_tail : FieldEmbedding.BoundedBy 97 op5ParentTail :=
  ⟨bounded_childB, bounded_childC⟩
theorem bounded_formula : FieldEmbedding.BoundedBy 97 op5ParentFormula :=
  ⟨bounded_op5Head, bounded_tail⟩

noncomputable section

/-! ## B. Per-row semantic data -/

def parentRoot :
    OpcodeSemantics.RootRealization (compInputs seedZ alphaA) (parentPub seedZ alphaA)
      (parentDec seedZ) where
  subject := op5Subject
  formula := op5ParentFormula
  result := op5Result
  head := op5Head
  tail := op5ParentTail
  subject_realizes := rfl
  formula_realizes := rfl
  result_realizes := rfl
  head_realizes := rfl
  tail_realizes := rfl

def parentTailR :
    OpcodeSemantics.TailRealization (compInputs seedZ alphaA).z (parentDec seedZ) where
  head := op5ChildFormulaB
  tail := op5ChildFormulaC
  head_realizes := rfl
  tail_realizes := rfl

def parentCall1 :
    OpcodeSemantics.CallRealization (compInputs seedZ alphaA).z
      (parentPub seedZ alphaA).sf1_s (parentPub seedZ alphaA).sf1_f
      (parentPub seedZ alphaA).sf1_e where
  subject := op5Subject
  formula := op5ChildFormulaB
  result := op5Sf1
  subject_realizes := rfl
  formula_realizes := rfl
  result_realizes := rfl

def parentCall2 :
    OpcodeSemantics.CallRealization (compInputs seedZ alphaA).z
      (parentPub seedZ alphaA).sf2_s (parentPub seedZ alphaA).sf2_f
      (parentPub seedZ alphaA).sf2_e where
  subject := op5Subject
  formula := op5ChildFormulaC
  result := op5Sf2
  subject_realizes := rfl
  formula_realizes := rfl
  result_realizes := rfl

private theorem op5_sf_pairFaithful :
    OpcodeSemantics.PairFaithful seedZ 97 op5Sf1 op5Sf2 where
  separates := fun _ => by
    rw [show NPR.fn op5Sf1 seedZ = ((fp seedZ op5Sf1).size, (fp seedZ op5Sf1).leaf,
        (fp seedZ op5Sf1).dyck) from by simp [fp, GlobalCarryRecognizer.enc, NPR.fn],
      show NPR.fn op5Sf2 seedZ = ((fp seedZ op5Sf2).size, (fp seedZ op5Sf2).leaf,
        (fp seedZ op5Sf2).dyck) from by simp [fp, GlobalCarryRecognizer.enc, NPR.fn]]
    simp only [fp, op5Sf1, op5Sf2, seedZ, GlobalCarryRecognizer.enc_atom,
      ComputeTable.FP.atomFP]
    decide
  left_bounded := bounded_sf1
  right_bounded := bounded_sf2

def parentComparisons : List ComparisonUse :=
  [ { role := .opcodeHead, left := op5Head, right := .atom 5 },
    { role := .formulaCons, left := op5ParentFormula, right := .cell op5Head op5ParentTail },
    { role := .tailCons, left := op5ParentTail,
      right := .cell op5ChildFormulaB op5ChildFormulaC },
    { role := .recursiveSubject, left := op5Subject, right := op5Subject },
    { role := .recursiveFormula, left := op5ChildFormulaB, right := op5ChildFormulaB },
    { role := .recursiveSubject, left := op5Subject, right := op5Subject },
    { role := .recursiveFormula, left := op5ChildFormulaC, right := op5ChildFormulaC },
    { role := .equalityOperand, left := op5Sf1, right := op5Sf2 },
    { role := .producedResult, left := op5Result, right := op5Result } ]

def parentRowData : ComputeRowSemanticData 97 5 (parentRow seedZ alphaA) where
  root := parentRoot
  tails := [parentTailR]
  branchTails := []
  calls :=
    [ { subjectFP := (parentPub seedZ alphaA).sf1_s
        formulaFP := (parentPub seedZ alphaA).sf1_f
        resultFP := (parentPub seedZ alphaA).sf1_e
        realization := parentCall1 },
      { subjectFP := (parentPub seedZ alphaA).sf2_s
        formulaFP := (parentPub seedZ alphaA).sf2_f
        resultFP := (parentPub seedZ alphaA).sf2_e
        realization := parentCall2 } ]
  windows := []
  axisGates := []
  tails_count := rfl
  branchTails_count := rfl
  calls_count := rfl
  windows_count := rfl
  axisGates_count := rfl
  realizedNouns := [op5Subject, op5ParentFormula, op5Result]
  subject_mem := by simp [parentRoot]
  formula_mem := by simp [parentRoot]
  result_mem := by simp [parentRoot]
  bounded := by
    intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h | h | h <;> subst h
    · exact bounded_subject
    · exact bounded_formula
    · exact bounded_result
  comparisons := parentComparisons
  comparison_faithful := by
    intro c hc
    simp only [parentComparisons, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with h | h | h | h | h | h | h | h | h <;> subst h
    · exact pairFaithful_self _ bounded_op5Head
    · exact pairFaithful_self _ bounded_formula
    · exact pairFaithful_self _ bounded_tail
    · exact pairFaithful_self _ bounded_subject
    · exact pairFaithful_self _ bounded_childB
    · exact pairFaithful_self _ bounded_subject
    · exact pairFaithful_self _ bounded_childC
    · exact op5_sf_pairFaithful
    · exact pairFaithful_self _ bounded_result
  comparison_leaves := by
    intro c hc
    simp only [parentComparisons, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with h | h | h | h | h | h | h | h | h <;> subst h <;>
      exact ⟨by decide, by decide⟩
  comparison_roles := rfl
  axisGate_listed := by intro gate hgate; simp at hgate
  axisGate_tail_mem := by intro gate hgate; simp at hgate
  needs :=
    { served := []
      served_count := rfl }

/-! ### The two `OP_1` child rows (`Λ = 5`) -/

def child1Root :
    OpcodeSemantics.RootRealization (compInputs seedZ alphaA) (child1Pub seedZ alphaA)
      (op1DecOf seedZ op5Sf1) where
  subject := op5Subject
  formula := op5ChildFormulaB
  result := op5Sf1
  head := op1Head
  tail := op5Sf1
  subject_realizes := rfl
  formula_realizes := rfl
  result_realizes := rfl
  head_realizes := rfl
  tail_realizes := rfl

def child2Root :
    OpcodeSemantics.RootRealization (compInputs seedZ alphaA) (child2Pub seedZ alphaA)
      (op1DecOf seedZ op5Sf2) where
  subject := op5Subject
  formula := op5ChildFormulaC
  result := op5Sf2
  head := op1Head
  tail := op5Sf2
  subject_realizes := rfl
  formula_realizes := rfl
  result_realizes := rfl
  head_realizes := rfl
  tail_realizes := rfl

def child1Comparisons : List ComparisonUse :=
  [ { role := .opcodeHead, left := op1Head, right := .atom 1 },
    { role := .formulaCons, left := op5ChildFormulaB, right := .cell op1Head op5Sf1 },
    { role := .producedResult, left := op5Sf1, right := op5Sf1 } ]

def child2Comparisons : List ComparisonUse :=
  [ { role := .opcodeHead, left := op1Head, right := .atom 1 },
    { role := .formulaCons, left := op5ChildFormulaC, right := .cell op1Head op5Sf2 },
    { role := .producedResult, left := op5Sf2, right := op5Sf2 } ]

def child1RowData : ComputeRowSemanticData 97 5 (child1Row seedZ alphaA) where
  root := child1Root
  tails := []
  branchTails := []
  calls := []
  windows := []
  axisGates := []
  tails_count := rfl
  branchTails_count := rfl
  calls_count := rfl
  windows_count := rfl
  axisGates_count := rfl
  realizedNouns := [op5Subject, op5ChildFormulaB, op5Sf1]
  subject_mem := by simp [child1Root]
  formula_mem := by simp [child1Root]
  result_mem := by simp [child1Root]
  bounded := by
    intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h | h | h <;> subst h
    · exact bounded_subject
    · exact bounded_childB
    · exact bounded_sf1
  comparisons := child1Comparisons
  comparison_faithful := by
    intro c hc
    simp only [child1Comparisons, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with h | h | h <;> subst h
    · exact pairFaithful_self _ bounded_op1Head
    · exact pairFaithful_self _ bounded_childB
    · exact pairFaithful_self _ bounded_sf1
  comparison_leaves := by
    intro c hc
    simp only [child1Comparisons, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with h | h | h <;> subst h <;> exact ⟨by decide, by decide⟩
  comparison_roles := rfl
  axisGate_listed := by intro gate hgate; simp at hgate
  axisGate_tail_mem := by intro gate hgate; simp at hgate
  needs :=
    { served := []
      served_count := rfl }

def child2RowData : ComputeRowSemanticData 97 5 (child2Row seedZ alphaA) where
  root := child2Root
  tails := []
  branchTails := []
  calls := []
  windows := []
  axisGates := []
  tails_count := rfl
  branchTails_count := rfl
  calls_count := rfl
  windows_count := rfl
  axisGates_count := rfl
  realizedNouns := [op5Subject, op5ChildFormulaC, op5Sf2]
  subject_mem := by simp [child2Root]
  formula_mem := by simp [child2Root]
  result_mem := by simp [child2Root]
  bounded := by
    intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h | h | h <;> subst h
    · exact bounded_subject
    · exact bounded_childC
    · exact bounded_sf2
  comparisons := child2Comparisons
  comparison_faithful := by
    intro c hc
    simp only [child2Comparisons, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with h | h | h <;> subst h
    · exact pairFaithful_self _ bounded_op1Head
    · exact pairFaithful_self _ bounded_childC
    · exact pairFaithful_self _ bounded_sf2
  comparison_leaves := by
    intro c hc
    simp only [child2Comparisons, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with h | h | h <;> subst h <;> exact ⟨by decide, by decide⟩
  comparison_roles := rfl
  axisGate_listed := by intro gate hgate; simp at hgate
  axisGate_tail_mem := by intro gate hgate; simp at hgate
  needs :=
    { served := []
      served_count := rfl }

/-! ### Indexed row accessor -/

def castRowData {row₁ row₂ : ComputeTable.State × ComputeTable.DTcomp K}
    (h : row₁ = row₂) (d : ComputeRowSemanticData 97 5 row₂) :
    ComputeRowSemanticData 97 5 row₁ :=
  h.symm ▸ d

def rowData : ∀ i : Fin (cfg seedZ alphaA).compRows,
    ComputeRowSemanticData 97 5 ((exec seedZ alphaA).computeRowAt i)
  | ⟨0, _⟩ => castRowData computeRowAt_zero parentRowData
  | ⟨1, _⟩ => castRowData computeRowAt_one child1RowData
  | ⟨2, _⟩ => castRowData computeRowAt_two child2RowData
  | ⟨n + 3, h⟩ => by simp only [cfg] at h; exact absurd h (by omega)

/-! ## C. Timestamp exponents of the four records -/

theorem ts_closed_recF :
    TimestampClosedAt (cfg seedZ alphaA).challenges.α (recF seedZ alphaA).ts :=
  ⟨1, by rw [ts_recF]; simp [cfg, alphaA]⟩
theorem ts_closed_recT :
    TimestampClosedAt (cfg seedZ alphaA).challenges.α (recT seedZ alphaA).ts :=
  ⟨2, by rw [ts_recT]; rfl⟩
theorem ts_closed_recB :
    TimestampClosedAt (cfg seedZ alphaA).challenges.α (recB seedZ alphaA).ts :=
  ⟨3, by rw [ts_recB]; rfl⟩
theorem ts_closed_recC :
    TimestampClosedAt (cfg seedZ alphaA).challenges.α (recC seedZ alphaA).ts :=
  ⟨4, by rw [ts_recC]; rfl⟩

def expF : ℕ := timestampExp (cfg seedZ alphaA).challenges.α (recF seedZ alphaA).ts
def expT : ℕ := timestampExp (cfg seedZ alphaA).challenges.α (recT seedZ alphaA).ts
def expB : ℕ := timestampExp (cfg seedZ alphaA).challenges.α (recB seedZ alphaA).ts
def expC : ℕ := timestampExp (cfg seedZ alphaA).challenges.α (recC seedZ alphaA).ts

theorem ts_eq_recF : (recF seedZ alphaA).ts = (cfg seedZ alphaA).challenges.α ^ expF :=
  timestampExp_spec ts_closed_recF
theorem ts_eq_recT : (recT seedZ alphaA).ts = (cfg seedZ alphaA).challenges.α ^ expT :=
  timestampExp_spec ts_closed_recT
theorem ts_eq_recB : (recB seedZ alphaA).ts = (cfg seedZ alphaA).challenges.α ^ expB :=
  timestampExp_spec ts_closed_recB
theorem ts_eq_recC : (recC seedZ alphaA).ts = (cfg seedZ alphaA).challenges.α ^ expC :=
  timestampExp_spec ts_closed_recC

theorem expF_ne_expT : expF ≠ expT := by
  intro h
  have hF := ts_recF.symm.trans ts_eq_recF
  have hT := ts_recT.symm.trans ts_eq_recT
  rw [h] at hF; exact alpha_pow_ne_12 (hF.trans hT.symm)
theorem expF_ne_expB : expF ≠ expB := by
  intro h
  have hF := ts_recF.symm.trans ts_eq_recF
  have hB := ts_recB.symm.trans ts_eq_recB
  rw [h] at hF; exact alpha_pow_ne_13 (hF.trans hB.symm)
theorem expF_ne_expC : expF ≠ expC := by
  intro h
  have hF := ts_recF.symm.trans ts_eq_recF
  have hC := ts_recC.symm.trans ts_eq_recC
  rw [h] at hF; exact alpha_pow_ne_14 (hF.trans hC.symm)
theorem expT_ne_expB : expT ≠ expB := by
  intro h
  have hT := ts_recT.symm.trans ts_eq_recT
  have hB := ts_recB.symm.trans ts_eq_recB
  rw [h] at hT; exact alpha_pow_ne_23 (hT.trans hB.symm)
theorem expT_ne_expC : expT ≠ expC := by
  intro h
  have hT := ts_recT.symm.trans ts_eq_recT
  have hC := ts_recC.symm.trans ts_eq_recC
  rw [h] at hT; exact alpha_pow_ne_24 (hT.trans hC.symm)
theorem expB_ne_expC : expB ≠ expC := by
  intro h
  have hB := ts_recB.symm.trans ts_eq_recB
  have hC := ts_recC.symm.trans ts_eq_recC
  rw [h] at hB; exact alpha_pow_ne_34 (hB.trans hC.symm)

theorem expT_ne_expF : expT ≠ expF := fun h => expF_ne_expT h.symm
theorem expB_ne_expF : expB ≠ expF := fun h => expF_ne_expB h.symm
theorem expC_ne_expF : expC ≠ expF := fun h => expF_ne_expC h.symm
theorem expB_ne_expT : expB ≠ expT := fun h => expT_ne_expB h.symm
theorem expC_ne_expT : expC ≠ expT := fun h => expT_ne_expC h.symm
theorem expC_ne_expB : expC ≠ expB := fun h => expB_ne_expC h.symm

/-! ## D. The memory axis tree and services -/

theorem memoryTreeAt_zero :
    (execA seedZ alphaA).memoryTreeAt ⟨0, by norm_num [cfg]⟩ = rootTreeA seedZ alphaA := rfl

theorem axisPath_three : axisPath 3 = [true] := by
  rw [axisPath_of_two_le (by norm_num)]; norm_num [axisPath_of_lt_two]
theorem axisPath_two : axisPath 2 = [false] := by
  rw [axisPath_of_two_le (by norm_num)]; norm_num [axisPath_of_lt_two]

set_option maxRecDepth 400000 in
theorem op5AxisTree_eq :
    exactAxisTree (cfg seedZ alphaA) (execA seedZ alphaA) ⟨0, by norm_num [cfg]⟩ =
      MTree.read expF
        (MTree.decompose MTree.halt
          (MTree.verify expF 3
            (MTree.read expT
              (MTree.decompose
                (MTree.verify expT 2
                  (MTree.read expB
                    (MTree.decompose MTree.halt
                      (MTree.verify expB 3 MTree.halt))))
                (MTree.read expC
                  (MTree.decompose MTree.halt
                    (MTree.verify expC 3 MTree.halt))))))) := by
  rw [exactAxisTree, memoryTreeAt_zero]
  simp [rootTreeA, tDecFA, tHalt5, tVerifyFA, tReadTA, tDecTA, tVerifyTA, tReadCA, tReadBA,
    tDecCA, tDecBA, tHaltC1, tVerifyCA, tHaltB1, tVerifyBA, tHalt4, tHalt3, mOne, mTwo, mLeaf,
    lblOf, Nock.AxisBridge.ofNTree, Nock.AxisBridge.MemWalk.toMTree, timestampExpAt,
    expF, expT, expB, expC,
    pReadFA, pDecF, pHalt5, pVerifyFA, pReadTA, pDecT, pVerifyTA, pReadCA, pReadBA,
    pDecC, pDecB, pHaltC1, pVerifyCA, pHaltB1, pVerifyBA, pHalt4, pHalt3,
    readPub, readPubA, decPub, haltPub, verifyPub, verifyPubA,
    recF, recT, recB, recC]

def serviceF : Service (cfg seedZ alphaA) (execA seedZ alphaA) where
  exponent := expF
  record := recF seedZ alphaA
  root := op5ParentFormula
  child := op5ParentTail
  axis := 3
  request_mem := by
    rw [show (execA seedZ alphaA).rawRequests = (exec seedZ alphaA).rawRequests from rfl,
      rawRequests_eq]; simp
  timestamp := ts_eq_recF
  realization :=
    { root_realizes := rfl
      child_realizes := rfl
      axis_realizes := by norm_num [recF] }
  served := by simp [op5ParentFormula, op5ParentTail, Noun.slot]

def serviceT : Service (cfg seedZ alphaA) (execA seedZ alphaA) where
  exponent := expT
  record := recT seedZ alphaA
  root := op5ParentTail
  child := op5ChildFormulaB
  axis := 2
  request_mem := by
    rw [show (execA seedZ alphaA).rawRequests = (exec seedZ alphaA).rawRequests from rfl,
      rawRequests_eq]; simp
  timestamp := ts_eq_recT
  realization :=
    { root_realizes := rfl
      child_realizes := rfl
      axis_realizes := by norm_num [recT] }
  served := by simp [op5ParentTail, op5ChildFormulaB, Noun.slot]

def serviceB : Service (cfg seedZ alphaA) (execA seedZ alphaA) where
  exponent := expB
  record := recB seedZ alphaA
  root := op5ChildFormulaB
  child := op5Sf1
  axis := 3
  request_mem := by
    rw [show (execA seedZ alphaA).rawRequests = (exec seedZ alphaA).rawRequests from rfl,
      rawRequests_eq]; simp
  timestamp := ts_eq_recB
  realization :=
    { root_realizes := rfl
      child_realizes := rfl
      axis_realizes := by norm_num [recB] }
  served := by simp [op5ChildFormulaB, op5Sf1, Noun.slot]

def serviceC : Service (cfg seedZ alphaA) (execA seedZ alphaA) where
  exponent := expC
  record := recC seedZ alphaA
  root := op5ChildFormulaC
  child := op5Sf2
  axis := 3
  request_mem := by
    rw [show (execA seedZ alphaA).rawRequests = (exec seedZ alphaA).rawRequests from rfl,
      rawRequests_eq]; simp
  timestamp := ts_eq_recC
  realization :=
    { root_realizes := rfl
      child_realizes := rfl
      axis_realizes := by norm_num [recC] }
  served := by simp [op5ChildFormulaC, op5Sf2, Noun.slot]

/-! ## E. The single root's trace -/

theorem rootResponseRecords_eq :
    rootResponseRecords (execA seedZ alphaA) ⟨0, by norm_num [cfg]⟩ =
      [recF seedZ alphaA, recT seedZ alphaA, recC seedZ alphaA, recB seedZ alphaA] := by
  simp [rootResponseRecords, memoryTreeAt_zero, rootTreeA, tDecFA, tHalt5, tVerifyFA,
    tReadTA, tDecTA, tVerifyTA, tReadCA, tReadBA, tDecCA, tDecBA, tHaltC1, tVerifyCA,
    tHaltB1, tVerifyBA, tHalt4, tHalt3, mOne, mTwo, mLeaf, lblOf, bfsForest,
    MemoryTable.responseRecords,
    pReadFA, pDecF, pHalt5, pVerifyFA, pReadTA, pDecT, pVerifyTA, pReadCA, pReadBA,
    pDecC, pDecB, pHaltC1, pVerifyCA, pHaltB1, pVerifyBA, pHalt4, pHalt3,
    readPub, readPubA, decPub, haltPub, verifyPub, verifyPubA]

def rootTrace : RootTrace (cfg seedZ alphaA) (execA seedZ alphaA) ⟨0, by norm_num [cfg]⟩ where
  subject := op5ParentFormula
  services := [serviceF, serviceT, serviceC, serviceB]
  recordPartition := by
    rw [rootResponseRecords_eq]
    simp [serviceF, serviceT, serviceC, serviceB]
  readPartition := by
    rw [op5AxisTree_eq]
    simp only [readExps, serviceF, serviceT, serviceC, serviceB,
      List.map_cons, List.map_nil]
    exact List.Perm.cons _ (List.Perm.cons _ (List.Perm.swap _ _ _))
  verifyPartition := by
    rw [op5AxisTree_eq]
    simp only [verifyExps, serviceF, serviceT, serviceC, serviceB,
      List.map_cons, List.map_nil]
    exact List.Perm.cons _ (List.Perm.cons _ (List.Perm.swap _ _ _))
  traversal := by
    rw [op5AxisTree_eq]
    refine ServiceWalk.read serviceF (by simp) rfl rfl ?_ ?_
    · rw [show serviceF.axis = 3 from rfl, axisPath_three]
      refine VerifyRoute.right (by simp [readCount]) (by simp [verifyCount]) ?_
      exact VerifyRoute.here rfl rfl
        (by simp [readCount, expT_ne_expF, expB_ne_expF, expC_ne_expF])
        (by simp [verifyCount, expT_ne_expF, expB_ne_expF, expC_ne_expF])
    · refine ServiceWalk.decompose ServiceWalk.halt ?_
      refine ServiceWalk.verify ?_
      refine ServiceWalk.read serviceT (by simp) rfl rfl ?_ ?_
      · rw [show serviceT.axis = 2 from rfl, axisPath_two]
        refine VerifyRoute.left ?_
          (by simp [readCount, expC_ne_expT])
          (by simp [verifyCount, expC_ne_expT])
        exact VerifyRoute.here rfl rfl
          (by simp [readCount, expB_ne_expT])
          (by simp [verifyCount, expB_ne_expT])
      · refine ServiceWalk.decompose ?_ ?_
        · refine ServiceWalk.verify ?_
          refine ServiceWalk.read serviceB (by simp) rfl rfl ?_ ?_
          · rw [show serviceB.axis = 3 from rfl, axisPath_three]
            refine VerifyRoute.right (by simp [readCount]) (by simp [verifyCount]) ?_
            exact VerifyRoute.here rfl rfl (by simp [readCount]) (by simp [verifyCount])
          · exact ServiceWalk.decompose ServiceWalk.halt (ServiceWalk.verify ServiceWalk.halt)
        · refine ServiceWalk.read serviceC (by simp) rfl rfl ?_ ?_
          · rw [show serviceC.axis = 3 from rfl, axisPath_three]
            refine VerifyRoute.right (by simp [readCount]) (by simp [verifyCount]) ?_
            exact VerifyRoute.here rfl rfl (by simp [readCount]) (by simp [verifyCount])
          · exact ServiceWalk.decompose ServiceWalk.halt (ServiceWalk.verify ServiceWalk.halt)

def rootTraces : ∀ i : Fin (cfg seedZ alphaA).kMem,
    RootTrace (cfg seedZ alphaA) (execA seedZ alphaA) i
  | ⟨0, _⟩ => rootTrace
  | ⟨n + 1, h⟩ => absurd (show n + 1 < 1 by simp only [cfg] at h; exact h) (by omega)

theorem finRange_kMem :
    List.finRange (cfg seedZ alphaA).kMem = [⟨0, by norm_num [cfg]⟩] := rfl

theorem forestTimestampPowers_eq :
    (List.finRange (cfg seedZ alphaA).kMem).flatMap
      (fun i => (rootTraces i).timestampPowers) =
      [alphaA, alphaA ^ 2, alphaA ^ 4, alphaA ^ 3] := by
  rw [finRange_kMem]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  simp only [RootTrace.timestampPowers, RootTrace.exponents, rootTraces, rootTrace,
    List.map_cons, List.map_nil]
  rw [show (serviceF.exponent : ℕ) = expF from rfl,
    show (serviceT.exponent : ℕ) = expT from rfl,
    show (serviceC.exponent : ℕ) = expC from rfl,
    show (serviceB.exponent : ℕ) = expB from rfl,
    ← ts_eq_recF, ← ts_eq_recT, ← ts_eq_recC, ← ts_eq_recB,
    ts_recF, ts_recT, ts_recC, ts_recB]

theorem forestTimestampPowers_nodup :
    ((List.finRange (cfg seedZ alphaA).kMem).flatMap
      (fun i => (rootTraces i).timestampPowers)).Nodup := by
  rw [forestTimestampPowers_eq]
  have h12 := alpha_pow_ne_12
  have h14 := alpha_pow_ne_14
  have h13 := alpha_pow_ne_13
  have h24 := alpha_pow_ne_24
  have h23 := alpha_pow_ne_23
  have h43 : alphaA ^ 4 ≠ alphaA ^ 3 := fun h => alpha_pow_ne_34 h.symm
  simp [List.nodup_cons, h12, h14, h13, h24, h23, h43]

/-! ## F. Vacuous `semanticCoverage` (`.s5`/`.s1` have `requiredServedLookups = 0`) -/

def lookupTuple {z : K} (l : ServedNounLookup z) :
    ComputeTable.MemRec K × Noun × ℕ × Noun :=
  (l.record, l.root, l.axis, l.child)

theorem castRowData_servedTuples
    {row₁ row₂ : ComputeTable.State × ComputeTable.DTcomp K}
    (h : row₁ = row₂) (d : ComputeRowSemanticData 97 5 row₂) :
    (castRowData h d).needs.served.map lookupTuple = d.needs.served.map lookupTuple := by
  subst h; rfl

theorem rowData_zero_servedTuples :
    (rowData ⟨0, by norm_num [cfg]⟩).needs.served.map lookupTuple = [] :=
  (castRowData_servedTuples computeRowAt_zero parentRowData).trans rfl
theorem rowData_one_servedTuples :
    (rowData ⟨1, by norm_num [cfg]⟩).needs.served.map lookupTuple = [] :=
  (castRowData_servedTuples computeRowAt_one child1RowData).trans rfl
theorem rowData_two_servedTuples :
    (rowData ⟨2, by norm_num [cfg]⟩).needs.served.map lookupTuple = [] :=
  (castRowData_servedTuples computeRowAt_two child2RowData).trans rfl

-- memoryTrace is defined after semanticData (forward dependency on D.rows)

/-! ## G. Semantic IO preimage -/

def semOf (axis : F) (root child : Noun) (exp : ℕ) : (nmrMEF F K).Rec :=
  (axis,
    ((((fp seedZ root).size, (fp seedZ root).dyck, (fp seedZ root).leaf),
      ((fp seedZ child).size, (fp seedZ child).dyck, (fp seedZ child).leaf)),
    exp))

def semF : (nmrMEF F K).Rec := semOf 3 op5ParentFormula op5ParentTail 1
def semT : (nmrMEF F K).Rec := semOf 2 op5ParentTail op5ChildFormulaB 2
def semB : (nmrMEF F K).Rec := semOf 3 op5ChildFormulaB op5Sf1 3
def semC : (nmrMEF F K).Rec := semOf 3 op5ChildFormulaC op5Sf2 4

theorem semF_preimage :
    memRecOfNMR F K ((nmrEncoding F K (cfg seedZ alphaA).challenges.α).encode semF) =
      recF seedZ alphaA := by
  ext <;> simp [memRecOfNMR, nmrEncoding, semF, semOf, cfg, recF, seedZ, alphaA, map_ofNat]

theorem semT_preimage :
    memRecOfNMR F K ((nmrEncoding F K (cfg seedZ alphaA).challenges.α).encode semT) =
      recT seedZ alphaA := by
  ext <;> simp [memRecOfNMR, nmrEncoding, semT, semOf, cfg, recT, seedZ, alphaA, map_ofNat,
    pow_two]

theorem semB_preimage :
    memRecOfNMR F K ((nmrEncoding F K (cfg seedZ alphaA).challenges.α).encode semB) =
      recB seedZ alphaA := by
  ext <;> simp [memRecOfNMR, nmrEncoding, semB, semOf, cfg, recB, seedZ, alphaA, map_ofNat,
    pow_succ]

theorem semC_preimage :
    memRecOfNMR F K ((nmrEncoding F K (cfg seedZ alphaA).challenges.α).encode semC) =
      recC seedZ alphaA := by
  ext <;> simp [memRecOfNMR, nmrEncoding, semC, semOf, cfg, recC, seedZ, alphaA, map_ofNat,
    pow_succ]

theorem semF_bridge :
    bridge F K (cfg seedZ alphaA).challenges.α (cfg seedZ alphaA).challenges.lam semF =
      NockVM.encRecFormR (recF seedZ alphaA) MemoryTable.formRDefault := by
  rw [← d2_record_bridge_agrees, semF_preimage]
  rfl
theorem semT_bridge :
    bridge F K (cfg seedZ alphaA).challenges.α (cfg seedZ alphaA).challenges.lam semT =
      NockVM.encRecFormR (recT seedZ alphaA) MemoryTable.formRDefault := by
  rw [← d2_record_bridge_agrees, semT_preimage]
  rfl
theorem semB_bridge :
    bridge F K (cfg seedZ alphaA).challenges.α (cfg seedZ alphaA).challenges.lam semB =
      NockVM.encRecFormR (recB seedZ alphaA) MemoryTable.formRDefault := by
  rw [← d2_record_bridge_agrees, semB_preimage]
  rfl
theorem semC_bridge :
    bridge F K (cfg seedZ alphaA).challenges.α (cfg seedZ alphaA).challenges.lam semC =
      NockVM.encRecFormR (recC seedZ alphaA) MemoryTable.formRDefault := by
  rw [← d2_record_bridge_agrees, semC_preimage]
  rfl

theorem semResp_nodup : [semF, semT, semC, semB].Nodup := by
  simp [semF, semT, semC, semB, semOf]

/-- `4` has multiplicative order `24` in `ZMod 97`. -/
theorem alphaA_order_base : orderOf (4 : F) = 24 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, ?_⟩
  intro m hm hpos
  interval_cases m <;> decide

/-- `α = 4 = φ 4` keeps multiplicative order `24` in `K3`. -/
theorem alphaA_order : orderOf alphaA = 24 := by
  have h := orderOf_injective φ.toMonoidHom φ_injective (4 : F)
  rw [alphaA_order_base] at h
  rw [alphaA_eq_image]; simpa using h

def semanticPreimage :
    SemanticIOPreimage (cfg seedZ alphaA) (exec seedZ alphaA) where
  timestampBound := 5
  timestampBound_le_order := by
    change 5 ≤ orderOf alphaA
    rw [alphaA_order]; norm_num
  semanticRequests := [semF, semT, semB, semC]
  semanticResponses := [semF, semT, semC, semB]
  requestTimestampBound := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp [semF, semT, semB, semC, semOf]
  responseTimestampBound := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp [semF, semT, semC, semB, semOf]
  semantic_lmio := by
    refine ⟨by norm_num [IO.InRange, cfg], [semF, semT, semC, semB], by decide,
      semResp_nodup, ?_, List.Perm.refl _⟩
    intro x
    have hp : List.Perm [semF, semT, semB, semC] [semF, semT, semC, semB] :=
      List.Perm.cons _ (List.Perm.cons _ (List.Perm.swap semC semB []))
    exact hp.mem_iff
  requestTimestamp_determines := by
    intro x hx y hy h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      first | (simp [semF, semT, semB, semC, semOf] at h; done) | rfl
  requests_bridge := by
    rw [bridgeRecords, List.map_cons, List.map_cons, List.map_cons, List.map_cons,
      List.map_nil, semF_bridge, semT_bridge, semB_bridge, semC_bridge, derived_requests]
  responses_bridge := by
    rw [bridgeRecords, List.map_cons, List.map_cons, List.map_cons, List.map_cons,
      List.map_nil, semF_bridge, semT_bridge, semC_bridge, semB_bridge, derived_responses]

theorem semanticExactLanguage :
    SemanticExactLanguage (cfg seedZ alphaA) (exec seedZ alphaA) :=
  ⟨computeRowsAccepted, memoryRowsAccepted, ⟨semanticPreimage⟩⟩

/-! ## H. Chained boundaries and traversable topology -/

/-- Every executed memory row carries the package `λ = formRDefault` (row encode). -/
theorem exec_lambda_package :
    ∀ i, ((exec seedZ alphaA).memoryPubAt i).lambda? = some MemoryTable.formRDefault := by
  intro i
  fin_cases i
  · rw [memoryPubAt_0]; simp only [pReadF, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_1]; simp only [pDecF, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_2]; simp only [pHalt5, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_3]; simp only [pVerifyF, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_4]; simp only [pReadT, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_5]; simp only [pDecT, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_6]; simp only [pVerifyT, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_7]; simp only [pReadC, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_8]; simp only [pReadB, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_9]; simp only [pDecC, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_10]; simp only [pDecB, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_11]; simp only [pHaltC1, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_12]; simp only [pVerifyC, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_13]; simp only [pHaltB1, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_14]; simp only [pVerifyB, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_15]; simp only [pHalt4, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_16]; simp only [pHalt3, readPub, decPub, verifyPub, haltPub]

theorem chained
    (hfirst :
      ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.counts = 0 ∧
        ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.indicator = 0) :
    ChainedSemanticExactLanguage (cfg seedZ alphaA) (exec seedZ alphaA) where
  semantic := semanticExactLanguage
  z_ne_zero := seedZ_ne_zero
  compute_wf := compute_wf_all
  memory_wf := memory_wf_all
  compute_chain := compute_chain
  memory_chain := memory_chain
  memory_first_counts := hfirst.1
  memory_first_indicator := hfirst.2
  memory_first_ipre := by rw [memoryPubAt_0]; rfl
  memory_last_icur := by
    have hlast :
        (cfg seedZ alphaA).orbit.lastIndex (cfg seedZ alphaA).memRows
          (cfg seedZ alphaA).memRows_pos = ⟨16, by norm_num [cfg]⟩ := rfl
    rw [hlast, memoryPubAt_16]; rfl

  memory_same_lambda := ExactExecution.memory_same_lambda_of_const _ (some MemoryTable.formRDefault)
    exec_lambda_package

theorem traversable
    (hfirst :
      ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.counts = 0 ∧
        ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.indicator = 0) :
    TraversableChainedSemanticExactLanguage (cfg seedZ alphaA) (exec seedZ alphaA) where
  chained := chained hfirst
  compute_topology := compute_topology
  memory_topology := memory_topology

/-! ## I. Bounded noun realization -/

theorem fpRealized {n : Noun} (hb : FieldEmbedding.BoundedBy 97 n) :
    FPRealized seedZ 97 (fp seedZ n) :=
  ⟨n, hb, rfl⟩

theorem fpActive {n : Noun} (hb : FieldEmbedding.BoundedBy 97 n) :
    FPSlotRealized seedZ 97 .active (fp seedZ n) :=
  ⟨fpRealized hb, FPRealized.ne_zero seedZ_ne_zero (fpRealized hb)⟩

theorem alphaA_ne_zero : alphaA ≠ 0 := by rw [alphaA]; decide

theorem recF_ne_zero : recF seedZ alphaA ≠ MemRec.zero := fun h =>
  alphaA_ne_zero (by simpa [recF, MemRec.zero] using congrArg MemRec.ts h)
theorem recT_ne_zero : recT seedZ alphaA ≠ MemRec.zero := fun h =>
  (pow_ne_zero 2 alphaA_ne_zero) (by simpa [recT, MemRec.zero] using congrArg MemRec.ts h)
theorem recB_ne_zero : recB seedZ alphaA ≠ MemRec.zero := fun h =>
  (pow_ne_zero 3 alphaA_ne_zero) (by simpa [recB, MemRec.zero] using congrArg MemRec.ts h)
theorem recC_ne_zero : recC seedZ alphaA ≠ MemRec.zero := fun h =>
  (pow_ne_zero 4 alphaA_ne_zero) (by simpa [recC, MemRec.zero] using congrArg MemRec.ts h)

theorem recF_active : MemRecSlotRealized seedZ 97 .active (recF seedZ alphaA) :=
  ⟨recF_ne_zero, fpActive bounded_formula, fpActive bounded_tail⟩
theorem recT_active : MemRecSlotRealized seedZ 97 .active (recT seedZ alphaA) :=
  ⟨recT_ne_zero, fpActive bounded_tail, fpActive bounded_childB⟩
theorem recB_active : MemRecSlotRealized seedZ 97 .active (recB seedZ alphaA) :=
  ⟨recB_ne_zero, fpActive bounded_childB, fpActive bounded_sf1⟩
theorem recC_active : MemRecSlotRealized seedZ 97 .active (recC seedZ alphaA) :=
  ⟨recC_ne_zero, fpActive bounded_childC, fpActive bounded_sf2⟩

theorem parentRow_nounRealization :
    ComputePublicRowNounRealization 97 (computePublicLabel (parentRow seedZ alphaA)) where
  subject := fpActive bounded_subject
  formula := fpActive bounded_formula
  evaluation := fpActive bounded_result
  subformula := by
    intro i; fin_cases i
    · exact ⟨fpActive bounded_subject, fpActive bounded_childB, fpActive bounded_sf1⟩
    · exact ⟨fpActive bounded_subject, fpActive bounded_childC, fpActive bounded_sf2⟩
    · exact ⟨rfl, rfl, rfl⟩
  memoryRecord := by
    intro i; fin_cases i
    · exact recF_active
    · exact recT_active
    · rfl

theorem child1Row_nounRealization :
    ComputePublicRowNounRealization 97 (computePublicLabel (child1Row seedZ alphaA)) where
  subject := fpActive bounded_subject
  formula := fpActive bounded_childB
  evaluation := fpActive bounded_sf1
  subformula := by intro i; fin_cases i <;> exact ⟨rfl, rfl, rfl⟩
  memoryRecord := by
    intro i; fin_cases i
    · exact recB_active
    · rfl
    · rfl

theorem child2Row_nounRealization :
    ComputePublicRowNounRealization 97 (computePublicLabel (child2Row seedZ alphaA)) where
  subject := fpActive bounded_subject
  formula := fpActive bounded_childC
  evaluation := fpActive bounded_sf2
  subformula := by intro i; fin_cases i <;> exact ⟨rfl, rfl, rfl⟩
  memoryRecord := by
    intro i; fin_cases i
    · exact recC_active
    · rfl
    · rfl

theorem computeTreeNounRealization :
    ComputePublicTreeNounRealization 97 (exec seedZ alphaA).computePublicTree := by
  have h : (bfsForest [(exec seedZ alphaA).computePublicTree]).map NTree.label =
      [computePublicLabel (parentRow seedZ alphaA),
        computePublicLabel (child1Row seedZ alphaA),
        computePublicLabel (child2Row seedZ alphaA)] := by
    rw [ExactExecution.computePublicTree_bfs, ExactExecution.computePublicRows, computeRows_eq]
    rfl
  unfold ComputePublicTreeNounRealization ComputePublicRowsNounRealization
  rw [h]
  refine List.forall_iff_forall_mem.mpr ?_
  intro row hrow
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
  rcases hrow with rfl | rfl | rfl
  · exact parentRow_nounRealization
  · exact child1Row_nounRealization
  · exact child2Row_nounRealization

theorem leafAtomHalt (k : ℕ) (hk : k < 97) (acc : K) :
    MemoryLeafAtomsRealized 97 (mLeaf seedZ (haltPub seedZ k acc)) :=
  ⟨k, hk, by
    show ((k : ℕ) : K) = (fp seedZ (Noun.atom k)).leaf
    simp [fp, GlobalCarryRecognizer.enc_atom]⟩

theorem leafAtoms_tHalt5 : MemoryLeafAtomsRealized 97 (tHalt5 seedZ alphaA) :=
  leafAtomHalt 5 (by norm_num) 0
theorem leafAtoms_tHalt4 : MemoryLeafAtomsRealized 97 (tHalt4 seedZ alphaA) :=
  leafAtomHalt 4 (by norm_num) (qC seedZ alphaA + qB seedZ alphaA)
theorem leafAtoms_tHalt3 : MemoryLeafAtomsRealized 97 (tHalt3 seedZ alphaA) :=
  leafAtomHalt 3 (by norm_num) (qB seedZ alphaA)
theorem leafAtoms_tHaltB1 : MemoryLeafAtomsRealized 97 (tHaltB1 seedZ alphaA) :=
  leafAtomHalt 1 (by norm_num) (qB seedZ alphaA)
theorem leafAtoms_tHaltC1 : MemoryLeafAtomsRealized 97 (tHaltC1 seedZ alphaA) :=
  leafAtomHalt 1 (by norm_num) (qC seedZ alphaA + qB seedZ alphaA)

theorem leafAtoms_tVerifyB : MemoryLeafAtomsRealized 97 (tVerifyB seedZ alphaA) :=
  leafAtoms_tHalt3
theorem leafAtoms_tDecB : MemoryLeafAtomsRealized 97 (tDecB seedZ alphaA) :=
  ⟨leafAtoms_tHaltB1, leafAtoms_tVerifyB⟩
theorem leafAtoms_tReadB : MemoryLeafAtomsRealized 97 (tReadB seedZ alphaA) :=
  leafAtoms_tDecB
theorem leafAtoms_tVerifyC : MemoryLeafAtomsRealized 97 (tVerifyC seedZ alphaA) :=
  leafAtoms_tHalt4
theorem leafAtoms_tDecC : MemoryLeafAtomsRealized 97 (tDecC seedZ alphaA) :=
  ⟨leafAtoms_tHaltC1, leafAtoms_tVerifyC⟩
theorem leafAtoms_tReadC : MemoryLeafAtomsRealized 97 (tReadC seedZ alphaA) :=
  leafAtoms_tDecC
theorem leafAtoms_tVerifyT : MemoryLeafAtomsRealized 97 (tVerifyT seedZ alphaA) :=
  leafAtoms_tReadB
theorem leafAtoms_tDecT : MemoryLeafAtomsRealized 97 (tDecT seedZ alphaA) :=
  ⟨leafAtoms_tVerifyT, leafAtoms_tReadC⟩
theorem leafAtoms_tReadT : MemoryLeafAtomsRealized 97 (tReadT seedZ alphaA) :=
  leafAtoms_tDecT
theorem leafAtoms_tVerifyF : MemoryLeafAtomsRealized 97 (tVerifyF seedZ alphaA) :=
  leafAtoms_tReadT
theorem leafAtoms_tDecF : MemoryLeafAtomsRealized 97 (tDecF seedZ alphaA) :=
  ⟨leafAtoms_tHalt5, leafAtoms_tVerifyF⟩
theorem leafAtoms_rootTree : MemoryLeafAtomsRealized 97 (rootTree seedZ alphaA) :=
  leafAtoms_tDecF

/-! ### Per-row public memory realizations -/

theorem memSingleChildRealization (pub : MemoryTable.Pub K)
    (hst : MemoryTable.fanoutMem pub.st = 1)
    (hpt : FPSlotRealized seedZ 97 .active pub.pt.noun)
    (hlc : FPSlotRealized seedZ 97 .active pub.lc.noun)
    (hrc : pub.rc = MemoryTable.Cell.zero)
    (hkind : memoryMemRecKind pub.st = .active)
    (hmem : MemRecSlotRealized seedZ 97 .active pub.mem) :
    MemoryPublicRowNounRealization 97 (lblOf seedZ pub) where
  parent := hpt
  child := by
    intro i; fin_cases i
    · show MemoryCellSlotRealized seedZ 97 (memoryChildKind pub.st 0) pub.lc
      rw [memoryChildKind, hst]; simpa [MemoryCellSlotRealized] using hlc
    · show MemoryCellSlotRealized seedZ 97 (memoryChildKind pub.st 1) pub.rc
      rw [memoryChildKind, hst]; simpa [MemoryCellSlotRealized] using hrc
  memoryRecord := by
    show MemRecSlotRealized seedZ 97 (memoryMemRecKind pub.st) pub.mem
    rw [hkind]; exact hmem

theorem memDecomposeRealization (pub : MemoryTable.Pub K)
    (hpt : FPSlotRealized seedZ 97 .active pub.pt.noun)
    (hlc : FPSlotRealized seedZ 97 .active pub.lc.noun)
    (hrc : FPSlotRealized seedZ 97 .active pub.rc.noun)
    (hmem : pub.mem = MemRec.zero) :
    MemoryPublicRowNounRealization 97
      (MemoryTable.MState.decompose, (memInputs seedZ, pub)) where
  parent := hpt
  child := by
    intro i; fin_cases i
    · exact hlc
    · exact hrc
  memoryRecord := hmem

theorem memHaltRealization (pub : MemoryTable.Pub K)
    (hpt : FPSlotRealized seedZ 97 .active pub.pt.noun)
    (hlc : pub.lc = MemoryTable.Cell.zero)
    (hrc : pub.rc = MemoryTable.Cell.zero)
    (hmem : pub.mem = MemRec.zero) :
    MemoryPublicRowNounRealization 97
      (MemoryTable.MState.halt, (memInputs seedZ, pub)) where
  parent := hpt
  child := by
    intro i; fin_cases i
    · exact hlc
    · exact hrc
  memoryRecord := hmem

theorem memoryForestNounRealization :
    MemoryPublicForestNounRealization 97 (exec seedZ alphaA).memoryForest := by
  unfold MemoryPublicForestNounRealization MemoryPublicRowsNounRealization
  rw [show (bfsForest (exec seedZ alphaA).memoryForest).map NTree.label =
      (exec seedZ alphaA).memoryRows from rfl, memoryRows_eq]
  refine List.forall_iff_forall_mem.mpr ?_
  intro row hrow
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
  rcases hrow with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact memSingleChildRealization _ rfl (fpActive bounded_formula)
        (fpActive bounded_formula) rfl rfl
        (recF_active.formRRow _)
    | exact memDecomposeRealization _ (fpActive bounded_formula) (fpActive bounded_op5Head) (fpActive bounded_tail) rfl
    | exact memHaltRealization _ (fpActive bounded_op5Head) rfl rfl rfl
    | exact memSingleChildRealization _ rfl (fpActive bounded_tail) (fpActive bounded_tail) rfl rfl
        (recF_active.formRRow _)
    | exact memSingleChildRealization _ rfl (fpActive bounded_tail) (fpActive bounded_tail) rfl rfl
        (recT_active.formRRow _)
    | exact memDecomposeRealization _ (fpActive bounded_tail) (fpActive bounded_childB) (fpActive bounded_childC) rfl
    | exact memSingleChildRealization _ rfl (fpActive bounded_childB) (fpActive bounded_childB) rfl
        rfl
        (recT_active.formRRow _)
    | exact memSingleChildRealization _ rfl (fpActive bounded_childC) (fpActive bounded_childC) rfl
        rfl
        (recC_active.formRRow _)
    | exact memSingleChildRealization _ rfl (fpActive bounded_childB) (fpActive bounded_childB) rfl
        rfl
        (recB_active.formRRow _)
    | exact memDecomposeRealization _ (fpActive bounded_childC) (fpActive bounded_op1Head) (fpActive bounded_sf2) rfl
    | exact memDecomposeRealization _ (fpActive bounded_childB) (fpActive bounded_op1Head) (fpActive bounded_sf1) rfl
    | exact memHaltRealization _ (fpActive bounded_op1Head) rfl rfl rfl
    | exact memSingleChildRealization _ rfl (fpActive bounded_sf2) (fpActive bounded_sf2) rfl rfl
        (recC_active.formRRow _)
    | exact memSingleChildRealization _ rfl (fpActive bounded_sf1) (fpActive bounded_sf1) rfl rfl
        (recB_active.formRRow _)
    | exact memHaltRealization _ (fpActive bounded_sf2) rfl rfl rfl
    | exact memHaltRealization _ (fpActive bounded_sf1) rfl rfl rfl

theorem nounRealization :
    ExactExecutionNounRealization 97 (cfg seedZ alphaA) (exec seedZ alphaA) where
  computeTree := computeTreeNounRealization
  memoryForest := memoryForestNounRealization
  memoryLeaves := by
    intro tree htree
    simp only [exec, List.mem_cons, List.not_mem_nil, or_false] at htree
    subst htree
    exact leafAtoms_rootTree

/-! ## J. The cumulative language bundle and assembled semantic data -/

theorem language
    (hfirst :
      ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.counts = 0 ∧
        ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.indicator = 0) :
    NounRealizedTraversableChainedSemanticExactLanguage 97 (cfg seedZ alphaA)
      (exec seedZ alphaA) where
  traversable := traversable hfirst
  nounRealization := nounRealization

def semanticData
    (hfirst :
      ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.counts = 0 ∧
        ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.indicator = 0) :
    SemanticTrace.ExactExecutionSemanticData 97 5 (cfg seedZ alphaA) (exec seedZ alphaA) where
  language := language hfirst
  rowAccepted := fun i => ExactExecution.computeRowAt_accepted computeRowsAccepted i
  rows := rowData

/-! ## K. Served memory trace -/

def memoryTrace
    (hfirst :
      ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.counts = 0 ∧
        ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.indicator = 0) :
    ExactServedMemoryTrace 97 5 (cfg seedZ alphaA) (exec seedZ alphaA) (semanticData hfirst)
      (execA seedZ alphaA) where
  roots := rootTraces
  timestampPowersNodup := forestTimestampPowers_nodup
  forestIndexRange := by
    rw [forestTimestampPowers_eq]
    norm_num [IO.InRange, cfg]
  semanticCoverage := by
    intro row lookup hlookup
    have hl : lookup ∈ (rowData row).needs.served := hlookup
    have hmem : lookupTuple lookup ∈ (rowData row).needs.served.map lookupTuple :=
      List.mem_map_of_mem hl
    fin_cases row
    · rw [rowData_zero_servedTuples] at hmem; simp at hmem
    · rw [rowData_one_servedTuples] at hmem; simp at hmem
    · rw [rowData_two_servedTuples] at hmem; simp at hmem

end

end Nock.NockVMROM.Thm54.TraceGen.Op5ConfigK3

#print axioms Nock.NockVMROM.Thm54.TraceGen.Op5ConfigK3.semanticPreimage
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op5ConfigK3.language
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op5ConfigK3.semanticData
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op5ConfigK3.memoryTrace
