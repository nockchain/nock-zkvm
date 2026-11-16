/-
  Nock/NockVMROM/Thm54/TraceGen/Op6LanguageK3.lean

  Stage 4d of the OP6 Layer-2 CORE, over `K3`: the per-row `ComputeRowSemanticData`,
  memory trace, semantic IO preimage, chained/traversable language, noun realization,
  and the assembled `ExactExecutionSemanticData 97 7` for the fan-out-2 branch program

      `*[0 [6 [[1 0] [[1 5] [1 6]]]]] = 5`

  Five committed records: parent formula@3 (`α¹`), parent formula-tail@2 (`α²`),
  branch-pair@2 (`α³`), child1 branchC@3 (`α⁴`), child2 condFormula@3 (`α⁵`).
  The `.s6` parent row has shared-subject threading: both children evaluate against `0`.
  The two `.s1` children reuse the OP1 three-entry census, adapted to `Λ = 7`.
  -- the paper
-/
import Nock.NockVMROM.Thm54.TraceGen.Op6RowWebK3
import Nock.NockVMROM.Thm54.ServedMemoryTrace
import Nock.NockVMROM.Thm54.AxisSoundness
import Nock.NockVMROM.Thm54.Language
import Nock.NockVMROM.Thm54.NounRealization
import Nock.NockVMROM.Thm54.SemanticTrace
import Mathlib.Tactic.IntervalCases

namespace Nock.NockVMROM.Thm54.TraceGen.Op6ConfigK3

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

theorem bounded_subject : FieldEmbedding.BoundedBy 97 op6Subject :=
  bounded_atom 0 (by norm_num)
theorem bounded_op6Head : FieldEmbedding.BoundedBy 97 (.atom 6) :=
  bounded_atom 6 (by norm_num)
theorem bounded_op1Head : FieldEmbedding.BoundedBy 97 op1Head :=
  bounded_atom 1 (by norm_num)
theorem bounded_result : FieldEmbedding.BoundedBy 97 op6Result :=
  bounded_atom 5 (by norm_num)
theorem bounded_condResult : FieldEmbedding.BoundedBy 97 op6CondResult :=
  bounded_atom 0 (by norm_num)
theorem bounded_condFormula : FieldEmbedding.BoundedBy 97 op6CondFormula :=
  ⟨bounded_op1Head, bounded_condResult⟩
theorem bounded_branchC : FieldEmbedding.BoundedBy 97 op6BranchC :=
  ⟨bounded_op1Head, bounded_result⟩
theorem bounded_branchD : FieldEmbedding.BoundedBy 97 op6BranchD :=
  ⟨bounded_op1Head, bounded_op6Head⟩
theorem bounded_branchPair : FieldEmbedding.BoundedBy 97 op6BranchPair :=
  ⟨bounded_branchC, bounded_branchD⟩
theorem bounded_parentTail : FieldEmbedding.BoundedBy 97 op6ParentTail :=
  ⟨bounded_condFormula, bounded_branchPair⟩
theorem bounded_parentFormula : FieldEmbedding.BoundedBy 97 op6ParentFormula :=
  ⟨bounded_op6Head, bounded_parentTail⟩

noncomputable section

/-! ## B. Per-row semantic data -/

def parentRoot :
    OpcodeSemantics.RootRealization (compInputs seedZ alphaA) (parentPub seedZ alphaA)
      (parentDec seedZ) where
  subject := op6Subject
  formula := op6ParentFormula
  result := op6Result
  head := .atom 6
  tail := op6ParentTail
  subject_realizes := rfl
  formula_realizes := rfl
  result_realizes := rfl
  head_realizes := rfl
  tail_realizes := rfl

def parentTailR :
    OpcodeSemantics.TailRealization (compInputs seedZ alphaA).z (parentDec seedZ) where
  head := op6CondFormula
  tail := op6BranchPair
  head_realizes := rfl
  tail_realizes := rfl

def parentBranchTailR :
    OpcodeSemantics.BranchTailRealization (compInputs seedZ alphaA).z (parentDec seedZ) where
  head := op6BranchC
  tail := op6BranchD
  head_realizes := rfl
  tail_realizes := rfl

def parentCall1 :
    OpcodeSemantics.CallRealization (compInputs seedZ alphaA).z
      (parentPub seedZ alphaA).sf1_s (parentPub seedZ alphaA).sf1_f
      (parentPub seedZ alphaA).sf1_e where
  subject := op6Subject
  formula := op6BranchC
  result := op6Result
  subject_realizes := rfl
  formula_realizes := rfl
  result_realizes := rfl

def parentCall2 :
    OpcodeSemantics.CallRealization (compInputs seedZ alphaA).z
      (parentPub seedZ alphaA).sf2_s (parentPub seedZ alphaA).sf2_f
      (parentPub seedZ alphaA).sf2_e where
  subject := op6Subject
  formula := op6CondFormula
  result := op6CondResult
  subject_realizes := rfl
  formula_realizes := rfl
  result_realizes := rfl

private theorem leaf_branchC :
    (GlobalCarryRecognizer.enc seedZ op6BranchC).leaf = (1 : K) + seedZ * 5 := by
  rw [GlobalCarryRecognizer.enc_leaf]
  show (NPR.listPoly (NPR.leafF (K := K) op6BranchC)).eval seedZ = _
  have hleaf : NPR.leafF (K := K) op6BranchC = [(1 : K), 5] := by
    simp [NPR.leafF, Noun.leafList, op6BranchC, op1Head, op6Result, List.map]
  rw [hleaf, NPR.listPoly_cons, NPR.listPoly_cons, NPR.listPoly_nil]
  simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_zero]
  ring

private theorem leaf_branchD :
    (GlobalCarryRecognizer.enc seedZ op6BranchD).leaf = (1 : K) + seedZ * 6 := by
  rw [GlobalCarryRecognizer.enc_leaf]
  show (NPR.listPoly (NPR.leafF (K := K) op6BranchD)).eval seedZ = _
  have hleaf : NPR.leafF (K := K) op6BranchD = [(1 : K), 6] := by
    simp [NPR.leafF, Noun.leafList, op6BranchD, op1Head, List.map]
  rw [hleaf, NPR.listPoly_cons, NPR.listPoly_cons, NPR.listPoly_nil]
  simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_zero]
  ring

private theorem encS_branchC_ne_branchD_K3 :
    fp seedZ op6BranchC ≠ fp seedZ op6BranchD := by
  intro h
  have hl := congrArg ComputeTable.FP.leaf h
  change (GlobalCarryRecognizer.enc seedZ op6BranchC).leaf =
    (GlobalCarryRecognizer.enc seedZ op6BranchD).leaf at hl
  rw [leaf_branchC, leaf_branchD, seedZ] at hl
  exact absurd hl (by decide)

private theorem op6_branch_fn_ne_K3 :
    NPR.fn op6BranchC (seedZ : K) ≠ NPR.fn op6BranchD seedZ := by
  intro h
  apply encS_branchC_ne_branchD_K3
  show GlobalCarryRecognizer.enc seedZ op6BranchC = GlobalCarryRecognizer.enc seedZ op6BranchD
  simp only [GlobalCarryRecognizer.enc_eq_fn, h]

private theorem op6_branch_pairFaithful_K3 :
    OpcodeSemantics.PairFaithful seedZ 97 op6BranchC op6BranchD where
  separates := fun _ => op6_branch_fn_ne_K3
  left_bounded := bounded_branchC
  right_bounded := bounded_branchD

def parentComparisons : List ComparisonUse :=
  [ { role := .opcodeHead, left := .atom 6, right := .atom 6 },
    { role := .formulaCons, left := op6ParentFormula, right := .cell (.atom 6) op6ParentTail },
    { role := .tailCons, left := op6ParentTail,
      right := .cell op6CondFormula op6BranchPair },
    { role := .branchTailCons, left := op6BranchPair,
      right := .cell op6BranchC op6BranchD },
    { role := .recursiveSubject, left := op6Subject, right := op6Subject },
    { role := .recursiveFormula, left := op6BranchC, right := op6BranchC },
    { role := .recursiveFormula, left := op6BranchC, right := op6BranchD },
    { role := .recursiveSubject, left := op6Subject, right := op6Subject },
    { role := .recursiveFormula, left := op6CondFormula, right := op6CondFormula },
    { role := .producedResult, left := op6Result, right := op6Result } ]

theorem seedZ_ne_one : (seedZ : K) ≠ 1 := by rw [seedZ]; decide

theorem seedZ_order_base : orderOf (8 : F) = 16 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, ?_⟩
  intro m hm hpos
  interval_cases m <;> decide

theorem seedZ_order : orderOf seedZ = 16 := by
  have h := orderOf_injective φ.toMonoidHom φ_injective (8 : F)
  rw [seedZ_order_base] at h
  have heq : seedZ = φ (8 : F) := by rw [seedZ]; simp only [map_ofNat]
  rw [heq]; exact h

theorem seedZ_order_gt_one : 1 < orderOf (seedZ : K) := by
  rw [seedZ_order]; norm_num

def parentCondWindow : OpcodeSemantics.SizeWindow seedZ op6CondResult where
  one_lt_order := seedZ_order_gt_one
  leaves_lt_order := by simp [op6CondResult, Noun.leaves]; exact seedZ_order_gt_one

def parentRowData : ComputeRowSemanticData 97 7 (parentRow seedZ alphaA) where
  root := parentRoot
  tails := [parentTailR]
  branchTails := [parentBranchTailR]
  calls :=
    [ { subjectFP := (parentPub seedZ alphaA).sf1_s
        formulaFP := (parentPub seedZ alphaA).sf1_f
        resultFP := (parentPub seedZ alphaA).sf1_e
        realization := parentCall1 },
      { subjectFP := (parentPub seedZ alphaA).sf2_s
        formulaFP := (parentPub seedZ alphaA).sf2_f
        resultFP := (parentPub seedZ alphaA).sf2_e
        realization := parentCall2 } ]
  windows := [{ noun := op6CondResult, window := parentCondWindow }]
  axisGates := []
  tails_count := rfl
  branchTails_count := rfl
  calls_count := rfl
  windows_count := rfl
  axisGates_count := rfl
  realizedNouns := [op6Subject, op6ParentFormula, op6Result]
  subject_mem := by simp [parentRoot]
  formula_mem := by simp [parentRoot]
  result_mem := by simp [parentRoot]
  bounded := by
    intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h | h | h <;> subst h
    · exact bounded_subject
    · exact bounded_parentFormula
    · exact bounded_result
  comparisons := parentComparisons
  comparison_faithful := by
    intro c hc
    simp only [parentComparisons, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with h | h | h | h | h | h | h | h | h | h <;> subst h
    · exact pairFaithful_self _ bounded_op6Head
    · exact pairFaithful_self _ bounded_parentFormula
    · exact pairFaithful_self _ bounded_parentTail
    · exact pairFaithful_self _ bounded_branchPair
    · exact pairFaithful_self _ bounded_subject
    · exact pairFaithful_self _ bounded_branchC
    · exact op6_branch_pairFaithful_K3
    · exact pairFaithful_self _ bounded_subject
    · exact pairFaithful_self _ bounded_condFormula
    · exact pairFaithful_self _ bounded_result
  comparison_leaves := by
    intro c hc
    simp only [parentComparisons, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with h | h | h | h | h | h | h | h | h | h <;> subst h <;>
      exact ⟨by decide, by decide⟩
  comparison_roles := rfl
  axisGate_listed := by intro gate hgate; simp at hgate
  axisGate_tail_mem := by intro gate hgate; simp at hgate
  needs :=
    { served := []
      served_count := rfl }

/-! ### The two `OP_1` child rows (`Λ = 7`) -/

def child1Root :
    OpcodeSemantics.RootRealization (compInputs seedZ alphaA) (child1Pub seedZ alphaA)
      (op1DecOf seedZ op6Result) where
  subject := op6Subject
  formula := op6BranchC
  result := op6Result
  head := op1Head
  tail := op6Result
  subject_realizes := rfl
  formula_realizes := rfl
  result_realizes := rfl
  head_realizes := rfl
  tail_realizes := rfl

def child2Root :
    OpcodeSemantics.RootRealization (compInputs seedZ alphaA) (child2Pub seedZ alphaA)
      (op1DecOf seedZ op6CondResult) where
  subject := op6Subject
  formula := op6CondFormula
  result := op6CondResult
  head := op1Head
  tail := op6CondResult
  subject_realizes := rfl
  formula_realizes := rfl
  result_realizes := rfl
  head_realizes := rfl
  tail_realizes := rfl

def child1Comparisons : List ComparisonUse :=
  [ { role := .opcodeHead, left := op1Head, right := .atom 1 },
    { role := .formulaCons, left := op6BranchC, right := .cell op1Head op6Result },
    { role := .producedResult, left := op6Result, right := op6Result } ]

def child2Comparisons : List ComparisonUse :=
  [ { role := .opcodeHead, left := op1Head, right := .atom 1 },
    { role := .formulaCons, left := op6CondFormula, right := .cell op1Head op6CondResult },
    { role := .producedResult, left := op6CondResult, right := op6CondResult } ]

def child1RowData : ComputeRowSemanticData 97 7 (child1Row seedZ alphaA) where
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
  realizedNouns := [op6Subject, op6BranchC, op6Result]
  subject_mem := by simp [child1Root]
  formula_mem := by simp [child1Root]
  result_mem := by simp [child1Root]
  bounded := by
    intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h | h | h <;> subst h
    · exact bounded_subject
    · exact bounded_branchC
    · exact bounded_result
  comparisons := child1Comparisons
  comparison_faithful := by
    intro c hc
    simp only [child1Comparisons, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with h | h | h <;> subst h
    · exact pairFaithful_self _ bounded_op1Head
    · exact pairFaithful_self _ bounded_branchC
    · exact pairFaithful_self _ bounded_result
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

def child2RowData : ComputeRowSemanticData 97 7 (child2Row seedZ alphaA) where
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
  realizedNouns := [op6Subject, op6CondFormula, op6CondResult]
  subject_mem := by simp [child2Root]
  formula_mem := by simp [child2Root]
  result_mem := by simp [child2Root]
  bounded := by
    intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h | h | h <;> subst h
    · exact bounded_subject
    · exact bounded_condFormula
    · exact bounded_condResult
  comparisons := child2Comparisons
  comparison_faithful := by
    intro c hc
    simp only [child2Comparisons, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with h | h | h <;> subst h
    · exact pairFaithful_self _ bounded_op1Head
    · exact pairFaithful_self _ bounded_condFormula
    · exact pairFaithful_self _ bounded_condResult
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

/-! ### Indexed row accessor (BFS order: parent, child1-branch, child2-cond) -/

def castRowData {row₁ row₂ : ComputeTable.State × ComputeTable.DTcomp K}
    (h : row₁ = row₂) (d : ComputeRowSemanticData 97 7 row₂) :
    ComputeRowSemanticData 97 7 row₁ :=
  h.symm ▸ d

def rowData : ∀ i : Fin (cfg seedZ alphaA).compRows,
    ComputeRowSemanticData 97 7 ((exec seedZ alphaA).computeRowAt i)
  | ⟨0, _⟩ => castRowData computeRowAt_zero parentRowData
  | ⟨1, _⟩ => castRowData computeRowAt_one child1RowData
  | ⟨2, _⟩ => castRowData computeRowAt_two child2RowData
  | ⟨n + 3, h⟩ => by simp only [cfg] at h; exact absurd h (by omega)

/-! ## C. Timestamp exponents of the five records -/

theorem ts_closed_recF :
    TimestampClosedAt (cfg seedZ alphaA).challenges.α (recF seedZ alphaA).ts :=
  ⟨1, by rw [ts_recF]; simp [cfg, alphaA]⟩
theorem ts_closed_recT :
    TimestampClosedAt (cfg seedZ alphaA).challenges.α (recT seedZ alphaA).ts :=
  ⟨2, by rw [ts_recT]; rfl⟩
theorem ts_closed_recP :
    TimestampClosedAt (cfg seedZ alphaA).challenges.α (recP seedZ alphaA).ts :=
  ⟨3, by rw [ts_recP]; rfl⟩
theorem ts_closed_recC1 :
    TimestampClosedAt (cfg seedZ alphaA).challenges.α (recC1 seedZ alphaA).ts :=
  ⟨4, by rw [ts_recC1]; rfl⟩
theorem ts_closed_recC2 :
    TimestampClosedAt (cfg seedZ alphaA).challenges.α (recC2 seedZ alphaA).ts :=
  ⟨5, by rw [ts_recC2]; rfl⟩

def expF : ℕ := timestampExp (cfg seedZ alphaA).challenges.α (recF seedZ alphaA).ts
def expT : ℕ := timestampExp (cfg seedZ alphaA).challenges.α (recT seedZ alphaA).ts
def expP : ℕ := timestampExp (cfg seedZ alphaA).challenges.α (recP seedZ alphaA).ts
def expC1 : ℕ := timestampExp (cfg seedZ alphaA).challenges.α (recC1 seedZ alphaA).ts
def expC2 : ℕ := timestampExp (cfg seedZ alphaA).challenges.α (recC2 seedZ alphaA).ts

theorem ts_eq_recF : (recF seedZ alphaA).ts = (cfg seedZ alphaA).challenges.α ^ expF :=
  timestampExp_spec ts_closed_recF
theorem ts_eq_recT : (recT seedZ alphaA).ts = (cfg seedZ alphaA).challenges.α ^ expT :=
  timestampExp_spec ts_closed_recT
theorem ts_eq_recP : (recP seedZ alphaA).ts = (cfg seedZ alphaA).challenges.α ^ expP :=
  timestampExp_spec ts_closed_recP
theorem ts_eq_recC1 : (recC1 seedZ alphaA).ts = (cfg seedZ alphaA).challenges.α ^ expC1 :=
  timestampExp_spec ts_closed_recC1
theorem ts_eq_recC2 : (recC2 seedZ alphaA).ts = (cfg seedZ alphaA).challenges.α ^ expC2 :=
  timestampExp_spec ts_closed_recC2

theorem expF_ne_expT : expF ≠ expT := by
  intro h
  have hF := ts_recF.symm.trans ts_eq_recF
  have hT := ts_recT.symm.trans ts_eq_recT
  rw [h] at hF; exact alpha_pow_ne_12 (hF.trans hT.symm)
theorem expF_ne_expP : expF ≠ expP := by
  intro h
  have hF := ts_recF.symm.trans ts_eq_recF
  have hP := ts_recP.symm.trans ts_eq_recP
  rw [h] at hF; exact alpha_pow_ne_13 (hF.trans hP.symm)
theorem expF_ne_expC1 : expF ≠ expC1 := by
  intro h
  have hF := ts_recF.symm.trans ts_eq_recF
  have hC1 := ts_recC1.symm.trans ts_eq_recC1
  rw [h] at hF; exact alpha_pow_ne_14 (hF.trans hC1.symm)
theorem expF_ne_expC2 : expF ≠ expC2 := by
  intro h
  have hF := ts_recF.symm.trans ts_eq_recF
  have hC2 := ts_recC2.symm.trans ts_eq_recC2
  rw [h] at hF; exact alpha_pow_ne_15 (hF.trans hC2.symm)
theorem expT_ne_expP : expT ≠ expP := by
  intro h
  have hT := ts_recT.symm.trans ts_eq_recT
  have hP := ts_recP.symm.trans ts_eq_recP
  rw [h] at hT; exact alpha_pow_ne_23 (hT.trans hP.symm)
theorem expT_ne_expC1 : expT ≠ expC1 := by
  intro h
  have hT := ts_recT.symm.trans ts_eq_recT
  have hC1 := ts_recC1.symm.trans ts_eq_recC1
  rw [h] at hT; exact alpha_pow_ne_24 (hT.trans hC1.symm)
theorem expT_ne_expC2 : expT ≠ expC2 := by
  intro h
  have hT := ts_recT.symm.trans ts_eq_recT
  have hC2 := ts_recC2.symm.trans ts_eq_recC2
  rw [h] at hT; exact alpha_pow_ne_25 (hT.trans hC2.symm)
theorem expP_ne_expC1 : expP ≠ expC1 := by
  intro h
  have hP := ts_recP.symm.trans ts_eq_recP
  have hC1 := ts_recC1.symm.trans ts_eq_recC1
  rw [h] at hP; exact alpha_pow_ne_34 (hP.trans hC1.symm)
theorem expP_ne_expC2 : expP ≠ expC2 := by
  intro h
  have hP := ts_recP.symm.trans ts_eq_recP
  have hC2 := ts_recC2.symm.trans ts_eq_recC2
  rw [h] at hP; exact alpha_pow_ne_35 (hP.trans hC2.symm)
theorem expC1_ne_expC2 : expC1 ≠ expC2 := by
  intro h
  have hC1 := ts_recC1.symm.trans ts_eq_recC1
  have hC2 := ts_recC2.symm.trans ts_eq_recC2
  rw [h] at hC1; exact alpha_pow_ne_45 (hC1.trans hC2.symm)

theorem expT_ne_expF : expT ≠ expF := fun h => expF_ne_expT h.symm
theorem expP_ne_expF : expP ≠ expF := fun h => expF_ne_expP h.symm
theorem expC1_ne_expF : expC1 ≠ expF := fun h => expF_ne_expC1 h.symm
theorem expC2_ne_expF : expC2 ≠ expF := fun h => expF_ne_expC2 h.symm
theorem expP_ne_expT : expP ≠ expT := fun h => expT_ne_expP h.symm
theorem expC1_ne_expT : expC1 ≠ expT := fun h => expT_ne_expC1 h.symm
theorem expC2_ne_expT : expC2 ≠ expT := fun h => expT_ne_expC2 h.symm
theorem expC1_ne_expP : expC1 ≠ expP := fun h => expP_ne_expC1 h.symm
theorem expC2_ne_expP : expC2 ≠ expP := fun h => expP_ne_expC2 h.symm
theorem expC2_ne_expC1 : expC2 ≠ expC1 := fun h => expC1_ne_expC2 h.symm

/-! ## D. The memory axis tree and services -/

theorem memoryTreeAt_zero :
    (execA seedZ alphaA).memoryTreeAt ⟨0, by norm_num [cfg]⟩ = rootTreeA seedZ alphaA := rfl

theorem axisPath_three : axisPath 3 = [true] := by
  rw [axisPath_of_two_le (by norm_num)]; norm_num [axisPath_of_lt_two]
theorem axisPath_two : axisPath 2 = [false] := by
  rw [axisPath_of_two_le (by norm_num)]; norm_num [axisPath_of_lt_two]

set_option maxRecDepth 400000 in
theorem op6AxisTree_eq :
    exactAxisTree (cfg seedZ alphaA) (execA seedZ alphaA) ⟨0, by norm_num [cfg]⟩ =
      MTree.read expF
        (MTree.decompose MTree.halt
          (MTree.verify expF 3
            (MTree.read expT
              (MTree.decompose
                (MTree.verify expT 2
                  (MTree.read expC2
                    (MTree.decompose MTree.halt
                      (MTree.verify expC2 3 MTree.halt))))
                (MTree.read expP
                  (MTree.decompose
                    (MTree.verify expP 2
                      (MTree.read expC1
                        (MTree.decompose MTree.halt
                          (MTree.verify expC1 3 MTree.halt))))
                    (MTree.decompose MTree.halt MTree.halt))))))) := by
  rw [exactAxisTree, memoryTreeAt_zero]
  simp [rootTreeA, tDecFA, tHalt6, tVerifyFA, tReadTA, tDecTA, tVerifyTA,
    tReadC2A, tDecC2A, tHalt1_c2, tVerifyC2A, tHalt0,
    tReadPA, tDecPA, tVerifyPA, tReadC1A, tDecC1A, tHalt1_c1, tVerifyC1A, tHalt5,
    tDecBranchD, tHalt1_d, tHalt6_d,
    mOne, mTwo, mLeaf,
    lblOf, Nock.AxisBridge.ofNTree, Nock.AxisBridge.MemWalk.toMTree, timestampExpAt,
    expF, expT, expP, expC1, expC2,
    pReadFA, pDecF, pHalt6, pVerifyFA, pReadTA, pDecT, pVerifyTA,
    pReadC2A, pDecC2, pHalt1_c2, pVerifyC2A, pHalt0,
    pReadPA, pDecP, pVerifyPA, pReadC1A, pDecC1, pHalt1_c1, pVerifyC1A, pHalt5,
    pDecBranchD, pHalt1_d, pHalt6_d,
    readPub, readPubA, decPub, haltPub, verifyPub, verifyPubA,
    recF, recT, recP, recC1, recC2]

def serviceF : Service (cfg seedZ alphaA) (execA seedZ alphaA) where
  exponent := expF
  record := recF seedZ alphaA
  root := op6ParentFormula
  child := op6ParentTail
  axis := 3
  request_mem := by
    rw [show (execA seedZ alphaA).rawRequests = (exec seedZ alphaA).rawRequests from rfl,
      rawRequests_eq]; simp
  timestamp := ts_eq_recF
  realization :=
    { root_realizes := rfl
      child_realizes := rfl
      axis_realizes := by norm_num [recF] }
  served := by simp [op6ParentFormula, op6ParentTail, Noun.slot]

def serviceT : Service (cfg seedZ alphaA) (execA seedZ alphaA) where
  exponent := expT
  record := recT seedZ alphaA
  root := op6ParentTail
  child := op6CondFormula
  axis := 2
  request_mem := by
    rw [show (execA seedZ alphaA).rawRequests = (exec seedZ alphaA).rawRequests from rfl,
      rawRequests_eq]; simp
  timestamp := ts_eq_recT
  realization :=
    { root_realizes := rfl
      child_realizes := rfl
      axis_realizes := by norm_num [recT] }
  served := by simp [op6ParentTail, op6CondFormula, Noun.slot]

def serviceP : Service (cfg seedZ alphaA) (execA seedZ alphaA) where
  exponent := expP
  record := recP seedZ alphaA
  root := op6BranchPair
  child := op6BranchC
  axis := 2
  request_mem := by
    rw [show (execA seedZ alphaA).rawRequests = (exec seedZ alphaA).rawRequests from rfl,
      rawRequests_eq]; simp
  timestamp := ts_eq_recP
  realization :=
    { root_realizes := rfl
      child_realizes := rfl
      axis_realizes := by norm_num [recP] }
  served := by simp [op6BranchPair, op6BranchC, Noun.slot]

def serviceC1 : Service (cfg seedZ alphaA) (execA seedZ alphaA) where
  exponent := expC1
  record := recC1 seedZ alphaA
  root := op6BranchC
  child := op6Result
  axis := 3
  request_mem := by
    rw [show (execA seedZ alphaA).rawRequests = (exec seedZ alphaA).rawRequests from rfl,
      rawRequests_eq]; simp
  timestamp := ts_eq_recC1
  realization :=
    { root_realizes := rfl
      child_realizes := rfl
      axis_realizes := by norm_num [recC1] }
  served := by simp [op6BranchC, op6Result, Noun.slot]

def serviceC2 : Service (cfg seedZ alphaA) (execA seedZ alphaA) where
  exponent := expC2
  record := recC2 seedZ alphaA
  root := op6CondFormula
  child := op6CondResult
  axis := 3
  request_mem := by
    rw [show (execA seedZ alphaA).rawRequests = (exec seedZ alphaA).rawRequests from rfl,
      rawRequests_eq]; simp
  timestamp := ts_eq_recC2
  realization :=
    { root_realizes := rfl
      child_realizes := rfl
      axis_realizes := by norm_num [recC2] }
  served := by simp [op6CondFormula, op6CondResult, Noun.slot]

/-! ## E. The single root's trace -/

theorem rootResponseRecords_eq :
    rootResponseRecords (execA seedZ alphaA) ⟨0, by norm_num [cfg]⟩ =
      [recF seedZ alphaA, recT seedZ alphaA, recP seedZ alphaA,
       recC2 seedZ alphaA, recC1 seedZ alphaA] := by
  simp [rootResponseRecords, memoryTreeAt_zero, rootTreeA,
    tDecFA, tHalt6, tVerifyFA, tReadTA, tDecTA, tVerifyTA,
    tReadC2A, tDecC2A, tHalt1_c2, tVerifyC2A, tHalt0,
    tReadPA, tDecPA, tVerifyPA, tReadC1A, tDecC1A, tHalt1_c1, tVerifyC1A, tHalt5,
    tDecBranchD, tHalt1_d, tHalt6_d,
    mOne, mTwo, mLeaf, lblOf, bfsForest,
    MemoryTable.responseRecords,
    pReadFA, pDecF, pHalt6, pVerifyFA, pReadTA, pDecT, pVerifyTA,
    pReadC2A, pDecC2, pHalt1_c2, pVerifyC2A, pHalt0,
    pReadPA, pDecP, pVerifyPA, pReadC1A, pDecC1, pHalt1_c1, pVerifyC1A, pHalt5,
    pDecBranchD, pHalt1_d, pHalt6_d,
    readPub, readPubA, decPub, haltPub, verifyPub, verifyPubA]

def rootTrace : RootTrace (cfg seedZ alphaA) (execA seedZ alphaA) ⟨0, by norm_num [cfg]⟩ where
  subject := op6ParentFormula
  services := [serviceF, serviceT, serviceP, serviceC2, serviceC1]
  recordPartition := by
    rw [rootResponseRecords_eq]
    simp [serviceF, serviceT, serviceP, serviceC2, serviceC1]
  readPartition := by
    rw [op6AxisTree_eq]
    simp only [readExps, serviceF, serviceT, serviceP, serviceC2, serviceC1,
      List.map_cons, List.map_nil]
    exact List.Perm.cons _ (List.Perm.cons _
      (List.Perm.swap _ _ _))
  verifyPartition := by
    rw [op6AxisTree_eq]
    simp only [verifyExps, serviceF, serviceT, serviceP, serviceC2, serviceC1,
      List.map_cons, List.map_nil]
    exact List.Perm.cons _ (List.Perm.cons _
      (List.Perm.swap _ _ _))
  traversal := by
    rw [op6AxisTree_eq]
    refine ServiceWalk.read serviceF (by simp) rfl rfl ?_ ?_
    · rw [show serviceF.axis = 3 from rfl, axisPath_three]
      refine VerifyRoute.right (by simp [readCount]) (by simp [verifyCount]) ?_
      exact VerifyRoute.here rfl rfl
        (by simp [readCount, expT_ne_expF, expP_ne_expF, expC1_ne_expF, expC2_ne_expF])
        (by simp [verifyCount, expT_ne_expF, expP_ne_expF, expC1_ne_expF, expC2_ne_expF])
    · refine ServiceWalk.decompose ServiceWalk.halt ?_
      refine ServiceWalk.verify ?_
      refine ServiceWalk.read serviceT (by simp) rfl rfl ?_ ?_
      · rw [show serviceT.axis = 2 from rfl, axisPath_two]
        refine VerifyRoute.left ?_
          (by simp [readCount, expP_ne_expT, expC1_ne_expT])
          (by simp [verifyCount, expP_ne_expT, expC1_ne_expT])
        exact VerifyRoute.here rfl rfl
          (by simp [readCount, expC2_ne_expT])
          (by simp [verifyCount, expC2_ne_expT])
      · refine ServiceWalk.decompose ?_ ?_
        · refine ServiceWalk.verify ?_
          refine ServiceWalk.read serviceC2 (by simp) rfl rfl ?_ ?_
          · rw [show serviceC2.axis = 3 from rfl, axisPath_three]
            refine VerifyRoute.right (by simp [readCount]) (by simp [verifyCount]) ?_
            exact VerifyRoute.here rfl rfl (by simp [readCount]) (by simp [verifyCount])
          · exact ServiceWalk.decompose ServiceWalk.halt (ServiceWalk.verify ServiceWalk.halt)
        · refine ServiceWalk.read serviceP (by simp) rfl rfl ?_ ?_
          · rw [show serviceP.axis = 2 from rfl, axisPath_two]
            refine VerifyRoute.left ?_
              (by simp [readCount])
              (by simp [verifyCount])
            exact VerifyRoute.here rfl rfl
              (by simp [readCount, expC1_ne_expP])
              (by simp [verifyCount, expC1_ne_expP])
          · refine ServiceWalk.decompose ?_ ?_
            · refine ServiceWalk.verify ?_
              refine ServiceWalk.read serviceC1 (by simp) rfl rfl ?_ ?_
              · rw [show serviceC1.axis = 3 from rfl, axisPath_three]
                refine VerifyRoute.right (by simp [readCount]) (by simp [verifyCount]) ?_
                exact VerifyRoute.here rfl rfl (by simp [readCount]) (by simp [verifyCount])
              · exact ServiceWalk.decompose ServiceWalk.halt
                  (ServiceWalk.verify ServiceWalk.halt)
            · exact ServiceWalk.decompose ServiceWalk.halt ServiceWalk.halt

def rootTraces : ∀ i : Fin (cfg seedZ alphaA).kMem,
    RootTrace (cfg seedZ alphaA) (execA seedZ alphaA) i
  | ⟨0, _⟩ => rootTrace
  | ⟨n + 1, h⟩ => absurd (show n + 1 < 1 by simp only [cfg] at h; exact h) (by omega)

theorem finRange_kMem :
    List.finRange (cfg seedZ alphaA).kMem = [⟨0, by norm_num [cfg]⟩] := rfl

theorem forestTimestampPowers_eq :
    (List.finRange (cfg seedZ alphaA).kMem).flatMap
      (fun i => (rootTraces i).timestampPowers) =
      [alphaA, alphaA ^ 2, alphaA ^ 3, alphaA ^ 5, alphaA ^ 4] := by
  rw [finRange_kMem]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  simp only [RootTrace.timestampPowers, RootTrace.exponents, rootTraces, rootTrace,
    List.map_cons, List.map_nil]
  rw [show (serviceF.exponent : ℕ) = expF from rfl,
    show (serviceT.exponent : ℕ) = expT from rfl,
    show (serviceP.exponent : ℕ) = expP from rfl,
    show (serviceC2.exponent : ℕ) = expC2 from rfl,
    show (serviceC1.exponent : ℕ) = expC1 from rfl,
    ← ts_eq_recF, ← ts_eq_recT, ← ts_eq_recP, ← ts_eq_recC2, ← ts_eq_recC1,
    ts_recF, ts_recT, ts_recP, ts_recC2, ts_recC1]

theorem forestTimestampPowers_nodup :
    ((List.finRange (cfg seedZ alphaA).kMem).flatMap
      (fun i => (rootTraces i).timestampPowers)).Nodup := by
  rw [forestTimestampPowers_eq]
  have h12 := alpha_pow_ne_12
  have h13 := alpha_pow_ne_13
  have h14 := alpha_pow_ne_14
  have h15 := alpha_pow_ne_15
  have h23 := alpha_pow_ne_23
  have h24 := alpha_pow_ne_24
  have h25 := alpha_pow_ne_25
  have h34 := alpha_pow_ne_34
  have h35 := alpha_pow_ne_35
  have h45 := alpha_pow_ne_45
  have h54 : alphaA ^ 5 ≠ alphaA ^ 4 := Ne.symm h45
  simp [List.nodup_cons, h12, h13, h14, h15, h23, h24, h25, h34, h35, h45, h54]

/-! ## F. Vacuous `semanticCoverage` (`.s6`/`.s1` have `requiredServedLookups = 0`) -/

def lookupTuple {z : K} (l : ServedNounLookup z) :
    ComputeTable.MemRec K × Noun × ℕ × Noun :=
  (l.record, l.root, l.axis, l.child)

theorem castRowData_servedTuples
    {row₁ row₂ : ComputeTable.State × ComputeTable.DTcomp K}
    (h : row₁ = row₂) (d : ComputeRowSemanticData 97 7 row₂) :
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

/-! ## G. Semantic IO preimage -/

def semOf (axis : F) (root child : Noun) (exp : ℕ) : (nmrMEF F K).Rec :=
  (axis,
    ((((fp seedZ root).size, (fp seedZ root).dyck, (fp seedZ root).leaf),
      ((fp seedZ child).size, (fp seedZ child).dyck, (fp seedZ child).leaf)),
    exp))

def semF : (nmrMEF F K).Rec := semOf 3 op6ParentFormula op6ParentTail 1
def semT : (nmrMEF F K).Rec := semOf 2 op6ParentTail op6CondFormula 2
def semP : (nmrMEF F K).Rec := semOf 2 op6BranchPair op6BranchC 3
def semC1 : (nmrMEF F K).Rec := semOf 3 op6BranchC op6Result 4
def semC2 : (nmrMEF F K).Rec := semOf 3 op6CondFormula op6CondResult 5

theorem semF_preimage :
    memRecOfNMR F K ((nmrEncoding F K (cfg seedZ alphaA).challenges.α).encode semF) =
      recF seedZ alphaA := by
  ext <;> simp [memRecOfNMR, nmrEncoding, semF, semOf, cfg, recF, seedZ, alphaA, map_ofNat]

theorem semT_preimage :
    memRecOfNMR F K ((nmrEncoding F K (cfg seedZ alphaA).challenges.α).encode semT) =
      recT seedZ alphaA := by
  ext <;> simp [memRecOfNMR, nmrEncoding, semT, semOf, cfg, recT, seedZ, alphaA, map_ofNat,
    pow_two]

theorem semP_preimage :
    memRecOfNMR F K ((nmrEncoding F K (cfg seedZ alphaA).challenges.α).encode semP) =
      recP seedZ alphaA := by
  ext <;> simp [memRecOfNMR, nmrEncoding, semP, semOf, cfg, recP, seedZ, alphaA, map_ofNat,
    pow_succ]

theorem semC1_preimage :
    memRecOfNMR F K ((nmrEncoding F K (cfg seedZ alphaA).challenges.α).encode semC1) =
      recC1 seedZ alphaA := by
  ext <;> simp [memRecOfNMR, nmrEncoding, semC1, semOf, cfg, recC1, seedZ, alphaA, map_ofNat,
    pow_succ]

theorem semC2_preimage :
    memRecOfNMR F K ((nmrEncoding F K (cfg seedZ alphaA).challenges.α).encode semC2) =
      recC2 seedZ alphaA := by
  ext <;> simp [memRecOfNMR, nmrEncoding, semC2, semOf, cfg, recC2, seedZ, alphaA, map_ofNat,
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
theorem semP_bridge :
    bridge F K (cfg seedZ alphaA).challenges.α (cfg seedZ alphaA).challenges.lam semP =
      NockVM.encRecFormR (recP seedZ alphaA) MemoryTable.formRDefault := by
  rw [← d2_record_bridge_agrees, semP_preimage]
  rfl
theorem semC1_bridge :
    bridge F K (cfg seedZ alphaA).challenges.α (cfg seedZ alphaA).challenges.lam semC1 =
      NockVM.encRecFormR (recC1 seedZ alphaA) MemoryTable.formRDefault := by
  rw [← d2_record_bridge_agrees, semC1_preimage]
  rfl
theorem semC2_bridge :
    bridge F K (cfg seedZ alphaA).challenges.α (cfg seedZ alphaA).challenges.lam semC2 =
      NockVM.encRecFormR (recC2 seedZ alphaA) MemoryTable.formRDefault := by
  rw [← d2_record_bridge_agrees, semC2_preimage]
  rfl

theorem semResp_nodup : [semF, semT, semP, semC1, semC2].Nodup := by
  simp [semF, semT, semP, semC1, semC2, semOf]

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
  timestampBound := 6
  timestampBound_le_order := by
    change 6 ≤ orderOf alphaA
    rw [alphaA_order]; norm_num
  semanticRequests := [semF, semT, semP, semC1, semC2]
  semanticResponses := [semF, semT, semP, semC2, semC1]
  requestTimestampBound := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      simp [semF, semT, semP, semC1, semC2, semOf]
  responseTimestampBound := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      simp [semF, semT, semP, semC1, semC2, semOf]
  semantic_lmio := by
    refine ⟨by norm_num [IO.InRange, cfg], [semF, semT, semP, semC1, semC2], by decide,
      semResp_nodup, ?_, List.Perm.cons _ (List.Perm.cons _ (List.Perm.cons _
        (List.Perm.swap _ _ _)))⟩
    exact fun _ => Iff.rfl
  requestTimestamp_determines := by
    intro x hx y hy h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl | rfl <;>
      first | (simp [semF, semT, semP, semC1, semC2, semOf] at h; done) | rfl
  requests_bridge := by
    rw [bridgeRecords, List.map_cons, List.map_cons, List.map_cons, List.map_cons,
      List.map_cons, List.map_nil, semF_bridge, semT_bridge, semP_bridge, semC1_bridge,
      semC2_bridge, derived_requests]
  responses_bridge := by
    rw [bridgeRecords, List.map_cons, List.map_cons, List.map_cons, List.map_cons,
      List.map_cons, List.map_nil, semF_bridge, semT_bridge, semP_bridge, semC2_bridge,
      semC1_bridge, derived_responses]

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
  · rw [memoryPubAt_2]; simp only [pHalt6, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_3]; simp only [pVerifyF, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_4]; simp only [pReadT, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_5]; simp only [pDecT, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_6]; simp only [pVerifyT, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_7]; simp only [pReadP, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_8]; simp only [pReadC2, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_9]; simp only [pDecP, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_10]; simp only [pDecC2, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_11]; simp only [pVerifyP, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_12]; simp only [pDecBranchD, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_13]; simp only [pHalt1_c2, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_14]; simp only [pVerifyC2, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_15]; simp only [pReadC1, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_16]; simp only [pHalt1_d, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_17]; simp only [pHalt6_d, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_18]; simp only [pHalt0, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_19]; simp only [pDecC1, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_20]; simp only [pHalt1_c1, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_21]; simp only [pVerifyC1, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_22]; simp only [pHalt5, readPub, decPub, verifyPub, haltPub]

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
          (cfg seedZ alphaA).memRows_pos = ⟨22, by norm_num [cfg]⟩ := rfl
    rw [hlast, memoryPubAt_22]; rfl

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
theorem recP_ne_zero : recP seedZ alphaA ≠ MemRec.zero := fun h =>
  (pow_ne_zero 3 alphaA_ne_zero) (by simpa [recP, MemRec.zero] using congrArg MemRec.ts h)
theorem recC1_ne_zero : recC1 seedZ alphaA ≠ MemRec.zero := fun h =>
  (pow_ne_zero 4 alphaA_ne_zero) (by simpa [recC1, MemRec.zero] using congrArg MemRec.ts h)
theorem recC2_ne_zero : recC2 seedZ alphaA ≠ MemRec.zero := fun h =>
  (pow_ne_zero 5 alphaA_ne_zero) (by simpa [recC2, MemRec.zero] using congrArg MemRec.ts h)

theorem recF_active : MemRecSlotRealized seedZ 97 .active (recF seedZ alphaA) :=
  ⟨recF_ne_zero, fpActive bounded_parentFormula, fpActive bounded_parentTail⟩
theorem recT_active : MemRecSlotRealized seedZ 97 .active (recT seedZ alphaA) :=
  ⟨recT_ne_zero, fpActive bounded_parentTail, fpActive bounded_condFormula⟩
theorem recP_active : MemRecSlotRealized seedZ 97 .active (recP seedZ alphaA) :=
  ⟨recP_ne_zero, fpActive bounded_branchPair, fpActive bounded_branchC⟩
theorem recC1_active : MemRecSlotRealized seedZ 97 .active (recC1 seedZ alphaA) :=
  ⟨recC1_ne_zero, fpActive bounded_branchC, fpActive bounded_result⟩
theorem recC2_active : MemRecSlotRealized seedZ 97 .active (recC2 seedZ alphaA) :=
  ⟨recC2_ne_zero, fpActive bounded_condFormula, fpActive bounded_condResult⟩

theorem parentRow_nounRealization :
    ComputePublicRowNounRealization 97 (computePublicLabel (parentRow seedZ alphaA)) where
  subject := fpActive bounded_subject
  formula := fpActive bounded_parentFormula
  evaluation := fpActive bounded_result
  subformula := by
    intro i; fin_cases i
    · exact ⟨fpActive bounded_subject, fpActive bounded_branchC, fpActive bounded_result⟩
    · exact ⟨fpActive bounded_subject, fpActive bounded_condFormula, fpActive bounded_condResult⟩
    · exact ⟨rfl, rfl, rfl⟩
  memoryRecord := by
    intro i; fin_cases i
    · exact recF_active
    · exact recT_active
    · exact recP_active

theorem child1Row_nounRealization :
    ComputePublicRowNounRealization 97 (computePublicLabel (child1Row seedZ alphaA)) where
  subject := fpActive bounded_subject
  formula := fpActive bounded_branchC
  evaluation := fpActive bounded_result
  subformula := by intro i; fin_cases i <;> exact ⟨rfl, rfl, rfl⟩
  memoryRecord := by
    intro i; fin_cases i
    · exact recC1_active
    · rfl
    · rfl

theorem child2Row_nounRealization :
    ComputePublicRowNounRealization 97 (computePublicLabel (child2Row seedZ alphaA)) where
  subject := fpActive bounded_subject
  formula := fpActive bounded_condFormula
  evaluation := fpActive bounded_condResult
  subformula := by intro i; fin_cases i <;> exact ⟨rfl, rfl, rfl⟩
  memoryRecord := by
    intro i; fin_cases i
    · exact recC2_active
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

theorem leafAtoms_tHalt6 : MemoryLeafAtomsRealized 97 (tHalt6 seedZ alphaA) :=
  leafAtomHalt 6 (by norm_num) _
theorem leafAtoms_tHalt5 : MemoryLeafAtomsRealized 97 (tHalt5 seedZ alphaA) :=
  leafAtomHalt 5 (by norm_num) _
theorem leafAtoms_tHalt0 : MemoryLeafAtomsRealized 97 (tHalt0 seedZ alphaA) :=
  leafAtomHalt 0 (by norm_num) _
theorem leafAtoms_tHalt1_c1 : MemoryLeafAtomsRealized 97 (tHalt1_c1 seedZ alphaA) :=
  leafAtomHalt 1 (by norm_num) _
theorem leafAtoms_tHalt1_c2 : MemoryLeafAtomsRealized 97 (tHalt1_c2 seedZ alphaA) :=
  leafAtomHalt 1 (by norm_num) _
theorem leafAtoms_tHalt1_d : MemoryLeafAtomsRealized 97 (tHalt1_d seedZ alphaA) :=
  leafAtomHalt 1 (by norm_num) _
theorem leafAtoms_tHalt6_d : MemoryLeafAtomsRealized 97 (tHalt6_d seedZ alphaA) :=
  leafAtomHalt 6 (by norm_num) _

theorem leafAtoms_tVerifyC1 : MemoryLeafAtomsRealized 97 (tVerifyC1 seedZ alphaA) :=
  leafAtoms_tHalt5
theorem leafAtoms_tDecC1 : MemoryLeafAtomsRealized 97 (tDecC1 seedZ alphaA) :=
  ⟨leafAtoms_tHalt1_c1, leafAtoms_tVerifyC1⟩
theorem leafAtoms_tReadC1 : MemoryLeafAtomsRealized 97 (tReadC1 seedZ alphaA) :=
  leafAtoms_tDecC1
theorem leafAtoms_tVerifyP : MemoryLeafAtomsRealized 97 (tVerifyP seedZ alphaA) :=
  leafAtoms_tReadC1
theorem leafAtoms_tDecBranchD : MemoryLeafAtomsRealized 97 (tDecBranchD seedZ alphaA) :=
  ⟨leafAtoms_tHalt1_d, leafAtoms_tHalt6_d⟩
theorem leafAtoms_tDecP : MemoryLeafAtomsRealized 97 (tDecP seedZ alphaA) :=
  ⟨leafAtoms_tVerifyP, leafAtoms_tDecBranchD⟩
theorem leafAtoms_tReadP : MemoryLeafAtomsRealized 97 (tReadP seedZ alphaA) :=
  leafAtoms_tDecP

theorem leafAtoms_tVerifyC2 : MemoryLeafAtomsRealized 97 (tVerifyC2 seedZ alphaA) :=
  leafAtoms_tHalt0
theorem leafAtoms_tDecC2 : MemoryLeafAtomsRealized 97 (tDecC2 seedZ alphaA) :=
  ⟨leafAtoms_tHalt1_c2, leafAtoms_tVerifyC2⟩
theorem leafAtoms_tReadC2 : MemoryLeafAtomsRealized 97 (tReadC2 seedZ alphaA) :=
  leafAtoms_tDecC2
theorem leafAtoms_tVerifyT : MemoryLeafAtomsRealized 97 (tVerifyT seedZ alphaA) :=
  leafAtoms_tReadC2

theorem leafAtoms_tDecT : MemoryLeafAtomsRealized 97 (tDecT seedZ alphaA) :=
  ⟨leafAtoms_tVerifyT, leafAtoms_tReadP⟩
theorem leafAtoms_tReadT : MemoryLeafAtomsRealized 97 (tReadT seedZ alphaA) :=
  leafAtoms_tDecT
theorem leafAtoms_tVerifyF : MemoryLeafAtomsRealized 97 (tVerifyF seedZ alphaA) :=
  leafAtoms_tReadT
theorem leafAtoms_tDecF : MemoryLeafAtomsRealized 97 (tDecF seedZ alphaA) :=
  ⟨leafAtoms_tHalt6, leafAtoms_tVerifyF⟩
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
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact memSingleChildRealization _ rfl
        (fpActive bounded_parentFormula) (fpActive bounded_parentFormula) rfl rfl
            (recF_active.formRRow _)
    | exact memDecomposeRealization _
        (fpActive bounded_parentFormula) (fpActive bounded_op6Head) (fpActive bounded_parentTail) rfl
    | exact memHaltRealization _ (fpActive bounded_op6Head) rfl rfl rfl
    | exact memSingleChildRealization _ rfl
        (fpActive bounded_parentTail) (fpActive bounded_parentTail) rfl rfl (recF_active.formRRow _)
    | exact memSingleChildRealization _ rfl
        (fpActive bounded_parentTail) (fpActive bounded_parentTail) rfl rfl (recT_active.formRRow _)
    | exact memDecomposeRealization _
        (fpActive bounded_parentTail) (fpActive bounded_condFormula) (fpActive bounded_branchPair) rfl
    | exact memSingleChildRealization _ rfl
        (fpActive bounded_condFormula) (fpActive bounded_condFormula) rfl rfl
            (recT_active.formRRow _)
    | exact memSingleChildRealization _ rfl
        (fpActive bounded_condFormula) (fpActive bounded_condFormula) rfl rfl
            (recC2_active.formRRow _)
    | exact memDecomposeRealization _
        (fpActive bounded_condFormula) (fpActive bounded_op1Head) (fpActive bounded_condResult) rfl
    | exact memHaltRealization _ (fpActive bounded_op1Head) rfl rfl rfl
    | exact memSingleChildRealization _ rfl
        (fpActive bounded_condResult) (fpActive bounded_condResult) rfl rfl
            (recC2_active.formRRow _)
    | exact memHaltRealization _ (fpActive bounded_condResult) rfl rfl rfl
    | exact memSingleChildRealization _ rfl
        (fpActive bounded_branchPair) (fpActive bounded_branchPair) rfl rfl (recP_active.formRRow _)
    | exact memDecomposeRealization _
        (fpActive bounded_branchPair) (fpActive bounded_branchC) (fpActive bounded_branchD) rfl
    | exact memSingleChildRealization _ rfl
        (fpActive bounded_branchC) (fpActive bounded_branchC) rfl rfl (recP_active.formRRow _)
    | exact memSingleChildRealization _ rfl
        (fpActive bounded_branchC) (fpActive bounded_branchC) rfl rfl (recC1_active.formRRow _)
    | exact memDecomposeRealization _
        (fpActive bounded_branchC) (fpActive bounded_op1Head) (fpActive bounded_result) rfl
    | exact memSingleChildRealization _ rfl
        (fpActive bounded_result) (fpActive bounded_result) rfl rfl (recC1_active.formRRow _)
    | exact memHaltRealization _ (fpActive bounded_result) rfl rfl rfl
    | exact memDecomposeRealization _
        (fpActive bounded_branchD) (fpActive bounded_op1Head) (fpActive bounded_op6Head) rfl
    | exact memHaltRealization _ (fpActive bounded_op6Head) rfl rfl rfl

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
    SemanticTrace.ExactExecutionSemanticData 97 7 (cfg seedZ alphaA) (exec seedZ alphaA) where
  language := language hfirst
  rowAccepted := fun i => ExactExecution.computeRowAt_accepted computeRowsAccepted i
  rows := rowData

/-! ## K. Served memory trace -/

def memoryTrace
    (hfirst :
      ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.counts = 0 ∧
        ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.indicator = 0) :
    ExactServedMemoryTrace 97 7 (cfg seedZ alphaA) (exec seedZ alphaA) (semanticData hfirst)
      (execA seedZ alphaA) where
  roots := rootTraces
  timestampPowersNodup := forestTimestampPowers_nodup
  forestIndexRange := by
    rw [forestTimestampPowers_eq]
    norm_num [IO.InRange, cfg, alphaA]
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

end Nock.NockVMROM.Thm54.TraceGen.Op6ConfigK3

#print axioms Nock.NockVMROM.Thm54.TraceGen.Op6ConfigK3.semanticPreimage
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op6ConfigK3.language
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op6ConfigK3.semanticData
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op6ConfigK3.memoryTrace
