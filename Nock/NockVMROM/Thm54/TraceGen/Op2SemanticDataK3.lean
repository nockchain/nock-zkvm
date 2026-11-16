/-
  Nock/NockVMROM/Thm54/TraceGen/Op2SemanticDataK3.lean

  Stage 3 of the OP2 Layer-2 CORE, over `K3`: the per-row `ComputeRowSemanticData` for the
  four-row fan-out-3 eval program `*[0 [2 [1 [0 1]] [1 [1 5]]]] = 5`.

  The `.s2` parent is the genuinely-new row: ten comparison roles
  (`requiredComparisonRoles.s2`), one active tail (`tailCons`), three recursive calls
  (the third with computed subject `sf1`), and no served lookups / axis gates / size
  windows.  The three `.s1` children reuse the OP1 three-entry census, adapted to `Λ = 7`
  (the parent formula has seven atoms).  Every comparison is diagonal, so faithfulness
  is `pairFaithful_self`.

  These bundles are the `rows` half of the eventual `ExactExecutionSemanticData`; they
  carry no `Vcomp`/`language` obligation
-/
import Nock.NockVMROM.Thm54.TraceGen.Op2ConfigK3
import Nock.NockVMROM.Thm54.SemanticTrace
import Nock.NockVMROM.Thm54.ChainedLanguage

namespace Nock.NockVMROM.Thm54.TraceGen.Op2ConfigK3

open Nock Nock.Walk Nock.NockVM Nock.MemoryTable Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticTrace
open Nock.NockVMROM.Thm54.TraceGen

/-! ## Diagonal pair-faithfulness and noun bounds -/

theorem pairFaithful_self (n : Noun) (h : FieldEmbedding.BoundedBy 97 n) :
    OpcodeSemantics.PairFaithful seedZ 97 n n where
  separates := fun hne => absurd rfl hne
  left_bounded := h
  right_bounded := h

theorem bounded_atom (k : ℕ) (hk : k < 97) : FieldEmbedding.BoundedBy 97 (.atom k) := by
  simp [FieldEmbedding.BoundedBy]; exact hk

theorem bounded_subject : FieldEmbedding.BoundedBy 97 op2Subject :=
  bounded_atom 0 (by norm_num)
theorem bounded_op2Head : FieldEmbedding.BoundedBy 97 op2Head :=
  bounded_atom 2 (by norm_num)
theorem bounded_op1Head : FieldEmbedding.BoundedBy 97 op1Head :=
  bounded_atom 1 (by norm_num)
theorem bounded_result : FieldEmbedding.BoundedBy 97 op2Result :=
  bounded_atom 5 (by norm_num)
theorem bounded_sf1 : FieldEmbedding.BoundedBy 97 op2Sf1 :=
  ⟨bounded_atom 0 (by norm_num), bounded_atom 1 (by norm_num)⟩
theorem bounded_sf2 : FieldEmbedding.BoundedBy 97 op2Sf2 :=
  ⟨bounded_atom 1 (by norm_num), bounded_atom 5 (by norm_num)⟩
theorem bounded_child1 : FieldEmbedding.BoundedBy 97 op2ChildFormula1 :=
  ⟨bounded_op1Head, bounded_sf1⟩
theorem bounded_child2 : FieldEmbedding.BoundedBy 97 op2ChildFormula2 :=
  ⟨bounded_op1Head, bounded_sf2⟩
theorem bounded_tail : FieldEmbedding.BoundedBy 97 op2ParentTail :=
  ⟨bounded_child1, bounded_child2⟩
theorem bounded_formula : FieldEmbedding.BoundedBy 97 op2ParentFormula :=
  ⟨bounded_op2Head, bounded_tail⟩

noncomputable section

/-! ## The `.s2` parent row -/

def parentRoot :
    OpcodeSemantics.RootRealization (compInputs seedZ alphaA) (parentPub seedZ alphaA)
      (parentDec seedZ) where
  subject := op2Subject
  formula := op2ParentFormula
  result := op2Result
  head := op2Head
  tail := op2ParentTail
  subject_realizes := rfl
  formula_realizes := rfl
  result_realizes := rfl
  head_realizes := rfl
  tail_realizes := rfl

def parentTail :
    OpcodeSemantics.TailRealization (compInputs seedZ alphaA).z (parentDec seedZ) where
  head := op2ChildFormula1
  tail := op2ChildFormula2
  head_realizes := rfl
  tail_realizes := rfl

def parentCall1 :
    OpcodeSemantics.CallRealization (compInputs seedZ alphaA).z
      (parentPub seedZ alphaA).sf1_s (parentPub seedZ alphaA).sf1_f
      (parentPub seedZ alphaA).sf1_e where
  subject := op2Subject
  formula := op2ChildFormula1
  result := op2Sf1
  subject_realizes := rfl
  formula_realizes := rfl
  result_realizes := rfl

def parentCall2 :
    OpcodeSemantics.CallRealization (compInputs seedZ alphaA).z
      (parentPub seedZ alphaA).sf2_s (parentPub seedZ alphaA).sf2_f
      (parentPub seedZ alphaA).sf2_e where
  subject := op2Subject
  formula := op2ChildFormula2
  result := op2Sf2
  subject_realizes := rfl
  formula_realizes := rfl
  result_realizes := rfl

def parentCall3 :
    OpcodeSemantics.CallRealization (compInputs seedZ alphaA).z
      (parentPub seedZ alphaA).sf3_s (parentPub seedZ alphaA).sf3_f
      (parentPub seedZ alphaA).sf3_e where
  subject := op2Sf1
  formula := op2Sf2
  result := op2Result
  subject_realizes := rfl
  formula_realizes := rfl
  result_realizes := rfl

/-- The ten-entry OP₂ comparison census, in the exact `requiredComparisonRoles.s2` order. -/
def parentComparisons : List ComparisonUse :=
  [ { role := .opcodeHead, left := op2Head, right := .atom 2 },
    { role := .formulaCons, left := op2ParentFormula, right := .cell op2Head op2ParentTail },
    { role := .tailCons, left := op2ParentTail,
      right := .cell op2ChildFormula1 op2ChildFormula2 },
    { role := .recursiveSubject, left := op2Subject, right := op2Subject },
    { role := .recursiveFormula, left := op2ChildFormula1, right := op2ChildFormula1 },
    { role := .recursiveSubject, left := op2Subject, right := op2Subject },
    { role := .recursiveFormula, left := op2ChildFormula2, right := op2ChildFormula2 },
    { role := .recursiveSubject, left := op2Sf1, right := op2Sf1 },
    { role := .recursiveFormula, left := op2Sf2, right := op2Sf2 },
    { role := .producedResult, left := op2Result, right := op2Result } ]

/-- Row semantic data for the nonterminal `OP_2` parent over `K3`. -/
def parentRowData : ComputeRowSemanticData 97 7 (parentRow seedZ alphaA) where
  root := parentRoot
  tails := [parentTail]
  branchTails := []
  calls :=
    [ { subjectFP := (parentPub seedZ alphaA).sf1_s
        formulaFP := (parentPub seedZ alphaA).sf1_f
        resultFP := (parentPub seedZ alphaA).sf1_e
        realization := parentCall1 },
      { subjectFP := (parentPub seedZ alphaA).sf2_s
        formulaFP := (parentPub seedZ alphaA).sf2_f
        resultFP := (parentPub seedZ alphaA).sf2_e
        realization := parentCall2 },
      { subjectFP := (parentPub seedZ alphaA).sf3_s
        formulaFP := (parentPub seedZ alphaA).sf3_f
        resultFP := (parentPub seedZ alphaA).sf3_e
        realization := parentCall3 } ]
  windows := []
  axisGates := []
  tails_count := rfl
  branchTails_count := rfl
  calls_count := rfl
  windows_count := rfl
  axisGates_count := rfl
  realizedNouns := [op2Subject, op2ParentFormula, op2Result]
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
    rcases hc with h | h | h | h | h | h | h | h | h | h <;> subst h
    · exact pairFaithful_self _ bounded_op2Head
    · exact pairFaithful_self _ bounded_formula
    · exact pairFaithful_self _ bounded_tail
    · exact pairFaithful_self _ bounded_subject
    · exact pairFaithful_self _ bounded_child1
    · exact pairFaithful_self _ bounded_subject
    · exact pairFaithful_self _ bounded_child2
    · exact pairFaithful_self _ bounded_sf1
    · exact pairFaithful_self _ bounded_sf2
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

/-! ## The three `OP_1` child rows (`Λ = 7`) -/

def child1Root :
    OpcodeSemantics.RootRealization (compInputs seedZ alphaA) (child1Pub seedZ alphaA)
      (op1DecOf seedZ op2Sf1) where
  subject := op2Subject
  formula := op2ChildFormula1
  result := op2Sf1
  head := op1Head
  tail := op2Sf1
  subject_realizes := rfl
  formula_realizes := rfl
  result_realizes := rfl
  head_realizes := rfl
  tail_realizes := rfl

def child2Root :
    OpcodeSemantics.RootRealization (compInputs seedZ alphaA) (child2Pub seedZ alphaA)
      (op1DecOf seedZ op2Sf2) where
  subject := op2Subject
  formula := op2ChildFormula2
  result := op2Sf2
  head := op1Head
  tail := op2Sf2
  subject_realizes := rfl
  formula_realizes := rfl
  result_realizes := rfl
  head_realizes := rfl
  tail_realizes := rfl

def child3Root :
    OpcodeSemantics.RootRealization (compInputs seedZ alphaA) (child3Pub seedZ alphaA)
      (op1DecOf seedZ op2Result) where
  subject := op2Sf1
  formula := op2Sf2
  result := op2Result
  head := op1Head
  tail := op2Result
  subject_realizes := rfl
  formula_realizes := rfl
  result_realizes := rfl
  head_realizes := rfl
  tail_realizes := rfl

def child1Comparisons : List ComparisonUse :=
  [ { role := .opcodeHead, left := op1Head, right := .atom 1 },
    { role := .formulaCons, left := op2ChildFormula1, right := .cell op1Head op2Sf1 },
    { role := .producedResult, left := op2Sf1, right := op2Sf1 } ]

def child2Comparisons : List ComparisonUse :=
  [ { role := .opcodeHead, left := op1Head, right := .atom 1 },
    { role := .formulaCons, left := op2ChildFormula2, right := .cell op1Head op2Sf2 },
    { role := .producedResult, left := op2Sf2, right := op2Sf2 } ]

def child3Comparisons : List ComparisonUse :=
  [ { role := .opcodeHead, left := op1Head, right := .atom 1 },
    { role := .formulaCons, left := op2Sf2, right := .cell op1Head op2Result },
    { role := .producedResult, left := op2Result, right := op2Result } ]

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
  realizedNouns := [op2Subject, op2ChildFormula1, op2Sf1]
  subject_mem := by simp [child1Root]
  formula_mem := by simp [child1Root]
  result_mem := by simp [child1Root]
  bounded := by
    intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h | h | h <;> subst h
    · exact bounded_subject
    · exact bounded_child1
    · exact bounded_sf1
  comparisons := child1Comparisons
  comparison_faithful := by
    intro c hc
    simp only [child1Comparisons, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with h | h | h <;> subst h
    · exact pairFaithful_self _ bounded_op1Head
    · exact pairFaithful_self _ bounded_child1
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
  realizedNouns := [op2Subject, op2ChildFormula2, op2Sf2]
  subject_mem := by simp [child2Root]
  formula_mem := by simp [child2Root]
  result_mem := by simp [child2Root]
  bounded := by
    intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h | h | h <;> subst h
    · exact bounded_subject
    · exact bounded_child2
    · exact bounded_sf2
  comparisons := child2Comparisons
  comparison_faithful := by
    intro c hc
    simp only [child2Comparisons, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with h | h | h <;> subst h
    · exact pairFaithful_self _ bounded_op1Head
    · exact pairFaithful_self _ bounded_child2
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

def child3RowData : ComputeRowSemanticData 97 7 (child3Row seedZ alphaA) where
  root := child3Root
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
  realizedNouns := [op2Sf1, op2Sf2, op2Result]
  subject_mem := by simp [child3Root]
  formula_mem := by simp [child3Root]
  result_mem := by simp [child3Root]
  bounded := by
    intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h | h | h <;> subst h
    · exact bounded_sf1
    · exact bounded_sf2
    · exact bounded_result
  comparisons := child3Comparisons
  comparison_faithful := by
    intro c hc
    simp only [child3Comparisons, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with h | h | h <;> subst h
    · exact pairFaithful_self _ bounded_op1Head
    · exact pairFaithful_self _ bounded_sf2
    · exact pairFaithful_self _ bounded_result
  comparison_leaves := by
    intro c hc
    simp only [child3Comparisons, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with h | h | h <;> subst h <;> exact ⟨by decide, by decide⟩
  comparison_roles := rfl
  axisGate_listed := by intro gate hgate; simp at hgate
  axisGate_tail_mem := by intro gate hgate; simp at hgate
  needs :=
    { served := []
      served_count := rfl }

/-! ## Indexed row accessor over the authoritative `exec.computeRowAt` -/

theorem computeRows_eq :
    (exec seedZ alphaA).computeRows =
      [parentRow seedZ alphaA, child1Row seedZ alphaA, child2Row seedZ alphaA,
        child3Row seedZ alphaA] := by
  norm_num [ExactExecution.computeRows, exec, computeTree, bfsForest, NTree.size,
    totalSize, NTree.label]

theorem computeRowAt_zero :
    (exec seedZ alphaA).computeRowAt ⟨0, by norm_num [cfg]⟩ = parentRow seedZ alphaA := by
  norm_num [ExactExecution.computeRowAt, computeRows_eq, cfg]

theorem computeRowAt_one :
    (exec seedZ alphaA).computeRowAt ⟨1, by norm_num [cfg]⟩ = child1Row seedZ alphaA := by
  norm_num [ExactExecution.computeRowAt, computeRows_eq, cfg]

theorem computeRowAt_two :
    (exec seedZ alphaA).computeRowAt ⟨2, by norm_num [cfg]⟩ = child2Row seedZ alphaA := by
  norm_num [ExactExecution.computeRowAt, computeRows_eq, cfg]

theorem computeRowAt_three :
    (exec seedZ alphaA).computeRowAt ⟨3, by norm_num [cfg]⟩ = child3Row seedZ alphaA := by
  norm_num [ExactExecution.computeRowAt, computeRows_eq, cfg]

/-- Transport row data along a row identification. -/
def castRowData {row₁ row₂ : ComputeTable.State × ComputeTable.DTcomp K}
    (h : row₁ = row₂) (d : ComputeRowSemanticData 97 7 row₂) :
    ComputeRowSemanticData 97 7 row₁ :=
  h.symm ▸ d

/-- The per-row semantic data over the authoritative canonical accessor. -/
def rowData : ∀ i : Fin (cfg seedZ alphaA).compRows,
    ComputeRowSemanticData 97 7 ((exec seedZ alphaA).computeRowAt i)
  | ⟨0, _⟩ => castRowData computeRowAt_zero parentRowData
  | ⟨1, _⟩ => castRowData computeRowAt_one child1RowData
  | ⟨2, _⟩ => castRowData computeRowAt_two child2RowData
  | ⟨3, _⟩ => castRowData computeRowAt_three child3RowData
  | ⟨n + 4, h⟩ => by
      simp only [cfg] at h
      exact absurd h (by omega)

end

end Nock.NockVMROM.Thm54.TraceGen.Op2ConfigK3

#print axioms Nock.NockVMROM.Thm54.TraceGen.Op2ConfigK3.parentRowData
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op2ConfigK3.child1RowData
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op2ConfigK3.child3RowData
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op2ConfigK3.rowData
