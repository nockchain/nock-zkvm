/-
  Nock/NockVMROM/Thm54/TraceGen/ConsSemanticData.lean

  The per-row `ComputeRowSemanticData` for the branching
  program `*[0 [[1 5] [1 6]]] = [5 6]`, over `K = ZMod 97`, `Λ = 4`.

  This is the genuinely-new shape.  The `.cons` autocons root carries the
  SIX-entry comparison census `requiredComparisonRoles.cons =
  [formulaCons, recursiveSubject, recursiveFormula, recursiveSubject, recursiveFormula,
  producedResult]` with TWO recursive calls (`requiredCallRealizations.cons = 2`) and NO opcode-head
  atom (autocons has no numeric head), unlike the three-entry `.s1` census OP1 carried.  Every
  comparison is diagonal — the autocons decomposition/subformula projections reproduce their targets
  exactly — so faithfulness reduces to `pairFaithful_self`.  The two `OP_1` children reuse the OP1
  three-entry census, adapted to the ConsConfig child rows and `Λ = 4`.

  These `ComputeRowSemanticData` bundles carry NO row-acceptance obligation (`Vcomp` and the
  `language`/`rowAccepted` fields of `ExactExecutionSemanticData` are separate); they are exactly the
  `rows` half of the eventual `ExactExecutionSemanticData`.  The indexed `rowData` accessor packages
  them over the authoritative `exec.computeRowAt`, so the remaining `ExactExecutionSemanticData`
  assembly only has to supply `language` and `rowAccepted`.
-/
import Nock.NockVMROM.Thm54.TraceGen.ConsConfig
import Nock.NockVMROM.Thm54.SemanticTrace

namespace Nock.NockVMROM.Thm54.TraceGen.ConsConfig

open Nock Nock.Walk Nock.NockVM Nock.MemoryTable Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticTrace
open Nock.NockVMROM.Thm54.TraceGen.ConsSkeleton

/-! ## Diagonal pair-faithfulness -/

/-- A self-comparison is faithful at any seed: the separation obligation is vacuous. -/
theorem pairFaithful_self (n : Noun) (h : FieldEmbedding.BoundedBy 97 n) :
    OpcodeSemantics.PairFaithful seedZ 97 n n where
  separates := fun hne => absurd rfl hne
  left_bounded := h
  right_bounded := h

/-! ## Boundedness of the slice's committed nouns -/

theorem bounded_atom (k : ℕ) (hk : k < 97) : FieldEmbedding.BoundedBy 97 (.atom k) := by
  simp [FieldEmbedding.BoundedBy]; exact hk

theorem bounded_subjectNoun : FieldEmbedding.BoundedBy 97 subjectNoun := bounded_atom 0 (by norm_num)
theorem bounded_op1Head : FieldEmbedding.BoundedBy 97 op1Head := bounded_atom 1 (by norm_num)
theorem bounded_leftResult : FieldEmbedding.BoundedBy 97 leftResult := bounded_atom 5 (by norm_num)
theorem bounded_rightResult : FieldEmbedding.BoundedBy 97 rightResult := bounded_atom 6 (by norm_num)
theorem bounded_leftFormula : FieldEmbedding.BoundedBy 97 leftFormula :=
  ⟨bounded_op1Head, bounded_leftResult⟩
theorem bounded_rightFormula : FieldEmbedding.BoundedBy 97 rightFormula :=
  ⟨bounded_op1Head, bounded_rightResult⟩
theorem bounded_formulaNoun : FieldEmbedding.BoundedBy 97 formulaNoun :=
  ⟨bounded_leftFormula, bounded_rightFormula⟩
theorem bounded_resultNoun : FieldEmbedding.BoundedBy 97 resultNoun :=
  ⟨bounded_leftResult, bounded_rightResult⟩

noncomputable section

/-! ## The `.cons` root realization and its two recursive calls -/

/-- The always-live root of the `.cons` autocons row: subject `0`, formula `[[1 5] [1 6]]`,
result `[5 6]`, head `[1 5]`, tail `[1 6]`. -/
def consRoot :
    OpcodeSemantics.RootRealization compInputs consPub consDec where
  subject := subjectNoun
  formula := formulaNoun
  result := resultNoun
  head := leftFormula
  tail := rightFormula
  subject_realizes := rfl
  formula_realizes := rfl
  result_realizes := rfl
  head_realizes := rfl
  tail_realizes := rfl

/-- The left recursive call `*[0 [1 5]] = 5`. -/
def consCall1 : RealizedCall seedZ where
  subjectFP := consPub.sf1_s
  formulaFP := consPub.sf1_f
  resultFP := consPub.sf1_e
  realization :=
    { subject := subjectNoun
      formula := leftFormula
      result := leftResult
      subject_realizes := rfl
      formula_realizes := rfl
      result_realizes := rfl }

/-- The right recursive call `*[0 [1 6]] = 6`. -/
def consCall2 : RealizedCall seedZ where
  subjectFP := consPub.sf2_s
  formulaFP := consPub.sf2_f
  resultFP := consPub.sf2_e
  realization :=
    { subject := subjectNoun
      formula := rightFormula
      result := rightResult
      subject_realizes := rfl
      formula_realizes := rfl
      result_realizes := rfl }

/-- The autocons row's SIX-entry census (`requiredComparisonRoles.cons`): formula cons, then the
two recursive `(subject, formula)` pairs, then the produced pair.  Every entry is diagonal. -/
def consComparisons : List ComparisonUse :=
  [ { role := .formulaCons, left := formulaNoun, right := .cell leftFormula rightFormula },
    { role := .recursiveSubject, left := subjectNoun, right := subjectNoun },
    { role := .recursiveFormula, left := leftFormula, right := leftFormula },
    { role := .recursiveSubject, left := subjectNoun, right := subjectNoun },
    { role := .recursiveFormula, left := rightFormula, right := rightFormula },
    { role := .producedResult, left := resultNoun, right := .cell leftResult rightResult } ]

/-- The semantic-CORE row bundle for the `.cons` autocons row. -/
def consRowData : ComputeRowSemanticData 97 4 consRow where
  root := consRoot
  tails := []
  branchTails := []
  calls := [consCall1, consCall2]
  windows := []
  axisGates := []
  tails_count := rfl
  branchTails_count := rfl
  calls_count := rfl
  windows_count := rfl
  axisGates_count := rfl
  realizedNouns := [subjectNoun, formulaNoun, resultNoun]
  subject_mem := by simp [consRoot]
  formula_mem := by simp [consRoot]
  result_mem := by simp [consRoot]
  bounded := by
    intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h | h | h <;> subst h
    · exact bounded_subjectNoun
    · exact bounded_formulaNoun
    · exact bounded_resultNoun
  comparisons := consComparisons
  comparison_faithful := by
    intro c hc
    simp only [consComparisons, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with h | h | h | h | h | h <;> subst h
    · exact pairFaithful_self _ bounded_formulaNoun
    · exact pairFaithful_self _ bounded_subjectNoun
    · exact pairFaithful_self _ bounded_leftFormula
    · exact pairFaithful_self _ bounded_subjectNoun
    · exact pairFaithful_self _ bounded_rightFormula
    · exact pairFaithful_self _ bounded_resultNoun
  comparison_leaves := by
    intro c hc
    simp only [consComparisons, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with h | h | h | h | h | h <;> subst h <;> exact ⟨by decide, by decide⟩
  comparison_roles := rfl
  axisGate_listed := by intro gate hgate; simp at hgate
  axisGate_tail_mem := by intro gate hgate; simp at hgate
  needs :=
    { served := []
      served_count := rfl }

/-! ## The two `OP_1` child rows (three-entry `.s1` census, adapted to `Λ = 4`) -/

/-- The left child's root realization: `*[0 [1 5]] = 5`. -/
def op1LRoot :
    OpcodeSemantics.RootRealization compInputs op1LPub (op1DecOf leftResult) where
  subject := subjectNoun
  formula := leftFormula
  result := leftResult
  head := op1Head
  tail := leftResult
  subject_realizes := rfl
  formula_realizes := rfl
  result_realizes := rfl
  head_realizes := rfl
  tail_realizes := rfl

/-- The right child's root realization: `*[0 [1 6]] = 6`. -/
def op1RRoot :
    OpcodeSemantics.RootRealization compInputs op1RPub (op1DecOf rightResult) where
  subject := subjectNoun
  formula := rightFormula
  result := rightResult
  head := op1Head
  tail := rightResult
  subject_realizes := rfl
  formula_realizes := rfl
  result_realizes := rfl
  head_realizes := rfl
  tail_realizes := rfl

def op1LComparisons : List ComparisonUse :=
  [ { role := .opcodeHead, left := op1Head, right := .atom 1 },
    { role := .formulaCons, left := leftFormula, right := .cell op1Head leftResult },
    { role := .producedResult, left := leftResult, right := leftResult } ]

def op1RComparisons : List ComparisonUse :=
  [ { role := .opcodeHead, left := op1Head, right := .atom 1 },
    { role := .formulaCons, left := rightFormula, right := .cell op1Head rightResult },
    { role := .producedResult, left := rightResult, right := rightResult } ]

/-- The semantic-CORE row bundle for the left `OP_1` child. -/
def op1LRowData : ComputeRowSemanticData 97 4 op1LRow where
  root := op1LRoot
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
  realizedNouns := [subjectNoun, leftFormula, leftResult]
  subject_mem := by simp [op1LRoot]
  formula_mem := by simp [op1LRoot]
  result_mem := by simp [op1LRoot]
  bounded := by
    intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h | h | h <;> subst h
    · exact bounded_subjectNoun
    · exact bounded_leftFormula
    · exact bounded_leftResult
  comparisons := op1LComparisons
  comparison_faithful := by
    intro c hc
    simp only [op1LComparisons, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with h | h | h <;> subst h
    · exact pairFaithful_self _ bounded_op1Head
    · exact pairFaithful_self _ bounded_leftFormula
    · exact pairFaithful_self _ bounded_leftResult
  comparison_leaves := by
    intro c hc
    simp only [op1LComparisons, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with h | h | h <;> subst h <;> exact ⟨by decide, by decide⟩
  comparison_roles := rfl
  axisGate_listed := by intro gate hgate; simp at hgate
  axisGate_tail_mem := by intro gate hgate; simp at hgate
  needs :=
    { served := []
      served_count := rfl }

/-- The semantic-CORE row bundle for the right `OP_1` child. -/
def op1RRowData : ComputeRowSemanticData 97 4 op1RRow where
  root := op1RRoot
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
  realizedNouns := [subjectNoun, rightFormula, rightResult]
  subject_mem := by simp [op1RRoot]
  formula_mem := by simp [op1RRoot]
  result_mem := by simp [op1RRoot]
  bounded := by
    intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h | h | h <;> subst h
    · exact bounded_subjectNoun
    · exact bounded_rightFormula
    · exact bounded_rightResult
  comparisons := op1RComparisons
  comparison_faithful := by
    intro c hc
    simp only [op1RComparisons, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with h | h | h <;> subst h
    · exact pairFaithful_self _ bounded_op1Head
    · exact pairFaithful_self _ bounded_rightFormula
    · exact pairFaithful_self _ bounded_rightResult
  comparison_leaves := by
    intro c hc
    simp only [op1RComparisons, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with h | h | h <;> subst h <;> exact ⟨by decide, by decide⟩
  comparison_roles := rfl
  axisGate_listed := by intro gate hgate; simp at hgate
  axisGate_tail_mem := by intro gate hgate; simp at hgate
  needs :=
    { served := []
      served_count := rfl }

/-! ## Indexed row accessor over the authoritative `exec.computeRowAt` -/

theorem computeRows_eq :
    exec.computeRows = [consRow, op1LRow, op1RRow] := by
  norm_num [ExactExecution.computeRows, exec, computeTree, bfsForest, NTree.size, totalSize,
    NTree.label]

theorem computeRowAt_zero :
    exec.computeRowAt ⟨0, by norm_num [cfg]⟩ = consRow := by
  norm_num [ExactExecution.computeRowAt, computeRows_eq, cfg]

theorem computeRowAt_one :
    exec.computeRowAt ⟨1, by norm_num [cfg]⟩ = op1LRow := by
  norm_num [ExactExecution.computeRowAt, computeRows_eq, cfg]

theorem computeRowAt_two :
    exec.computeRowAt ⟨2, by norm_num [cfg]⟩ = op1RRow := by
  norm_num [ExactExecution.computeRowAt, computeRows_eq, cfg]

/-- Transport row data along a row identification. -/
def castRowData {row₁ row₂ : ComputeTable.State × ComputeTable.DTcomp F}
    (h : row₁ = row₂) (d : ComputeRowSemanticData 97 4 row₂) :
    ComputeRowSemanticData 97 4 row₁ :=
  h.symm ▸ d

/-- The per-row semantic data over the authoritative canonical accessor: the `rows` half of the
eventual `ExactExecutionSemanticData` for the branching slice. -/
def rowData : ∀ i : Fin cfg.compRows,
    ComputeRowSemanticData 97 4 (exec.computeRowAt i)
  | ⟨0, _⟩ => castRowData computeRowAt_zero consRowData
  | ⟨1, _⟩ => castRowData computeRowAt_one op1LRowData
  | ⟨2, _⟩ => castRowData computeRowAt_two op1RRowData
  | ⟨n + 3, h⟩ => by
      simp only [cfg] at h
      exact absurd h (by omega)

end

end Nock.NockVMROM.Thm54.TraceGen.ConsConfig

#print axioms Nock.NockVMROM.Thm54.TraceGen.ConsConfig.consRowData
#print axioms Nock.NockVMROM.Thm54.TraceGen.ConsConfig.op1LRowData
#print axioms Nock.NockVMROM.Thm54.TraceGen.ConsConfig.op1RRowData
#print axioms Nock.NockVMROM.Thm54.TraceGen.ConsConfig.rowData
