/-
  Nock/NockVMROM/Thm54/TraceGen/Op1SemanticData.lean

  The row-level `ComputeRowSemanticData` for the single
  `OP_1` (`.s1`, quote) compute row of `*[0 [1 5]] = 5`, and the assembled
  `SemanticTrace.ExactExecutionSemanticData 97 3 Op1Config.cfg Op1Config.exec`.

  The `.s1` census is the three roles `[opcodeHead, formulaCons, producedResult]`: every entry is a self-comparison here
  (`head = atom 1`, `formula = [1 5]`, `result = tail = 5`), so faithfulness is the diagonal
  `pairFaithful_self` and the leaf bounds are `≤ Λ = 3`.  There are no tails, calls, windows, axis
  gates, or served lookups (`OP_1` has `requiredServedLookups.s1 = 0`).
-/
import Nock.NockVMROM.Thm54.TraceGen.Op1Language
import Nock.NockVMROM.Thm54.SemanticTrace

namespace Nock.NockVMROM.Thm54.TraceGen.Op1Config

open Nock Nock.Walk Nock.NockVM Nock.MemoryTable Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticTrace
open Nock.NockVMROM.Thm54.TraceGen.Op1Skeleton

/-! ## Diagonal pair-faithfulness -/

/-- A self-comparison is faithful at any seed: the separation obligation is vacuous. -/
theorem pairFaithful_self (n : Noun) (h : FieldEmbedding.BoundedBy 97 n) :
    OpcodeSemantics.PairFaithful seedZ 97 n n where
  separates := fun hne => absurd rfl hne
  left_bounded := h
  right_bounded := h

/-! ## The `OP_1` root realization and its 3-entry census -/

/-- The always-live root of the `OP_1` row: subject `0`, formula `[1 5]`, result/tail `5`, head `1`. -/
noncomputable def op1Root :
    OpcodeSemantics.RootRealization (computeInputs seedZ alphaA) (computePub seedZ alphaA)
      (computeDec seedZ) where
  subject := subjectNoun
  formula := formulaNoun
  result := resultNoun
  head := headNoun
  tail := resultNoun
  subject_realizes := rfl
  formula_realizes := rfl
  result_realizes := rfl
  head_realizes := rfl
  tail_realizes := rfl

/-- The quote row's census: opcode head `1`, formula cons `[1 5]`, produced result `5`
(`requiredComparisonRoles.s1`). -/
def op1Comparisons : List ComparisonUse :=
  [ { role := .opcodeHead, left := headNoun, right := .atom 1 },
    { role := .formulaCons, left := formulaNoun, right := .cell headNoun resultNoun },
    { role := .producedResult, left := resultNoun, right := resultNoun } ]

/-- The full semantic-CORE bundle for the single `OP_1` row. -/
noncomputable def op1RowData : ComputeRowSemanticData 97 3 (computeRow seedZ alphaA) where
  root := op1Root
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
  realizedNouns := [subjectNoun, formulaNoun, resultNoun]
  subject_mem := by simp [op1Root]
  formula_mem := by simp [op1Root]
  result_mem := by simp [op1Root]
  bounded := by
    intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h | h | h <;> subst h
    · exact bounded_subjectNoun
    · exact bounded_formulaNoun
    · exact bounded_resultNoun
  comparisons := op1Comparisons
  comparison_faithful := by
    intro c hc
    simp only [op1Comparisons, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with h | h | h <;> subst h
    · exact pairFaithful_self _ bounded_headNoun
    · exact pairFaithful_self _ bounded_formulaNoun
    · exact pairFaithful_self _ bounded_resultNoun
  comparison_leaves := by
    intro c hc
    simp only [op1Comparisons, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with h | h | h <;> subst h <;> exact ⟨by decide, by decide⟩
  comparison_roles := rfl
  axisGate_listed := by intro gate hgate; simp at hgate
  axisGate_tail_mem := by intro gate hgate; simp at hgate
  needs :=
    { served := []
      served_count := rfl }

/-! ## The single-row `ExactExecutionSemanticData` -/

theorem computeRowAt_zero :
    (exec seedZ alphaA).computeRowAt ⟨0, by norm_num [cfg]⟩ = computeRow seedZ alphaA := by
  norm_num [ExactExecution.computeRowAt, computeRows_eq, cfg]

/-- Transport row data along a row identification. -/
def castRowData {row₁ row₂ : ComputeTable.State × ComputeTable.DTcomp F}
    (h : row₁ = row₂) (d : ComputeRowSemanticData 97 3 row₂) :
    ComputeRowSemanticData 97 3 row₁ :=
  h.symm ▸ d

noncomputable def rowData : ∀ i : Fin (cfg seedZ alphaA).compRows,
    ComputeRowSemanticData 97 3 ((exec seedZ alphaA).computeRowAt i)
  | ⟨0, _⟩ => castRowData computeRowAt_zero op1RowData
  | ⟨n + 1, h⟩ => by
      simp only [cfg] at h
      exact absurd h (by omega)

/-- The exact per-row semantic data of the OP1 slice. -/
noncomputable def semanticData
    (hread : Vmem (memoryInputs seedZ) (readPub seedZ alphaA))
    (hdec : Vmem (memoryInputs seedZ) (decomposePub seedZ alphaA))
    (hver : Vmem (memoryInputs seedZ) (verifyPub seedZ alphaA)) :
    SemanticTrace.ExactExecutionSemanticData 97 3 (cfg seedZ alphaA) (exec seedZ alphaA) where
  language := language hread hdec hver
  rowAccepted := fun i => ExactExecution.computeRowAt_accepted computeRowsAccepted i
  rows := rowData

end Nock.NockVMROM.Thm54.TraceGen.Op1Config
