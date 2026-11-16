/-
  Nock/NockVMROM/Thm54/TraceGen/Op9MemoryTraceK3.lean

  Stage 3 of the OP9 Layer-2 CORE, over `K3`: the same-execution served-memory
  trace `ExactServedMemoryTrace 97 7 cfg exec semanticData` for

      `*[0 [9 [2 [1 [[1 7] [1 9]]]]]] = 7`

  The thirty-row TWO-root reconstruction services FIVE committed records
  through five nested `read_root`/`verify_child` pairs across two memory trees:
  Root A (formula decomposition, 19 rows) and Root B (arm-fetch descent, 11 rows).

  **OP9 is the first opcode with NON-VACUOUS `semanticCoverage`.**  The parent
  `.s9` row has `requiredServedLookups = 1` (the arm-fetch on the computed core),
  and the coverage proof explicitly provides `serviceArm ∈ rootB.services`.
  -- the paper
-/
import Nock.NockVMROM.Thm54.TraceGen.Op9ConfigK3
import Nock.NockVMROM.Thm54.ServedMemoryTrace
import Nock.NockVMROM.Thm54.AxisSoundness
import Nock.NockVMROM.Thm54.SemanticTrace
import Nock.NockVMROM.Thm54.ChainedLanguage
import Nock.NockVMROM.Thm54.RecognizerCompleteness

namespace Nock.NockVMROM.Thm54.TraceGen.Op9ConfigK3

open Nock Nock.Walk Nock.NockVM
open Nock.ComputeTable Nock.MemoryTable
open Nock.AxisBatching Nock.AxisBatching.MTree
open Nock.AxisBridge
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ServedMemoryTrace
open Nock.NockVMROM.Thm54.SemanticTrace
open Nock.NockVMROM.Thm54.TraceGen

noncomputable section

theorem pairFaithful_self (n : Noun) (h : FieldEmbedding.BoundedBy 97 n) :
    OpcodeSemantics.PairFaithful seedZ 97 n n where
  separates := fun hne => absurd rfl hne
  left_bounded := h
  right_bounded := h

/-! ## A. BFS row equalities -/

theorem computeRows_eq :
    (exec seedZ alphaA).computeRows =
      [parentRow seedZ alphaA, child1Row seedZ alphaA, child2Row seedZ alphaA] := by
  simp [ExactExecution.computeRows, exec, computeTree, bfsForest]

theorem computeRowAt_zero :
    (exec seedZ alphaA).computeRowAt ⟨0, by norm_num [cfg]⟩ = parentRow seedZ alphaA := by
  norm_num [ExactExecution.computeRowAt, computeRows_eq, cfg]

theorem computeRowAt_one :
    (exec seedZ alphaA).computeRowAt ⟨1, by norm_num [cfg]⟩ = child1Row seedZ alphaA := by
  norm_num [ExactExecution.computeRowAt, computeRows_eq, cfg]

theorem computeRowAt_two :
    (exec seedZ alphaA).computeRowAt ⟨2, by norm_num [cfg]⟩ = child2Row seedZ alphaA := by
  norm_num [ExactExecution.computeRowAt, computeRows_eq, cfg]

/-! ## B. Per-row semantic data (parent `.s9` + two `.s1` children) -/

def parentRoot :
    OpcodeSemantics.RootRealization (compInputs seedZ alphaA) (parentPub seedZ alphaA)
      (parentDec seedZ) where
  subject := op9Subject
  formula := op9ParentFormula
  result := op9Result
  head := op9Head
  tail := op9ParentTail
  subject_realizes := rfl
  formula_realizes := rfl
  result_realizes := rfl
  head_realizes := rfl
  tail_realizes := rfl

def parentTailR :
    OpcodeSemantics.TailRealization (compInputs seedZ alphaA).z (parentDec seedZ) where
  head := op9AxisAtom
  tail := op9CoreFormula
  head_realizes := rfl
  tail_realizes := rfl

def parentCall1 :
    OpcodeSemantics.CallRealization (compInputs seedZ alphaA).z
      (parentPub seedZ alphaA).sf1_s (parentPub seedZ alphaA).sf1_f
      (parentPub seedZ alphaA).sf1_e where
  subject := op9Subject
  formula := op9CoreFormula
  result := op9CoreNoun
  subject_realizes := rfl
  formula_realizes := rfl
  result_realizes := rfl

def parentCall2 :
    OpcodeSemantics.CallRealization (compInputs seedZ alphaA).z
      (parentPub seedZ alphaA).sf2_s (parentPub seedZ alphaA).sf2_f
      (parentPub seedZ alphaA).sf2_e where
  subject := op9CoreNoun
  formula := op9Arm
  result := op9Result
  subject_realizes := rfl
  formula_realizes := rfl
  result_realizes := rfl

def parentAxisGate : Σ tail : OpcodeSemantics.TailRealization (compInputs seedZ alphaA).z
    (parentDec seedZ),
    AxisAtomComparisonCertificate (compInputs seedZ alphaA).z 97 (parentDec seedZ) tail where
  fst := parentTailR
  snd :=
    { axis := 2
      faithful := pairFaithful_self (.atom 2) (by simp [FieldEmbedding.BoundedBy]) }

def parentServedLookup : ServedNounLookup (compInputs seedZ alphaA).z where
  record := recArm seedZ alphaA
  root := op9CoreNoun
  axis := 2
  child := op9Arm
  realization :=
    { root_realizes := rfl
      child_realizes := rfl
      axis_realizes := by norm_num [recArm] }
  served := Nock.NockVMROM.Thm54.RecognizerCompleteness.servedLookup_of_slot op9_slot

def parentComparisons : List ComparisonUse :=
  [ { role := .opcodeHead, left := .atom 9, right := .atom 9 },
    { role := .formulaCons, left := op9ParentFormula,
      right := .cell (.atom 9) op9ParentTail },
    { role := .tailCons, left := op9ParentTail,
      right := .cell op9AxisAtom op9CoreFormula },
    { role := .axisAtom, left := op9AxisAtom, right := op9AxisAtom },
    { role := .recursiveSubject, left := op9Subject, right := op9Subject },
    { role := .recursiveFormula, left := op9CoreFormula, right := op9CoreFormula },
    { role := .recursiveSubject, left := op9CoreNoun, right := op9CoreNoun },
    { role := .producedResult, left := op9Result, right := op9Result } ]

def parentRowData : ComputeRowSemanticData 97 7 (parentRow seedZ alphaA) where
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
  axisGates := [parentAxisGate]
  tails_count := rfl
  branchTails_count := rfl
  calls_count := rfl
  windows_count := rfl
  axisGates_count := rfl
  realizedNouns := [op9Subject, op9ParentFormula, op9Result]
  subject_mem := by simp [parentRoot]
  formula_mem := by simp [parentRoot]
  result_mem := by simp [parentRoot]
  bounded := by
    intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h | h | h <;> subst h <;>
      simp [op9Subject, op9ParentFormula, op9Result, op9ParentTail, op9AxisAtom,
        op9CoreFormula, op9Head, op9CoreNoun, op9Arm, FieldEmbedding.BoundedBy]
  comparisons := parentComparisons
  comparison_faithful := by
    intro c hc
    simp only [parentComparisons, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with h | h | h | h | h | h | h | h <;> subst h <;>
      exact pairFaithful_self _
        (by simp [op9Subject, op9ParentFormula, op9ParentTail, op9AxisAtom, op9CoreFormula,
            op9CoreNoun, op9Arm, op9Result, FieldEmbedding.BoundedBy])
  comparison_leaves := by
    intro c hc
    simp only [parentComparisons, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with h | h | h | h | h | h | h | h <;> subst h <;>
      simp [ComparisonUse.LeavesBounded, op9Subject, op9ParentFormula, op9ParentTail,
        op9AxisAtom, op9CoreFormula, op9CoreNoun, op9Arm, op9Result, Noun.leaves]
  comparison_roles := by
    simp [parentComparisons, requiredComparisonRoles, parentRow, ComparisonUse.role]
  axisGate_listed := by
    intro gate hgate
    replace hgate := List.mem_singleton.1 hgate
    subst hgate
    simp [parentComparisons, parentAxisGate, parentTailR, op9AxisAtom]
  axisGate_tail_mem := by
    intro gate hgate
    replace hgate := List.mem_singleton.1 hgate
    subst hgate
    simp [parentAxisGate]
    exact List.mem_singleton_self _
  needs :=
    { served := [parentServedLookup]
      served_count := rfl }

/-! ### The two `OP_1` child rows (`.s1` — constant, no served lookups) -/

def child1Root :
    OpcodeSemantics.RootRealization (compInputs seedZ alphaA) (child1Pub seedZ alphaA)
      (op1DecOf seedZ op9CoreNoun) where
  subject := op9Subject
  formula := op9CoreFormula
  result := op9CoreNoun
  head := op1Head
  tail := op9CoreNoun
  subject_realizes := rfl
  formula_realizes := rfl
  result_realizes := rfl
  head_realizes := rfl
  tail_realizes := rfl

def child1Comparisons : List ComparisonUse :=
  [ { role := .opcodeHead, left := .atom 1, right := .atom 1 },
    { role := .formulaCons, left := op9CoreFormula, right := .cell (.atom 1) op9CoreNoun },
    { role := .producedResult, left := op9CoreNoun, right := op9CoreNoun } ]

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
  realizedNouns := [op9Subject, op9CoreFormula, op9CoreNoun]
  subject_mem := by simp [child1Root]
  formula_mem := by simp [child1Root]
  result_mem := by simp [child1Root]
  bounded := by
    intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h | h | h <;> subst h <;>
      simp [op9Subject, op9CoreFormula, op9CoreNoun, FieldEmbedding.BoundedBy]
  comparisons := child1Comparisons
  comparison_faithful := by
    intro c hc
    simp only [child1Comparisons, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with h | h | h <;> subst h <;>
      exact pairFaithful_self _
        (by simp [op9Subject, op9CoreFormula, op9CoreNoun, FieldEmbedding.BoundedBy])
  comparison_leaves := by
    intro c hc
    simp only [child1Comparisons, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with h | h | h <;> subst h <;>
      simp [ComparisonUse.LeavesBounded, op9Subject, op9CoreFormula, op9CoreNoun, Noun.leaves]
  comparison_roles := by
    simp [child1Comparisons, requiredComparisonRoles, child1Row, ComparisonUse.role]
  axisGate_listed := by intro gate hgate; simp at hgate
  axisGate_tail_mem := by intro gate hgate; simp at hgate
  needs :=
    { served := []
      served_count := rfl }

def child2Root :
    OpcodeSemantics.RootRealization (compInputs seedZ alphaA) (child2Pub seedZ alphaA)
      (op1DecOf seedZ op9Result) where
  subject := op9CoreNoun
  formula := op9Arm
  result := op9Result
  head := op1Head
  tail := op9Result
  subject_realizes := rfl
  formula_realizes := rfl
  result_realizes := rfl
  head_realizes := rfl
  tail_realizes := rfl

def child2Comparisons : List ComparisonUse :=
  [ { role := .opcodeHead, left := .atom 1, right := .atom 1 },
    { role := .formulaCons, left := op9Arm, right := .cell (.atom 1) op9Result },
    { role := .producedResult, left := op9Result, right := op9Result } ]

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
  realizedNouns := [op9CoreNoun, op9Arm, op9Result]
  subject_mem := by simp [child2Root]
  formula_mem := by simp [child2Root]
  result_mem := by simp [child2Root]
  bounded := by
    intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h | h | h <;> subst h <;>
      simp [op9CoreNoun, op9Arm, op9Result, FieldEmbedding.BoundedBy]
  comparisons := child2Comparisons
  comparison_faithful := by
    intro c hc
    simp only [child2Comparisons, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with h | h | h <;> subst h <;>
      exact pairFaithful_self _
        (by simp [op9CoreNoun, op9Arm, op9Result, FieldEmbedding.BoundedBy])
  comparison_leaves := by
    intro c hc
    simp only [child2Comparisons, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with h | h | h <;> subst h <;>
      simp [ComparisonUse.LeavesBounded, op9CoreNoun, op9Arm, op9Result, Noun.leaves]
  comparison_roles := by
    simp [child2Comparisons, requiredComparisonRoles, child2Row, ComparisonUse.role]
  axisGate_listed := by intro gate hgate; simp at hgate
  axisGate_tail_mem := by intro gate hgate; simp at hgate
  needs :=
    { served := []
      served_count := rfl }

/-! ## C. Row-data accessor + cast -/

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

/-! ## D. Timestamp exponents and distinctness -/

theorem ts_recF : (recF seedZ alphaA).ts = alphaA := rfl
theorem ts_recT : (recT seedZ alphaA).ts = alphaA ^ 2 := rfl
theorem ts_recArm : (recArm seedZ alphaA).ts = alphaA ^ 3 := rfl
theorem ts_recCoreF : (recCoreF seedZ alphaA).ts = alphaA ^ 4 := rfl
theorem ts_recArmF : (recArmF seedZ alphaA).ts = alphaA ^ 5 := rfl

theorem alpha_pow_ne_12 : alphaA ≠ alphaA ^ 2 := by decide
theorem alpha_pow_ne_13 : alphaA ≠ alphaA ^ 3 := by decide
theorem alpha_pow_ne_14 : alphaA ≠ alphaA ^ 4 := by decide
theorem alpha_pow_ne_15 : alphaA ≠ alphaA ^ 5 := by decide
theorem alpha_pow_ne_23 : alphaA ^ 2 ≠ alphaA ^ 3 := by decide
theorem alpha_pow_ne_24 : alphaA ^ 2 ≠ alphaA ^ 4 := by decide
theorem alpha_pow_ne_25 : alphaA ^ 2 ≠ alphaA ^ 5 := by decide
theorem alpha_pow_ne_34 : alphaA ^ 3 ≠ alphaA ^ 4 := by decide
theorem alpha_pow_ne_35 : alphaA ^ 3 ≠ alphaA ^ 5 := by decide
theorem alpha_pow_ne_45 : alphaA ^ 4 ≠ alphaA ^ 5 := by decide

theorem ts_closed_recF :
    TimestampClosedAt (cfg seedZ alphaA).challenges.α (recF seedZ alphaA).ts :=
  ⟨1, by rw [ts_recF]; simp [cfg, alphaA]⟩
theorem ts_closed_recT :
    TimestampClosedAt (cfg seedZ alphaA).challenges.α (recT seedZ alphaA).ts :=
  ⟨2, by rw [ts_recT]; rfl⟩
theorem ts_closed_recArm :
    TimestampClosedAt (cfg seedZ alphaA).challenges.α (recArm seedZ alphaA).ts :=
  ⟨3, by rw [ts_recArm]; rfl⟩
theorem ts_closed_recCoreF :
    TimestampClosedAt (cfg seedZ alphaA).challenges.α (recCoreF seedZ alphaA).ts :=
  ⟨4, by rw [ts_recCoreF]; rfl⟩
theorem ts_closed_recArmF :
    TimestampClosedAt (cfg seedZ alphaA).challenges.α (recArmF seedZ alphaA).ts :=
  ⟨5, by rw [ts_recArmF]; rfl⟩

def expF : ℕ := timestampExp (cfg seedZ alphaA).challenges.α (recF seedZ alphaA).ts
def expT : ℕ := timestampExp (cfg seedZ alphaA).challenges.α (recT seedZ alphaA).ts
def expArm : ℕ := timestampExp (cfg seedZ alphaA).challenges.α (recArm seedZ alphaA).ts
def expCoreF : ℕ := timestampExp (cfg seedZ alphaA).challenges.α (recCoreF seedZ alphaA).ts
def expArmF : ℕ := timestampExp (cfg seedZ alphaA).challenges.α (recArmF seedZ alphaA).ts

theorem ts_eq_recF : (recF seedZ alphaA).ts = (cfg seedZ alphaA).challenges.α ^ expF :=
  timestampExp_spec ts_closed_recF
theorem ts_eq_recT : (recT seedZ alphaA).ts = (cfg seedZ alphaA).challenges.α ^ expT :=
  timestampExp_spec ts_closed_recT
theorem ts_eq_recArm : (recArm seedZ alphaA).ts = (cfg seedZ alphaA).challenges.α ^ expArm :=
  timestampExp_spec ts_closed_recArm
theorem ts_eq_recCoreF :
    (recCoreF seedZ alphaA).ts = (cfg seedZ alphaA).challenges.α ^ expCoreF :=
  timestampExp_spec ts_closed_recCoreF
theorem ts_eq_recArmF :
    (recArmF seedZ alphaA).ts = (cfg seedZ alphaA).challenges.α ^ expArmF :=
  timestampExp_spec ts_closed_recArmF

theorem expF_ne_expT : expF ≠ expT := by
  intro h
  have hF := ts_recF.symm.trans ts_eq_recF
  have hT := ts_recT.symm.trans ts_eq_recT
  rw [h] at hF; exact alpha_pow_ne_12 (hF.trans hT.symm)
theorem expF_ne_expArm : expF ≠ expArm := by
  intro h
  have hF := ts_recF.symm.trans ts_eq_recF
  have hA := ts_recArm.symm.trans ts_eq_recArm
  rw [h] at hF; exact alpha_pow_ne_13 (hF.trans hA.symm)
theorem expF_ne_expCoreF : expF ≠ expCoreF := by
  intro h
  have hF := ts_recF.symm.trans ts_eq_recF
  have hC := ts_recCoreF.symm.trans ts_eq_recCoreF
  rw [h] at hF; exact alpha_pow_ne_14 (hF.trans hC.symm)
theorem expF_ne_expArmF : expF ≠ expArmF := by
  intro h
  have hF := ts_recF.symm.trans ts_eq_recF
  have hA := ts_recArmF.symm.trans ts_eq_recArmF
  rw [h] at hF; exact alpha_pow_ne_15 (hF.trans hA.symm)
theorem expT_ne_expArm : expT ≠ expArm := by
  intro h
  have hT := ts_recT.symm.trans ts_eq_recT
  have hA := ts_recArm.symm.trans ts_eq_recArm
  rw [h] at hT; exact alpha_pow_ne_23 (hT.trans hA.symm)
theorem expT_ne_expCoreF : expT ≠ expCoreF := by
  intro h
  have hT := ts_recT.symm.trans ts_eq_recT
  have hC := ts_recCoreF.symm.trans ts_eq_recCoreF
  rw [h] at hT; exact alpha_pow_ne_24 (hT.trans hC.symm)
theorem expT_ne_expArmF : expT ≠ expArmF := by
  intro h
  have hT := ts_recT.symm.trans ts_eq_recT
  have hA := ts_recArmF.symm.trans ts_eq_recArmF
  rw [h] at hT; exact alpha_pow_ne_25 (hT.trans hA.symm)
theorem expArm_ne_expCoreF : expArm ≠ expCoreF := by
  intro h
  have hA := ts_recArm.symm.trans ts_eq_recArm
  have hC := ts_recCoreF.symm.trans ts_eq_recCoreF
  rw [h] at hA; exact alpha_pow_ne_34 (hA.trans hC.symm)
theorem expArm_ne_expArmF : expArm ≠ expArmF := by
  intro h
  have hA := ts_recArm.symm.trans ts_eq_recArm
  have hB := ts_recArmF.symm.trans ts_eq_recArmF
  rw [h] at hA; exact alpha_pow_ne_35 (hA.trans hB.symm)
theorem expCoreF_ne_expArmF : expCoreF ≠ expArmF := by
  intro h
  have hC := ts_recCoreF.symm.trans ts_eq_recCoreF
  have hA := ts_recArmF.symm.trans ts_eq_recArmF
  rw [h] at hC; exact alpha_pow_ne_45 (hC.trans hA.symm)

theorem expT_ne_expF : expT ≠ expF := fun h => expF_ne_expT h.symm
theorem expArm_ne_expF : expArm ≠ expF := fun h => expF_ne_expArm h.symm
theorem expCoreF_ne_expF : expCoreF ≠ expF := fun h => expF_ne_expCoreF h.symm
theorem expArmF_ne_expF : expArmF ≠ expF := fun h => expF_ne_expArmF h.symm
theorem expArm_ne_expT : expArm ≠ expT := fun h => expT_ne_expArm h.symm
theorem expCoreF_ne_expT : expCoreF ≠ expT := fun h => expT_ne_expCoreF h.symm
theorem expArmF_ne_expT : expArmF ≠ expT := fun h => expT_ne_expArmF h.symm
theorem expCoreF_ne_expArm : expCoreF ≠ expArm := fun h => expArm_ne_expCoreF h.symm
theorem expArmF_ne_expArm : expArmF ≠ expArm := fun h => expArm_ne_expArmF h.symm
theorem expArmF_ne_expCoreF : expArmF ≠ expCoreF := fun h => expCoreF_ne_expArmF h.symm

/-! ## E. The five compute-side services

Root A serves: F (formula@3), T (tail@2), CoreF (coreFormula@3)
Root B serves: Arm (core@2), ArmF (arm@3) -/

theorem rawRequests_eq :
    (exec seedZ alphaA).rawRequests =
      [recF seedZ alphaA, recT seedZ alphaA, recArm seedZ alphaA,
        recCoreF seedZ alphaA, recArmF seedZ alphaA] := by
  rw [ExactExecution.rawRequests_eq_computeRows, computeRows_eq]
  simp [NockVM.activeRequestRecords, parentRow, child1Row, child2Row,
    parentPub, child1Pub, child2Pub, op1PubOf]

def serviceF : Service (cfg seedZ alphaA) (execA seedZ alphaA) where
  exponent := expF
  record := recF seedZ alphaA
  root := op9ParentFormula
  child := op9ParentTail
  axis := 3
  request_mem := by
    rw [show (execA seedZ alphaA).rawRequests = (exec seedZ alphaA).rawRequests from rfl,
      rawRequests_eq]; simp
  timestamp := ts_eq_recF
  realization :=
    { root_realizes := rfl
      child_realizes := rfl
      axis_realizes := by norm_num [recF] }
  served := by simp [op9ParentFormula, op9ParentTail, Noun.slot]

def serviceT : Service (cfg seedZ alphaA) (execA seedZ alphaA) where
  exponent := expT
  record := recT seedZ alphaA
  root := op9ParentTail
  child := op9AxisAtom
  axis := 2
  request_mem := by
    rw [show (execA seedZ alphaA).rawRequests = (exec seedZ alphaA).rawRequests from rfl,
      rawRequests_eq]; simp
  timestamp := ts_eq_recT
  realization :=
    { root_realizes := rfl
      child_realizes := rfl
      axis_realizes := by norm_num [recT] }
  served := by simp [op9ParentTail, op9AxisAtom, Noun.slot]

def serviceArm : Service (cfg seedZ alphaA) (execA seedZ alphaA) where
  exponent := expArm
  record := recArm seedZ alphaA
  root := op9CoreNoun
  child := op9Arm
  axis := 2
  request_mem := by
    rw [show (execA seedZ alphaA).rawRequests = (exec seedZ alphaA).rawRequests from rfl,
      rawRequests_eq]; simp
  timestamp := ts_eq_recArm
  realization :=
    { root_realizes := rfl
      child_realizes := rfl
      axis_realizes := by norm_num [recArm] }
  served := by simp [op9CoreNoun, op9Arm, Noun.slot]

def serviceCoreF : Service (cfg seedZ alphaA) (execA seedZ alphaA) where
  exponent := expCoreF
  record := recCoreF seedZ alphaA
  root := op9CoreFormula
  child := op9CoreNoun
  axis := 3
  request_mem := by
    rw [show (execA seedZ alphaA).rawRequests = (exec seedZ alphaA).rawRequests from rfl,
      rawRequests_eq]; simp
  timestamp := ts_eq_recCoreF
  realization :=
    { root_realizes := rfl
      child_realizes := rfl
      axis_realizes := by norm_num [recCoreF] }
  served := by simp [op9CoreFormula, op9CoreNoun, Noun.slot]

def serviceArmF : Service (cfg seedZ alphaA) (execA seedZ alphaA) where
  exponent := expArmF
  record := recArmF seedZ alphaA
  root := op9Arm
  child := op9Result
  axis := 3
  request_mem := by
    rw [show (execA seedZ alphaA).rawRequests = (exec seedZ alphaA).rawRequests from rfl,
      rawRequests_eq]; simp
  timestamp := ts_eq_recArmF
  realization :=
    { root_realizes := rfl
      child_realizes := rfl
      axis_realizes := by norm_num [recArmF] }
  served := by simp [op9Arm, op9Result, Noun.slot]

/-! ## F. Root trace construction -/

theorem memoryTreeAt_zero :
    (execA seedZ alphaA).memoryTreeAt ⟨0, by norm_num [cfg]⟩ = rootTreeAView seedZ alphaA := rfl
theorem memoryTreeAt_one :
    (execA seedZ alphaA).memoryTreeAt ⟨1, by norm_num [cfg]⟩ = rootTreeBView seedZ alphaA := rfl

theorem rootResponseRecordsA_eq :
    rootResponseRecords (execA seedZ alphaA) ⟨0, by norm_num [cfg]⟩ =
      [recF seedZ alphaA, recT seedZ alphaA, recCoreF seedZ alphaA] := by
  simp [rootResponseRecords, memoryTreeAt_zero, rootTreeAView,
    mOne, mTwo, mLeaf, lblOf, bfsForest, MemoryTable.responseRecords,
    pReadFA, pDecPF, pHalt9, pVerifyFA, pReadTA, pDecPT, pVerifyTA, pHaltA2,
    pReadCoreFA, pDecCF, pHaltH1a, pVerifyCoreFA, pDecCN, pDecArmA, pHaltH1b,
    pHaltA7, pDecCTA, pHaltH1c, pHaltA9,
    readPub, readPubA, decPub, haltPub, verifyPub, verifyPubA]

theorem rootResponseRecordsB_eq :
    rootResponseRecords (execA seedZ alphaA) ⟨1, by norm_num [cfg]⟩ =
      [recArm seedZ alphaA, recArmF seedZ alphaA] := by
  simp [rootResponseRecords, memoryTreeAt_one, rootTreeBView,
    mOne, mTwo, mLeaf, lblOf, bfsForest, MemoryTable.responseRecords,
    pReadArmA, pDecCN_B, pVerifyArmA, pReadArmFA, pDecArmB, pHaltH1_B1,
    pVerifyArmFA, pHaltA7_B, pDecCT_B, pHaltH1_B2, pHaltA9_B,
    readPub, readPubA, decPub, haltPub, verifyPub, verifyPubA]

theorem axisPath_three : axisPath 3 = [true] := by
  rw [axisPath_of_two_le (by norm_num)]
  norm_num [axisPath_of_lt_two]

theorem axisPath_two : axisPath 2 = [false] := by
  rw [axisPath_of_two_le (by norm_num)]
  norm_num [axisPath_of_lt_two]

set_option maxRecDepth 800000 in
theorem op9AxisTreeA_eq :
    exactAxisTree (cfg seedZ alphaA) (execA seedZ alphaA) ⟨0, by norm_num [cfg]⟩ =
      MTree.read expF
        (MTree.decompose MTree.halt
          (MTree.verify expF 3
            (MTree.read expT
              (MTree.decompose
                (MTree.verify expT 2 MTree.halt)
                (MTree.read expCoreF
                  (MTree.decompose MTree.halt
                    (MTree.verify expCoreF 3
                      (MTree.decompose
                        (MTree.decompose MTree.halt MTree.halt)
                        (MTree.decompose MTree.halt MTree.halt))))))))) := by
  rw [exactAxisTree, memoryTreeAt_zero]
  simp [rootTreeAView, mOne, mTwo, mLeaf, lblOf,
    Nock.AxisBridge.ofNTree, Nock.AxisBridge.MemWalk.toMTree, timestampExpAt,
    expF, expT, expCoreF,
    pReadFA, pDecPF, pHalt9, pVerifyFA, pReadTA, pDecPT, pVerifyTA, pHaltA2,
    pReadCoreFA, pDecCF, pHaltH1a, pVerifyCoreFA, pDecCN, pDecArmA, pHaltH1b,
    pHaltA7, pDecCTA, pHaltH1c, pHaltA9,
    readPub, readPubA, decPub, haltPub, verifyPub, verifyPubA,
    recF, recT, recCoreF]

set_option maxRecDepth 800000 in
theorem op9AxisTreeB_eq :
    exactAxisTree (cfg seedZ alphaA) (execA seedZ alphaA) ⟨1, by norm_num [cfg]⟩ =
      MTree.read expArm
        (MTree.decompose
          (MTree.verify expArm 2
            (MTree.read expArmF
              (MTree.decompose MTree.halt
                (MTree.verify expArmF 3 MTree.halt))))
          (MTree.decompose MTree.halt MTree.halt)) := by
  rw [exactAxisTree, memoryTreeAt_one]
  simp [rootTreeBView, mOne, mTwo, mLeaf, lblOf,
    Nock.AxisBridge.ofNTree, Nock.AxisBridge.MemWalk.toMTree, timestampExpAt,
    expArm, expArmF,
    pReadArmA, pDecCN_B, pVerifyArmA, pReadArmFA, pDecArmB, pHaltH1_B1,
    pVerifyArmFA, pHaltA7_B, pDecCT_B, pHaltH1_B2, pHaltA9_B,
    readPub, readPubA, decPub, haltPub, verifyPub, verifyPubA,
    recArm, recArmF]

/-! ### Root A trace: formula decomposition (serves F, T, CoreF) -/

def rootTraceA : RootTrace (cfg seedZ alphaA) (execA seedZ alphaA) ⟨0, by norm_num [cfg]⟩ where
  subject := op9ParentFormula
  services := [serviceF, serviceT, serviceCoreF]
  recordPartition := by
    rw [rootResponseRecordsA_eq]
    simp [serviceF, serviceT, serviceCoreF]
  readPartition := by
    rw [op9AxisTreeA_eq]
    simp only [readExps, serviceF, serviceT, serviceCoreF, List.map_cons, List.map_nil,
      List.nil_append, List.append_nil, List.singleton_append]
    exact List.Perm.refl _
  verifyPartition := by
    rw [op9AxisTreeA_eq]
    simp only [verifyExps, serviceF, serviceT, serviceCoreF, List.map_cons, List.map_nil,
      List.nil_append, List.append_nil, List.singleton_append, List.cons_append]
    exact List.Perm.refl _
  traversal := by
    rw [op9AxisTreeA_eq]
    refine ServiceWalk.read serviceF (by simp) rfl rfl ?_ ?_
    · rw [show serviceF.axis = 3 from rfl, axisPath_three]
      refine VerifyRoute.right (by simp [readCount]) (by simp [verifyCount]) ?_
      exact VerifyRoute.here rfl rfl
        (by simp [readCount, expT_ne_expF, expCoreF_ne_expF])
        (by simp [verifyCount, expT_ne_expF, expCoreF_ne_expF])
    · refine ServiceWalk.decompose ServiceWalk.halt ?_
      refine ServiceWalk.verify ?_
      refine ServiceWalk.read serviceT (by simp) rfl rfl ?_ ?_
      · rw [show serviceT.axis = 2 from rfl, axisPath_two]
        refine VerifyRoute.left ?_
          (by simp [readCount, expCoreF_ne_expT])
          (by simp [verifyCount, expCoreF_ne_expT])
        exact VerifyRoute.here rfl rfl (by simp [readCount]) (by simp [verifyCount])
      · refine ServiceWalk.decompose (ServiceWalk.verify ServiceWalk.halt) ?_
        refine ServiceWalk.read serviceCoreF (by simp) rfl rfl ?_ ?_
        · rw [show serviceCoreF.axis = 3 from rfl, axisPath_three]
          refine VerifyRoute.right (by simp [readCount]) (by simp [verifyCount]) ?_
          exact VerifyRoute.here rfl rfl (by simp [readCount]) (by simp [verifyCount])
        · exact ServiceWalk.decompose ServiceWalk.halt
            (ServiceWalk.verify
              (ServiceWalk.decompose
                (ServiceWalk.decompose ServiceWalk.halt ServiceWalk.halt)
                (ServiceWalk.decompose ServiceWalk.halt ServiceWalk.halt)))

/-! ### Root B trace: arm-fetch descent (serves Arm, ArmF) -/

def rootTraceB : RootTrace (cfg seedZ alphaA) (execA seedZ alphaA) ⟨1, by norm_num [cfg]⟩ where
  subject := op9CoreNoun
  services := [serviceArm, serviceArmF]
  recordPartition := by
    rw [rootResponseRecordsB_eq]
    simp [serviceArm, serviceArmF]
  readPartition := by
    rw [op9AxisTreeB_eq]
    simp only [readExps, serviceArm, serviceArmF, List.map_cons, List.map_nil,
      List.nil_append, List.append_nil, List.singleton_append]
    exact List.Perm.refl _
  verifyPartition := by
    rw [op9AxisTreeB_eq]
    simp only [verifyExps, serviceArm, serviceArmF, List.map_cons, List.map_nil,
      List.nil_append, List.append_nil, List.singleton_append]
    exact List.Perm.refl _
  traversal := by
    rw [op9AxisTreeB_eq]
    refine ServiceWalk.read serviceArm (by simp) rfl rfl ?_ ?_
    · rw [show serviceArm.axis = 2 from rfl, axisPath_two]
      refine VerifyRoute.left ?_
        (by simp [readCount, expArmF_ne_expArm])
        (by simp [verifyCount, expArmF_ne_expArm])
      exact VerifyRoute.here rfl rfl
        (by simp [readCount, expArmF_ne_expArm])
        (by simp [verifyCount, expArmF_ne_expArm])
    · refine ServiceWalk.decompose ?_ (ServiceWalk.decompose ServiceWalk.halt ServiceWalk.halt)
      refine ServiceWalk.verify ?_
      refine ServiceWalk.read serviceArmF (by simp) rfl rfl ?_ ?_
      · rw [show serviceArmF.axis = 3 from rfl, axisPath_three]
        refine VerifyRoute.right (by simp [readCount]) (by simp [verifyCount]) ?_
        exact VerifyRoute.here rfl rfl (by simp [readCount]) (by simp [verifyCount])
      · exact ServiceWalk.decompose ServiceWalk.halt (ServiceWalk.verify ServiceWalk.halt)

/-! ## G. Root traces indexed by `Fin cfg.kMem` -/

def rootTraces : ∀ i : Fin (cfg seedZ alphaA).kMem,
    RootTrace (cfg seedZ alphaA) (execA seedZ alphaA) i
  | ⟨0, _⟩ => rootTraceA
  | ⟨1, _⟩ => rootTraceB
  | ⟨n + 2, h⟩ => absurd (show n + 2 < 2 by simp only [cfg] at h; exact h) (by omega)

theorem finRange_kMem :
    List.finRange (cfg seedZ alphaA).kMem =
      [⟨0, by norm_num [cfg]⟩, ⟨1, by norm_num [cfg]⟩] := rfl

/-! ## H. Aggregate timestamp multiset -/

theorem forestTimestampPowers_eq :
    (List.finRange (cfg seedZ alphaA).kMem).flatMap
      (fun i => (rootTraces i).timestampPowers) =
      [alphaA, alphaA ^ 2, alphaA ^ 4, alphaA ^ 3, alphaA ^ 5] := by
  rw [finRange_kMem]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, rootTraces]
  simp only [RootTrace.timestampPowers, RootTrace.exponents, rootTraceA, rootTraceB,
    List.map_cons, List.map_nil]
  simp only [List.cons_append, List.nil_append]
  rw [show (serviceF.exponent : ℕ) = expF from rfl,
    show (serviceT.exponent : ℕ) = expT from rfl,
    show (serviceCoreF.exponent : ℕ) = expCoreF from rfl,
    show (serviceArm.exponent : ℕ) = expArm from rfl,
    show (serviceArmF.exponent : ℕ) = expArmF from rfl,
    ← ts_eq_recF, ← ts_eq_recT, ← ts_eq_recCoreF, ← ts_eq_recArm, ← ts_eq_recArmF,
    ts_recF, ts_recT, ts_recCoreF, ts_recArm, ts_recArmF]

theorem forestTimestampPowers_nodup :
    ((List.finRange (cfg seedZ alphaA).kMem).flatMap
      (fun i => (rootTraces i).timestampPowers)).Nodup := by
  rw [forestTimestampPowers_eq]
  have h12 := alpha_pow_ne_12
  have h14 := alpha_pow_ne_14
  have h13 := alpha_pow_ne_13
  have h15 := alpha_pow_ne_15
  have h24 := alpha_pow_ne_24
  have h23 := alpha_pow_ne_23
  have h25 := alpha_pow_ne_25
  have h43 : alphaA ^ 4 ≠ alphaA ^ 3 := fun h => alpha_pow_ne_34 h.symm
  have h45 := alpha_pow_ne_45
  have h35 := alpha_pow_ne_35
  simp [List.nodup_cons, h12, h14, h13, h15, h24, h23, h25, h43, h45, h35]

/-! ## I. Semantic coverage (NON-VACUOUS for the parent `.s9` row) -/

def lookupTuple {z : K} (l : ServedNounLookup z) :
    ComputeTable.MemRec K × Noun × ℕ × Noun :=
  (l.record, l.root, l.axis, l.child)

theorem castRowData_servedTuples
    {row₁ row₂ : ComputeTable.State × ComputeTable.DTcomp K}
    (h : row₁ = row₂) (d : ComputeRowSemanticData 97 7 row₂) :
    (castRowData h d).needs.served.map lookupTuple = d.needs.served.map lookupTuple := by
  subst h; rfl

theorem rowData_zero_servedTuples :
    (rowData ⟨0, by norm_num [cfg]⟩).needs.served.map lookupTuple =
      [(recArm seedZ alphaA, op9CoreNoun, 2, op9Arm)] :=
  (castRowData_servedTuples computeRowAt_zero parentRowData).trans
    (by simp [parentRowData, lookupTuple, parentServedLookup]; exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩)
theorem rowData_one_servedTuples :
    (rowData ⟨1, by norm_num [cfg]⟩).needs.served.map lookupTuple = [] :=
  (castRowData_servedTuples computeRowAt_one child1RowData).trans
    (by simp [child1RowData, lookupTuple])
theorem rowData_two_servedTuples :
    (rowData ⟨2, by norm_num [cfg]⟩).needs.served.map lookupTuple = [] :=
  (castRowData_servedTuples computeRowAt_two child2RowData).trans
    (by simp [child2RowData, lookupTuple])

/-! ## J. The exact served memory trace

The memory trace is parametric in `semanticData` — it requires only that `D.rows = rowData`,
which holds by construction once the language is assembled in a later file. -/

def memoryTrace
    (D : SemanticTrace.ExactExecutionSemanticData 97 7 (cfg seedZ alphaA) (exec seedZ alphaA))
    (hrows : D.rows = rowData) :
    ExactServedMemoryTrace 97 7 (cfg seedZ alphaA) (exec seedZ alphaA) D
      (execA seedZ alphaA) where
  roots := rootTraces
  timestampPowersNodup := forestTimestampPowers_nodup
  forestIndexRange := by
    rw [forestTimestampPowers_eq]
    norm_num [IO.InRange, cfg]
  semanticCoverage := by
    intro row lookup hlookup
    have hl : lookup ∈ (D.rows row).needs.served := hlookup
    rw [hrows] at hl
    have hmem : lookupTuple lookup ∈ (rowData row).needs.served.map lookupTuple :=
      List.mem_map.mpr ⟨lookup, hl, rfl⟩
    fin_cases row
    · -- Parent row: one served lookup (arm fetch), covered by serviceArm in Root B
      rw [rowData_zero_servedTuples] at hmem
      simp only [List.mem_singleton] at hmem
      have htuple : (lookup.record, lookup.root, lookup.axis, lookup.child) =
          (recArm seedZ alphaA, op9CoreNoun, 2, op9Arm) := hmem
      refine ⟨⟨1, by norm_num [cfg]⟩, serviceArm, ?_, ?_, ?_, ?_, ?_⟩
      · simp [rootTraces, rootTraceB]
      · exact (congrArg Prod.fst htuple).symm
      · exact (congrArg (fun p => p.2.1) htuple).symm
      · exact (congrArg (fun p => p.2.2.2) htuple).symm
      · exact (congrArg (fun p => p.2.2.1) htuple).symm
    · -- Child 1: no served lookups
      rw [rowData_one_servedTuples] at hmem; simp at hmem
    · -- Child 2: no served lookups
      rw [rowData_two_servedTuples] at hmem; simp at hmem

end

end Nock.NockVMROM.Thm54.TraceGen.Op9ConfigK3

#print axioms Nock.NockVMROM.Thm54.TraceGen.Op9ConfigK3.rootTraceA
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op9ConfigK3.rootTraceB
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op9ConfigK3.memoryTrace
