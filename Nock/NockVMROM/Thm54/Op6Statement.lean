import Nock.NockVMROM.Thm54.NonterminalServedRow
import Nock.NockVMROM.Thm54.TraceGen.Op6Gen

/-!
# OP₆ nonterminal parent compute-row core (the fan-out-2 branch row)

This module builds the genuinely-new **`OP_6` parent compute row** over the shared `K97cubic`
carrier of `NonterminalServedRow`, mirroring `Op7Statement.lean` / `Op8Statement.lean` but for
the `.s6` state — the branch compute row (`fanoutComp.s6 = 2`, `requiredCallRealizations.s6 = 2`),
with an active tail decomposition (`tailCons`), an active **branch-tail decomposition**
(`branchTailCons`), and **shared-subject threading**: both recursive children evaluate against the
same row subject.

OP₆ is COMPUTE-ONLY / served-vacuous: `requiredServedLookups.s6 = 0`, so this row consumes no
global-carry lookup.  The two recursive calls are the concrete constant program of the OP₆
Layer-1 slice:

* `call2 = *[0 [1 0]] = 0`   (sf2, the condition evaluator — subject = row subject `0`),
* `call1 = *[0 [1 5]] = 5`   (sf1, the taken branch — subject = row subject `0`, selected by cond=0).

The row result is `call1.result = 5` (the taken branch's evaluation).

## Scope note

Same shape as `Op7Statement.lean` / `Op8Statement.lean`: the `.s6` parent compute row, its derived
semantics, and the ten-comparison `LocalOpcodeCertificate.s6`.  The `BuildableNockExecution` /
`Data` needed for the full `op6Statement` via `SingleRootModule.statementSR` is in
`TraceGen/Op6DataK3.lean`.
-/

namespace Nock.NockVMROM.Thm54.Op6Statement

open scoped Classical
open Nock Nock.Noun Nock.Walk
open ComputeTable
open Nock.NockVMROM.Thm54.SemanticTrace
open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.NockVMROM.Thm54.NonterminalServedRow
open Nock.NockVMROM.Thm54.TraceGen

noncomputable section

local instance prime97op6 : Fact (Nat.Prime 97) := ⟨by norm_num⟩
local instance char97op6 : CharP K97cubic 97 := inferInstance

/-! ## The `OP_6` parent nouns and its `.s6` public/decomposition data

The nouns are reused verbatim from the OP₆ Layer-1 slice (`TraceGen/Op6Gen.lean`). -/

/-- The `OP_6` head atom (`.atom 6`). -/
def op6HeadS : Noun := .atom 6

theorem op6ParentFormula_cons : op6ParentFormula = .cell op6HeadS op6ParentTail := rfl
theorem op6ParentTail_cons :
    op6ParentTail = .cell op6CondFormula op6BranchPair := rfl
theorem op6BranchPair_cons :
    op6BranchPair = .cell op6BranchC op6BranchD := rfl

/-- The formula-open record `[6 [b [c d]]] @3`. -/
def op6FormulaOpenRecordS : MemRec K97cubic where
  root := encS op6ParentFormula
  child := encS op6ParentTail
  axis := 3
  ts := fixtureAlpha

/-- The formula-tail record `[b [c d]] @2`. -/
def op6FormulaTailRecordS : MemRec K97cubic where
  root := encS op6ParentTail
  child := encS op6CondFormula
  axis := 2
  ts := fixtureAlpha ^ 2

/-- The branch-pair record `[c d] @2`. -/
def op6BranchPairRecordS : MemRec K97cubic where
  root := encS op6BranchPair
  child := encS op6BranchC
  axis := 2
  ts := fixtureAlpha ^ 3

def op6ParentDecS : ComputeTable.Dec K97cubic where
  f_h := encS op6HeadS
  f_t := encS op6ParentTail
  f_th := encS op6CondFormula
  f_tt := encS op6BranchPair
  f_tth := encS op6BranchC
  f_ttt := encS op6BranchD

/-- The `.s6` public record with shared-subject threading: both sf1_s and sf2_s point to
`encS op6Subject` (the row subject for both children). -/
def op6ParentPubS : ComputeTable.Pub K97cubic where
  state := .s6
  s := encS op6Subject
  f := encS op6ParentFormula
  e := encS op6Result
  sf1_s := encS op6Subject
  sf1_f := encS op6BranchC
  sf1_e := encS op6Result
  sf2_s := encS op6Subject
  sf2_f := encS op6CondFormula
  sf2_e := encS op6CondResult
  sf3_s := 0
  sf3_f := 0
  sf3_e := 0
  ln_prev := 1
  ln := fixtureAlpha ^ 3
  mr1 := op6FormulaOpenRecordS
  mr2 := op6FormulaTailRecordS
  mr3 := op6BranchPairRecordS

def op6ParentRowS : State × ComputeTable.DTcomp K97cubic :=
  (.s6, (servedInputs, op6ParentPubS, op6ParentDecS))

/-- The accepted algorithmic verifier row for the `OP_6` parent: `pub.f` opens as `[6 [b [c d]]]`,
the three live records reconstruct the formula-open, formula-tail, and branch-pair cells, and the
`.s6` evaluation block selects the taken branch by condition value. -/
theorem op6ParentS_accepts : Vcomp servedInputs op6ParentPubS op6ParentDecS := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact GlobalCarryRecognizer.enc_cons servedSeed_ne op6HeadS op6ParentTail
  · ext <;>
      norm_num [op6ParentPubS, op6FormulaOpenRecordS, op6ParentDecS, servedInputs, encS,
        op6ParentFormula, op6ParentTail]
  · simp [SVhead, headAtom, op6ParentPubS, op6ParentDecS, servedInputs, encS, op6HeadS,
      GlobalCarryRecognizer.enc_atom, State.toNat]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · ext <;>
        norm_num [op6ParentPubS, op6FormulaTailRecordS, op6ParentDecS, servedInputs, encS,
          op6ParentTail, op6CondFormula]
    · exact (GlobalCarryRecognizer.enc_cons servedSeed_ne op6CondFormula op6BranchPair).symm
    · ext <;>
        norm_num [op6ParentPubS, op6BranchPairRecordS, op6ParentDecS, servedInputs, encS,
          op6BranchPair, op6BranchC]
    · exact (GlobalCarryRecognizer.enc_cons servedSeed_ne op6BranchC op6BranchD).symm
    · simp [op6ParentPubS, servedInputs]
  · have hleaf0 : op6ParentPubS.sf2_e.leaf = 0 := by
      simp [op6ParentPubS, encS, op6CondResult, GlobalCarryRecognizer.enc_atom,
        ComputeTable.FP.atomFP]
    refine ⟨rfl, ?_, rfl, rfl, rfl, ?_, ?_, Or.inl hleaf0, rfl, rfl, rfl⟩
    · simp only [op6ParentPubS, op6ParentDecS, encS, op6CondResult,
        GlobalCarryRecognizer.enc_atom, ComputeTable.FP.atomFP, Nat.cast_zero, ite_true]
    · simp [op6ParentPubS, encS, op6CondResult, GlobalCarryRecognizer.enc_atom,
        ComputeTable.FP.atomFP, servedInputs]
    · simp [op6ParentPubS, encS, op6CondResult, GlobalCarryRecognizer.enc_atom,
        ComputeTable.FP.atomFP]

/-! ### Parent row data and its certificate -/

def op6ParentRoot : OpcodeSemantics.RootRealization servedInputs op6ParentPubS op6ParentDecS where
  subject := op6Subject
  formula := op6ParentFormula
  result := op6Result
  head := op6HeadS
  tail := op6ParentTail
  subject_realizes := rfl
  formula_realizes := rfl
  result_realizes := rfl
  head_realizes := rfl
  tail_realizes := rfl

def op6Tail : OpcodeSemantics.TailRealization servedInputs.z op6ParentDecS where
  head := op6CondFormula
  tail := op6BranchPair
  head_realizes := rfl
  tail_realizes := rfl

def op6Branch : OpcodeSemantics.BranchTailRealization servedInputs.z op6ParentDecS where
  head := op6BranchC
  tail := op6BranchD
  head_realizes := rfl
  tail_realizes := rfl

/-- call1 is the TAKEN BRANCH: subject = op6Subject, formula = c (branchC), result = op6Result. -/
def op6Call1 :
    OpcodeSemantics.CallRealization servedInputs.z
      op6ParentPubS.sf1_s op6ParentPubS.sf1_f op6ParentPubS.sf1_e where
  subject := op6Subject
  formula := op6BranchC
  result := op6Result
  subject_realizes := rfl
  formula_realizes := rfl
  result_realizes := rfl

/-- call2 is the CONDITION EVALUATOR: subject = op6Subject, formula = b (condFormula),
result = op6CondResult (=.atom 0). -/
def op6Call2 :
    OpcodeSemantics.CallRealization servedInputs.z
      op6ParentPubS.sf2_s op6ParentPubS.sf2_f op6ParentPubS.sf2_e where
  subject := op6Subject
  formula := op6CondFormula
  result := op6CondResult
  subject_realizes := rfl
  formula_realizes := rfl
  result_realizes := rfl

/-! ### Branch-pair separation -/

private theorem encS_branchC_ne_branchD : encS op6BranchC ≠ encS op6BranchD := by
  intro h
  have hleaf := congrArg ComputeTable.FP.leaf h
  simp only [encS, op6BranchC, op6BranchD,
    GlobalCarryRecognizer.enc_cons servedSeed_ne,
    GlobalCarryRecognizer.enc_atom, ComputeTable.FP.cons, ComputeTable.FP.atomFP] at hleaf
  have h56 : (5 : K97cubic) = (6 : K97cubic) :=
    mul_left_cancel₀ servedSeed_ne (add_left_cancel hleaf)
  exact absurd (cast_injOn_97 (show (5 : ℕ) ∈ Set.Iio 97 from by norm_num)
    (show (6 : ℕ) ∈ Set.Iio 97 from by norm_num) h56) (by norm_num)

private theorem op6_branch_fn_ne :
    NPR.fn op6BranchC (servedSeed : K97cubic) ≠ NPR.fn op6BranchD servedSeed := by
  intro h
  apply encS_branchC_ne_branchD
  show GlobalCarryRecognizer.enc servedSeed op6BranchC =
    GlobalCarryRecognizer.enc servedSeed op6BranchD
  simp only [GlobalCarryRecognizer.enc_eq_fn, h]

private theorem op6_branch_pairFaithful :
    OpcodeSemantics.PairFaithful servedSeed 97 op6BranchC op6BranchD where
  separates := fun _ => op6_branch_fn_ne
  left_bounded := by simp [op6BranchC, FieldEmbedding.BoundedBy]
  right_bounded := by simp [op6BranchD, FieldEmbedding.BoundedBy]

/-! ### Comparison census and row data -/

/-- The ten-entry OP₆ comparison census, in the exact `requiredComparisonRoles.s6` order.
The key comparisons: (1) the branch-tail decomposition `hbranchTail` certifies `[c d]`,
(2) `h1fZero` + `h1fOne` both list the taken formula against the two branches (one trivial,
one certifying the selection). -/
def op6ParentComparisons : List ComparisonUse :=
  [ { role := .opcodeHead, left := op6HeadS, right := .atom 6 },
    { role := .formulaCons, left := op6ParentFormula, right := .cell op6HeadS op6ParentTail },
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

/-- Row semantic data for the nonterminal `OP_6` parent: one tail realization, one branch-tail
realization, two recursive calls, ten comparisons, one size window (the condition result is a
1-leaf atom), and no axis gate / served lookup (compute-only).  `Λ = 7` because
`op6ParentFormula` has 7 leaves. -/
def op6ParentRowData : ComputeRowSemanticData 97 7 op6ParentRowS where
  root := op6ParentRoot
  tails := [op6Tail]
  branchTails := [op6Branch]
  calls :=
    [ { subjectFP := op6ParentPubS.sf1_s
        formulaFP := op6ParentPubS.sf1_f
        resultFP := op6ParentPubS.sf1_e
        realization := op6Call1 },
      { subjectFP := op6ParentPubS.sf2_s
        formulaFP := op6ParentPubS.sf2_f
        resultFP := op6ParentPubS.sf2_e
        realization := op6Call2 } ]
  windows := [{ noun := op6CondResult, window := servedSeed_window_atom 0 }]
  axisGates := []
  tails_count := rfl
  branchTails_count := rfl
  calls_count := rfl
  windows_count := rfl
  axisGates_count := rfl
  realizedNouns := [op6Subject, op6ParentFormula, op6Result]
  subject_mem := by simp [op6ParentRoot]
  formula_mem := by simp [op6ParentRoot]
  result_mem := by simp [op6ParentRoot]
  bounded := by
    intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h | h | h <;> subst h
    · simp [op6Subject]
    · simp [op6ParentFormula, op6ParentTail, op6CondFormula, op6BranchPair, op6BranchC, op6BranchD,
        FieldEmbedding.BoundedBy]
    · show FieldEmbedding.BoundedBy 97 (Noun.atom 5)
      simp [FieldEmbedding.BoundedBy]
  comparisons := op6ParentComparisons
  comparison_faithful := by
    intro c hc
    simp only [op6ParentComparisons, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with h | h | h | h | h | h | h | h | h | h <;> subst h
    · exact pairFaithful_self _
        (by simp [op6HeadS])
    · exact pairFaithful_self _
        (by simp [op6ParentFormula, op6ParentTail, op6CondFormula, op6BranchPair, op6BranchC,
          op6BranchD])
    · exact pairFaithful_self _
        (by simp [op6ParentTail, op6CondFormula, op6BranchPair, op6BranchC, op6BranchD,
          FieldEmbedding.BoundedBy])
    · exact pairFaithful_self _
        (by simp [op6BranchPair, op6BranchC, op6BranchD, FieldEmbedding.BoundedBy])
    · exact pairFaithful_self _
        (by simp [op6Subject])
    · exact pairFaithful_self _
        (by simp [op6BranchC])
    · exact op6_branch_pairFaithful
    · exact pairFaithful_self _
        (by simp [op6Subject])
    · exact pairFaithful_self _
        (by simp [op6CondFormula])
    · exact pairFaithful_self _
        (by simp [op6Result])
  comparison_leaves := by
    intro c hc
    simp only [op6ParentComparisons, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with h | h | h | h | h | h | h | h | h | h <;> subst h <;>
      simp [ComparisonUse.LeavesBounded, op6HeadS, op6ParentFormula, op6ParentTail,
        op6CondFormula, op6BranchPair, op6BranchC, op6BranchD, op6Subject,
        op6Result, Noun.leaves]
  comparison_roles := rfl
  axisGate_listed := by intro gate hgate; simp at hgate
  axisGate_tail_mem := by intro gate hgate; simp at hgate
  needs :=
    { served := []
      served_count := rfl }

/-- **The `OP_6` parent certificate.**  The ten comparison premises, the two recursive-call
evaluations (`*[0 [1 0]] = 0`, `*[0 [1 5]] = 5`), the condition bound (atom `0 < 97`), the
condition size window (1 leaf), and the accepted `Vcomp` row assemble the fan-out-2 `.s6`
local opcode certificate. -/
theorem op6ParentCertificate_nonempty :
    Nonempty (LocalOpcodeCertificate 97 7 op6ParentRowData) := by
  refine ⟨.s6 op6ParentRowData 1 op6Tail op6Branch op6Call1 op6Call2 rfl servedSeed_ne
    (by norm_num) cast_injOn_97 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (show FieldEmbedding.BoundedBy 97 op6CondResult from by simp [op6CondResult])
    (servedSeed_window_atom 0)
    ?_ ?_ op6ParentS_accepts⟩
  · simp [ComparisonListed, op6ParentRowData, op6ParentComparisons, op6ParentRoot, op6HeadS]
  · simp [ComparisonListed, op6ParentRowData, op6ParentComparisons, op6ParentRoot,
      op6ParentFormula]
  · simp [ComparisonListed, op6ParentRowData, op6ParentComparisons, op6ParentRoot, op6Tail,
      op6ParentTail]
  · simp [ComparisonListed, op6ParentRowData, op6ParentComparisons, op6Branch, op6Tail,
      op6BranchPair]
  · simp [ComparisonListed, op6ParentRowData, op6ParentComparisons, op6ParentRoot, op6Call1,
      op6Subject]
  · simp [ComparisonListed, op6ParentRowData, op6ParentComparisons, op6Call1, op6Branch]
  · simp [ComparisonListed, op6ParentRowData, op6ParentComparisons, op6Call1, op6Branch]
  · simp [ComparisonListed, op6ParentRowData, op6ParentComparisons, op6ParentRoot, op6Call2,
      op6Subject]
  · simp [ComparisonListed, op6ParentRowData, op6ParentComparisons, op6Tail, op6Call2]
  · simp [ComparisonListed, op6ParentRowData, op6ParentComparisons, op6ParentRoot, op6Call1,
      op6Result]
  · rfl
  · rfl

/-- **Derived Nock semantics of the nonterminal `OP_6` parent.**  A real ROM `eval`-step and a
bounded evaluation `*[0 [6 [[1 0] [[1 5] [1 6]]]]] = 5`. -/
theorem op6ParentS_semantics :
    ∃ (fuel : ℕ) (successor : Verb),
      Verb.StepROM (Verb.program op6Subject op6ParentFormula) successor ∧
        FieldEmbedding.evalFBy 97 (fuel + 1) op6Subject op6ParentFormula = some op6Result := by
  obtain ⟨cert⟩ := op6ParentCertificate_nonempty
  exact cert.semantics

end

#print axioms Nock.NockVMROM.Thm54.Op6Statement.op6ParentS_accepts
#print axioms Nock.NockVMROM.Thm54.Op6Statement.op6ParentRowData
#print axioms Nock.NockVMROM.Thm54.Op6Statement.op6ParentCertificate_nonempty
#print axioms Nock.NockVMROM.Thm54.Op6Statement.op6ParentS_semantics

end Nock.NockVMROM.Thm54.Op6Statement
