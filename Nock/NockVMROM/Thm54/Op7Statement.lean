import Nock.NockVMROM.Thm54.NonterminalServedRow
import Nock.NockVMROM.Thm54.TraceGen.Op7Gen

/-!
# OP₇ nonterminal parent compute-row core (the fan-out-2 compose row)

This module builds the genuinely-new **`OP_7` parent compute row** over the shared `K97cubic`
carrier of `NonterminalServedRow`, mirroring `Op5Statement.lean` but for the `.s7` state — the
compose compute row (`fanoutComp.s7 = 2`, `requiredCallRealizations.s7 = 2`), with an active
tail decomposition (`tailCons`) and genuine **subject threading**: the consumer child's subject is
the helper child's result, not the row subject.

OP₇ is COMPUTE-ONLY / served-vacuous: `requiredServedLookups.s7 = 0`, so this row consumes no
global-carry lookup.  The two recursive calls are the concrete constant program of the OP₇
Layer-1 slice:

* `call2 = *[0 [1 3]] = 3`   (sf2, the helper — subject = row subject `0`),
* `call1 = *[3 [1 5]] = 5`   (sf1, the consumer — subject = helper result `3`, threaded).

The row result is `call1.result = 5` (the consumer's evaluation with the threaded subject).

## Scope note

Same shape as `Op5Statement.lean`: the `.s7` parent compute row, its derived semantics, and the
eight-comparison `LocalOpcodeCertificate.s7`.  The `BuildableNockExecution` / `Data` needed for
the full `op7Statement` via `SingleRootModule.statementSR` is in `TraceGen/Op7DataK3.lean`.
-/

namespace Nock.NockVMROM.Thm54.Op7Statement

open scoped Classical
open Nock Nock.Noun Nock.Walk
open ComputeTable
open Nock.NockVMROM.Thm54.SemanticTrace
open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.NockVMROM.Thm54.NonterminalServedRow
open Nock.NockVMROM.Thm54.TraceGen

noncomputable section

local instance prime97op7 : Fact (Nat.Prime 97) := ⟨by norm_num⟩
local instance char97op7 : CharP K97cubic 97 := inferInstance

/-! ## The `OP_7` parent nouns and its `.s7` public/decomposition data

The nouns are reused verbatim from the OP₇ Layer-1 slice (`TraceGen/Op7Gen.lean`). -/

/-- The `OP_7` head atom (`.atom 7`). -/
def op7HeadS : Noun := .atom 7

theorem op7ParentFormula_cons : op7ParentFormula = .cell op7HeadS op7ParentTail := rfl
theorem op7ParentTail_cons :
    op7ParentTail = .cell op7ChildFormulaB op7ChildFormulaC := rfl

/-- The formula-open record `[7 [b c]] @3`. -/
def op7FormulaOpenRecordS : MemRec K97cubic where
  root := encS op7ParentFormula
  child := encS op7ParentTail
  axis := 3
  ts := fixtureAlpha

/-- The formula-tail record `[b c] @2`. -/
def op7FormulaTailRecordS : MemRec K97cubic where
  root := encS op7ParentTail
  child := encS op7ChildFormulaB
  axis := 2
  ts := fixtureAlpha ^ 2

def op7ParentDecS : ComputeTable.Dec K97cubic where
  f_h := encS op7HeadS
  f_t := encS op7ParentTail
  f_th := encS op7ChildFormulaB
  f_tt := encS op7ChildFormulaC
  f_tth := 0
  f_ttt := 0

/-- The `.s7` public record with subject threading: `sf1_s = encS op7Sb` (the helper result, not
the row subject), and `sf2_s = encS op7Subject` (the row subject for the helper). -/
def op7ParentPubS : ComputeTable.Pub K97cubic where
  state := .s7
  s := encS op7Subject
  f := encS op7ParentFormula
  e := encS op7Result
  sf1_s := encS op7Sb
  sf1_f := encS op7ChildFormulaC
  sf1_e := encS op7Result
  sf2_s := encS op7Subject
  sf2_f := encS op7ChildFormulaB
  sf2_e := encS op7Sb
  sf3_s := 0
  sf3_f := 0
  sf3_e := 0
  ln_prev := 1
  ln := fixtureAlpha ^ 2
  mr1 := op7FormulaOpenRecordS
  mr2 := op7FormulaTailRecordS
  mr3 := MemRec.zero

def op7ParentRowS : State × ComputeTable.DTcomp K97cubic :=
  (.s7, (servedInputs, op7ParentPubS, op7ParentDecS))

/-- The accepted algorithmic verifier row for the `OP_7` parent: `pub.f` opens as `[7 [b c]]`, the
two live records reconstruct the formula-open and formula-tail cells, and the `.s7` evaluation block
threads the consumer subject `sf1_s` to the helper result `sf2_e` (subject threading). -/
theorem op7ParentS_accepts : Vcomp servedInputs op7ParentPubS op7ParentDecS := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact GlobalCarryRecognizer.enc_cons servedSeed_ne op7HeadS op7ParentTail
  · ext <;>
      norm_num [op7ParentPubS, op7FormulaOpenRecordS, op7ParentDecS, servedInputs, encS,
        op7ParentFormula, op7ParentTail]
  · simp [SVhead, headAtom, op7ParentPubS, op7ParentDecS, servedInputs, encS, op7HeadS,
      GlobalCarryRecognizer.enc_atom, State.toNat]
  · refine ⟨?_, ?_, ?_, ?_⟩
    · ext <;>
        norm_num [op7ParentPubS, op7FormulaTailRecordS, op7ParentDecS, servedInputs, encS,
          op7ParentTail, op7ChildFormulaB]
    · exact (GlobalCarryRecognizer.enc_cons servedSeed_ne op7ChildFormulaB op7ChildFormulaC).symm
    · rfl
    · simp [op7ParentPubS, servedInputs]
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### Parent row data and its certificate -/

def op7ParentRoot : OpcodeSemantics.RootRealization servedInputs op7ParentPubS op7ParentDecS where
  subject := op7Subject
  formula := op7ParentFormula
  result := op7Result
  head := op7HeadS
  tail := op7ParentTail
  subject_realizes := rfl
  formula_realizes := rfl
  result_realizes := rfl
  head_realizes := rfl
  tail_realizes := rfl

def op7Tail : OpcodeSemantics.TailRealization servedInputs.z op7ParentDecS where
  head := op7ChildFormulaB
  tail := op7ChildFormulaC
  head_realizes := rfl
  tail_realizes := rfl

/-- call1 is the CONSUMER: subject = op7Sb (threaded from helper result), formula = c, result =
op7Result. -/
def op7Call1 :
    OpcodeSemantics.CallRealization servedInputs.z
      op7ParentPubS.sf1_s op7ParentPubS.sf1_f op7ParentPubS.sf1_e where
  subject := op7Sb
  formula := op7ChildFormulaC
  result := op7Result
  subject_realizes := rfl
  formula_realizes := rfl
  result_realizes := rfl

/-- call2 is the HELPER: subject = op7Subject (row subject), formula = b, result = op7Sb. -/
def op7Call2 :
    OpcodeSemantics.CallRealization servedInputs.z
      op7ParentPubS.sf2_s op7ParentPubS.sf2_f op7ParentPubS.sf2_e where
  subject := op7Subject
  formula := op7ChildFormulaB
  result := op7Sb
  subject_realizes := rfl
  formula_realizes := rfl
  result_realizes := rfl

/-- The eight-entry OP₇ comparison census, in the exact `requiredComparisonRoles.s7` order. -/
def op7ParentComparisons : List ComparisonUse :=
  [ { role := .opcodeHead, left := op7HeadS, right := .atom 7 },
    { role := .formulaCons, left := op7ParentFormula, right := .cell op7HeadS op7ParentTail },
    { role := .tailCons, left := op7ParentTail,
      right := .cell op7ChildFormulaB op7ChildFormulaC },
    { role := .recursiveSubject, left := op7Subject, right := op7Subject },
    { role := .recursiveFormula, left := op7ChildFormulaB, right := op7ChildFormulaB },
    { role := .recursiveSubject, left := op7Sb, right := op7Sb },
    { role := .recursiveFormula, left := op7ChildFormulaC, right := op7ChildFormulaC },
    { role := .producedResult, left := op7Result, right := op7Result } ]

/-- Row semantic data for the nonterminal `OP_7` parent: one tail realization, two recursive
calls, eight comparisons, and no size window / axis gate / served lookup (compute-only). -/
def op7ParentRowData : ComputeRowSemanticData 97 5 op7ParentRowS where
  root := op7ParentRoot
  tails := [op7Tail]
  branchTails := []
  calls :=
    [ { subjectFP := op7ParentPubS.sf1_s
        formulaFP := op7ParentPubS.sf1_f
        resultFP := op7ParentPubS.sf1_e
        realization := op7Call1 },
      { subjectFP := op7ParentPubS.sf2_s
        formulaFP := op7ParentPubS.sf2_f
        resultFP := op7ParentPubS.sf2_e
        realization := op7Call2 } ]
  windows := []
  axisGates := []
  tails_count := rfl
  branchTails_count := rfl
  calls_count := rfl
  windows_count := rfl
  axisGates_count := rfl
  realizedNouns := [op7Subject, op7ParentFormula, op7Result]
  subject_mem := by simp [op7ParentRoot]
  formula_mem := by simp [op7ParentRoot]
  result_mem := by simp [op7ParentRoot]
  bounded := by
    intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h | h | h <;> subst h
    · simp [op7Subject]
    · simp [op7ParentFormula, op7ParentTail, op7ChildFormulaB, op7ChildFormulaC,
        FieldEmbedding.BoundedBy]
    · show FieldEmbedding.BoundedBy 97 (Noun.atom 5)
      simp [FieldEmbedding.BoundedBy]
  comparisons := op7ParentComparisons
  comparison_faithful := by
    intro c hc
    simp only [op7ParentComparisons, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with h | h | h | h | h | h | h | h <;> subst h
    · exact pairFaithful_self _
        (by simp [op7HeadS])
    · exact pairFaithful_self _
        (by simp [op7ParentFormula, op7ParentTail, op7ChildFormulaB, op7ChildFormulaC])
    · exact pairFaithful_self _
        (by simp [op7ParentTail, op7ChildFormulaB, op7ChildFormulaC, FieldEmbedding.BoundedBy])
    · exact pairFaithful_self _
        (by simp [op7Subject])
    · exact pairFaithful_self _
        (by simp [op7ChildFormulaB])
    · exact pairFaithful_self _
        (by simp [op7Sb])
    · exact pairFaithful_self _
        (by simp [op7ChildFormulaC, FieldEmbedding.BoundedBy])
    · exact pairFaithful_self _
        (by simp [op7Result])
  comparison_leaves := by
    intro c hc
    simp only [op7ParentComparisons, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with h | h | h | h | h | h | h | h <;> subst h <;>
      simp [ComparisonUse.LeavesBounded, op7HeadS, op7ParentFormula, op7ParentTail,
        op7ChildFormulaB, op7ChildFormulaC, op7Subject, op7Sb, op7Result, Noun.leaves]
  comparison_roles := rfl
  axisGate_listed := by intro gate hgate; simp at hgate
  axisGate_tail_mem := by intro gate hgate; simp at hgate
  needs :=
    { served := []
      served_count := rfl }

/-- **The `OP_7` parent certificate.**  The eight comparison premises, the two recursive-call
evaluations (`*[0 [1 3]] = 3`, `*[3 [1 5]] = 5`), and the accepted `Vcomp` row assemble
the fan-out-2 `.s7` local opcode certificate. -/
theorem op7ParentCertificate_nonempty :
    Nonempty (LocalOpcodeCertificate 97 5 op7ParentRowData) := by
  refine ⟨.s7 op7ParentRowData 1 op7Tail op7Call1 op7Call2 rfl servedSeed_ne
    cast_injOn_97 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ op7ParentS_accepts⟩
  · simp [ComparisonListed, op7ParentRowData, op7ParentComparisons, op7ParentRoot, op7HeadS]
  · simp [ComparisonListed, op7ParentRowData, op7ParentComparisons, op7ParentRoot,
      op7ParentFormula]
  · simp [ComparisonListed, op7ParentRowData, op7ParentComparisons, op7ParentRoot, op7Tail,
      op7ParentTail]
  · simp [ComparisonListed, op7ParentRowData, op7ParentComparisons, op7ParentRoot, op7Call2,
      op7Subject]
  · simp [ComparisonListed, op7ParentRowData, op7ParentComparisons, op7Tail, op7Call2]
  · simp [ComparisonListed, op7ParentRowData, op7ParentComparisons, op7Call1, op7Call2]
  · simp [ComparisonListed, op7ParentRowData, op7ParentComparisons, op7Tail, op7Call1]
  · simp [ComparisonListed, op7ParentRowData, op7ParentComparisons, op7ParentRoot, op7Call1,
      op7Result]
  · rfl
  · rfl

/-- **Derived Nock semantics of the nonterminal `OP_7` parent.**  A real ROM `eval`-step and a
bounded evaluation `*[0 [7 [[1 3] [1 5]]]] = 5`. -/
theorem op7ParentS_semantics :
    ∃ (fuel : ℕ) (successor : Verb),
      Verb.StepROM (Verb.program op7Subject op7ParentFormula) successor ∧
        FieldEmbedding.evalFBy 97 (fuel + 1) op7Subject op7ParentFormula = some op7Result := by
  obtain ⟨cert⟩ := op7ParentCertificate_nonempty
  exact cert.semantics

end

#print axioms Nock.NockVMROM.Thm54.Op7Statement.op7ParentS_accepts
#print axioms Nock.NockVMROM.Thm54.Op7Statement.op7ParentRowData
#print axioms Nock.NockVMROM.Thm54.Op7Statement.op7ParentCertificate_nonempty
#print axioms Nock.NockVMROM.Thm54.Op7Statement.op7ParentS_semantics

end Nock.NockVMROM.Thm54.Op7Statement
