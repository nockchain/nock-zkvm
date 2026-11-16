import Nock.NockVMROM.Thm54.NonterminalServedRow
import Nock.NockVMROM.Thm54.TraceGen.Op8Gen

/-!
# OP₈ nonterminal parent compute-row core (the fan-out-2 push row)

This module builds the genuinely-new **`OP_8` parent compute row** over the shared `K97cubic`
carrier of `NonterminalServedRow`, mirroring `Op7Statement.lean` but for the `.s8` state — the
push compute row (`fanoutComp.s8 = 2`, `requiredCallRealizations.s8 = 2`), with an active
tail decomposition (`tailCons`) and **autocons subject threading**: the consumer child's subject
is `[sb a]` — the cons of the helper result with the original row subject (the OP8 "push"),
not just the helper result alone (OP7) and not the row subject alone.

OP₈ is COMPUTE-ONLY / served-vacuous: `requiredServedLookups.s8 = 0`, so this row consumes no
global-carry lookup.  The two recursive calls are the concrete constant program of the OP₈
Layer-1 slice:

* `call2 = *[0 [1 3]] = 3`   (sf2, the helper — subject = row subject `0`),
* `call1 = *[[3 0] [1 5]] = 5`   (sf1, the consumer — subject = pushed `[3 0]`, threaded).

The row result is `call1.result = 5` (the consumer's evaluation with the autocons subject).

## Scope note

Same shape as `Op7Statement.lean`: the `.s8` parent compute row, its derived semantics, and the
eight-comparison `LocalOpcodeCertificate.s8`.  The `BuildableNockExecution` / `Data` needed for
the full `op8Statement` via `SingleRootModule.statementSR` is in `TraceGen/Op8DataK3.lean`.
-/

namespace Nock.NockVMROM.Thm54.Op8Statement

open scoped Classical
open Nock Nock.Noun Nock.Walk
open ComputeTable
open Nock.NockVMROM.Thm54.SemanticTrace
open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.NockVMROM.Thm54.NonterminalServedRow
open Nock.NockVMROM.Thm54.TraceGen

noncomputable section

local instance prime97op8 : Fact (Nat.Prime 97) := ⟨by norm_num⟩
local instance char97op8 : CharP K97cubic 97 := inferInstance

/-! ## The `OP_8` parent nouns and its `.s8` public/decomposition data

The nouns are reused verbatim from the OP₈ Layer-1 slice (`TraceGen/Op8Gen.lean`). -/

/-- The `OP_8` head atom (`.atom 8`). -/
def op8HeadS : Noun := .atom 8

theorem op8ParentFormula_cons : op8ParentFormula = .cell op8HeadS op8ParentTail := rfl
theorem op8ParentTail_cons :
    op8ParentTail = .cell op8ChildFormulaB op8ChildFormulaC := rfl

/-- The formula-open record `[8 [b c]] @3`. -/
def op8FormulaOpenRecordS : MemRec K97cubic where
  root := encS op8ParentFormula
  child := encS op8ParentTail
  axis := 3
  ts := fixtureAlpha

/-- The formula-tail record `[b c] @2`. -/
def op8FormulaTailRecordS : MemRec K97cubic where
  root := encS op8ParentTail
  child := encS op8ChildFormulaB
  axis := 2
  ts := fixtureAlpha ^ 2

def op8ParentDecS : ComputeTable.Dec K97cubic where
  f_h := encS op8HeadS
  f_t := encS op8ParentTail
  f_th := encS op8ChildFormulaB
  f_tt := encS op8ChildFormulaC
  f_tth := 0
  f_ttt := 0

/-- The `.s8` public record with autocons subject threading: `sf1_s = encS op8PushedSubject`
(the autocons `[sb a]`, not just the helper result), and `sf2_s = encS op8Subject` (the row
subject for the helper). -/
def op8ParentPubS : ComputeTable.Pub K97cubic where
  state := .s8
  s := encS op8Subject
  f := encS op8ParentFormula
  e := encS op8Result
  sf1_s := encS op8PushedSubject
  sf1_f := encS op8ChildFormulaC
  sf1_e := encS op8Result
  sf2_s := encS op8Subject
  sf2_f := encS op8ChildFormulaB
  sf2_e := encS op8Sb
  sf3_s := 0
  sf3_f := 0
  sf3_e := 0
  ln_prev := 1
  ln := fixtureAlpha ^ 2
  mr1 := op8FormulaOpenRecordS
  mr2 := op8FormulaTailRecordS
  mr3 := MemRec.zero

def op8ParentRowS : State × ComputeTable.DTcomp K97cubic :=
  (.s8, (servedInputs, op8ParentPubS, op8ParentDecS))

/-- The accepted algorithmic verifier row for the `OP_8` parent: `pub.f` opens as `[8 [b c]]`, the
two live records reconstruct the formula-open and formula-tail cells, and the `.s8` evaluation block
threads the consumer subject `sf1_s` to the autocons `cons(sf2_e, s)`. -/
theorem op8ParentS_accepts : Vcomp servedInputs op8ParentPubS op8ParentDecS := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact GlobalCarryRecognizer.enc_cons servedSeed_ne op8HeadS op8ParentTail
  · ext <;>
      norm_num [op8ParentPubS, op8FormulaOpenRecordS, op8ParentDecS, servedInputs, encS,
        op8ParentFormula, op8ParentTail]
  · simp [SVhead, headAtom, op8ParentPubS, op8ParentDecS, servedInputs, encS, op8HeadS,
      GlobalCarryRecognizer.enc_atom, State.toNat]
  · refine ⟨?_, ?_, ?_, ?_⟩
    · ext <;>
        norm_num [op8ParentPubS, op8FormulaTailRecordS, op8ParentDecS, servedInputs, encS,
          op8ParentTail, op8ChildFormulaB]
    · exact (GlobalCarryRecognizer.enc_cons servedSeed_ne op8ChildFormulaB op8ChildFormulaC).symm
    · rfl
    · simp [op8ParentPubS, servedInputs]
  · exact ⟨GlobalCarryRecognizer.enc_cons servedSeed_ne op8Sb op8Subject,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### Parent row data and its certificate -/

def op8ParentRoot : OpcodeSemantics.RootRealization servedInputs op8ParentPubS op8ParentDecS where
  subject := op8Subject
  formula := op8ParentFormula
  result := op8Result
  head := op8HeadS
  tail := op8ParentTail
  subject_realizes := rfl
  formula_realizes := rfl
  result_realizes := rfl
  head_realizes := rfl
  tail_realizes := rfl

def op8Tail : OpcodeSemantics.TailRealization servedInputs.z op8ParentDecS where
  head := op8ChildFormulaB
  tail := op8ChildFormulaC
  head_realizes := rfl
  tail_realizes := rfl

/-- call1 is the CONSUMER: subject = op8PushedSubject (autocons `[sb a]`), formula = c, result =
op8Result. -/
def op8Call1 :
    OpcodeSemantics.CallRealization servedInputs.z
      op8ParentPubS.sf1_s op8ParentPubS.sf1_f op8ParentPubS.sf1_e where
  subject := op8PushedSubject
  formula := op8ChildFormulaC
  result := op8Result
  subject_realizes := rfl
  formula_realizes := rfl
  result_realizes := rfl

/-- call2 is the HELPER: subject = op8Subject (row subject), formula = b, result = op8Sb. -/
def op8Call2 :
    OpcodeSemantics.CallRealization servedInputs.z
      op8ParentPubS.sf2_s op8ParentPubS.sf2_f op8ParentPubS.sf2_e where
  subject := op8Subject
  formula := op8ChildFormulaB
  result := op8Sb
  subject_realizes := rfl
  formula_realizes := rfl
  result_realizes := rfl

/-- The eight-entry OP₈ comparison census, in the exact `requiredComparisonRoles.s8` order.
The key difference from OP₇: comparison 6 (`h1s`) compares the autocons `[sb a]` against
`.cell op8Sb op8Subject`, not against the bare helper result. -/
def op8ParentComparisons : List ComparisonUse :=
  [ { role := .opcodeHead, left := op8HeadS, right := .atom 8 },
    { role := .formulaCons, left := op8ParentFormula, right := .cell op8HeadS op8ParentTail },
    { role := .tailCons, left := op8ParentTail,
      right := .cell op8ChildFormulaB op8ChildFormulaC },
    { role := .recursiveSubject, left := op8Subject, right := op8Subject },
    { role := .recursiveFormula, left := op8ChildFormulaB, right := op8ChildFormulaB },
    { role := .recursiveSubject, left := op8PushedSubject,
      right := .cell op8Sb op8Subject },
    { role := .recursiveFormula, left := op8ChildFormulaC, right := op8ChildFormulaC },
    { role := .producedResult, left := op8Result, right := op8Result } ]

/-- Row semantic data for the nonterminal `OP_8` parent: one tail realization, two recursive
calls, eight comparisons, and no size window / axis gate / served lookup (compute-only). -/
def op8ParentRowData : ComputeRowSemanticData 97 5 op8ParentRowS where
  root := op8ParentRoot
  tails := [op8Tail]
  branchTails := []
  calls :=
    [ { subjectFP := op8ParentPubS.sf1_s
        formulaFP := op8ParentPubS.sf1_f
        resultFP := op8ParentPubS.sf1_e
        realization := op8Call1 },
      { subjectFP := op8ParentPubS.sf2_s
        formulaFP := op8ParentPubS.sf2_f
        resultFP := op8ParentPubS.sf2_e
        realization := op8Call2 } ]
  windows := []
  axisGates := []
  tails_count := rfl
  branchTails_count := rfl
  calls_count := rfl
  windows_count := rfl
  axisGates_count := rfl
  realizedNouns := [op8Subject, op8ParentFormula, op8Result]
  subject_mem := by simp [op8ParentRoot]
  formula_mem := by simp [op8ParentRoot]
  result_mem := by simp [op8ParentRoot]
  bounded := by
    intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h | h | h <;> subst h
    · simp [op8Subject]
    · simp [op8ParentFormula, op8ParentTail, op8ChildFormulaB, op8ChildFormulaC,
        FieldEmbedding.BoundedBy]
    · show FieldEmbedding.BoundedBy 97 (Noun.atom 5)
      simp [FieldEmbedding.BoundedBy]
  comparisons := op8ParentComparisons
  comparison_faithful := by
    intro c hc
    simp only [op8ParentComparisons, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with h | h | h | h | h | h | h | h <;> subst h
    · exact pairFaithful_self _
        (by simp [op8HeadS])
    · exact pairFaithful_self _
        (by simp [op8ParentFormula, op8ParentTail, op8ChildFormulaB, op8ChildFormulaC])
    · exact pairFaithful_self _
        (by simp [op8ParentTail, op8ChildFormulaB, op8ChildFormulaC, FieldEmbedding.BoundedBy])
    · exact pairFaithful_self _
        (by simp [op8Subject])
    · exact pairFaithful_self _
        (by simp [op8ChildFormulaB])
    · exact pairFaithful_self _
        (by simp [op8PushedSubject, op8Sb, op8Subject])
    · exact pairFaithful_self _
        (by simp [op8ChildFormulaC, FieldEmbedding.BoundedBy])
    · exact pairFaithful_self _
        (by simp [op8Result])
  comparison_leaves := by
    intro c hc
    simp only [op8ParentComparisons, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with h | h | h | h | h | h | h | h <;> subst h <;>
      simp [ComparisonUse.LeavesBounded, op8HeadS, op8ParentFormula, op8ParentTail,
        op8ChildFormulaB, op8ChildFormulaC, op8Subject, op8Sb, op8Result,
        op8PushedSubject, Noun.leaves]
  comparison_roles := rfl
  axisGate_listed := by intro gate hgate; simp at hgate
  axisGate_tail_mem := by intro gate hgate; simp at hgate
  needs :=
    { served := []
      served_count := rfl }

/-- **The `OP_8` parent certificate.**  The eight comparison premises, the two recursive-call
evaluations (`*[0 [1 3]] = 3`, `*[[3 0] [1 5]] = 5`), and the accepted `Vcomp` row assemble
the fan-out-2 `.s8` local opcode certificate.  The `h1s` comparison certifies the autocons
`[sb a]` against `(.cell call2.result data.root.subject)` (EC.8.1). -/
theorem op8ParentCertificate_nonempty :
    Nonempty (LocalOpcodeCertificate 97 5 op8ParentRowData) := by
  refine ⟨.s8 op8ParentRowData 1 op8Tail op8Call1 op8Call2 rfl servedSeed_ne
    cast_injOn_97 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ op8ParentS_accepts⟩
  · simp [ComparisonListed, op8ParentRowData, op8ParentComparisons, op8ParentRoot, op8HeadS]
  · simp [ComparisonListed, op8ParentRowData, op8ParentComparisons, op8ParentRoot,
      op8ParentFormula]
  · simp [ComparisonListed, op8ParentRowData, op8ParentComparisons, op8ParentRoot, op8Tail,
      op8ParentTail]
  · simp [ComparisonListed, op8ParentRowData, op8ParentComparisons, op8ParentRoot, op8Call2,
      op8Subject]
  · simp [ComparisonListed, op8ParentRowData, op8ParentComparisons, op8Tail, op8Call2]
  · simp [ComparisonListed, op8ParentRowData, op8ParentComparisons, op8Call1, op8Call2,
      op8PushedSubject, op8ParentRoot, op8Subject, op8Sb]
  · simp [ComparisonListed, op8ParentRowData, op8ParentComparisons, op8Tail, op8Call1]
  · simp [ComparisonListed, op8ParentRowData, op8ParentComparisons, op8ParentRoot, op8Call1,
      op8Result]
  · rfl
  · rfl

/-- **Derived Nock semantics of the nonterminal `OP_8` parent.**  A real ROM `eval`-step and a
bounded evaluation `*[0 [8 [[1 3] [1 5]]]] = 5`. -/
theorem op8ParentS_semantics :
    ∃ (fuel : ℕ) (successor : Verb),
      Verb.StepROM (Verb.program op8Subject op8ParentFormula) successor ∧
        FieldEmbedding.evalFBy 97 (fuel + 1) op8Subject op8ParentFormula = some op8Result := by
  obtain ⟨cert⟩ := op8ParentCertificate_nonempty
  exact cert.semantics

end

#print axioms Nock.NockVMROM.Thm54.Op8Statement.op8ParentS_accepts
#print axioms Nock.NockVMROM.Thm54.Op8Statement.op8ParentRowData
#print axioms Nock.NockVMROM.Thm54.Op8Statement.op8ParentCertificate_nonempty
#print axioms Nock.NockVMROM.Thm54.Op8Statement.op8ParentS_semantics

end Nock.NockVMROM.Thm54.Op8Statement
