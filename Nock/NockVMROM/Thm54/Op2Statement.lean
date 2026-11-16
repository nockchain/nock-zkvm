import Nock.NockVMROM.Thm54.NonterminalServedRow
import Nock.NockVMROM.Thm54.TraceGen.Op2Gen

/-!
# OP₂ nonterminal parent compute-row core (the fan-out-3 `eval` row)

This module builds the genuinely-new **`OP_2` parent compute row** over the shared `K97cubic`
carrier of `NonterminalServedRow`, mirroring `Op3Statement.lean` but for the `.s2` state — the
max-width compute row (`fanoutComp.s2 = 3`, `requiredCallRealizations.s2 = 3`), the first row
with an active tail decomposition (`tailCons`) and a computed-subject third child.

OP₂ is COMPUTE-ONLY / served-vacuous: `requiredServedLookups.s2 = 0`, so this row consumes no
global-carry lookup (unlike OP₃'s `.s3` row, whose one recursive call is the served `OP_0` row).
The three recursive calls are the concrete constant program of the OP₂ Layer-1 slice:

* `call1 = *[0 [1 [0 1]]] = [0 1]`   (`sf1`),
* `call2 = *[0 [1 [1 5]]] = [1 5]`   (`sf2`),
* `call3 = *[[0 1] [1 5]] = 5`        (the produced result, subject = the computed `sf1`).

Everything here is compute-side: an accepted `Vcomp` row whose `.s2` evaluation
block threads `sf1/sf2/sf3` and whose two live memory records are the formula-open `[2 [b c]] @3` and
the formula-tail `[b c] @2` records; its full `ComputeRowSemanticData`, its
ten-comparison `LocalOpcodeCertificate.s2`, and therefore its derived Nock semantics (a real ROM
`eval`-step + a bounded `evalFBy` producing `op2Result`).

## Scope note

Same shape as `Op3Statement.lean:20-32`: this lands the genuinely-new hard site — the `.s2`
fan-out-3 parent compute row and its derived semantics — as a coherent, kernel-clean partial.  The
served-vacuous single-root memory reconstruction over a cubic carrier (the `BuildableNockExecution`
/ `Data` needed for the full `op2Statement` via `SingleRootModule.statementSR`) is the remaining
work; OP₂'s memory forest, unlike OP₃'s, is single-root (`kMem = 1`) but carries the axis-2
formula-tail descent that has no Layer-1 committed fixture (`Op2Gen.lean:32-46`).
-/

namespace Nock.NockVMROM.Thm54.Op2Statement

open scoped Classical
open Nock Nock.Noun Nock.Walk
open ComputeTable
open Nock.NockVMROM.Thm54.SemanticTrace
open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.NockVMROM.Thm54.NonterminalServedRow
open Nock.NockVMROM.Thm54.TraceGen

noncomputable section

local instance prime97op2 : Fact (Nat.Prime 97) := ⟨by norm_num⟩
local instance char97op2 : CharP K97cubic 97 := inferInstance

/-! ## The `OP_2` parent nouns and its `.s2` public/decomposition data

The nouns are reused verbatim from the OP₂ Layer-1 slice (`TraceGen/Op2Gen.lean`). -/

/-- The `OP_2` head atom (`.atom 2`). -/
def op2HeadS : Noun := .atom 2

theorem op2ParentFormula_cons : op2ParentFormula = .cell op2HeadS op2ParentTail := rfl
theorem op2ParentTail_cons : op2ParentTail = .cell op2ChildFormula1 op2ChildFormula2 := rfl

/-- The formula-open record `[2 [b c]] @3`. -/
def op2FormulaOpenRecordS : MemRec K97cubic where
  root := encS op2ParentFormula
  child := encS op2ParentTail
  axis := 3
  ts := fixtureAlpha

/-- The formula-tail record `[b c] @2`. -/
def op2FormulaTailRecordS : MemRec K97cubic where
  root := encS op2ParentTail
  child := encS op2ChildFormula1
  axis := 2
  ts := fixtureAlpha ^ 2

def op2ParentDecS : ComputeTable.Dec K97cubic where
  f_h := encS op2HeadS
  f_t := encS op2ParentTail
  f_th := encS op2ChildFormula1
  f_tt := encS op2ChildFormula2
  f_tth := 0
  f_ttt := 0

def op2ParentPubS : ComputeTable.Pub K97cubic where
  state := .s2
  s := encS op2Subject
  f := encS op2ParentFormula
  e := encS op2Result
  sf1_s := encS op2Subject
  sf1_f := encS op2ChildFormula1
  sf1_e := encS op2Sf1
  sf2_s := encS op2Subject
  sf2_f := encS op2ChildFormula2
  sf2_e := encS op2Sf2
  sf3_s := encS op2Sf1
  sf3_f := encS op2Sf2
  sf3_e := encS op2Result
  ln_prev := 1
  ln := fixtureAlpha ^ 2
  mr1 := op2FormulaOpenRecordS
  mr2 := op2FormulaTailRecordS
  mr3 := MemRec.zero

def op2ParentRowS : State × ComputeTable.DTcomp K97cubic :=
  (.s2, (servedInputs, op2ParentPubS, op2ParentDecS))

/-- The accepted algorithmic verifier row for the `OP_2` parent: `pub.f` opens as `[2 [b c]]`, the
two live records reconstruct the formula-open and formula-tail cells, and the `.s2` evaluation block
threads `sf1/sf2/sf3` to `op2Result`. -/
theorem op2ParentS_accepts : Vcomp servedInputs op2ParentPubS op2ParentDecS := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact GlobalCarryRecognizer.enc_cons servedSeed_ne op2HeadS op2ParentTail
  · ext <;>
      norm_num [op2ParentPubS, op2FormulaOpenRecordS, op2ParentDecS, servedInputs, encS,
        op2ParentFormula, op2ParentTail]
  · simp [SVhead, headAtom, op2ParentPubS, op2ParentDecS, servedInputs, encS, op2HeadS,
      GlobalCarryRecognizer.enc_atom, State.toNat]
  · refine ⟨?_, ?_, ?_, ?_⟩
    · ext <;>
        norm_num [op2ParentPubS, op2FormulaTailRecordS, op2ParentDecS, servedInputs, encS,
          op2ParentTail, op2ChildFormula1]
    · exact (GlobalCarryRecognizer.enc_cons servedSeed_ne op2ChildFormula1 op2ChildFormula2).symm
    · rfl
    · simp [op2ParentPubS, servedInputs]
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem op2ParentS_wf : ComputeTable.WF servedInputs op2ParentPubS where
  rlc5 := by simp [op2ParentPubS]
  size8 := by simp [op2ParentPubS]
  size11 := by simp [op2ParentPubS]

/-! ### Parent row data and its certificate -/

def op2ParentRoot : OpcodeSemantics.RootRealization servedInputs op2ParentPubS op2ParentDecS where
  subject := op2Subject
  formula := op2ParentFormula
  result := op2Result
  head := op2HeadS
  tail := op2ParentTail
  subject_realizes := rfl
  formula_realizes := rfl
  result_realizes := rfl
  head_realizes := rfl
  tail_realizes := rfl

def op2Tail : OpcodeSemantics.TailRealization servedInputs.z op2ParentDecS where
  head := op2ChildFormula1
  tail := op2ChildFormula2
  head_realizes := rfl
  tail_realizes := rfl

def op2Call1 :
    OpcodeSemantics.CallRealization servedInputs.z
      op2ParentPubS.sf1_s op2ParentPubS.sf1_f op2ParentPubS.sf1_e where
  subject := op2Subject
  formula := op2ChildFormula1
  result := op2Sf1
  subject_realizes := rfl
  formula_realizes := rfl
  result_realizes := rfl

def op2Call2 :
    OpcodeSemantics.CallRealization servedInputs.z
      op2ParentPubS.sf2_s op2ParentPubS.sf2_f op2ParentPubS.sf2_e where
  subject := op2Subject
  formula := op2ChildFormula2
  result := op2Sf2
  subject_realizes := rfl
  formula_realizes := rfl
  result_realizes := rfl

def op2Call3 :
    OpcodeSemantics.CallRealization servedInputs.z
      op2ParentPubS.sf3_s op2ParentPubS.sf3_f op2ParentPubS.sf3_e where
  subject := op2Sf1
  formula := op2Sf2
  result := op2Result
  subject_realizes := rfl
  formula_realizes := rfl
  result_realizes := rfl

/-- The ten-entry OP₂ comparison census, in the exact `requiredComparisonRoles.s2` order. -/
def op2ParentComparisons : List ComparisonUse :=
  [ { role := .opcodeHead, left := op2HeadS, right := .atom 2 },
    { role := .formulaCons, left := op2ParentFormula, right := .cell op2HeadS op2ParentTail },
    { role := .tailCons, left := op2ParentTail,
      right := .cell op2ChildFormula1 op2ChildFormula2 },
    { role := .recursiveSubject, left := op2Subject, right := op2Subject },
    { role := .recursiveFormula, left := op2ChildFormula1, right := op2ChildFormula1 },
    { role := .recursiveSubject, left := op2Subject, right := op2Subject },
    { role := .recursiveFormula, left := op2ChildFormula2, right := op2ChildFormula2 },
    { role := .recursiveSubject, left := op2Sf1, right := op2Sf1 },
    { role := .recursiveFormula, left := op2Sf2, right := op2Sf2 },
    { role := .producedResult, left := op2Result, right := op2Result } ]

/-- Row semantic data for the nonterminal `OP_2` parent: one tail realization, three recursive
calls, ten comparisons, and no size window / axis gate / served lookup (compute-only). -/
def op2ParentRowData : ComputeRowSemanticData 97 7 op2ParentRowS where
  root := op2ParentRoot
  tails := [op2Tail]
  branchTails := []
  calls :=
    [ { subjectFP := op2ParentPubS.sf1_s
        formulaFP := op2ParentPubS.sf1_f
        resultFP := op2ParentPubS.sf1_e
        realization := op2Call1 },
      { subjectFP := op2ParentPubS.sf2_s
        formulaFP := op2ParentPubS.sf2_f
        resultFP := op2ParentPubS.sf2_e
        realization := op2Call2 },
      { subjectFP := op2ParentPubS.sf3_s
        formulaFP := op2ParentPubS.sf3_f
        resultFP := op2ParentPubS.sf3_e
        realization := op2Call3 } ]
  windows := []
  axisGates := []
  tails_count := rfl
  branchTails_count := rfl
  calls_count := rfl
  windows_count := rfl
  axisGates_count := rfl
  realizedNouns := [op2Subject, op2ParentFormula, op2Result]
  subject_mem := by simp [op2ParentRoot]
  formula_mem := by simp [op2ParentRoot]
  result_mem := by simp [op2ParentRoot]
  bounded := by
    intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h | h | h <;> subst h <;>
      simp [op2Subject, op2ParentFormula, op2ParentTail, op2ChildFormula1, op2ChildFormula2,
        op2Result, FieldEmbedding.BoundedBy]
  comparisons := op2ParentComparisons
  comparison_faithful := by
    intro c hc
    simp only [op2ParentComparisons, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with h | h | h | h | h | h | h | h | h | h <;> subst h <;>
      exact pairFaithful_self _
        (by simp [op2HeadS, op2ParentFormula, op2ParentTail, op2ChildFormula1, op2ChildFormula2,
          op2Subject, op2Sf1, op2Sf2, op2Result, FieldEmbedding.BoundedBy])
  comparison_leaves := by
    intro c hc
    simp only [op2ParentComparisons, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with h | h | h | h | h | h | h | h | h | h <;> subst h <;>
      simp [ComparisonUse.LeavesBounded, op2HeadS, op2ParentFormula, op2ParentTail,
        op2ChildFormula1, op2ChildFormula2, op2Subject, op2Sf1, op2Sf2, op2Result, Noun.leaves]
  comparison_roles := rfl
  axisGate_listed := by intro gate hgate; simp at hgate
  axisGate_tail_mem := by intro gate hgate; simp at hgate
  needs :=
    { served := []
      served_count := rfl }

/-- **The `OP_2` parent certificate.**  The ten comparison premises, the three recursive-call
evaluations (`*[0 [1 [0 1]]] = [0 1]`, `*[0 [1 [1 5]]] = [1 5]`, `*[[0 1] [1 5]] = 5`), and the
accepted `Vcomp` row assemble the fan-out-3 `.s2` local opcode certificate. -/
theorem op2ParentCertificate_nonempty :
    Nonempty (LocalOpcodeCertificate 97 7 op2ParentRowData) := by
  refine ⟨.s2 op2ParentRowData 3 op2Tail op2Call1 op2Call2 op2Call3 rfl servedSeed_ne
    cast_injOn_97 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ op2ParentS_accepts⟩
  · simp [ComparisonListed, op2ParentRowData, op2ParentComparisons, op2ParentRoot, op2HeadS]
  · simp [ComparisonListed, op2ParentRowData, op2ParentComparisons, op2ParentRoot,
      op2ParentFormula]
  · simp [ComparisonListed, op2ParentRowData, op2ParentComparisons, op2ParentRoot, op2Tail,
      op2ParentTail]
  · simp [ComparisonListed, op2ParentRowData, op2ParentComparisons, op2ParentRoot, op2Call1,
      op2Subject]
  · simp [ComparisonListed, op2ParentRowData, op2ParentComparisons, op2Tail, op2Call1]
  · simp [ComparisonListed, op2ParentRowData, op2ParentComparisons, op2ParentRoot, op2Call2,
      op2Subject]
  · simp [ComparisonListed, op2ParentRowData, op2ParentComparisons, op2Tail, op2Call2]
  · simp [ComparisonListed, op2ParentRowData, op2ParentComparisons, op2Call1, op2Call3]
  · simp [ComparisonListed, op2ParentRowData, op2ParentComparisons, op2Call2, op2Call3]
  · simp [ComparisonListed, op2ParentRowData, op2ParentComparisons, op2ParentRoot, op2Call3,
      op2Result]
  · rfl
  · rfl
  · rfl

/-- **Derived Nock semantics of the nonterminal `OP_2` parent.**  A real ROM `eval`-step and a
bounded evaluation `*[0 [2 [1 [0 1]] [1 [1 5]]]] = 5`. -/
theorem op2ParentS_semantics :
    ∃ (fuel : ℕ) (successor : Verb),
      Verb.StepROM (Verb.program op2Subject op2ParentFormula) successor ∧
        FieldEmbedding.evalFBy 97 (fuel + 1) op2Subject op2ParentFormula = some op2Result := by
  obtain ⟨cert⟩ := op2ParentCertificate_nonempty
  exact cert.semantics

end

#print axioms Nock.NockVMROM.Thm54.Op2Statement.op2ParentS_accepts
#print axioms Nock.NockVMROM.Thm54.Op2Statement.op2ParentRowData
#print axioms Nock.NockVMROM.Thm54.Op2Statement.op2ParentCertificate_nonempty
#print axioms Nock.NockVMROM.Thm54.Op2Statement.op2ParentS_semantics

end Nock.NockVMROM.Thm54.Op2Statement
