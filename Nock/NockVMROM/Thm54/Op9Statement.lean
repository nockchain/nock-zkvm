import Nock.NockVMROM.Thm54.NonterminalServedRow
import Nock.NockVMROM.Thm54.TraceGen.Op9Gen
import Nock.NockVMROM.Thm54.RecognizerCompleteness

/-!
# OP₉ nonterminal parent compute-row core (the fan-out-2 `invoke` row)

This module builds the genuinely-new **`OP_9` parent compute row** over the shared `K97cubic`
carrier of `NonterminalServedRow`, mirroring `Op2Statement.lean` but for the `.s9` state — the
invoke row (`fanoutComp .s9 = 2`, `requiredCallRealizations .s9 = 2`), the first row with a
non-vacuous served lookup (`requiredServedLookups .s9 = 1`), an axis-atom gate
(`requiredAxisAtomGates .s9 = 1`), and a computed-core second child.

OP₉ is the first opcode with a NON-VACUOUS served side: `requiredServedLookups .s9 = 1`, so
`needs.served` has one entry (the arm-fetch `ServedNounLookup`).  The arm-fetch record
`mr3 = ⟨core, arm, 2⟩` is rooted at the COMPUTED core `sf_evaluation_1` and its axis is the
(arbitrary) atom `b = 2` — the non-vacuous served lookup.

The two recursive calls are the concrete invoke program of the OP₉ Layer-1 slice
(`TraceGen/Op9Gen.lean`, `*[0 [9 [2 [1 [[1 7] [1 9]]]]]] = 7`):

* `call1 = *[0 [1 [[1 7] [1 9]]]] = [[1 7] [1 9]]`   (core),
* `call2 = *[[[1 7] [1 9]] [1 7]] = 7`                (arm invocation on computed core).

Everything here is compute-side: an accepted `Vcomp` row whose `.s9`
evaluation block threads core/arm/result and whose three live memory records are the
formula-open `[9 [b c]] @3`, the formula-tail `[b c] @2`, and the ARM FETCH `⟨core, arm, b⟩`
records; its full `ComputeRowSemanticData`, its eight-comparison
`LocalOpcodeCertificate.s9`, and therefore its derived Nock semantics (a real ROM `invoke`-step +
a bounded `evalFBy` producing `op9Result`).
-/

namespace Nock.NockVMROM.Thm54.Op9Statement

open scoped Classical
open Nock Nock.Noun Nock.Walk
open ComputeTable
open Nock.NockVMROM.Thm54.SemanticTrace
open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.NockVMROM.Thm54.NonterminalServedRow
open Nock.NockVMROM.Thm54.TraceGen

noncomputable section

local instance prime97op9 : Fact (Nat.Prime 97) := ⟨by norm_num⟩
local instance char97op9 : CharP K97cubic 97 := inferInstance

/-! ## The `OP_9` parent nouns and its `.s9` public/decomposition data

The nouns are reused verbatim from the OP₉ Layer-1 slice (`TraceGen/Op9Gen.lean`). -/

/-- The `OP_9` head atom (`.atom 9`). -/
def op9HeadS : Noun := .atom 9

theorem op9ParentFormula_cons : op9ParentFormula = .cell op9HeadS op9ParentTail := rfl
theorem op9ParentTail_cons : op9ParentTail = .cell op9AxisAtom op9CoreFormula := rfl

/-- The formula-open record `[9 [b c]] @3` (`mr1`). -/
def op9FormulaOpenRecordS : MemRec K97cubic where
  root := encS op9ParentFormula
  child := encS op9ParentTail
  axis := 3
  ts := fixtureAlpha

/-- The formula-tail record `[b c] @2` (`mr2`, the axis-2 descent). -/
def op9FormulaTailRecordS : MemRec K97cubic where
  root := encS op9ParentTail
  child := encS op9AxisAtom
  axis := 2
  ts := fixtureAlpha ^ 2

/-- The arm-fetch record `⟨core, arm, 2⟩` (`mr3`). -/
def op9ArmFetchRecordS : MemRec K97cubic where
  root := encS op9CoreNoun
  child := encS op9Arm
  axis := 2
  ts := fixtureAlpha ^ 3

def op9ParentDecS : ComputeTable.Dec K97cubic where
  f_h := encS op9HeadS
  f_t := encS op9ParentTail
  f_th := encS op9AxisAtom
  f_tt := encS op9CoreFormula
  f_tth := 0
  f_ttt := 0

def op9ParentPubS : ComputeTable.Pub K97cubic where
  state := .s9
  s := encS op9Subject
  f := encS op9ParentFormula
  e := encS op9Result
  sf1_s := encS op9Subject
  sf1_f := encS op9CoreFormula
  sf1_e := encS op9CoreNoun
  sf2_s := encS op9CoreNoun
  sf2_f := encS op9Arm
  sf2_e := encS op9Result
  sf3_s := 0
  sf3_f := 0
  sf3_e := 0
  ln_prev := 1
  ln := fixtureAlpha ^ 3
  mr1 := op9FormulaOpenRecordS
  mr2 := op9FormulaTailRecordS
  mr3 := op9ArmFetchRecordS

def op9ParentRowS : State × ComputeTable.DTcomp K97cubic :=
  (.s9, (servedInputs, op9ParentPubS, op9ParentDecS))

/-- The accepted algorithmic verifier row for the `OP_9` parent: `pub.f` opens as `[9 [b c]]`, the
three live records reconstruct the formula-open, formula-tail, and arm-fetch cells, and the `.s9`
evaluation block threads core/arm/result to `op9Result`. -/
theorem op9ParentS_accepts : Vcomp servedInputs op9ParentPubS op9ParentDecS := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact GlobalCarryRecognizer.enc_cons servedSeed_ne op9HeadS op9ParentTail
  · ext <;>
      norm_num [op9ParentPubS, op9FormulaOpenRecordS, op9ParentDecS, servedInputs, encS,
        op9ParentFormula, op9ParentTail]
  · simp [SVhead, headAtom, op9ParentPubS, op9ParentDecS, servedInputs, encS, op9HeadS,
      GlobalCarryRecognizer.enc_atom, State.toNat]
  · refine ⟨?_, ?_, ?_, ?_⟩
    · ext <;>
        norm_num [op9ParentPubS, op9FormulaTailRecordS, op9ParentDecS, servedInputs, encS,
          op9ParentTail, op9AxisAtom]
    · exact (GlobalCarryRecognizer.enc_cons servedSeed_ne op9AxisAtom op9CoreFormula).symm
    · ext <;>
        simp [op9ParentPubS, op9ArmFetchRecordS, op9ParentDecS, servedInputs, encS,
          op9AxisAtom, GlobalCarryRecognizer.enc_atom, ComputeTable.FP.atomFP]
    · simp [op9ParentPubS, servedInputs]
  · refine ⟨rfl, rfl, rfl, rfl, ⟨rfl, rfl, rfl⟩, ?_, ?_⟩
    · simp [op9ParentDecS, encS, op9AxisAtom, servedInputs,
        GlobalCarryRecognizer.enc_atom, ComputeTable.FP.atomFP]
    · simp [op9ParentDecS, encS, op9AxisAtom,
        GlobalCarryRecognizer.enc_atom, ComputeTable.FP.atomFP]

theorem op9ParentS_wf : ComputeTable.WF servedInputs op9ParentPubS where
  rlc5 := by simp [op9ParentPubS]
  size8 := by simp [op9ParentPubS]
  size11 := by simp [op9ParentPubS]

/-! ### Parent row data and its certificate -/

def op9ParentRoot : OpcodeSemantics.RootRealization servedInputs op9ParentPubS op9ParentDecS where
  subject := op9Subject
  formula := op9ParentFormula
  result := op9Result
  head := op9HeadS
  tail := op9ParentTail
  subject_realizes := rfl
  formula_realizes := rfl
  result_realizes := rfl
  head_realizes := rfl
  tail_realizes := rfl

def op9Tail : OpcodeSemantics.TailRealization servedInputs.z op9ParentDecS where
  head := op9AxisAtom
  tail := op9CoreFormula
  head_realizes := rfl
  tail_realizes := rfl

def op9Call1 :
    OpcodeSemantics.CallRealization servedInputs.z
      op9ParentPubS.sf1_s op9ParentPubS.sf1_f op9ParentPubS.sf1_e where
  subject := op9Subject
  formula := op9CoreFormula
  result := op9CoreNoun
  subject_realizes := rfl
  formula_realizes := rfl
  result_realizes := rfl

def op9Call2 :
    OpcodeSemantics.CallRealization servedInputs.z
      op9ParentPubS.sf2_s op9ParentPubS.sf2_f op9ParentPubS.sf2_e where
  subject := op9CoreNoun
  formula := op9Arm
  result := op9Result
  subject_realizes := rfl
  formula_realizes := rfl
  result_realizes := rfl

/-- The eight-entry OP₉ comparison census, in the exact `requiredComparisonRoles .s9` order. -/
def op9ParentComparisons : List ComparisonUse :=
  [ { role := .opcodeHead, left := op9HeadS, right := .atom 9 },
    { role := .formulaCons, left := op9ParentFormula, right := .cell op9HeadS op9ParentTail },
    { role := .tailCons, left := op9ParentTail,
      right := .cell op9AxisAtom op9CoreFormula },
    { role := .axisAtom, left := op9AxisAtom, right := .atom 2 },
    { role := .recursiveSubject, left := op9Subject, right := op9Subject },
    { role := .recursiveFormula, left := op9CoreFormula, right := op9CoreFormula },
    { role := .recursiveSubject, left := op9CoreNoun, right := op9CoreNoun },
    { role := .producedResult, left := op9Result, right := op9Result } ]

/-- The OP₉ axis gate: the axis atom `b = 2` is verified by PairFaithful against `.atom 2`. -/
def op9AxisGate : Σ tail : OpcodeSemantics.TailRealization servedInputs.z op9ParentDecS,
    AxisAtomComparisonCertificate servedInputs.z 97 op9ParentDecS tail where
  fst := op9Tail
  snd :=
    { axis := 2
      faithful := pairFaithful_self (.atom 2)
        (by simp [FieldEmbedding.BoundedBy]) }

/-- The served arm-fetch lookup: `slot 2 core = arm` served on the computed core. -/
def op9ServedLookup : ServedNounLookup servedInputs.z where
  record := op9ArmFetchRecordS
  root := op9CoreNoun
  axis := 2
  child := op9Arm
  realization :=
    { root_realizes := rfl
      child_realizes := rfl
      axis_realizes := by norm_num [op9ArmFetchRecordS] }
  served := Nock.NockVMROM.Thm54.RecognizerCompleteness.servedLookup_of_slot op9_slot

/-- Row semantic data for the nonterminal `OP_9` parent: one tail realization, two recursive
calls, eight comparisons, one axis gate, one served lookup, and no size window. -/
def op9ParentRowData : ComputeRowSemanticData 97 7 op9ParentRowS where
  root := op9ParentRoot
  tails := [op9Tail]
  branchTails := []
  calls :=
    [ { subjectFP := op9ParentPubS.sf1_s
        formulaFP := op9ParentPubS.sf1_f
        resultFP := op9ParentPubS.sf1_e
        realization := op9Call1 },
      { subjectFP := op9ParentPubS.sf2_s
        formulaFP := op9ParentPubS.sf2_f
        resultFP := op9ParentPubS.sf2_e
        realization := op9Call2 } ]
  windows := []
  axisGates := [op9AxisGate]
  tails_count := rfl
  branchTails_count := rfl
  calls_count := rfl
  windows_count := rfl
  axisGates_count := rfl
  realizedNouns := [op9Subject, op9ParentFormula, op9Result]
  subject_mem := by simp [op9ParentRoot]
  formula_mem := by simp [op9ParentRoot]
  result_mem := by simp [op9ParentRoot]
  bounded := by
    intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h | h | h <;> subst h <;>
      simp [op9Subject, op9ParentFormula, op9ParentTail, op9AxisAtom, op9CoreFormula,
        op9CoreNoun, op9Result, FieldEmbedding.BoundedBy]
  comparisons := op9ParentComparisons
  comparison_faithful := by
    intro c hc
    simp only [op9ParentComparisons, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with h | h | h | h | h | h | h | h <;> subst h <;>
      exact pairFaithful_self _
        (by       simp [op9HeadS, op9ParentFormula, op9ParentTail, op9AxisAtom, op9CoreFormula,
            op9CoreNoun, op9Subject, op9Result, FieldEmbedding.BoundedBy])
  comparison_leaves := by
    intro c hc
    simp only [op9ParentComparisons, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with h | h | h | h | h | h | h | h <;> subst h <;>
      simp [ComparisonUse.LeavesBounded, op9HeadS, op9ParentFormula, op9ParentTail,
        op9AxisAtom, op9CoreFormula, op9CoreNoun, op9Subject, op9Result, Noun.leaves]
  comparison_roles := rfl
  axisGate_listed := by
    intro gate hgate
    replace hgate := List.mem_singleton.mp hgate
    subst hgate
    simp [op9ParentComparisons, op9AxisGate, op9Tail, op9AxisAtom]
  axisGate_tail_mem := by
    intro gate hgate
    replace hgate := List.mem_singleton.mp hgate
    subst hgate
    exact List.mem_singleton_self _
  needs :=
    { served := [op9ServedLookup]
      served_count := rfl }

/-- **The `OP_9` parent certificate.**  The eight comparison premises, the two recursive-call
evaluations (`*[0 [1 [[1 7] [1 9]]]] = [[1 7] [1 9]]`, `*[[[1 7] [1 9]] [1 7]] = 7`), the
arm-fetch served lookup, and the accepted `Vcomp` row assemble the fan-out-2 `.s9` local opcode
certificate. -/
theorem op9ParentCertificate_nonempty :
    Nonempty (LocalOpcodeCertificate 97 7 op9ParentRowData) := by
  refine ⟨.s9 op9ParentRowData 3 2 op9Tail op9Call1 op9Call2 rfl servedSeed_ne
    cast_injOn_97 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ op9ParentS_accepts⟩
  · simp [ComparisonListed, op9ParentRowData, op9ParentComparisons, op9ParentRoot, op9HeadS]
  · simp [ComparisonListed, op9ParentRowData, op9ParentComparisons, op9ParentRoot,
      op9ParentFormula]
  · simp [ComparisonListed, op9ParentRowData, op9ParentComparisons, op9ParentRoot, op9Tail,
      op9ParentTail]
  · simp [ComparisonListed, op9ParentRowData, op9ParentComparisons, op9Tail, op9AxisAtom]
  · simp [ComparisonListed, op9ParentRowData, op9ParentComparisons, op9ParentRoot, op9Call1,
      op9Subject]
  · simp [ComparisonListed, op9ParentRowData, op9ParentComparisons, op9Tail, op9Call1,
      op9CoreFormula]
  · simp [ComparisonListed, op9ParentRowData, op9ParentComparisons, op9Call1, op9Call2,
      op9CoreNoun]
  · simp [ComparisonListed, op9ParentRowData, op9ParentComparisons, op9ParentRoot, op9Call2,
      op9Result]
  · exact op9ServedLookup.realization
  · exact op9ServedLookup.served
  · rfl
  · rfl

/-- **Derived Nock semantics of the nonterminal `OP_9` parent.**  A real ROM `invoke`-step and a
bounded evaluation `*[0 [9 [2 [1 [[1 7] [1 9]]]]]] = 7`. -/
theorem op9ParentS_semantics :
    ∃ (fuel : ℕ) (successor : Verb),
      Verb.StepROM (Verb.program op9Subject op9ParentFormula) successor ∧
        FieldEmbedding.evalFBy 97 (fuel + 1) op9Subject op9ParentFormula = some op9Result := by
  obtain ⟨cert⟩ := op9ParentCertificate_nonempty
  exact cert.semantics

end

#print axioms Nock.NockVMROM.Thm54.Op9Statement.op9ParentS_accepts
#print axioms Nock.NockVMROM.Thm54.Op9Statement.op9ParentRowData
#print axioms Nock.NockVMROM.Thm54.Op9Statement.op9ParentCertificate_nonempty
#print axioms Nock.NockVMROM.Thm54.Op9Statement.op9ParentS_semantics

end Nock.NockVMROM.Thm54.Op9Statement
