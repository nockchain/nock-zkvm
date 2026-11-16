import Nock.NockVMROM.Thm54.NonterminalServedRow
import Nock.NockVMROM.Thm54.TraceGen.Op5Gen

/-!
# OP₅ nonterminal parent compute-row core (the fan-out-2 equality row)

This module builds the genuinely-new **`OP_5` parent compute row** over the shared `K97cubic`
carrier of `NonterminalServedRow`, mirroring `Op2Statement.lean` but for the `.s5` state — the
equality-test compute row (`fanoutComp.s5 = 2`, `requiredCallRealizations.s5 = 2`), with an
active tail decomposition (`tailCons`) and the distinctive `equalityOperand` comparison gate.

OP₅ is COMPUTE-ONLY / served-vacuous: `requiredServedLookups.s5 = 0`, so this row consumes no
global-carry lookup.  The two recursive calls are the concrete constant program of the OP₅
Layer-1 slice:

* `call1 = *[0 [1 3]] = 3`   (sf1, first operand),
* `call2 = *[0 [1 4]] = 4`   (sf2, second operand).

The row result is `Noun.tis sf1 sf2 = Noun.tis 3 4 = atom 1` (distinct operands).

## Scope note

Same shape as `Op2Statement.lean`: the `.s5` parent compute row, its derived semantics, and the
nine-comparison `LocalOpcodeCertificate.s5`.  The `BuildableNockExecution` / `Data` needed for
the full `op5Statement` via `SingleRootModule.statementSR` is in `TraceGen/Op5DataK3.lean`.
-/

namespace Nock.NockVMROM.Thm54.Op5Statement

open scoped Classical
open Nock Nock.Noun Nock.Walk
open ComputeTable
open Nock.NockVMROM.Thm54.SemanticTrace
open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.NockVMROM.Thm54.NonterminalServedRow
open Nock.NockVMROM.Thm54.TraceGen

noncomputable section

local instance prime97op5 : Fact (Nat.Prime 97) := ⟨by norm_num⟩
local instance char97op5 : CharP K97cubic 97 := inferInstance

/-! ## The `OP_5` parent nouns and its `.s5` public/decomposition data

The nouns are reused verbatim from the OP₅ Layer-1 slice (`TraceGen/Op5Gen.lean`). -/

/-- The `OP_5` head atom (`.atom 5`). -/
def op5HeadS : Noun := .atom 5

theorem op5ParentFormula_cons : op5ParentFormula = .cell op5HeadS op5ParentTail := rfl
theorem op5ParentTail_cons :
    op5ParentTail = .cell op5ChildFormulaB op5ChildFormulaC := rfl

/-- The formula-open record `[5 [b c]] @3`. -/
def op5FormulaOpenRecordS : MemRec K97cubic where
  root := encS op5ParentFormula
  child := encS op5ParentTail
  axis := 3
  ts := fixtureAlpha

/-- The formula-tail record `[b c] @2`. -/
def op5FormulaTailRecordS : MemRec K97cubic where
  root := encS op5ParentTail
  child := encS op5ChildFormulaB
  axis := 2
  ts := fixtureAlpha ^ 2

def op5ParentDecS : ComputeTable.Dec K97cubic where
  f_h := encS op5HeadS
  f_t := encS op5ParentTail
  f_th := encS op5ChildFormulaB
  f_tt := encS op5ChildFormulaC
  f_tth := 0
  f_ttt := 0

def op5ParentPubS : ComputeTable.Pub K97cubic where
  state := .s5
  s := encS op5Subject
  f := encS op5ParentFormula
  e := encS op5Result
  sf1_s := encS op5Subject
  sf1_f := encS op5ChildFormulaB
  sf1_e := encS op5Sf1
  sf2_s := encS op5Subject
  sf2_f := encS op5ChildFormulaC
  sf2_e := encS op5Sf2
  sf3_s := 0
  sf3_f := 0
  sf3_e := 0
  ln_prev := 1
  ln := fixtureAlpha ^ 2
  mr1 := op5FormulaOpenRecordS
  mr2 := op5FormulaTailRecordS
  mr3 := MemRec.zero

def op5ParentRowS : State × ComputeTable.DTcomp K97cubic :=
  (.s5, (servedInputs, op5ParentPubS, op5ParentDecS))

/-! ### Encoding distinctness for the equality gate -/

private theorem encS_atom3_ne_atom4 : encS op5Sf1 ≠ encS op5Sf2 := by
  intro h
  have hleaf : (3 : K97cubic) = 4 := by
    have := congrArg ComputeTable.FP.leaf h
    simpa [encS, op5Sf1, op5Sf2, GlobalCarryRecognizer.enc_atom, ComputeTable.FP.atomFP] using this
  exact absurd (cast_injOn_97 (show (3 : ℕ) ∈ Set.Iio 97 from by norm_num)
    (show (4 : ℕ) ∈ Set.Iio 97 from by norm_num) hleaf) (by norm_num)

/-- The accepted algorithmic verifier row for the `OP_5` parent: `pub.f` opens as `[5 [b c]]`, the
two live records reconstruct the formula-open and formula-tail cells, and the `.s5` evaluation block
threads `sf1/sf2` to `op5Result = Noun.tis sf1 sf2`. -/
theorem op5ParentS_accepts : Vcomp servedInputs op5ParentPubS op5ParentDecS := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact GlobalCarryRecognizer.enc_cons servedSeed_ne op5HeadS op5ParentTail
  · ext <;>
      norm_num [op5ParentPubS, op5FormulaOpenRecordS, op5ParentDecS, servedInputs, encS,
        op5ParentFormula, op5ParentTail]
  · simp [SVhead, headAtom, op5ParentPubS, op5ParentDecS, servedInputs, encS, op5HeadS,
      GlobalCarryRecognizer.enc_atom, State.toNat]
  · refine ⟨?_, ?_, ?_, ?_⟩
    · ext <;>
        norm_num [op5ParentPubS, op5FormulaTailRecordS, op5ParentDecS, servedInputs, encS,
          op5ParentTail, op5ChildFormulaB]
    · exact (GlobalCarryRecognizer.enc_cons servedSeed_ne op5ChildFormulaB op5ChildFormulaC).symm
    · rfl
    · simp [op5ParentPubS, servedInputs]
  · refine ⟨rfl, rfl, rfl, rfl, ⟨rfl, rfl, rfl⟩, ?_, ?_, ?_⟩
    · -- pub.e.size = inp.z  (i.e. servedSeed^1 = servedSeed)
      show (encS (Noun.atom 1)).size = servedSeed
      simp [encS, GlobalCarryRecognizer.enc_atom, ComputeTable.FP.atomFP]
    · -- pub.e.dyck = 0
      show (encS (Noun.atom 1)).dyck = (0 : K97cubic)
      simp [encS, GlobalCarryRecognizer.enc_atom, ComputeTable.FP.atomFP]
    · -- pub.e.leaf = FP.eqOp pub.sf1_e pub.sf2_e
      show (encS (Noun.atom 1)).leaf = ComputeTable.FP.eqOp (encS op5Sf1) (encS op5Sf2)
      have heq : ComputeTable.FP.eqOp (encS op5Sf1) (encS op5Sf2) = 1 := by
        unfold ComputeTable.FP.eqOp; exact if_neg encS_atom3_ne_atom4
      rw [heq]
      simp [encS, GlobalCarryRecognizer.enc_atom, ComputeTable.FP.atomFP]

/-! ### Parent row data and its certificate -/

def op5ParentRoot : OpcodeSemantics.RootRealization servedInputs op5ParentPubS op5ParentDecS where
  subject := op5Subject
  formula := op5ParentFormula
  result := op5Result
  head := op5HeadS
  tail := op5ParentTail
  subject_realizes := rfl
  formula_realizes := rfl
  result_realizes := rfl
  head_realizes := rfl
  tail_realizes := rfl

def op5Tail : OpcodeSemantics.TailRealization servedInputs.z op5ParentDecS where
  head := op5ChildFormulaB
  tail := op5ChildFormulaC
  head_realizes := rfl
  tail_realizes := rfl

def op5Call1 :
    OpcodeSemantics.CallRealization servedInputs.z
      op5ParentPubS.sf1_s op5ParentPubS.sf1_f op5ParentPubS.sf1_e where
  subject := op5Subject
  formula := op5ChildFormulaB
  result := op5Sf1
  subject_realizes := rfl
  formula_realizes := rfl
  result_realizes := rfl

def op5Call2 :
    OpcodeSemantics.CallRealization servedInputs.z
      op5ParentPubS.sf2_s op5ParentPubS.sf2_f op5ParentPubS.sf2_e where
  subject := op5Subject
  formula := op5ChildFormulaC
  result := op5Sf2
  subject_realizes := rfl
  formula_realizes := rfl
  result_realizes := rfl

/-- The nine-entry OP₅ comparison census, in the exact `requiredComparisonRoles.s5` order. -/
def op5ParentComparisons : List ComparisonUse :=
  [ { role := .opcodeHead, left := op5HeadS, right := .atom 5 },
    { role := .formulaCons, left := op5ParentFormula, right := .cell op5HeadS op5ParentTail },
    { role := .tailCons, left := op5ParentTail,
      right := .cell op5ChildFormulaB op5ChildFormulaC },
    { role := .recursiveSubject, left := op5Subject, right := op5Subject },
    { role := .recursiveFormula, left := op5ChildFormulaB, right := op5ChildFormulaB },
    { role := .recursiveSubject, left := op5Subject, right := op5Subject },
    { role := .recursiveFormula, left := op5ChildFormulaC, right := op5ChildFormulaC },
    { role := .equalityOperand, left := op5Sf1, right := op5Sf2 },
    { role := .producedResult, left := op5Result, right := op5Result } ]

/-- The NPR fingerprints of atoms `3` and `4` differ at any seed (their leaf polynomials are
distinct constants `3 ≠ 4` in char 97). -/
private theorem op5_sf_fn_ne :
    NPR.fn op5Sf1 (servedSeed : K97cubic) ≠ NPR.fn op5Sf2 servedSeed := by
  intro h
  apply encS_atom3_ne_atom4
  show GlobalCarryRecognizer.enc servedSeed op5Sf1 = GlobalCarryRecognizer.enc servedSeed op5Sf2
  simp only [GlobalCarryRecognizer.enc_eq_fn, h]

/-- Pair-faithfulness for the equality-operand comparison: atoms `3` and `4` are separated at any
seed because their leaf polynomials are distinct constants. -/
private theorem op5_eq_operands_pairFaithful :
    OpcodeSemantics.PairFaithful servedSeed 97 op5Sf1 op5Sf2 where
  separates := fun _ => op5_sf_fn_ne
  left_bounded := by simp [op5Sf1]
  right_bounded := by simp [op5Sf2]

/-- Row semantic data for the nonterminal `OP_5` parent: one tail realization, two recursive
calls, nine comparisons, and no size window / axis gate / served lookup (compute-only). -/
def op5ParentRowData : ComputeRowSemanticData 97 5 op5ParentRowS where
  root := op5ParentRoot
  tails := [op5Tail]
  branchTails := []
  calls :=
    [ { subjectFP := op5ParentPubS.sf1_s
        formulaFP := op5ParentPubS.sf1_f
        resultFP := op5ParentPubS.sf1_e
        realization := op5Call1 },
      { subjectFP := op5ParentPubS.sf2_s
        formulaFP := op5ParentPubS.sf2_f
        resultFP := op5ParentPubS.sf2_e
        realization := op5Call2 } ]
  windows := []
  axisGates := []
  tails_count := rfl
  branchTails_count := rfl
  calls_count := rfl
  windows_count := rfl
  axisGates_count := rfl
  realizedNouns := [op5Subject, op5ParentFormula, op5Result]
  subject_mem := by simp [op5ParentRoot]
  formula_mem := by simp [op5ParentRoot]
  result_mem := by simp [op5ParentRoot]
  bounded := by
    intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h | h | h <;> subst h
    · simp [op5Subject]
    · simp [op5ParentFormula, op5ParentTail, op5ChildFormulaB, op5ChildFormulaC,
        FieldEmbedding.BoundedBy]
    · show FieldEmbedding.BoundedBy 97 (Noun.atom 1)
      simp [FieldEmbedding.BoundedBy]
  comparisons := op5ParentComparisons
  comparison_faithful := by
    intro c hc
    simp only [op5ParentComparisons, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with h | h | h | h | h | h | h | h | h <;> subst h
    · exact pairFaithful_self _
        (by simp [op5HeadS])
    · exact pairFaithful_self _
        (by simp [op5ParentFormula, op5ParentTail, op5ChildFormulaB, op5ChildFormulaC])
    · exact pairFaithful_self _
        (by simp [op5ParentTail, op5ChildFormulaB, op5ChildFormulaC, FieldEmbedding.BoundedBy])
    · exact pairFaithful_self _
        (by simp [op5Subject])
    · exact pairFaithful_self _
        (by simp [op5ChildFormulaB])
    · exact pairFaithful_self _
        (by simp [op5Subject])
    · exact pairFaithful_self _
        (by simp [op5ChildFormulaC, FieldEmbedding.BoundedBy])
    · exact op5_eq_operands_pairFaithful
    · exact pairFaithful_self _
        (show FieldEmbedding.BoundedBy 97 (Noun.atom 1) from by simp [FieldEmbedding.BoundedBy])
  comparison_leaves := by
    intro c hc
    simp only [op5ParentComparisons, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with h | h | h | h | h | h | h | h | h <;> subst h <;>
      simp [ComparisonUse.LeavesBounded, op5HeadS, op5ParentFormula, op5ParentTail,
        op5ChildFormulaB, op5ChildFormulaC, op5Subject, op5Sf1, op5Sf2,
        show op5Result = Noun.atom 1 from rfl, Noun.leaves]
  comparison_roles := rfl
  axisGate_listed := by intro gate hgate; simp at hgate
  axisGate_tail_mem := by intro gate hgate; simp at hgate
  needs :=
    { served := []
      served_count := rfl }

/-- **The `OP_5` parent certificate.**  The nine comparison premises, the two recursive-call
evaluations (`*[0 [1 3]] = 3`, `*[0 [1 4]] = 4`), and the accepted `Vcomp` row assemble
the fan-out-2 `.s5` local opcode certificate. -/
theorem op5ParentCertificate_nonempty :
    Nonempty (LocalOpcodeCertificate 97 5 op5ParentRowData) := by
  refine ⟨.s5 op5ParentRowData 1 op5Tail op5Call1 op5Call2 rfl servedSeed_ne
    cast_injOn_97 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ op5ParentS_accepts⟩
  · simp [ComparisonListed, op5ParentRowData, op5ParentComparisons, op5ParentRoot, op5HeadS]
  · simp [ComparisonListed, op5ParentRowData, op5ParentComparisons, op5ParentRoot,
      op5ParentFormula]
  · simp [ComparisonListed, op5ParentRowData, op5ParentComparisons, op5ParentRoot, op5Tail,
      op5ParentTail]
  · simp [ComparisonListed, op5ParentRowData, op5ParentComparisons, op5ParentRoot, op5Call1,
      op5Subject]
  · simp [ComparisonListed, op5ParentRowData, op5ParentComparisons, op5Tail, op5Call1]
  · simp [ComparisonListed, op5ParentRowData, op5ParentComparisons, op5ParentRoot, op5Call2,
      op5Subject]
  · simp [ComparisonListed, op5ParentRowData, op5ParentComparisons, op5Tail, op5Call2]
  · simp [ComparisonListed, op5ParentRowData, op5ParentComparisons, op5Call1, op5Call2]
  · simp [ComparisonListed, op5ParentRowData, op5ParentComparisons, op5ParentRoot, op5Call1,
      op5Call2, op5Result]
  · rfl
  · rfl

/-- **Derived Nock semantics of the nonterminal `OP_5` parent.**  A real ROM `eval`-step and a
bounded evaluation `*[0 [5 [1 3] [1 4]]] = 1`. -/
theorem op5ParentS_semantics :
    ∃ (fuel : ℕ) (successor : Verb),
      Verb.StepROM (Verb.program op5Subject op5ParentFormula) successor ∧
        FieldEmbedding.evalFBy 97 (fuel + 1) op5Subject op5ParentFormula = some op5Result := by
  obtain ⟨cert⟩ := op5ParentCertificate_nonempty
  exact cert.semantics

end

#print axioms Nock.NockVMROM.Thm54.Op5Statement.op5ParentS_accepts
#print axioms Nock.NockVMROM.Thm54.Op5Statement.op5ParentRowData
#print axioms Nock.NockVMROM.Thm54.Op5Statement.op5ParentCertificate_nonempty
#print axioms Nock.NockVMROM.Thm54.Op5Statement.op5ParentS_semantics

end Nock.NockVMROM.Thm54.Op5Statement
