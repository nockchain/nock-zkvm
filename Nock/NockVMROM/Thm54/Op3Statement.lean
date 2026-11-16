import Nock.NockVMROM.Thm54.NonterminalServedRow

/-!
# OP₃ nonterminal parent compute-row core (the `wut` produced-result gate)

This module builds the genuinely-new **`OP_3` parent compute row** on top of the shared OP₀ served
child of `NonterminalServedRow`, mirroring the `OP_4` parent block there but with the `.s3`
produced-result gate `?` in place of `OP_4`'s
increment `incMod`.

The recursive call is reused verbatim from the OP₀ slice: `*[subjectS [0 2]] = /[2 subjectS] =
resultS`. The parent formula is `[3 [0 2]]`; the produced result is
`?(resultS) = op3ParentResultS` (`resultS =.atom 7` is an atom, so `?` returns `.atom 1`).

Everything here is compute-side: an accepted `Vcomp` row whose `.s3`
evaluation block is discharged through `OpcodeSemantics.enc_wut_eq`, its full
`ComputeRowSemanticData`, its `LocalOpcodeCertificate.s3`, and therefore its derived Nock
semantics (a real ROM `?`-step + a bounded `evalFBy` producing `?(resultS)`).

## Scope note (correcting `Op3Gen.lean:25-34` and the Layer-2 plan)

That is accurate for the *compute*
side (this file) but NOT for the memory side: the served-memory forest's **root `A`** in
`MultiRootServedFixture.lean` is rooted at `encS parentFormulaS` and threads `parentRecordS`
(`⟨encS parentFormulaS, encS formulaS, 3, α⟩`) through its nine rows, census distinctness, NMR
bridge, and every downstream reassembly.  Because the parent formula head atom changes
(`.atom 4 →.atom 3`), `encS parentFormulaS` changes, so root `A` and the whole
`MultiRootServedFixture` / `MultiRootHonestCommitment` reassembly (~3300 lines) must be re-derived
for `.s3` before an `op3Execution : BuildableNockExecution` and `op3Statement` can be assembled.
This file lands the genuinely-new hard site — the `.s3`/`wut` parent compute row and its derived
semantics — as a coherent, kernel-clean partial; the memory-forest clone is the remaining work.
-/

namespace Nock.NockVMROM.Thm54.Op3Statement

open scoped Classical
open Nock Nock.Noun Nock.Walk
open ComputeTable
open Nock.NockVMROM.Thm54.SemanticTrace
open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.NockVMROM.Thm54.NonterminalServedRow

noncomputable section

local instance prime97'' : Fact (Nat.Prime 97) := ⟨by norm_num⟩
local instance char97'' : CharP K97cubic 97 := inferInstance

/-! ## The `OP_3` parent whose one recursive call is the served `OP_0` row

`OP_3` applies the cell test `?` to the result of its one recursive call.  The call
is the OP₀ served row of `NonterminalServedRow`, so the parent's derived Nock semantics genuinely
consume a served global-carry lookup. -/

/-- The `OP_3` head atom (`.atom 3`), vs `OP_4`'s `.atom 4`. -/
def op3ParentHeadS : Noun := .atom 3
def op3ParentFormulaS : Noun := .cell op3ParentHeadS formulaS
/-- The produced result: `?(resultS)`.  `resultS =.atom 7` is an atom, so `? =.atom 1`. -/
def op3ParentResultS : Noun := Noun.wut resultS

theorem op3ParentFormulaS_cons : op3ParentFormulaS = .cell op3ParentHeadS formulaS := rfl

theorem op3_wut_gate : Noun.wut resultS = op3ParentResultS := rfl
theorem op3ParentResultS_atom : op3ParentResultS = Noun.atom 1 := rfl

def op3ParentRecordS : MemRec K97cubic where
  root := encS op3ParentFormulaS
  child := encS formulaS
  axis := 3
  ts := fixtureAlpha

def op3ParentDecS : ComputeTable.Dec K97cubic where
  f_h := encS op3ParentHeadS
  f_t := encS formulaS
  f_th := 0
  f_tt := 0
  f_tth := 0
  f_ttt := 0

def op3ParentPubS : ComputeTable.Pub K97cubic where
  state := .s3
  s := encS subjectS
  f := encS op3ParentFormulaS
  e := encS op3ParentResultS
  sf1_s := encS subjectS
  sf1_f := encS formulaS
  sf1_e := encS resultS
  sf2_s := 0
  sf2_f := 0
  sf2_e := 0
  sf3_s := 0
  sf3_f := 0
  sf3_e := 0
  ln_prev := 1
  ln := fixtureAlpha
  mr1 := op3ParentRecordS
  mr2 := MemRec.zero
  mr3 := MemRec.zero

def op3ParentRowS : State × ComputeTable.DTcomp K97cubic :=
  (.s3, (servedInputs, op3ParentPubS, op3ParentDecS))

/-- The `.s3` evaluation-block fingerprint bridge: `enc z (?value) = atomFP z (qm z (enc z value))`
at the served seed, for `value = resultS`. -/
theorem enc_op3ParentResultS :
    encS op3ParentResultS
      = FP.atomFP servedSeed (FP.qm servedSeed (encS resultS)) := by
  show GlobalCarryRecognizer.enc servedSeed (Noun.wut resultS) = _
  exact OpcodeSemantics.enc_wut_eq (servedSeed_window_atom 7)

theorem op3ParentS_accepts : Vcomp servedInputs op3ParentPubS op3ParentDecS := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact GlobalCarryRecognizer.enc_cons servedSeed_ne op3ParentHeadS formulaS
  · ext <;>
      norm_num [op3ParentPubS, op3ParentRecordS, op3ParentDecS, servedInputs, encS,
        op3ParentFormulaS]
  · simp [SVhead, headAtom, op3ParentPubS, op3ParentDecS, servedInputs, encS, op3ParentHeadS,
      GlobalCarryRecognizer.enc_atom, State.toNat]
  · norm_num [memBlk, op3ParentPubS, servedInputs, MemRec.zero]
  · refine ⟨rfl, rfl, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ?_, ?_, ?_⟩
    · show (encS op3ParentResultS).size = servedInputs.z
      rw [enc_op3ParentResultS]; rfl
    · show (encS op3ParentResultS).dyck = 0
      rw [enc_op3ParentResultS]; rfl
    · show (encS op3ParentResultS).leaf = FP.qm servedInputs.z (encS resultS)
      rw [enc_op3ParentResultS]; rfl

theorem op3ParentS_wf : ComputeTable.WF servedInputs op3ParentPubS where
  rlc5 := by simp [op3ParentPubS]
  size8 := by simp [op3ParentPubS]
  size11 := by simp [op3ParentPubS]

/-- The compute-line handoff: the parent's `ln` is the served row's `ln_prev`. -/
theorem op3_compute_line_handoffS : op3ParentPubS.ln = servedPub.ln_prev := rfl

def op3ParentOutS : Fin 3 → Option (State × ComputeTable.DTcomp K97cubic)
  | 0 => some servedRow
  | 1 => none
  | 2 => none

theorem op3ParentRowS_accepts : ComputeTable.Fcomp op3ParentRowS op3ParentOutS := by
  refine ⟨rfl, op3ParentS_accepts, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [op3ParentRowS, op3ParentOutS, ComputeTable.fanoutComp]
  · intro i hi
    fin_cases i
    · simp [op3ParentOutS, ComputeTable.sfTriple,
        op3ParentRowS, servedRow, op3ParentPubS, servedPub]
    · simp [op3ParentRowS, ComputeTable.fanoutComp] at hi
    · simp [op3ParentRowS, ComputeTable.fanoutComp] at hi

/-- The two-row nonterminal compute tree: an `OP_3` root with the served `OP_0` row as its one
child. -/
def op3ComputeTreeS : NTree (State × ComputeTable.DTcomp K97cubic) :=
  .node op3ParentRowS [.node servedRow []]

theorem op3ComputeTreeS_rvt : RVT (ComputeTable.Fcomp (K := K97cubic)) op3ComputeTreeS := by
  unfold op3ComputeTreeS RVT
  refine ⟨?_, ?_, ?_⟩
  · rw [show (fun i : Fin 3 => (NTree.node op3ParentRowS [.node servedRow []]).childLabel i) =
        op3ParentOutS by
      funext i
      fin_cases i <;> rfl]
    exact op3ParentRowS_accepts
  · intro t ht
    simp only [List.mem_singleton] at ht
    subst t
    unfold RVT
    exact ⟨servedRow_accepts, by simp, ⟨fun _ => servedRow_accepts, fun _ => rfl⟩⟩
  · simp [NTree.isLeaf, ComputeTable.Fcomp, op3ParentRowS, ComputeTable.fanoutComp]

/-- The root is genuinely nonterminal and its single successor is the served `OP_0` row. -/
theorem op3ParentS_is_genuinely_nonterminal :
    op3ParentPubS.state = .s3 ∧ ComputeTable.fanoutComp op3ParentPubS.state = 1 ∧
      op3ParentOutS 0 = some servedRow ∧ servedRow.1 = State.s0 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ### Parent row data and its certificate -/

def op3ParentRoot : OpcodeSemantics.RootRealization servedInputs op3ParentPubS op3ParentDecS where
  subject := subjectS
  formula := op3ParentFormulaS
  result := op3ParentResultS
  head := op3ParentHeadS
  tail := formulaS
  subject_realizes := rfl
  formula_realizes := rfl
  result_realizes := rfl
  head_realizes := rfl
  tail_realizes := rfl

def op3ParentCall :
    OpcodeSemantics.CallRealization servedSeed
      op3ParentPubS.sf1_s op3ParentPubS.sf1_f op3ParentPubS.sf1_e where
  subject := subjectS
  formula := formulaS
  result := resultS
  subject_realizes := rfl
  formula_realizes := rfl
  result_realizes := rfl

def op3ParentComparisons : List ComparisonUse :=
  [ { role := .opcodeHead, left := op3ParentHeadS, right := .atom 3 },
    { role := .formulaCons, left := op3ParentFormulaS, right := .cell op3ParentHeadS formulaS },
    { role := .recursiveSubject, left := subjectS, right := subjectS },
    { role := .recursiveFormula, left := formulaS, right := formulaS },
    { role := .producedResult, left := op3ParentResultS, right := op3ParentResultS } ]

/-- Row semantic data for the nonterminal `OP_3` parent, including the bounded power window that
the served `resultS =.atom 7` supplies. -/
def op3ParentRowData : ComputeRowSemanticData 97 3 op3ParentRowS where
  root := op3ParentRoot
  tails := []
  branchTails := []
  calls :=
    [ { subjectFP := op3ParentPubS.sf1_s
        formulaFP := op3ParentPubS.sf1_f
        resultFP := op3ParentPubS.sf1_e
        realization := op3ParentCall } ]
  windows := [{ noun := resultS, window := servedSeed_window_atom 7 }]
  axisGates := []
  tails_count := rfl
  branchTails_count := rfl
  calls_count := rfl
  windows_count := rfl
  axisGates_count := rfl
  realizedNouns := [subjectS, op3ParentFormulaS, op3ParentResultS]
  subject_mem := by simp [op3ParentRoot]
  formula_mem := by simp [op3ParentRoot]
  result_mem := by simp [op3ParentRoot]
  bounded := by
    intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h | h | h <;> subst h <;>
      simp [subjectS, op3ParentFormulaS, op3ParentResultS, resultS, Noun.wut, op3ParentHeadS,
        formulaS, headS, tailS, FieldEmbedding.BoundedBy]
  comparisons := op3ParentComparisons
  comparison_faithful := by
    intro c hc
    simp only [op3ParentComparisons, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with h | h | h | h | h <;> subst h
    · exact pairFaithful_self _ (by simp [op3ParentHeadS])
    · exact pairFaithful_self _
        (by simp [op3ParentFormulaS, op3ParentHeadS, formulaS, headS, tailS,
          FieldEmbedding.BoundedBy])
    · exact pairFaithful_self _ (by simp [subjectS, FieldEmbedding.BoundedBy])
    · exact pairFaithful_self _ (by simp [formulaS, headS, tailS, FieldEmbedding.BoundedBy])
    · exact pairFaithful_self _ (by simp [op3ParentResultS, resultS, Noun.wut,
        FieldEmbedding.BoundedBy])
  comparison_leaves := by
    intro c hc
    simp only [op3ParentComparisons, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with h | h | h | h | h <;> subst h <;>
      simp [ComparisonUse.LeavesBounded, op3ParentFormulaS, op3ParentHeadS, op3ParentResultS,
        resultS, Noun.wut, subjectS, formulaS, headS, tailS, Noun.leaves]
  comparison_roles := rfl
  axisGate_listed := by intro gate hgate; simp at hgate
  axisGate_tail_mem := by intro gate hgate; simp at hgate
  needs :=
    { served := []
      served_count := rfl }

/-- The parent certificate consumes the served row's derived evaluation as its recursive-call
premise, so the whole two-row chain rests on the `OP_0` global-carry service.  The produced-result
comparison is the `wut` cell test, not `OP_4`'s increment. -/
theorem op3ParentCertificate_nonempty :
    Nonempty (LocalOpcodeCertificate 97 3 op3ParentRowData) := by
  obtain ⟨fuel, _, _, heval⟩ := served_semantics
  refine ⟨.s3 op3ParentRowData (fuel + 1) op3ParentCall rfl servedSeed_ne
    cast_injOn_97 ?_ ?_ ?_ ?_ ?_ (servedSeed_window_atom 7) heval op3ParentS_accepts⟩
  · simp [ComparisonListed, op3ParentRowData, op3ParentComparisons, op3ParentRoot, op3ParentHeadS]
  · simp [ComparisonListed, op3ParentRowData, op3ParentComparisons, op3ParentRoot,
      op3ParentFormulaS]
  · simp [ComparisonListed, op3ParentRowData, op3ParentComparisons, op3ParentRoot, op3ParentCall,
      subjectS]
  · simp [ComparisonListed, op3ParentRowData, op3ParentComparisons, op3ParentRoot, op3ParentCall]
  · simp [ComparisonListed, op3ParentRowData, op3ParentComparisons, op3ParentRoot, op3ParentCall,
      op3ParentResultS]

/-- **Derived Nock semantics of the nonterminal `OP_3` parent.**  A real ROM `?`-step and a bounded
evaluation `*[subjectS [3 [0 2]]] = ?(resultS)`. -/
theorem op3ParentS_semantics :
    ∃ (fuel : ℕ) (successor : Verb),
      Verb.StepROM (Verb.program subjectS op3ParentFormulaS) successor ∧
        FieldEmbedding.evalFBy 97 (fuel + 1) subjectS op3ParentFormulaS =
          some op3ParentResultS := by
  obtain ⟨cert⟩ := op3ParentCertificate_nonempty
  exact cert.semantics

end

#print axioms Nock.NockVMROM.Thm54.Op3Statement.op3ParentS_accepts
#print axioms Nock.NockVMROM.Thm54.Op3Statement.op3ParentRowS_accepts
#print axioms Nock.NockVMROM.Thm54.Op3Statement.op3ComputeTreeS_rvt
#print axioms Nock.NockVMROM.Thm54.Op3Statement.op3ParentRowData
#print axioms Nock.NockVMROM.Thm54.Op3Statement.op3ParentCertificate_nonempty
#print axioms Nock.NockVMROM.Thm54.Op3Statement.op3ParentS_semantics

end Nock.NockVMROM.Thm54.Op3Statement
