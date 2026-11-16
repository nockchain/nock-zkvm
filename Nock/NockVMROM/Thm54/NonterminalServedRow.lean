import Nock.NockVMROM.Thm54.BuildableExecution
import Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete

/-!
# Nonterminal OP₀ served-lookup row data

Two additive results about the nonterminal fixture track.

**A. The F97 fixture cannot carry row-level semantic data at its own seed.**  F97 pins
`fixtureSeed = 1`, and its root row is `OP_4`.  `OP_4`'s arithmetized evaluation
column asserts `sf1_e.size = z`, which is reflected back to "the recursive
result is an atom" only inside the bounded power window `SizeWindow` — and `SizeWindow z n` requires
`1 < orderOf z`.  At `z = 1` the order is `1`, so *no* `SizeWindow` exists for any noun, hence no
`ComputeRowSemanticData` for the F97 root row, hence no `ExactExecutionSemanticData` and no
`BuildableNockExecution` over F97's own `cfg`/`exec`.  This is a property of the F97 *seed choice*,
not of the paper: the paper's seed is a sampled challenge, and the honest sampler excludes exactly
this bad-seed set (`SizeWindowCounting.sizeWindowFailureSeeds`).

**B. A genuine `OP_0` served lookup at a repaired seed.**  `OP_0` is the only opcode that performs a
memory lookup, through the slot operator whose per-node axis carry is
the paper and whose validity clause is the paper.  At the repaired seed `z = -1` (order `2`,
so every atom has a size window) we build a *genuine* `OP_0` compute row over the same field
`K97cubic`: an accepted `Vcomp` row whose `mr2` record realizes a real `GlobalCarryAxis.ServedLookup`, its full `ComputeRowSemanticData`, its
`LocalOpcodeCertificate.s0`, and therefore its derived Nock semantics.  This is the first
`requiredServedLookups`-nonzero row data in the tree; every prior milestone used a terminal `OP_1`
row whose served list is empty by definition.

The `OP_0` row is then placed as the single recursive call of an `OP_4` parent, giving an accepted
two-row `RVT` compute tree (`Fcomp`) in which the parent's derived semantics
consume the child's served lookup as their `evalFBy` premise. -/

namespace Nock.NockVMROM.Thm54.NonterminalServedRow

open scoped Classical
open Nock Nock.Noun Nock.Walk
open ComputeTable
open Nock.NockVMROM.Thm54.SemanticTrace
open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete

noncomputable section

local instance prime97' : Fact (Nat.Prime 97) := ⟨by norm_num⟩
local instance char97' : CharP K97cubic 97 := inferInstance

/-! ## A. No size window at the F97 seed -/

/-- `SizeWindow` demands a nontrivial multiplicative order of the seed. -/
theorem no_sizeWindow_of_orderOf_le_one {K : Type*} [Field K] {z : K} {n : Noun}
    (h : orderOf z ≤ 1) : ¬ OpcodeSemantics.SizeWindow z n := by
  intro hw
  exact absurd hw.one_lt_order (by omega)

/-- The F97 fixture seed is `1`. -/
theorem fixtureSeed_eq_one : fixtureSeed = (1 : K97cubic) := rfl

/-- At the F97 seed no noun has a bounded power window. -/
theorem no_sizeWindow_at_fixtureSeed (n : Noun) :
    ¬ OpcodeSemantics.SizeWindow fixtureSeed n := by
  apply no_sizeWindow_of_orderOf_le_one
  rw [fixtureSeed_eq_one, orderOf_one]

/-- The F97 root row is `OP_4`, whose semantic-row data must contain exactly one size window
(`requiredSizeWindows .s4 = 1`).  At the F97 seed that window cannot exist, so the row has no
`ComputeRowSemanticData`. -/
theorem no_semantic_data_for_parentLabel (q Λ : ℕ) :
    IsEmpty (ComputeRowSemanticData q Λ parentLabel) := by
  constructor
  intro data
  have hcount : data.windows.length = 1 := by
    have := data.windows_count
    simpa [parentLabel, requiredSizeWindows] using this
  obtain ⟨w, hw⟩ : ∃ w, w ∈ data.windows := by
    cases hlist : data.windows with
    | nil => rw [hlist] at hcount; simp at hcount
    | cons a l => exact ⟨a, by simp⟩
  have hz : (parentLabel.2.1).z = fixtureSeed := rfl
  exact no_sizeWindow_at_fixtureSeed w.noun (hz ▸ w.window)

/-- The authoritative first canonical compute row of the F97 execution is its `OP_4` parent. -/
theorem exec97_computeRowAt_zero :
    exec97.computeRowAt ⟨0, by norm_num [cfg97]⟩ = parentLabel := by
  norm_num [ExactExecution.computeRowAt, ExactExecution.computeRows, exec97,
    Nock.Walk.bfsForest, cfg97, computeTree]

/-- Consequently the F97 execution carries no exact semantic-row bundle at its own seed. -/
theorem no_semantic_data_for_exec97 (q Λ : ℕ) :
    IsEmpty (ExactExecutionSemanticData q Λ cfg97 exec97) := by
  constructor
  intro data
  have hrow := data.rows ⟨0, by norm_num [cfg97]⟩
  rw [exec97_computeRowAt_zero] at hrow
  exact (no_semantic_data_for_parentLabel q Λ).false hrow

/-- Therefore no `BuildableNockExecution` can be built on the F97 `cfg`/`exec` pair.  The universal
constructor's input boundary is not the obstruction; the fixture's seed is. -/
theorem no_buildable_execution_over_f97
    (E : BuildableNockExecution F97 K97cubic)
    (hcfg : E.cfg = cfg97) (hexec : HEq E.exec exec97) : False := by
  obtain ⟨q, hq, Λ, cfg, execA, exec, henc, sd, mt, rn, rcb, qlr, tnz, kl, pio, mio⟩ := E
  subst hcfg
  have hexec' : exec = exec97 := eq_of_heq hexec
  subst hexec'
  exact (no_semantic_data_for_exec97 q Λ).false sd

/-- Separately from the seed, the F97 row *states* expose no served lookup at all: its rows are
`OP_4` and `OP_1`, and `requiredServedLookups` is zero on both.  Even repaired, F97 would not
witness OP₀/OP₉ coverage. -/
theorem f97_rows_require_no_served_lookups :
    ∀ row ∈ exec97.computeRows, requiredServedLookups row.1 = 0 := by
  intro row hrow
  rw [execution_rows.1] at hrow
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
  rcases hrow with h | h <;> subst h <;> rfl

/-! ## B. A genuine `OP_0` served row at a repaired seed

The seed `-1` has multiplicative order `2` in `K97cubic`, so every atom (one leaf) has a bounded
power window; that is the only shape `OP_3`/`OP_4`/`OP_6` ever need. -/

/-- Two is nonzero in the cubic extension of `𝔽₉₇`. -/
theorem two_ne_zero_K97 : (2 : K97cubic) ≠ 0 := by
  intro hk
  have hbase : (2 : F97) ≠ 0 := by decide
  apply hbase
  apply (algebraMap F97 K97cubic).injective
  simpa only [map_ofNat, map_zero] using hk

theorem neg_one_ne_one_K97 : (-1 : K97cubic) ≠ 1 := by
  intro h
  apply two_ne_zero_K97
  linear_combination -h

/-- The repaired seed. -/
def servedSeed : K97cubic := -1

theorem servedSeed_ne : servedSeed ≠ 0 := by
  simp [servedSeed]

theorem one_lt_orderOf_servedSeed : 1 < orderOf servedSeed := by
  have hfin : IsOfFinOrder servedSeed :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by norm_num, by norm_num [servedSeed]⟩
  have h0 : orderOf servedSeed ≠ 0 := by
    rw [Ne, orderOf_eq_zero_iff]
    exact fun hc => hc hfin
  have h1 : orderOf servedSeed ≠ 1 := by
    rw [Ne, orderOf_eq_one_iff]
    exact neg_one_ne_one_K97
  omega

/-- Every atom has a bounded power window at the repaired seed.  This is precisely the shape the
`OP_4` gate needs. -/
theorem servedSeed_window_atom (k : ℕ) :
    OpcodeSemantics.SizeWindow servedSeed (.atom k) where
  one_lt_order := one_lt_orderOf_servedSeed
  leaves_lt_order := by
    have := one_lt_orderOf_servedSeed
    simpa [Noun.leaves] using this

/-- Repaired-seed encoder. -/
def encS (n : Noun) : FP K97cubic := GlobalCarryRecognizer.enc servedSeed n

/-! ### The served nouns

`subjectS` is a genuine cell, so axis `2` is a real left descent of the slot walk
, not the trivial axis `1`. -/

def subjectS : Noun := .cell (.atom 7) (.atom 9)
def resultS : Noun := .atom 7
def headS : Noun := .atom 0
def tailS : Noun := .atom 2
def formulaS : Noun := .cell headS tailS

theorem slot_subjectS : Noun.slot 2 subjectS = some resultS := by
  simp [subjectS, resultS, Noun.slot]

def servedInputs : ComputeTable.Inputs K97cubic where
  α := fixtureAlpha
  z := servedSeed
  a := 0
  b := 0
  c := 0

def servedDec : ComputeTable.Dec K97cubic where
  f_h := encS headS
  f_t := encS tailS
  f_th := 0
  f_tt := 0
  f_tth := 0
  f_ttt := 0

/-- The `OP_0` memory record: root is the *subject*, child is the served node, and the axis column
is the tail's leaf value. -/
def servedRecord : MemRec K97cubic where
  root := encS subjectS
  child := encS resultS
  axis := 2
  ts := fixtureAlpha ^ 3

def servedFormulaRecord : MemRec K97cubic where
  root := encS formulaS
  child := encS tailS
  axis := 3
  ts := fixtureAlpha ^ 2

def servedPub : ComputeTable.Pub K97cubic where
  state := .s0
  s := encS subjectS
  f := encS formulaS
  e := encS resultS
  sf1_s := 0
  sf1_f := 0
  sf1_e := 0
  sf2_s := 0
  sf2_f := 0
  sf2_e := 0
  sf3_s := 0
  sf3_f := 0
  sf3_e := 0
  ln_prev := fixtureAlpha
  ln := fixtureAlpha ^ 3
  mr1 := servedFormulaRecord
  mr2 := servedRecord
  mr3 := MemRec.zero

def servedRow : State × ComputeTable.DTcomp K97cubic :=
  (.s0, (servedInputs, servedPub, servedDec))

/-- The `OP_0` row is accepted by the production compute verifier. -/
theorem served_accepts : Vcomp servedInputs servedPub servedDec := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact GlobalCarryRecognizer.enc_cons servedSeed_ne headS tailS
  · ext <;>
      norm_num [servedPub, servedFormulaRecord, servedDec, servedInputs, encS,
        formulaS, tailS]; ring
  · simp [SVhead, headAtom, servedPub, servedDec, servedInputs, encS, headS,
      GlobalCarryRecognizer.enc_atom, State.toNat]
  · refine ⟨?_, rfl, ?_, ?_, ?_⟩
    · ext <;>
        norm_num [servedPub, servedRecord, servedDec, servedInputs, encS, tailS,
          GlobalCarryRecognizer.enc_atom]; ring
    · simp only [servedPub, servedInputs]
      ring
    · simp [servedDec, servedInputs, encS, tailS, GlobalCarryRecognizer.enc_atom]
    · simp [servedDec, encS, tailS, GlobalCarryRecognizer.enc_atom]
  · simp [evalV, servedPub, sfz1, sfz2, sfz3]

theorem served_wf : ComputeTable.WF servedInputs servedPub where
  rlc5 := by simp [servedPub]
  size8 := by simp [servedPub]
  size11 := by simp [servedPub]

/-! ### The served lookup itself -/

/-- The `mr2` record realizes the noun triple `(subject, served node, axis 2)`. -/
theorem servedRecord_realizes :
    OpcodeSemantics.RealizesMemRec servedSeed servedRecord subjectS resultS 2 where
  root_realizes := rfl
  child_realizes := rfl
  axis_realizes := by norm_num [servedRecord]

/-- A genuine global-carry service: axis `2` is the left child of the reconstructed subject tree
. -/
theorem servedLookup_served :
    GlobalCarryAxis.ServedLookup
      (GlobalCarryRecognizer.ofNoun subjectS 1) 2 resultS where
  matched := by
    refine ⟨GlobalCarryRecognizer.ofNoun (.atom 7) 2, ?_, ?_, ?_⟩
    · exact GlobalCarryAxis.Sub.node_l GlobalCarryAxis.Sub.refl
    · simp
    · simp [resultS]

def servedLookup : ServedNounLookup servedSeed where
  record := servedRecord
  root := subjectS
  axis := 2
  child := resultS
  realization := servedRecord_realizes
  served := servedLookup_served

/-! ### Row semantic data and its local certificate -/

def servedRoot : OpcodeSemantics.RootRealization servedInputs servedPub servedDec where
  subject := subjectS
  formula := formulaS
  result := resultS
  head := headS
  tail := tailS
  subject_realizes := rfl
  formula_realizes := rfl
  result_realizes := rfl
  head_realizes := rfl
  tail_realizes := rfl

/-- Pair faithfulness is free on a diagonal pair: the separation hypothesis is vacuous. -/
theorem pairFaithful_self (n : Noun) (h : FieldEmbedding.BoundedBy 97 n) :
    OpcodeSemantics.PairFaithful servedSeed 97 n n where
  separates := fun hne => absurd rfl hne
  left_bounded := h
  right_bounded := h

def servedComparisons : List ComparisonUse :=
  [ { role := .opcodeHead, left := headS, right := .atom 0 },
    { role := .formulaCons, left := formulaS, right := .cell headS tailS },
    { role := .recursiveFormula, left := tailS, right := .atom 2 } ]

/-- Full row-level semantic data for the `OP_0` row: three census comparisons, no calls, no size
windows, no axis gates, and exactly one served lookup. -/
def servedRowData : ComputeRowSemanticData 97 3 servedRow where
  root := servedRoot
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
  realizedNouns := [subjectS, formulaS, resultS]
  subject_mem := by simp [servedRoot]
  formula_mem := by simp [servedRoot]
  result_mem := by simp [servedRoot]
  bounded := by
    intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h | h | h <;> subst h <;>
      simp [subjectS, formulaS, resultS, headS, tailS, FieldEmbedding.BoundedBy]
  comparisons := servedComparisons
  comparison_faithful := by
    intro c hc
    simp only [servedComparisons, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with h | h | h <;> subst h
    · exact pairFaithful_self _ (by simp [headS])
    · exact pairFaithful_self _ (by simp [formulaS, headS, tailS, FieldEmbedding.BoundedBy])
    · exact pairFaithful_self _ (by simp [tailS])
  comparison_leaves := by
    intro c hc
    simp only [servedComparisons, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with h | h | h <;> subst h <;>
      simp [ComparisonUse.LeavesBounded, formulaS, headS, tailS, Noun.leaves]
  comparison_roles := rfl
  axisGate_listed := by intro gate hgate; simp at hgate
  axisGate_tail_mem := by intro gate hgate; simp at hgate
  needs :=
    { served := [servedLookup]
      served_count := rfl }

/-- The `OP_0` row is genuinely covered: its served list is nonempty, unlike every terminal `OP_1`
fixture used so far. -/
theorem servedRowData_served_nonvacuous :
    servedRowData.needs.served = [servedLookup] ∧
      requiredServedLookups servedRow.1 = 1 :=
  ⟨rfl, rfl⟩

theorem cast_injOn_97 :
    Set.InjOn (fun k : ℕ => (k : K97cubic)) (Set.Iio 97) := by
  intro m hm n hn h
  exact CharP.natCast_injOn_Iio K97cubic 97 hm hn h

/-- The production `OP_0` local certificate on the row above. -/
def servedCertificate : LocalOpcodeCertificate 97 3 servedRowData :=
  .s0 servedRowData 0 2 rfl servedSeed_ne cast_injOn_97
    (by simp [ComparisonListed, servedRowData, servedComparisons, servedRoot, headS])
    (by simp [ComparisonListed, servedRowData, servedComparisons, servedRoot])
    (by simp [ComparisonListed, servedRowData, servedComparisons, servedRoot, tailS])
    servedRecord_realizes servedLookup_served served_accepts

/-- **Derived Nock semantics of the served row.**  The certificate is discharged through the
production `OP_0` theorem, giving a real ROM step and a real bounded evaluation
`\[a b\] ⟶ /(b, a)`. -/
theorem served_semantics :
    ∃ (fuel : ℕ) (successor : Verb),
      Verb.StepROM (Verb.program subjectS formulaS) successor ∧
        FieldEmbedding.evalFBy 97 (fuel + 1) subjectS formulaS = some resultS :=
  servedCertificate.semantics

/-! ### The nonterminal `OP_4` parent whose one recursive call is the served `OP_0` row

`OP_4` has no memory record of its own; its semantics are the increment of the
recursive call's result, and its bounded-power-window premise is exactly what fails at the F97
seed.  Here the call is the `OP_0` row above, so the parent's derived Nock semantics genuinely
consume a served global-carry lookup. -/

def parentHeadS : Noun := .atom 4
def parentFormulaS : Noun := .cell parentHeadS formulaS
def parentResultS : Noun := .atom 8

def parentRecordS : MemRec K97cubic where
  root := encS parentFormulaS
  child := encS formulaS
  axis := 3
  ts := fixtureAlpha

def parentDecS : ComputeTable.Dec K97cubic where
  f_h := encS parentHeadS
  f_t := encS formulaS
  f_th := 0
  f_tt := 0
  f_tth := 0
  f_ttt := 0

def parentPubS : ComputeTable.Pub K97cubic where
  state := .s4
  s := encS subjectS
  f := encS parentFormulaS
  e := encS parentResultS
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
  mr1 := parentRecordS
  mr2 := MemRec.zero
  mr3 := MemRec.zero

def parentRowS : State × ComputeTable.DTcomp K97cubic :=
  (.s4, (servedInputs, parentPubS, parentDecS))

theorem parentS_accepts : Vcomp servedInputs parentPubS parentDecS := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact GlobalCarryRecognizer.enc_cons servedSeed_ne parentHeadS formulaS
  · ext <;>
      norm_num [parentPubS, parentRecordS, parentDecS, servedInputs, encS, parentFormulaS]
  · simp [SVhead, headAtom, parentPubS, parentDecS, servedInputs, encS, parentHeadS,
      GlobalCarryRecognizer.enc_atom, State.toNat]
  · norm_num [memBlk, parentPubS, servedInputs, MemRec.zero]
  · simp [evalV, parentPubS, parentDecS, servedInputs, sfz2, sfz3, encS, resultS,
      parentResultS, GlobalCarryRecognizer.enc_atom, FP.inc, FP.atomFP]; norm_num

theorem parentS_wf : ComputeTable.WF servedInputs parentPubS where
  rlc5 := by simp [parentPubS]
  size8 := by simp [parentPubS]
  size11 := by simp [parentPubS]

/-- The compute-line handoff: the parent's `ln` is the served row's `ln_prev`. -/
theorem compute_line_handoffS : parentPubS.ln = servedPub.ln_prev := rfl

def parentOutS : Fin 3 → Option (State × ComputeTable.DTcomp K97cubic)
  | 0 => some servedRow
  | 1 => none
  | 2 => none

theorem parentRowS_accepts : ComputeTable.Fcomp parentRowS parentOutS := by
  refine ⟨rfl, parentS_accepts, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [parentRowS, parentOutS, ComputeTable.fanoutComp]
  · intro i hi
    fin_cases i
    · simp [parentOutS, ComputeTable.sfTriple,
        parentRowS, servedRow, parentPubS, servedPub]
    · simp [parentRowS, ComputeTable.fanoutComp] at hi
    · simp [parentRowS, ComputeTable.fanoutComp] at hi

theorem servedRow_accepts : ComputeTable.Fcomp servedRow (fun _ => none) := by
  refine ⟨rfl, served_accepts, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [servedRow, ComputeTable.fanoutComp]
  · intro i hi
    simp [servedRow, ComputeTable.fanoutComp] at hi

/-- The two-row nonterminal compute tree: an `OP_4` root with the served `OP_0` row as its one
child. -/
def computeTreeS : NTree (State × ComputeTable.DTcomp K97cubic) :=
  .node parentRowS [.node servedRow []]

theorem computeTreeS_rvt : RVT (ComputeTable.Fcomp (K := K97cubic)) computeTreeS := by
  unfold computeTreeS RVT
  refine ⟨?_, ?_, ?_⟩
  · rw [show (fun i : Fin 3 => (NTree.node parentRowS [.node servedRow []]).childLabel i) =
        parentOutS by
      funext i
      fin_cases i <;> rfl]
    exact parentRowS_accepts
  · intro t ht
    simp only [List.mem_singleton] at ht
    subst t
    unfold RVT
    exact ⟨servedRow_accepts, by simp, ⟨fun _ => servedRow_accepts, fun _ => rfl⟩⟩
  · simp [NTree.isLeaf, ComputeTable.Fcomp, parentRowS, ComputeTable.fanoutComp]

/-- The root is genuinely nonterminal and its single successor is the served `OP_0` row. -/
theorem parentS_is_genuinely_nonterminal :
    parentPubS.state = .s4 ∧ ComputeTable.fanoutComp parentPubS.state = 1 ∧
      parentOutS 0 = some servedRow ∧ servedRow.1 = State.s0 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ### Parent row data and its certificate -/

theorem q_eq_ringChar97 : (97 : ℕ) = ringChar K97cubic :=
  (ringChar.eq K97cubic 97).symm

theorem incMod_resultS :
    OpcodeSemantics.incMod (ringChar K97cubic) resultS = parentResultS := by
  rw [← q_eq_ringChar97]
  norm_num [OpcodeSemantics.incMod, resultS, parentResultS]

def parentRoot : OpcodeSemantics.RootRealization servedInputs parentPubS parentDecS where
  subject := subjectS
  formula := parentFormulaS
  result := parentResultS
  head := parentHeadS
  tail := formulaS
  subject_realizes := rfl
  formula_realizes := rfl
  result_realizes := rfl
  head_realizes := rfl
  tail_realizes := rfl

def parentCall :
    OpcodeSemantics.CallRealization servedSeed
      parentPubS.sf1_s parentPubS.sf1_f parentPubS.sf1_e where
  subject := subjectS
  formula := formulaS
  result := resultS
  subject_realizes := rfl
  formula_realizes := rfl
  result_realizes := rfl

def parentComparisons : List ComparisonUse :=
  [ { role := .opcodeHead, left := parentHeadS, right := .atom 4 },
    { role := .formulaCons, left := parentFormulaS, right := .cell parentHeadS formulaS },
    { role := .recursiveSubject, left := subjectS, right := subjectS },
    { role := .recursiveFormula, left := formulaS, right := formulaS },
    { role := .producedResult, left := parentResultS, right := parentResultS } ]

/-- Row semantic data for the nonterminal `OP_4` parent, including the bounded power window that
the F97 seed cannot supply. -/
def parentRowData : ComputeRowSemanticData 97 3 parentRowS where
  root := parentRoot
  tails := []
  branchTails := []
  calls :=
    [ { subjectFP := parentPubS.sf1_s
        formulaFP := parentPubS.sf1_f
        resultFP := parentPubS.sf1_e
        realization := parentCall } ]
  windows := [{ noun := resultS, window := servedSeed_window_atom 7 }]
  axisGates := []
  tails_count := rfl
  branchTails_count := rfl
  calls_count := rfl
  windows_count := rfl
  axisGates_count := rfl
  realizedNouns := [subjectS, parentFormulaS, parentResultS]
  subject_mem := by simp [parentRoot]
  formula_mem := by simp [parentRoot]
  result_mem := by simp [parentRoot]
  bounded := by
    intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h | h | h <;> subst h <;>
      simp [subjectS, parentFormulaS, parentResultS, parentHeadS, formulaS, headS, tailS,
        FieldEmbedding.BoundedBy]
  comparisons := parentComparisons
  comparison_faithful := by
    intro c hc
    simp only [parentComparisons, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with h | h | h | h | h <;> subst h
    · exact pairFaithful_self _ (by simp [parentHeadS])
    · exact pairFaithful_self _
        (by simp [parentFormulaS, parentHeadS, formulaS, headS, tailS,
          FieldEmbedding.BoundedBy])
    · exact pairFaithful_self _ (by simp [subjectS, FieldEmbedding.BoundedBy])
    · exact pairFaithful_self _ (by simp [formulaS, headS, tailS, FieldEmbedding.BoundedBy])
    · exact pairFaithful_self _ (by simp [parentResultS])
  comparison_leaves := by
    intro c hc
    simp only [parentComparisons, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with h | h | h | h | h <;> subst h <;>
      simp [ComparisonUse.LeavesBounded, parentFormulaS, parentHeadS, parentResultS,
        subjectS, formulaS, headS, tailS, Noun.leaves]
  comparison_roles := rfl
  axisGate_listed := by intro gate hgate; simp at hgate
  axisGate_tail_mem := by intro gate hgate; simp at hgate
  needs :=
    { served := []
      served_count := rfl }

/-- The parent certificate consumes the served row's derived evaluation as its recursive-call
premise, so the whole two-row chain rests on the `OP_0` global-carry service. -/
theorem parentCertificate_nonempty :
    Nonempty (LocalOpcodeCertificate 97 3 parentRowData) := by
  obtain ⟨fuel, _, _, heval⟩ := served_semantics
  refine ⟨.s4 parentRowData (fuel + 1) parentCall rfl servedSeed_ne q_eq_ringChar97
    cast_injOn_97 ?_ ?_ ?_ ?_ ?_ (servedSeed_window_atom 7) heval parentS_accepts⟩
  · simp [ComparisonListed, parentRowData, parentComparisons, parentRoot, parentHeadS]
  · simp [ComparisonListed, parentRowData, parentComparisons, parentRoot, parentFormulaS]
  · simp [ComparisonListed, parentRowData, parentComparisons, parentRoot, parentCall, subjectS]
  · simp [ComparisonListed, parentRowData, parentComparisons, parentRoot, parentCall]
  · have hinc :
        OpcodeSemantics.incMod (ringChar K97cubic) parentCall.result = parentResultS :=
      incMod_resultS
    simp only [ComparisonListed, hinc]
    simp [parentRowData, parentComparisons, parentRoot, parentResultS]

/-- **Derived Nock semantics of the nonterminal parent.** -/
theorem parentS_semantics :
    ∃ (fuel : ℕ) (successor : Verb),
      Verb.StepROM (Verb.program subjectS parentFormulaS) successor ∧
        FieldEmbedding.evalFBy 97 (fuel + 1) subjectS parentFormulaS = some parentResultS := by
  obtain ⟨cert⟩ := parentCertificate_nonempty
  exact cert.semantics

end

#print axioms Nock.NockVMROM.Thm54.NonterminalServedRow.no_sizeWindow_at_fixtureSeed
#print axioms Nock.NockVMROM.Thm54.NonterminalServedRow.no_semantic_data_for_parentLabel
#print axioms Nock.NockVMROM.Thm54.NonterminalServedRow.no_semantic_data_for_exec97
#print axioms Nock.NockVMROM.Thm54.NonterminalServedRow.no_buildable_execution_over_f97
#print axioms Nock.NockVMROM.Thm54.NonterminalServedRow.f97_rows_require_no_served_lookups
#print axioms Nock.NockVMROM.Thm54.NonterminalServedRow.served_accepts
#print axioms Nock.NockVMROM.Thm54.NonterminalServedRow.servedRowData
#print axioms Nock.NockVMROM.Thm54.NonterminalServedRow.servedCertificate
#print axioms Nock.NockVMROM.Thm54.NonterminalServedRow.served_semantics
#print axioms Nock.NockVMROM.Thm54.NonterminalServedRow.parentS_accepts
#print axioms Nock.NockVMROM.Thm54.NonterminalServedRow.parentRowS_accepts
#print axioms Nock.NockVMROM.Thm54.NonterminalServedRow.computeTreeS_rvt
#print axioms Nock.NockVMROM.Thm54.NonterminalServedRow.parentRowData
#print axioms Nock.NockVMROM.Thm54.NonterminalServedRow.parentCertificate_nonempty
#print axioms Nock.NockVMROM.Thm54.NonterminalServedRow.parentS_semantics

end Nock.NockVMROM.Thm54.NonterminalServedRow
