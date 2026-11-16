import Nock.NockVMROM.Thm54.CensusExtraClosure
import Nock.NockVMROM.Thm54.DistinctCensusExecution
import Nock.NockVMROM.Thm54.MultiRootServedFixture
import Nock.NockVMROM.Thm54.BuildableTopology
import Nock.Framework.Thm54.SegmentedRAP

/-!
# `C6`, the root-exponent-zero carrier, measured BEFORE any field is added

**Scope.  This module adds no field to any structure.**  `ExactExecution` still has six fields,
`ChainedSemanticExactLanguage` still has ten, `BuildableNockExecution` still has fourteen, and
`ResidualPremises` still has four, of which `firstLine` is still one.  Nothing here discharges
`firstLine`, ticks a `§J` checkbox, or writes `redteam-status.json`.

## What `C6` proposes

```
compute_first_line : (computePubAt ⟨0, cfg.compRows_pos⟩).ln_prev = 1
```

so that `ResidualPremises.firstLine : FirstLineStartsAtOne E.exec` becomes a projection.  §3.6(5)
grades its equivalence risk **MAXIMAL — the field is a verbatim rename**, and defends it anyway as
"an honest relocation" of a convention the honest prover supplies.

## Verdict recorded here: the relocation defence does NOT survive, and the reason is structural

Three measurements, in order.

1. **Equivalence — the field is the premise, at every layer.**
   `c6_field_is_definitionally_firstLine` is `Iff.rfl`, and `c6_discharge_is_the_identity` is
   `fun h => h`.  There is no intervening content anywhere, so §3.6(5)'s grade is confirmed rather
   than softened.

2. **Layer — the defence rested on a sibling that does not exist.**  That symmetry is **not** an accident of drafting and must not be used as an argument: the memory
   pins are there because the memory AIR *has* a boundary segment carrying exactly three
   constraints (`mem_seg_counts`, `memoryBoundarySegment_iff`), and the language is *characterised*
   by segmented-RAP satisfaction (`chainedSemanticExactLanguage_iff_segmentedRAP`).  The compute
   chained AIR's boundary segment is **empty** — `compute_air_boundary_segment_is_empty`, zero
   constraints against the memory table's three (`c6_boundary_slot_contrast`) — mirroring the fact
   that the paper's compute table has no initial-line constraint while its walk table does.  So a first-line field on the language would make
   `chainedSemanticExactLanguage_of_segmentedRAP` unprovable from its present hypotheses and
   `chainedSemanticExactLanguage_iff_segmentedRAP` false: `compute_rap_content_does_not_pin_first_
   ln_prev` exhibits a one-row compute trace satisfying the *entire* compute-side content of that
   characterisation (`computeSegmentedRAP_wholeTrace_iff`: per-row `Vcomp` plus the adjacent line
   hand-off, and nothing else) with first-row `ln_prev = 2 ≠ 1`.

3. **Truth and witness — both pass, and neither rescues the field.**  `firstLine` holds at all
   three live fixtures (`c6_true_at_all_three_live_fixtures`) and the extended carrier is
   inhabited at all three (`c6_shadow_witness_at_all_three_live_fixtures`, over the shadow
   `ChainedSemanticExactLanguageWithComputeFirstLine`).

   **The statement was weaker than this paragraph and than its own name, and
   the STATEMENT is what was repaired.**  The `ChainedSemanticExactLanguage`
   half is available at F73 as a projection of the carrier's own `semanticData` field, so the
   conjunct is **strengthened** (`c6_shadow_witness_at_concrete`) rather than the paragraph
   weakened.

## What the missing object actually is

Not a carrier field: **the compute AIR's empty `.boundary` segment**.  That slot exists, is the
exact structural counterpart of the memory table's three first-row pins, and is where an initial
`ln_prev` constraint would belong if it belonged anywhere.  Putting it there would make `firstLine`
a consequence of `ComputeRowsAccepted` rather than a hypothesis, and would preserve the
segmented-RAP characterisation instead of breaking it.

## Verified paper frame

* the paper — the heading "`RAP_walk` Initial Inputs & Constraints"; the paper — item 3
  of that list, "The initial line constraint `ln(1) = α`".  The paper's initial-line constraint is
  an **input constraint of the walk RAP**.
* the paper — "Prover builds columns `ln`, `count`".
* the paper — the walk increment `ln(i) = α · ln(i-1)`.
* the paper — "from the initial line constraint `ln(1) = α` and the line number increment
  constraint `ln(i) = α · ln(i-1)` it holds that `ln(k) = α^k`".  This is exactly the shape of
  `GenericHonestData.ln_prev_pow_nat`: base case `P.firstLine`, step from `compute_chain` and
  `vcomp_ln`.
* the paper — "The `ln` column, which keeps track of the total number of memory accesses
  requested until that row (inclusive), also needs to be constrained", with the compute recurrence
  displayed at `1885-1887` (the equation itself on `1886`).  **This is the whole of what the
  compute table says about `ln`; there is no compute initial-line constraint.**
* the paper — "`(α, α², α³) : K³` uniformly random extension field element powers used to
  keep track of the memory access timestamps".
* the paper — `V_comp`'s per-row line checks `ln = ln_prev · z^k`, the
  procedural form of the `1886` recurrence.  Per-row only; no first-row case.
* the paper — `W_comp := (ln_prev, ln, mem_record₁, mem_record₂, mem_record₃)`: `ln_prev` is
  a **witness** column the prover supplies.

Production `PremiseKind` cannot express `paperAnalog` and files it
under `paperProtocol` (`residualPremises_kinds`); both readings stay recorded and neither moves.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.FirstLineCarrier

open Nock Nock.NockVMROM Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.GenericHonestCommitment
open Nock.Reified

noncomputable section


variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- The two prime facts the fixture base fields need; both are `local instance`s in the fixture
modules, so they must be re-declared to state anything about those fixtures here. -/
local instance ao120_prime97 : Fact (Nat.Prime 97) := ⟨by norm_num⟩

local instance ao120_prime73 : Fact (Nat.Prime 73) := ⟨by norm_num⟩

/-! ## A. Equivalence test — the proposed field IS the premise

Both directions are `rfl`, at whichever structure the
field is hung on: the statement does not mention the carrying structure at all. -/

/-- **C6 equivalence test.**  Contrast `C2`, whose conjunct lives at the
noun-realization layer and reaches the reconstructed skeleton only through `Classical.choose_spec` -/
theorem c6_field_is_definitionally_firstLine
    {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    ((exec.computePubAt ⟨0, cfg.compRows_pos⟩).ln_prev = 1) ↔ FirstLineStartsAtOne exec :=
  Iff.rfl

/-- The discharge `C6` would buy is the identity function.  A carrier field of this shape moves
`ResidualPremises.firstLine` from one record to another and derives nothing. -/
theorem c6_discharge_is_the_identity
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : (exec.computePubAt ⟨0, cfg.compRows_pos⟩).ln_prev = 1) :
    FirstLineStartsAtOne exec :=
  h

/-- The premise is unchanged by this module: `ResidualPremises` still has four named fields and
`firstLine` is still one of them. -/
theorem residualPremises_still_four_at_ao120
    {E : BuildableNockExecution F K} (P : ResidualPremises E) :
    P =
      { inactiveDec := P.inactiveDec
        axisAtoms := P.axisAtoms
        q_eq_ringChar := P.q_eq_ringChar } := by
  cases P
  rfl

/-! ## B. Layer test — the compute AIR has no boundary slot, and the memory AIR does

This is the measurement that decides `C6`.  The `memory_first_counts` / `memory_first_indicator` /
`memory_first_ipre` fields of `ChainedSemanticExactLanguage` are *not* honest-prover conventions
recorded on the carrier; they are the memory AIR's boundary constraints, recovered from
segmented-RAP satisfaction by `memoryBoundarySegment_iff`.  The compute AIR has no such
constraints, which is why the language has no compute-side first-row field. -/

/-- The compute chained AIR's `.boundary` segment carries **no constraints at all**.  This is the
Lean mirror of the paper: the paper constrains `ln` only by the per-row recurrence, and
the initial-line constraint the paper belongs to the *walk* table -/
theorem compute_air_boundary_segment_is_empty :
    (Nock.Framework.Thm54.kindSeg Nock.Reified.Trans.computeAIRchained .boundary).constraints
      = [] :=
  Nock.Framework.Thm54.comp_boundary_terminal_segs_empty.1

/-- The slot contrast, in one statement: the memory chained AIR's boundary segment carries exactly
the three memory first-row pins, and the compute chained AIR's boundary segment carries zero.
A compute first-row `ln_prev` pin has **no AIR constraint behind it**, so it is not the sibling of
`memory_first_ipre` and must not be argued for as one -/
theorem c6_boundary_slot_contrast :
    (Nock.Framework.Thm54.kindSeg (Nock.Reified.Trans.memoryAIRchained (K := K))
          .boundary).constraints.length = 3 ∧
      (Nock.Framework.Thm54.kindSeg Nock.Reified.Trans.computeAIRchained
        .boundary).constraints.length = 0 :=
  ⟨Nock.Framework.Thm54.mem_seg_counts.2.2.1,
    Nock.Framework.Thm54.comp_seg_counts.2.2.1⟩

/-- The whole compute-side content of segmented-RAP satisfaction, restated so the next theorem can
be read against it: per-row `Vcomp`, plus the adjacent line hand-off, and nothing else.  There is
no first-row conjunct on the right-hand side, whereas the memory analogue has four endpoint
conjuncts -/
theorem compute_rap_content_is_exactly_vcomp_and_chain (cfg : ExactConfig F K)
    (pub : Fin cfg.compRows → ComputeTable.Pub K)
    (dec : Fin cfg.compRows → ComputeTable.Dec K)
    (hwf : ∀ i, ComputeTable.WF cfg.challenges.computeInputs (pub i))
    (hz : cfg.challenges.z ≠ 0) :
    (∃ ex : Fin cfg.compRows → ComputeTable.Extra K,
      ComputeSegmentedRAPSatisfies cfg
        (encodeComputeTrace
          (fun i => computeEnvFull cfg.challenges.computeInputs
            (ComputeTable.opSel (pub i).state) (pub i) (dec i) (ex i))
          cfg.compNodes))
      ↔
    ((∀ i, ComputeTable.Vcomp cfg.challenges.computeInputs (pub i) (dec i)) ∧
      ∀ i : Fin cfg.compRows, ∀ hi : (i : ℕ) + 1 < cfg.compRows,
        (pub i).ln = (pub ⟨(i : ℕ) + 1, hi⟩).ln_prev) :=
  computeSegmentedRAP_wholeTrace_iff cfg pub dec hwf hz

namespace F73Probe

open Nock.NockVMROM.Thm54.ConcreteStrictPackage

/-- The perturbed first compute row: `ln_prev` is moved off `1`, and the two products `V_comp`
actually checks (`ln = ln_prev · α` and the single active record timestamp) move with it. -/
def nonunitFirstPub : ComputeTable.Pub K73cubic :=
  { computePub honestSeed honestAlpha with
      ln_prev := 2
      ln := 2 * honestAlpha
      mr1 := { (computePub honestSeed honestAlpha).mr1 with ts := 2 * honestAlpha } }

/-- That row as a one-row compute trace, on which the adjacent hand-off is vacuous. -/
def oneRowPub (_ : Fin 1) : ComputeTable.Pub K73cubic := nonunitFirstPub

/-- **C6 layer test, negative.**  A one-row compute trace satisfies the *entire* compute-side
content of `chainedSemanticExactLanguage_iff_segmentedRAP` — per-row `V_comp` and the adjacent line
hand-off, which `compute_rap_content_is_exactly_vcomp_and_chain` shows is all of it — while its
first row has `ln_prev = 2 ≠ 1`.

Two consequences, both of which bear directly on where `C6` could be hung.  A first-line field on
`ChainedSemanticExactLanguage` would leave `chainedSemanticExactLanguage_of_segmentedRAP` with no
source for the new field and would falsify `chainedSemanticExactLanguage_iff_segmentedRAP`; and the
constraint is not AIR-backed at any layer, so it can only ever be *asserted* of the honest prover,
never recovered from acceptance -/
theorem compute_rap_content_does_not_pin_first_ln_prev :
    (∀ i : Fin 1, ∀ hi : (i : ℕ) + 1 < 1,
        (oneRowPub i).ln = (oneRowPub ⟨(i : ℕ) + 1, hi⟩).ln_prev) ∧
      ComputeTable.Vcomp (computeInputs honestSeed honestAlpha) nonunitFirstPub
        (computeDec honestSeed) ∧
      nonunitFirstPub.ln_prev ≠ 1 := by
  refine ⟨fun i hi => absurd hi (by omega), ?_, ?_⟩
  · exact GenericHonestCommitment.Concrete.f73_vcomp_accepts_nonzero_first_ln_prev.1
  · exact GenericHonestCommitment.Concrete.f73_vcomp_accepts_nonzero_first_ln_prev.2

end F73Probe

/-! ## C. -/

/-- F97, the released fixture under `DistinctCensusFold2.packageR` -/
theorem firstLine_at_distinctCensus :
    FirstLineStartsAtOne DistinctCensusExecution.execD := by
  unfold FirstLineStartsAtOne
  change (DistinctCensusExecution.execD.computePubAt
    ⟨0, DistinctCensusExecution.cfgD.compRows_pos⟩).ln_prev = 1
  rw [DistinctCensusExecution.computePubAtD_zero]
  rfl

/-- The multi-root served fixture -/
theorem firstLine_at_multiRoot :
    FirstLineStartsAtOne MultiRootServedFixture.multiRootExecution.exec := by
  unfold FirstLineStartsAtOne
  change (MultiRootServedFixture.execS.computePubAt
    ⟨0, MultiRootServedFixture.cfgS.compRows_pos⟩).ln_prev = 1
  rw [MultiRootServedFixture.computePubAtS_zero]
  rfl

/-- F73, the concrete fixture -/
theorem firstLine_at_concrete :
    FirstLineStartsAtOne BuildableConcrete.concreteExecution.exec := by
  unfold FirstLineStartsAtOne
  change ((ConcreteStrictPackage.exec ConcreteStrictPackage.honestSeed
    ConcreteStrictPackage.honestAlpha).computePubAt
      ⟨0, (ConcreteStrictPackage.cfg ConcreteStrictPackage.honestSeed
        ConcreteStrictPackage.honestAlpha).compRows_pos⟩).ln_prev = 1
  rw [ConcreteStrictPackage.computePubAt_zero]
  rfl

theorem c6_true_at_all_three_live_fixtures :
    FirstLineStartsAtOne DistinctCensusExecution.execD ∧
      FirstLineStartsAtOne MultiRootServedFixture.multiRootExecution.exec ∧
      FirstLineStartsAtOne BuildableConcrete.concreteExecution.exec :=
  ⟨firstLine_at_distinctCensus, firstLine_at_multiRoot, firstLine_at_concrete⟩

/-! ## D. Non-vacuity witness (J.0.3) — gate (4), PASSED, on a shadow extension

J.0.3 asks for a compiled witness inhabiting the **extended** structure at a real honest execution.
Since `C6`'s field is a `Prop`, inhabiting the extended language is exactly inhabiting the present
one together with the new conjunct, so the witness can be — and here is — compiled *before* the
field is added rather than after.  The shadow structure below is a local declaration and is not a
field of anything. -/

/-- The extension `C6` proposes, hung at the layer this module argues is its only faithful home,
as a **shadow** structure.  Nothing in the build consumes it; `ChainedSemanticExactLanguage` is
untouched and still has ten fields. -/
structure ChainedSemanticExactLanguageWithComputeFirstLine
    (cfg : ExactConfig F K) (exec : ExactExecution cfg) : Prop where
  /-- Everything the present language asserts. -/
  chained : ChainedSemanticExactLanguage cfg exec
  /-- The proposed `C6` conjunct -/
  compute_first_ln_prev : (exec.computePubAt ⟨0, cfg.compRows_pos⟩).ln_prev = 1

/-- J.0.3 witness at the released F97 fixture. -/
theorem c6_shadow_witness_at_distinctCensus
    (hfirstD :
      (DistinctCensusExecution.execD.memoryPubAt
          ⟨0, by norm_num [DistinctCensusExecution.cfgD]⟩).pt.counts = 0 ∧
        (DistinctCensusExecution.execD.memoryPubAt
          ⟨0, by norm_num [DistinctCensusExecution.cfgD]⟩).pt.indicator = 0) :
    ChainedSemanticExactLanguageWithComputeFirstLine
      DistinctCensusExecution.cfgD DistinctCensusExecution.execD :=
  ⟨DistinctCensusExecution.chainedD hfirstD, firstLine_at_distinctCensus⟩

/-- J.0.3 witness at the multi-root served fixture. -/
theorem c6_shadow_witness_at_multiRoot :
    ChainedSemanticExactLanguageWithComputeFirstLine
      MultiRootServedFixture.cfgS MultiRootServedFixture.execS :=
  ⟨MultiRootServedFixture.chainedS, firstLine_at_multiRoot⟩

/-- J.0.3 witness at the F73 concrete fixture.

The third conjunct of
`c6_shadow_witness_at_all_three_live_fixtures` was the *bare* premise
`FirstLineStartsAtOne concreteExecution.exec`, not an inhabitant of the extended carrier, while its
name and five documents said all three fixtures inhabited the extension.  The `ChainedSemanticExactLanguage`
half is available at F73 with no new mathematics — it is a projection of the carrier's own
`semanticData` field — so the conjunct is strengthened rather than the documents weakened. -/
theorem c6_shadow_witness_at_concrete :
    ChainedSemanticExactLanguageWithComputeFirstLine
      BuildableConcrete.concreteExecution.cfg BuildableConcrete.concreteExecution.exec :=
  ⟨BuildableConcrete.concreteExecution.semanticData.language.traversable.chained,
    firstLine_at_concrete⟩

/-- All three live fixtures inhabit the extended carrier.  Gate (4) is passed, and `C6` therefore
fails on the equivalence gate alone — not for want of a witness.

Nothing is weakened — the two other
conjuncts are unchanged and the F73 conjunct now strictly implies its predecessor by
`ChainedSemanticExactLanguageWithComputeFirstLine.compute_first_ln_prev`.* -/
theorem c6_shadow_witness_at_all_three_live_fixtures
    (hfirstD :
      (DistinctCensusExecution.execD.memoryPubAt
          ⟨0, by norm_num [DistinctCensusExecution.cfgD]⟩).pt.counts = 0 ∧
        (DistinctCensusExecution.execD.memoryPubAt
          ⟨0, by norm_num [DistinctCensusExecution.cfgD]⟩).pt.indicator = 0) :
    ChainedSemanticExactLanguageWithComputeFirstLine
        DistinctCensusExecution.cfgD DistinctCensusExecution.execD ∧
      ChainedSemanticExactLanguageWithComputeFirstLine
        MultiRootServedFixture.cfgS MultiRootServedFixture.execS ∧
      ChainedSemanticExactLanguageWithComputeFirstLine
        BuildableConcrete.concreteExecution.cfg BuildableConcrete.concreteExecution.exec :=
  ⟨c6_shadow_witness_at_distinctCensus hfirstD, c6_shadow_witness_at_multiRoot,
    c6_shadow_witness_at_concrete⟩

/-! ## E.

The proposed condition is a **local scalar boundary condition**, which §0 permits explicitly (the
`q(1) = 1` base of the queue-length gate is the same shape), and not a positional lookup.  The
receipt below is the precise sense in which that is true: the condition is a function of the first
compute row alone.  It therefore reads no committed line, no back-reference, and nothing in the
memory multiset — two executions may differ in every memory row and every later compute row and
still agree on it. -/

/-- **Canon receipt.**  `FirstLineStartsAtOne` depends only on the first compute row.  It performs
no lookup of a row committed at another line, holds no back-reference, and never touches the memory
forest, so it introduces no position into the memory multiset. -/
theorem c6_reads_only_the_first_compute_row
    {cfg : ExactConfig F K} (e₁ e₂ : ExactExecution cfg)
    (h : e₁.computeRowAt ⟨0, cfg.compRows_pos⟩ = e₂.computeRowAt ⟨0, cfg.compRows_pos⟩) :
    FirstLineStartsAtOne e₁ ↔ FirstLineStartsAtOne e₂ := by
  unfold FirstLineStartsAtOne ExactExecution.computePubAt
  rw [h]

/-- Sharper form of the same receipt: the condition reads one scalar column of that row. -/
theorem c6_is_one_scalar_column
    {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    FirstLineStartsAtOne exec ↔
      (exec.computeRowAt ⟨0, cfg.compRows_pos⟩).2.2.1.ln_prev = 1 :=
  Iff.rfl

end

end Nock.NockVMROM.Thm54.FirstLineCarrier

#print axioms Nock.NockVMROM.Thm54.FirstLineCarrier.c6_field_is_definitionally_firstLine
#print axioms Nock.NockVMROM.Thm54.FirstLineCarrier.c6_discharge_is_the_identity
#print axioms Nock.NockVMROM.Thm54.FirstLineCarrier.residualPremises_still_four_at_ao120
#print axioms Nock.NockVMROM.Thm54.FirstLineCarrier.compute_air_boundary_segment_is_empty
#print axioms Nock.NockVMROM.Thm54.FirstLineCarrier.c6_boundary_slot_contrast
#print axioms Nock.NockVMROM.Thm54.FirstLineCarrier.compute_rap_content_is_exactly_vcomp_and_chain
#print axioms
  Nock.NockVMROM.Thm54.FirstLineCarrier.F73Probe.compute_rap_content_does_not_pin_first_ln_prev
#print axioms Nock.NockVMROM.Thm54.FirstLineCarrier.firstLine_at_distinctCensus
#print axioms Nock.NockVMROM.Thm54.FirstLineCarrier.firstLine_at_multiRoot
#print axioms Nock.NockVMROM.Thm54.FirstLineCarrier.firstLine_at_concrete
#print axioms Nock.NockVMROM.Thm54.FirstLineCarrier.c6_true_at_all_three_live_fixtures
#print axioms Nock.NockVMROM.Thm54.FirstLineCarrier.c6_shadow_witness_at_distinctCensus
#print axioms Nock.NockVMROM.Thm54.FirstLineCarrier.c6_shadow_witness_at_multiRoot
#print axioms Nock.NockVMROM.Thm54.FirstLineCarrier.c6_shadow_witness_at_concrete
#print axioms
  Nock.NockVMROM.Thm54.FirstLineCarrier.c6_shadow_witness_at_all_three_live_fixtures
#print axioms Nock.NockVMROM.Thm54.FirstLineCarrier.c6_reads_only_the_first_compute_row
#print axioms Nock.NockVMROM.Thm54.FirstLineCarrier.c6_is_one_scalar_column
