import Nock.NockVMROM.Thm54.CensusExtraClosure
import Nock.NockVMROM.Thm54.BuildableTopology
import Nock.NockVMROM.Thm54.MultiRootServedFixture
import Nock.RedTeam.Batch96Thm54GenericHonestCommitment

/-!
# The four `CensusRecordPremises` extras

Different context from
the prover.  **Nothing here inhabits a named premise, adds a carrier field, or weakens a census
predicate.**

**Generically it is a TRADE; at the live released fixture it is a genuine unconditional discharge.**

* the forward half is compiled and is not in doubt — `skeletonBounded_of_consDecomposed` derives the
  whole premise from the object (`redteam_consDecomposed_gives_the_premise` re-instantiates it);
* the reverse half fails at the very layer `SemanticSkeleton.BoundedBy` quantifies over.

So `ConsDecomposedRow` is **strictly stronger** than the conclusion, not equivalent to it.  Written
as a dichotomy: had the reverse half held, the object would have been the premise under another name; it fails, so the object is a *new, strictly stronger* named premise.
Either way the generic named-premise count does not go down, and
`censusRecordPremises_still_five_here` records exactly that.

`ConsDecomposedRow` is **not held on `E`**.  It is not a field of `BuildableNockExecution`, not a
field of `ComputeRowSemanticData`, and no declaration in the tree produces it from `E`; the only
device that would reflect `Vcomp`'s fingerprint-level `f = cons(f_h, f_t)` to the noun equation is
`OpcodeSemantics.PairFaithful`, whose `right_bounded` field is the sought conclusion
(`redteam_consReflection_is_circular`).  That last point is what makes the swap a trade rather than
a rename: the paper states the three constraints between **fingerprints**, and `ConsDecomposedRow` is their **noun-level**
reflection, which is one step further than the paper's own sentence.

**`combinedBounded` is not newly derived; the dependency is relocated.**

**The fixture-level result IS real, and it is unconditional in the only sense available here.**
`distinctCensus_skeletonBounded_and_combinedBounded` takes no hypothesis beyond the `P` and `M` that
the *statement of the premise itself* requires — `CensusRecordPremises E P M` is indexed by exactly
that pair, so the discharged fields and the named fields quantify identically.
`redteam_distinctCensus_two_of_five_fields_are_filled` compiles the consequence into the real record:
at `distinctCensusExecution` a `CensusRecordPremises` is obtainable from **three** named extras, not
five.  Its hypothesis is non-vacuous: `redteam_distinctCensus_compRows_is_three` shows the index type
is inhabited and `redteam_distinctCensus_row_zero_consDecomposed` exhibits a row at which
`ConsDecomposedRow` has content rather than being an empty conjunction of guarded fields.

*Scope that the ledger must carry.*

**Yes, and it is unusable at all three live fixtures, for two different reasons.**

Put together on a window noun that attains the bound they pin the order exactly
(`redteam_route_pins_the_order`, re-proved independently).

* `distinctCensusExecution` (`Λ = 7`, `z = 8 : K97cubic`, `orderOf z = 16`): the recorded hypothesis
  is **false** (`redteam_route_false_at_distinctCensus`), and the residual gap is exhibited at a live
  seed by an eight-leaf noun (`redteam_gap_at_distinctCensus`).
* `concreteExecution` (`Λ = 2`, `z = honestSeed = 1`, `orderOf z = 1`): the recorded hypothesis
  *holds* (`1 ≤ 3`) but sampled `SizeWindow` is **unsatisfiable at that seed** — for every noun
  (`redteam_concrete_sizeWindow_is_empty`).  The bridge therefore certifies nothing.
* `multiRootExecution` (`Λ = 3`, `z = servedSeed = -1`, `orderOf z = 2`): the recorded hypothesis
  *holds* (`2 ≤ 4`) but sampled `SizeWindow` covers **only single-leaf nouns** and no cell
  (`redteam_multiRoot_sizeWindow_covers_only_leaves`, `redteam_multiRoot_sizeWindow_excludes_cells`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch136

open scoped Classical
open Nock Nock.Walk
open Nock.NockVMROM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTrace
open Nock.NockVMROM.Thm54.GenericHonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestData
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.CensusExtraClosure

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-! ## §A. -/

/-- **Forward half, re-instantiated.** -/
theorem redteam_consDecomposed_gives_the_premise (E : BuildableNockExecution F K)
    (P : ResidualPremises E) (M : MemoryRecordPremises E)
    (hc : ∀ i : Fin E.cfg.compRows, ConsDecomposedRow (E.semanticData.rows i)) :
    (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)).BoundedBy E.q :=
  skeletonBounded_of_consDecomposed E P M hc

/-- A `q`-bounded compute-row skeleton whose formula is a genuine **cell** and is still not the
`cons` of its two recorded first-level decomposition slots. -/
def rtConsShapedNotConsRow : ComputeRowSkeleton where
  state := .s1
  subject := .atom 0
  formula := .cell (.atom 0) (.cell (.atom 0) (.atom 0))
  evaluation := .atom 0
  decomposition := fun _ _ => .atom 0
  subformula := fun _ _ _ => .atom 0
  memoryRecord := fun _ _ => ⟨.atom 0, .atom 0, 1⟩

/-- **Reverse half fails, at the layer `SemanticSkeleton.BoundedBy` quantifies over.**  Hence
`ConsDecomposedRow` is strictly stronger than the conclusion it produces, not equivalent to it. -/
theorem redteam_bounded_cons_shaped_row_is_not_consDecomposed :
    ComputeRowSkeleton.BoundedBy 1 rtConsShapedNotConsRow ∧
      (∃ l r : Noun, rtConsShapedNotConsRow.formula = .cell l r) ∧
      rtConsShapedNotConsRow.formula ≠
        .cell (rtConsShapedNotConsRow.decomposition .f_h rfl)
          (rtConsShapedNotConsRow.decomposition .f_t rfl) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨_, _, rfl⟩, ?_⟩
  · simp [rtConsShapedNotConsRow]
  · simp [rtConsShapedNotConsRow]
  · simp [rtConsShapedNotConsRow]
  · intro slot h; simp [rtConsShapedNotConsRow]
  · intro i h slot; simp [rtConsShapedNotConsRow]
  · intro i h; simp [rtConsShapedNotConsRow, MemRecSkeleton.BoundedBy]
  · simp [rtConsShapedNotConsRow]

/-- **Why the paper's own sentence does not already supply the object.**  `Vcomp` states the three
`cons` constraints between fingerprints; the only reflection device to nouns is `PairFaithful`, and
its `right_bounded` field is the conclusion the reflection would be used to reach.  Independently
re-derived. -/
theorem redteam_consReflection_is_circular {z : K} {q : ℕ} {h t : Noun}
    (hpf : OpcodeSemantics.PairFaithful z q (.cell h t) (.cell h t)) :
    FieldEmbedding.BoundedBy q h ∧ FieldEmbedding.BoundedBy q t :=
  hpf.right_bounded

/-! ### §A.1 `combinedBounded` — relocated, not newly derived -/

theorem redteam_combinedBounded_needs_only_named_skeletonBounded
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryRecordPremises E)
    (hs : (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)).BoundedBy E.q)
    (hgt : 11 < ringChar K) :
    ProductionP8Containment.CombinedBoundedBy K E.q
      (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)) :=
  GenericHonestData.combinedBounded_of_skeletonBounded_at_consumed_q E P M hs hgt

/-- Both
arrows are exhibited side by side, so the ledger reading "`combinedBounded` becomes fully derived"
is a relocation of the dependency from `skeletonBounded` onto `ConsDecomposedRow`, not the removal
of an assumption. -/
theorem redteam_consDecomposed_route_factors_through_skeletonBounded
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryRecordPremises E)
    (hc : ∀ i : Fin E.cfg.compRows, ConsDecomposedRow (E.semanticData.rows i))
    (hgt : 11 < ringChar K) :
    ((skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)).BoundedBy E.q) ∧
      ProductionP8Containment.CombinedBoundedBy K E.q
        (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)) :=
  ⟨skeletonBounded_of_consDecomposed E P M hc,
    redteam_combinedBounded_needs_only_named_skeletonBounded E P M
      (skeletonBounded_of_consDecomposed E P M hc) hgt⟩

/-- The named-premise count is unchanged by the reduction: still five fields, none deleted. -/
theorem redteam_censusRecordPremises_still_five {E : BuildableNockExecution F K}
    {P : ResidualPremises E} {M : MemoryRecordPremises E}
    (C : CensusRecordPremises E P M) :
    C =
      { slotSemantics := C.slotSemantics
        census := C.census
        sizeWindowBound := C.sizeWindowBound
        skeletonBounded := C.skeletonBounded
        combinedBounded := C.combinedBounded } := by
  cases C
  rfl

/-! ### §A.2 The fixture-level result, measured -/

section LiveFixtures

open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.NockVMROM.Thm54.DistinctCensusExecution
open Nock.NockVMROM.Thm54.MultiRootServedFixture
open Nock.NockVMROM.Thm54.BuildableConcrete
open Nock.NockVMROM.Thm54.ConcreteStrictPackage

local instance : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic
local instance char97b136 : CharP K97cubic 97 := inferInstance
local instance : CharP K97cubic (ringChar K97cubic) := ringChar.charP K97cubic

-- Form R leftover first-row `counts = 0` / `indicator = 0` (live is `chainOneBitWeight`).
variable (hfirstD :
  (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.counts = 0 ∧
    (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.indicator = 0)

theorem redteam_distinctCensus_compRows_is_three :
    (distinctCensusExecution hfirstD).cfg.compRows = 3 := rfl

/-- …and at row `0` the object has content: `formula_cons` is a real cell equation and `tail_cons`
fires, since the OP5 row is tail-decomposed. -/
theorem redteam_distinctCensus_row_zero_consDecomposed :
    ConsDecomposedRow
      ((distinctCensusExecution hfirstD).semanticData.rows
        ⟨0, (distinctCensusExecution hfirstD).cfg.compRows_pos⟩) :=
  distinctCensus_consDecomposed hfirstD ⟨0, (distinctCensusExecution hfirstD).cfg.compRows_pos⟩

/-- **Two of the five census extras are filled at the released fixture.**  The record is obtained
from **three** named extras rather than five, for every `P` / `M`.  This is the exact scope of the
fixture-level gain: the discharge quantifies over the same `P` / `M` that the discharged fields'
own types require, so it is unconditional relative to the premise it replaces. -/
def redteam_distinctCensus_two_of_five_fields_are_filled
    (P : ResidualPremises (distinctCensusExecution hfirstD))
    (M : MemoryRecordPremises (distinctCensusExecution hfirstD))
    (slotSemantics :
      ∀ s ∈ computeSkeletonRows
          (skeletonOfNodes (computeNodesOf (distinctCensusExecution hfirstD) P)
            (memoryNodesOf (distinctCensusExecution hfirstD) M)),
        ServedLookupBridge.SkeletonSlotSemantics s)
    (census :
      EdgeComparisonCensus.CombinedSkeletonCensus K97cubic
        (skeletonOfNodes (computeNodesOf (distinctCensusExecution hfirstD) P)
          (memoryNodesOf (distinctCensusExecution hfirstD) M))
        (distinctCensusExecution hfirstD).Λ)
    (sizeWindowBound :
      SizeWindowCounting.SizeWindowNounsBoundedBy
        (skeletonOfNodes (computeNodesOf (distinctCensusExecution hfirstD) P)
          (memoryNodesOf (distinctCensusExecution hfirstD) M))
        (distinctCensusExecution hfirstD).Λ) :
    CensusRecordPremises (distinctCensusExecution hfirstD) P M where
  slotSemantics := slotSemantics
  census := census
  sizeWindowBound := sizeWindowBound
  skeletonBounded := (distinctCensus_skeletonBounded_and_combinedBounded hfirstD P M).1
  combinedBounded := (distinctCensus_skeletonBounded_and_combinedBounded hfirstD P M).2

/-- Recorded here so the §J.2 scope cannot be
read as "the released fixture's census bundle is inhabited". -/
theorem redteam_residualPremises_inhabited_at_f73 :
    Nonempty (ResidualPremises concreteExecution) :=
  Nock.RedTeam.Batch96.ConcretePremises.f73_residualPremises_nonvacuous

/-! ## §B. -/

/-- Sampled `SizeWindow` is two **lower** bounds on `orderOf z`. -/
theorem redteam_sizeWindow_is_two_lower_bounds {z : K} {n : Noun} :
    OpcodeSemantics.SizeWindow z n ↔ (1 < orderOf z ∧ n.leaves < orderOf z) :=
  ⟨fun h => ⟨h.one_lt_order, h.leaves_lt_order⟩, fun h => ⟨h.1, h.2⟩⟩

/-- Independently re-proved: on a window noun attaining the bound, the two together pin the order. -/
theorem redteam_route_pins_the_order {z : K} {n : Noun} {Λ : ℕ}
    (hw : OpcodeSemantics.SizeWindow z n) (hleaves : n.leaves = Λ)
    (hord : orderOf z ≤ Λ + 1) :
    orderOf z = Λ + 1 := by
  have h := hw.leaves_lt_order
  rw [hleaves] at h
  omega

/-- The extra itself never mentions the seed, so the recorded hypothesis cannot be necessary. -/
theorem redteam_sizeWindowBound_is_seed_free (S : SemanticSkeleton) (Λ : ℕ) :
    SizeWindowCounting.SizeWindowNounsBoundedBy S Λ ↔
      ∀ n ∈ SizeWindowCounting.skeletonSizeWindowNouns S, n.leaves ≤ Λ :=
  Iff.rfl

/-! ### §B.1 Fixture 1 — the released F97 `(distinctCensusExecution hfirstD)`: the hypothesis is FALSE -/

theorem redteam_distinctCensus_numerals :
    (distinctCensusExecution hfirstD).Λ = 7 ∧
      (distinctCensusExecution hfirstD).cfg.challenges.z = (8 : K97cubic) ∧
      orderOf (distinctCensusExecution hfirstD).cfg.challenges.z = 16 :=
  ⟨rfl, rfl, omega8_order⟩

theorem redteam_route_false_at_distinctCensus :
    ¬ orderOf (distinctCensusExecution hfirstD).cfg.challenges.z ≤ (distinctCensusExecution hfirstD).Λ + 1 := by
  rw [(redteam_distinctCensus_numerals hfirstD).2.2, (redteam_distinctCensus_numerals hfirstD).1]
  omega

/-- An independent eight-leaf noun. -/
def rtEight : Noun :=
  .cell (.cell (.cell (.atom 0) (.atom 0)) (.cell (.atom 0) (.atom 0)))
    (.cell (.cell (.atom 0) (.atom 0)) (.cell (.atom 0) (.atom 0)))

theorem rtEight_leaves : rtEight.leaves = 8 := by
  simp [rtEight, Noun.leaves]

/-- **The gap, at the live released seed.**  Even complete sampled `SizeWindow` certifies only
`leaves ≤ 15` there while the extra demands `leaves ≤ 7`; `rtEight` sits in the gap. -/
theorem redteam_gap_at_distinctCensus :
    OpcodeSemantics.SizeWindow (distinctCensusExecution hfirstD).cfg.challenges.z rtEight ∧
      ¬ rtEight.leaves ≤ (distinctCensusExecution hfirstD).Λ := by
  have hord : orderOf (distinctCensusExecution hfirstD).cfg.challenges.z = 16 :=
    (redteam_distinctCensus_numerals hfirstD).2.2
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [hord]; omega
  · rw [rtEight_leaves, hord]; omega
  · rw [rtEight_leaves, (redteam_distinctCensus_numerals hfirstD).1]; omega

/-! ### §B.2 Fixture 2 — the F73 `concreteExecution`: the hypothesis holds and `SizeWindow` is empty -/

theorem redteam_concrete_numerals :
    concreteExecution.Λ = 2 ∧
      concreteExecution.cfg.challenges.z = (1 : K73cubic) ∧
      orderOf concreteExecution.cfg.challenges.z = 1 := by
  refine ⟨rfl, rfl, ?_⟩
  show orderOf (1 : K73cubic) = 1
  simp

/-- The recorded hypothesis *holds* here — and buys nothing. -/
theorem redteam_route_holds_at_concrete :
    orderOf concreteExecution.cfg.challenges.z ≤ concreteExecution.Λ + 1 := by
  rw [redteam_concrete_numerals.2.2, redteam_concrete_numerals.1]
  omega

/-- **Sampled `SizeWindow` is unsatisfiable at the F73 seed**, for every noun, because the seed is
`1` and `SizeWindow` opens with `1 < orderOf z`. -/
theorem redteam_concrete_sizeWindow_is_empty (n : Noun) :
    ¬ OpcodeSemantics.SizeWindow concreteExecution.cfg.challenges.z n := by
  intro hw
  have h := hw.one_lt_order
  rw [redteam_concrete_numerals.2.2] at h
  omega

/-! ### §B.3 Fixture 3 — the F97 `multiRootExecution`: the hypothesis holds and covers no cell -/

theorem redteam_multiRoot_seed :
    multiRootExecution.cfg.challenges.z = (-1 : K97cubic) := rfl

theorem redteam_multiRoot_numerals :
    multiRootExecution.Λ = 3 ∧
      orderOf multiRootExecution.cfg.challenges.z = 2 := by
  refine ⟨rfl, ?_⟩
  rw [redteam_multiRoot_seed]
  have hsq : (-1 : K97cubic) ^ 2 = 1 := by ring
  have hne : (-1 : K97cubic) ≠ 1 := by
    intro h
    have h2 : (2 : K97cubic) = 0 := by linear_combination -h
    exact NonterminalServedRow.two_ne_zero_K97 h2
  exact orderOf_eq_prime hsq hne

/-- The recorded hypothesis *holds* here too. -/
theorem redteam_route_holds_at_multiRoot :
    orderOf multiRootExecution.cfg.challenges.z ≤ multiRootExecution.Λ + 1 := by
  rw [redteam_multiRoot_numerals.2, redteam_multiRoot_numerals.1]
  omega

/-- **Sampled `SizeWindow` at the F97 multi-root seed covers only single-leaf nouns.** -/
theorem redteam_multiRoot_sizeWindow_covers_only_leaves {n : Noun}
    (hw : OpcodeSemantics.SizeWindow multiRootExecution.cfg.challenges.z n) :
    n.leaves = 1 := by
  have h := hw.leaves_lt_order
  rw [redteam_multiRoot_numerals.2] at h
  have h1 := n.one_le_leaves
  omega

theorem redteam_multiRoot_sizeWindow_excludes_cells (l r : Noun) :
    ¬ OpcodeSemantics.SizeWindow multiRootExecution.cfg.challenges.z (.cell l r) := by
  intro hw
  have h := redteam_multiRoot_sizeWindow_covers_only_leaves hw
  simp only [Noun.leaves] at h
  have hl := l.one_le_leaves
  have hr := r.one_le_leaves
  omega

end LiveFixtures

/-! ## §C. Section 2 item 3 — the `Λ` occurrence claim, verified by transport

The claim is
**CONFIRMED**, and the compiled form below is stronger than a field-by-field reading: a structure
update that changes `Λ` and replaces `comparison_leaves` **and nothing else** typechecks only if no
other field of the record mentions `Λ`.

Field-by-field, for the record: `BuildableNockExecution` has fourteen fields
(`BuildableNockExecution.eta_with_memoryTrace`), of which `Λ` is one and only `semanticData` and
`memoryTrace` are `Λ`-indexed; `ExactExecutionSemanticData` has three fields, of which only `rows`
passes `Λ` on; `ComputeRowSemanticData` has twenty-two, of which only `comparison_leaves` mentions
it; `ExactServedMemoryTrace` has four (`roots`, `timestampPowersNodup`, `forestIndexRange`,
`semanticCoverage`) and none mentions `Λ`.  **No carrier field is added here.** -/

/-- **`Λ` is confined to `comparison_leaves`.**  Replacing that one field retypes the whole row
record at an arbitrary `Λ'`. -/
def redteam_row_data_transport_of_Lambda {q Λ Λ' : ℕ}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (d : ComputeRowSemanticData q Λ row)
    (h : ∀ c ∈ d.comparisons, c.LeavesBounded Λ') :
    ComputeRowSemanticData q Λ' row :=
  { d with comparison_leaves := h }

/-- …and the transport is the identity on every other field, `comparisons` and `needs` included. -/
theorem redteam_row_data_transport_is_pointwise {q Λ Λ' : ℕ}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (d : ComputeRowSemanticData q Λ row)
    (h : ∀ c ∈ d.comparisons, c.LeavesBounded Λ') :
    (redteam_row_data_transport_of_Lambda d h).comparisons = d.comparisons ∧
      (redteam_row_data_transport_of_Lambda d h).needs = d.needs ∧
      (redteam_row_data_transport_of_Lambda d h).realizedNouns = d.realizedNouns ∧
      (redteam_row_data_transport_of_Lambda d h).root = d.root :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The same at the execution level: only `rows` carries `Λ`. -/
def redteam_semantic_data_transport_of_Lambda {q Λ Λ' : ℕ} {cfg : ExactConfig F K}
    {exec : ExactExecution cfg}
    (D : ExactExecutionSemanticData q Λ cfg exec)
    (h : ∀ (i : Fin cfg.compRows), ∀ c ∈ (D.rows i).comparisons, c.LeavesBounded Λ') :
    ExactExecutionSemanticData q Λ' cfg exec where
  language := D.language
  rowAccepted := D.rowAccepted
  rows := fun i => redteam_row_data_transport_of_Lambda (D.rows i) (h i)

/-- **`ExactServedMemoryTrace` takes `Λ` only as an inert type parameter.**  All four fields are
copied verbatim across the transport — in particular `semanticCoverage`, whose statement reads
`needs.served`, which the transport leaves fixed. -/
def redteam_served_trace_transport_of_Lambda {q Λ Λ' : ℕ} {cfg : ExactConfig F K}
    {exec : ExactExecution cfg}
    {D : ExactExecutionSemanticData q Λ cfg exec} {execA : ExactExecution cfg}
    (h : ∀ (i : Fin cfg.compRows), ∀ c ∈ (D.rows i).comparisons, c.LeavesBounded Λ')
    (T : ServedMemoryTrace.ExactServedMemoryTrace q Λ cfg exec D execA) :
    ServedMemoryTrace.ExactServedMemoryTrace q Λ' cfg exec
      (redteam_semantic_data_transport_of_Lambda D h) execA where
  roots := T.roots
  timestampPowersNodup := T.timestampPowersNodup
  forestIndexRange := T.forestIndexRange
  semanticCoverage := T.semanticCoverage

/-! ## §D. Section 2 items 4–5 — `census`, `slotSemantics`, non-circularity -/

/-- **`census` IS the paper's leaf window on the reconstructed list**, re-derived independently:
`CombinedSkeletonCensus` unfolds to `leaves ≤ Λ` on `skeletonPairs` and on `edgePairs`, nothing
more and nothing less.  *Precision for the ledger:* this is an unfolding receipt.  It shows the
premise has no content beyond those two leaf windows; it does not by itself prove that neither
conjunct is separately reducible. -/
theorem redteam_census_is_the_leaf_window (S : SemanticSkeleton) (Λ : ℕ) :
    EdgeComparisonCensus.CombinedSkeletonCensus K S Λ ↔
      ((∀ pair ∈ BoundSemanticTrace.skeletonPairs K S,
          pair.1.leaves ≤ Λ ∧ pair.2.leaves ≤ Λ) ∧
        (∀ pair ∈ EdgeComparisonCensus.edgePairs S.computeTree,
          pair.1.leaves ≤ Λ ∧ pair.2.leaves ≤ Λ)) :=
  ⟨fun h => ⟨h.p8.leaves_bounded, h.edges.leaves_bounded⟩, fun h => ⟨⟨h.1⟩, ⟨h.2⟩⟩⟩

/-- `RowStateNeeds` has exactly two fields and neither ties a served lookup to the row's own
memory records. -/
theorem redteam_rowStateNeeds_two_fields {z : K} {st : ComputeTable.State}
    (needs : RowStateNeeds z st) :
    needs = { served := needs.served, served_count := needs.served_count } := by
  cases needs
  rfl

/-- **`semanticCoverage` is an identity on exactly the four components the missing identification is
about.**  It produces a `Service` whose `record`, `root`, `child` and `axis` are the *same* as the
lookup's; it never relates them to the reconstructed skeleton. -/
theorem redteam_semanticCoverage_is_a_four_component_identity {q Λ : ℕ} {cfg : ExactConfig F K}
    {exec : ExactExecution cfg}
    {D : ExactExecutionSemanticData q Λ cfg exec} {execA : ExactExecution cfg}
    (T : ServedMemoryTrace.ExactServedMemoryTrace q Λ cfg exec D execA)
    (row : Fin cfg.compRows) (lookup : ServedNounLookup (exec.computeRowAt row).2.1.z)
    (hl : lookup ∈ (D.rows row).needs.served) :
    ∃ (i : Fin cfg.kMem) (s : ServedMemoryTrace.Service cfg execA),
      s ∈ (T.roots i).services ∧
        s.record = lookup.record ∧ s.root = lookup.root ∧
        s.child = lookup.child ∧ s.axis = lookup.axis :=
  T.semanticCoverage row lookup hl

/-! ## §E. Accounting — nothing moved -/

theorem redteam_residual_pair_still_eleven_one_two : 11 + 1 + 2 = 14 := rfl

#print axioms redteam_consDecomposed_gives_the_premise
#print axioms redteam_bounded_cons_shaped_row_is_not_consDecomposed
#print axioms redteam_consReflection_is_circular
#print axioms redteam_combinedBounded_needs_only_named_skeletonBounded
#print axioms redteam_consDecomposed_route_factors_through_skeletonBounded
#print axioms redteam_censusRecordPremises_still_five
#print axioms redteam_distinctCensus_compRows_is_three
#print axioms redteam_distinctCensus_row_zero_consDecomposed
#print axioms redteam_distinctCensus_two_of_five_fields_are_filled
#print axioms redteam_residualPremises_inhabited_at_f73
#print axioms redteam_sizeWindow_is_two_lower_bounds
#print axioms redteam_route_pins_the_order
#print axioms redteam_sizeWindowBound_is_seed_free
#print axioms redteam_distinctCensus_numerals
#print axioms redteam_route_false_at_distinctCensus
#print axioms redteam_gap_at_distinctCensus
#print axioms redteam_concrete_numerals
#print axioms redteam_route_holds_at_concrete
#print axioms redteam_concrete_sizeWindow_is_empty
#print axioms redteam_multiRoot_seed
#print axioms redteam_multiRoot_numerals
#print axioms redteam_route_holds_at_multiRoot
#print axioms redteam_multiRoot_sizeWindow_covers_only_leaves
#print axioms redteam_multiRoot_sizeWindow_excludes_cells
#print axioms redteam_row_data_transport_of_Lambda
#print axioms redteam_row_data_transport_is_pointwise
#print axioms redteam_semantic_data_transport_of_Lambda
#print axioms redteam_served_trace_transport_of_Lambda
#print axioms redteam_census_is_the_leaf_window
#print axioms redteam_rowStateNeeds_two_fields
#print axioms redteam_semanticCoverage_is_a_four_component_identity
#print axioms redteam_residual_pair_still_eleven_one_two

end

end Nock.RedTeam.Batch136
