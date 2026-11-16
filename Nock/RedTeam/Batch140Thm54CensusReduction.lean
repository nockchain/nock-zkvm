import Nock.NockVMROM.Thm54.CensusExtraClosure
import Nock.NockVMROM.Thm54.SkeletonCommitment
import Nock.RedTeam.Batch137Thm54CarrierProgram

/-!
**Nothing here
inhabits a named premise, adds a carrier field, weakens a census predicate, or ticks a `§J` box.**
`BuildableNockExecution` keeps its fourteen fields, `HonestCommitment.Data` its sixteen,
`ResidualPremises` its four and `CensusRecordPremises` its five.  No statement below is a verdict on
the paper construction, which is not in question at any point.

## §A.

Between them those settle that the reduction's *two* hypotheses are
independent of each other, and that the window is strictly weaker than the conclusion.

They do **not** settle the question the equivalence test actually asks — whether `RowLeafWindow` is
a relabelling of `census`.  For that the converse direction is needed: does `census` imply
`RowLeafWindow`?  `b140_census_does_not_imply_rowLeafWindow` compiles that it does not, at an OP3
row.  The mechanism is the same one `CensusExtraClosure` §C already uses for `sizeWindowBound`: the
OP3 comparison list mentions `sf 0.result` only under `Noun.wut`, whose value has one leaf
whatever its argument, so the census never inspects that noun while `RowLeafWindow` bounds it.

Consequently the two predicates are independent in **both** directions and `RowLeafWindow` is not a
rename of `census`.  The reduction is a genuine change of object.

The same artifact carries a scope note that should not be lost: because `census ⊬ RowLeafWindow`,
the reduction is **not a weakening** of the residual.  `RowLeafWindow` demands the window on nouns
the census does not read — every row's `subject`, and every subformula projection at every row,
including slots no comparison mentions.  What makes the trade legitimate is not that the new
obligation is smaller but that it is the paper's own object rather than a Lean-side artifact.

## §B. Does `RowLeafWindow` hold at F97?  It is **undecided in this build**, and here is the residual

The verdict is neither "holds" nor "fails".  It is not derivable from what the build records, and it
is not refutable either, so the F97 census bundle is **not** inhabited and the `§J` `census` row is
**not** tickable.  What is compiled is the exact residual.

1. `b140_distinctCensus_reconstruction_states` — every row of the reconstruction
   `skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)` at the released fixture is `.s5` or
   `.s1`, for every `(P, M)` pair.  This is `reconstructed_rows_are_nodes` composed with
   `reconstructed_row_state`, both already in the build.
2. `b140_distinctCensus_rowLeafWindow_residual` — the F97 window therefore follows from just two
   inputs: the three public triples, and the `OP_5` row's subformula projections.
3. `b140_s5_third_subformula_is_atom` — at an `OP_5` row the third subformula index is the literal
   `.atom 0` in all three slots, so the projection obligation is **six** nouns, not nine.  By
   `reconstructed_subformula_is_a_chosen_witness` each of the six is a `chooseNoun`, characterised
   only up to `enc` and `BoundedBy q`.
4. `b140_distinctCensus_censusRecordPremises_of_triples_and_op5` — the whole five-field bundle at
   F97 from exactly those two inputs.  This is a **conditional** theorem and is not an inhabitation;
   `CensusExtraClosure.censusRecordPremises_still_five_here` is unchanged.

Why the six chosen nouns cannot be resolved here.  `Batch137.redteam_c2_noncarrier_route_blocked`
already compiles that an atom range plus an encoding equation do not determine a leaf count at a
non-degenerate seed.  What §B adds is the *fixture-specific* form of that obstruction, because at
F97 `Batch137.redteam_leaves_eq_of_enc_eq_of_windows` does give something: equal encodings force
equal leaf counts as soon as **both** counts sit below `orderOf z`.  At the released fixture
`orderOf z = 16` while `Λ = 7` (`CensusExtraClosure.distinctCensus_Lambda_and_order`), so the gap is
exactly the band `8 … 15`, and `b140_f97_size_coordinate_cannot_enforce_the_window` exhibits it: a
four-leaf noun and a twenty-leaf noun have the same `size` coordinate at the fixture seed, one
inside the window and one outside.  The `size` coordinate is the only coordinate of `enc` that is a
function of the leaf count alone, so it cannot enforce `leaves ≤ 7`.

This is the same arithmetic that `CensusExtraClosure.sizeWindow_gap_at_distinctCensus` records for
`sizeWindowBound`; §B records that `census` inherits it through `RowLeafWindow` at the `OP_5` row.

## §C.

The
transcriptions are exact, including argument order at `OP_8`:

* `f = cons(f_h, f_t)`, "always operative" — the paper (prose), `1848` (the item);
* `cons(f_th, f_tt) = f_t` under `∑_{i∈{2,5,6,7,8,9}} op_i = 1` — guard the paper, equation
  the paper;
* `cons(f_tth, f_ttt) = f_tt` under `op_6 = 1` — guard the paper, equation the paper;
* `OP_8`'s pushed subject `child_one_input ← (cons(sf_evaluation₂, input_subject),
  formula_tail_tail)` — the paper, with `sf_evaluation₂` first, as `RowCellIdentities`'s
  `push_cons` has it;
* the `cons`-state check `evaluation = cons(sf_evaluation₁, sf_evaluation₂)` — the paper,
  under the `type(formula_head) = cell ⇒ state = cons` guard at the paper, and transcribed in
  the `e` row of `tab:V_comp_equality` at the paper.

No `cons` equation of `RowCellIdentities` is a Lean invention.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch140

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

/-! ## §A. `census` does not imply `RowLeafWindow`

`s3WindowRow` sets `state :=.s3`, is described as an `OP3` row, and
> its large noun is the `sf 0.result` projection the `OP_3` comparison list reaches under
> `Noun.wut` — which is `evaluation = ?(sf_evaluation_1)` at the paper, inside the branch
> `\ElsIf{formula_head = 3}` … `state = OP_3` that opens at `1763`.  `.s3` is `OP_3` by
> `ComputeTable.lean:140-150` (`State.toNat.s3 = 3`).  `BL-2`'s opcode identification is right and
> its site list over-counts: the defect is at three sites, not five, and none of them is here. -/

/-- An OP3 skeleton row whose only large noun is `sf 0.result` — the subformula projection the OP3
comparison list mentions only under `Noun.wut`.  Every noun the census actually inspects has at most
two leaves. -/
def s3WindowRow : ComputeRowSkeleton where
  state := .s3
  subject := .atom 0
  formula := .cell (.atom 0) (.atom 0)
  evaluation := .atom 0
  decomposition := fun _ _ => .atom 0
  subformula := fun _ _ slot => if slot = TripleSlot.result then fourLeaves else .atom 0
  memoryRecord := fun _ _ => ⟨.atom 0, .atom 0, 1⟩

def s3WindowSkeleton : SemanticSkeleton where
  computeTree := .node s3WindowRow []
  memoryForest := []

theorem s3WindowSkeleton_computeRows :
    computeSkeletonRows s3WindowSkeleton = [s3WindowRow] := by
  unfold computeSkeletonRows s3WindowSkeleton
  rw [bfsForest_cons_eq _ (by simp)]
  simp [bfsForest_nil]

/-- The large projection really is the one `RowLeafWindow` reads. -/
theorem s3WindowRow_subformula_result :
    P8Census.skeletonSubformula s3WindowRow 0 .result = fourLeaves := by
  simp [P8Census.skeletonSubformula, s3WindowRow, ComputeTable.fanoutComp]

/-- **The converse direction of the equivalence test.**  `CombinedSkeletonCensus` holds at `Λ = 2`
on this OP3 skeleton while `RowLeafWindow 2` fails at its only row, so `census` does not imply the
window.

The failure is uniform in `Λ`, not placed at a degenerate value: the window fails at every `Λ < 4`
while the census still holds at `Λ = 2`. -/
theorem b140_census_does_not_imply_rowLeafWindow :
    EdgeComparisonCensus.CombinedSkeletonCensus K s3WindowSkeleton 2 ∧
      ∀ Λ : ℕ, Λ < 4 → ¬ RowLeafWindow Λ s3WindowRow := by
  constructor
  · refine ⟨⟨?_⟩, ⟨?_⟩⟩
    · intro pair hp
      unfold BoundSemanticTrace.skeletonPairs at hp
      rw [List.mem_append] at hp
      rcases hp with hp | hp
      · simp only [SemanticSkeleton.publicClaim, s3WindowSkeleton, s3WindowRow,
          NTree.label_node, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl <;> simp [Noun.leaves]
      · rw [List.mem_map] at hp
        obtain ⟨c, hc, rfl⟩ := hp
        unfold P8Census.skeletonComparisonCensus at hc
        rw [List.mem_flatMap] at hc
        obtain ⟨s, hs, hcs⟩ := hc
        rw [s3WindowSkeleton_computeRows, List.mem_singleton] at hs
        subst hs
        simp only [P8Census.skeletonComparisons, s3WindowRow, P8Census.skeletonDec,
          P8Census.skeletonSubformula, P8Census.skeletonUse, decActive,
          hasTailDecomposition, ComputeTable.fanoutComp, List.mem_cons,
          List.not_mem_nil, or_false] at hcs
        rcases hcs with rfl | rfl | rfl | rfl | rfl <;>
          simp [SemanticTrace.ComparisonUse.pair, Noun.leaves, wut_leaves]
    · intro pair hp
      unfold EdgeComparisonCensus.edgePairs s3WindowSkeleton at hp
      rw [bfsForest_cons_eq _ (by simp)] at hp
      simp [bfsForest_nil, EdgeComparisonCensus.rowEdgePairs, NTree.childOpt] at hp
  · intro Λ hΛ hw
    have h := hw.2.2.2 0 .result
    rw [s3WindowRow_subformula_result, fourLeaves_leaves] at h
    omega

/-! ## §B. The F97 residual, measured -/

section F97

open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.NockVMROM.Thm54.DistinctCensusExecution

local instance : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic

-- Form R leftover first-row counts (live is `chainOneBitWeight`).
variable (hfirstD :
  (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.counts = 0 ∧
    (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.indicator = 0)
include hfirstD

/-- Every row of the F97 reconstruction is `OP_5` or `OP_1`, for every `(P, M)` pair. -/
theorem b140_distinctCensus_reconstruction_states
    (P : ResidualPremises (distinctCensusExecution hfirstD))
    (M : MemoryRecordPremises (distinctCensusExecution hfirstD)) :
    ∀ s ∈ computeSkeletonRows
        (skeletonOfNodes (computeNodesOf (distinctCensusExecution hfirstD) P)
          (memoryNodesOf (distinctCensusExecution hfirstD) M)),
      s.state = .s5 ∨ s.state = .s1 := by
  intro s hs
  obtain ⟨i, rfl⟩ := reconstructed_rows_are_nodes (distinctCensusExecution hfirstD) P M hs
  rw [reconstructed_row_state]
  exact distinctCensus_row_states hfirstD i

/-- At an `OP_5` row the third subformula index is the literal `.atom 0` in all three slots, because
`fanoutComp.s5 = 2`.  So the `OP_5` window obligation is six nouns, not nine. -/
theorem b140_s5_third_subformula_is_atom {s : ComputeRowSkeleton} (h : s.state = .s5)
    (slot : TripleSlot) :
    P8Census.skeletonSubformula s 2 slot = .atom 0 := by
  rw [P8Census.skeletonSubformula, dif_neg]
  rw [h]
  decide

/-- **The F97 leaf window, reduced to two inputs.**  The three public triples, plus the `OP_5` row's
subformula projections, give `RowLeafWindow` at every row of the reconstruction.  The two `OP_1`
rows need nothing beyond their triples.

Conditional, and deliberately so: neither input is supplied by any field of
`(distinctCensusExecution hfirstD)`, `P`, `M`, or `HonestCommitment.Data`. -/
theorem b140_distinctCensus_rowLeafWindow_residual
    (P : ResidualPremises (distinctCensusExecution hfirstD))
    (M : MemoryRecordPremises (distinctCensusExecution hfirstD))
    (htriple : ∀ s ∈ computeSkeletonRows
        (skeletonOfNodes (computeNodesOf (distinctCensusExecution hfirstD) P)
          (memoryNodesOf (distinctCensusExecution hfirstD) M)),
      s.subject.leaves ≤ (distinctCensusExecution hfirstD).Λ ∧
        s.formula.leaves ≤ (distinctCensusExecution hfirstD).Λ ∧
          s.evaluation.leaves ≤ (distinctCensusExecution hfirstD).Λ)
    (hop5 : ∀ s ∈ computeSkeletonRows
        (skeletonOfNodes (computeNodesOf (distinctCensusExecution hfirstD) P)
          (memoryNodesOf (distinctCensusExecution hfirstD) M)),
      s.state = .s5 →
        ∀ (i : Fin 3) (slot : TripleSlot),
          (P8Census.skeletonSubformula s i slot).leaves ≤ (distinctCensusExecution hfirstD).Λ) :
    ∀ s ∈ computeSkeletonRows
        (skeletonOfNodes (computeNodesOf (distinctCensusExecution hfirstD) P)
          (memoryNodesOf (distinctCensusExecution hfirstD) M)),
      RowLeafWindow (distinctCensusExecution hfirstD).Λ s := by
  intro s hs
  obtain ⟨h1, h2, h3⟩ := htriple s hs
  rcases b140_distinctCensus_reconstruction_states hfirstD P M s hs with h5 | hs1
  · exact ⟨h1, h2, h3, hop5 s hs h5⟩
  · refine rowLeafWindow_of_fanout_zero (distinctCensus_one_le_Lambda hfirstD) ?_ h1 h2 h3
    rw [hs1]
    decide

/-- **The whole five-field bundle at F97 from those two inputs.**

**This is not an inhabitation.**  Both hypotheses are hypotheses; no `CensusRecordPremises` term is
produced from nothing, and `censusRecordPremises_still_five_here` is unchanged. -/
theorem b140_distinctCensus_censusRecordPremises_of_triples_and_op5
    (P : ResidualPremises (distinctCensusExecution hfirstD))
    (M : MemoryRecordPremises (distinctCensusExecution hfirstD))
    (htriple : ∀ s ∈ computeSkeletonRows
        (skeletonOfNodes (computeNodesOf (distinctCensusExecution hfirstD) P)
          (memoryNodesOf (distinctCensusExecution hfirstD) M)),
      s.subject.leaves ≤ (distinctCensusExecution hfirstD).Λ ∧
        s.formula.leaves ≤ (distinctCensusExecution hfirstD).Λ ∧
          s.evaluation.leaves ≤ (distinctCensusExecution hfirstD).Λ)
    (hop5 : ∀ s ∈ computeSkeletonRows
        (skeletonOfNodes (computeNodesOf (distinctCensusExecution hfirstD) P)
          (memoryNodesOf (distinctCensusExecution hfirstD) M)),
      s.state = .s5 →
        ∀ (i : Fin 3) (slot : TripleSlot),
          (P8Census.skeletonSubformula s i slot).leaves ≤ (distinctCensusExecution hfirstD).Λ) :
    CensusRecordPremises (distinctCensusExecution hfirstD) P M :=
  distinctCensus_censusRecordPremises_of_leafWindow hfirstD P M
    (b140_distinctCensus_rowLeafWindow_residual hfirstD P M htriple hop5)

/-- A twenty-leaf noun: `20 ≡ 4 [MOD 16]`. -/
def twentyLeaves : Noun := .cell fourLeaves (.cell eightLeaves eightLeaves)

theorem twentyLeaves_leaves : twentyLeaves.leaves = 20 := by
  simp [twentyLeaves, fourLeaves, eightLeaves, Noun.leaves]

/-- **Why the six chosen nouns are not resolvable at F97.**  `enc`'s `size` coordinate is
`z ^ n.leaves` and is the only coordinate that is a function of the leaf count alone.  At the
released fixture `orderOf z = 16` while `Λ = 7`, so that coordinate is blind to the band `8 … 15`:
a four-leaf noun and a twenty-leaf noun share it, one inside the window and one outside.

Together with `Batch137.redteam_leaves_eq_of_enc_eq_of_windows` — which pins leaf counts only when
*both* sit below `orderOf z` — this is the exact residual at the `OP_5` row: the window would follow
from `chosen.leaves < 16`, which nothing in the build supplies.  It is the same arithmetic
`CensusExtraClosure.sizeWindow_gap_at_distinctCensus` records for `sizeWindowBound`. -/
theorem b140_f97_size_coordinate_cannot_enforce_the_window :
    (GlobalCarryRecognizer.enc (distinctCensusExecution hfirstD).cfg.challenges.z fourLeaves).size =
        (GlobalCarryRecognizer.enc (distinctCensusExecution hfirstD).cfg.challenges.z twentyLeaves).size ∧
      fourLeaves.leaves ≤ (distinctCensusExecution hfirstD).Λ ∧
        ¬ twentyLeaves.leaves ≤ (distinctCensusExecution hfirstD).Λ := by
  have h16 : (distinctCensusExecution hfirstD).cfg.challenges.z ^ 16 = 1 := by
    have h := pow_orderOf_eq_one (distinctCensusExecution hfirstD).cfg.challenges.z
    rwa [(distinctCensus_Lambda_and_order hfirstD).2] at h
  refine ⟨?_, ?_, ?_⟩
  · simp only [GlobalCarryRecognizer.enc_size, fourLeaves_leaves, twentyLeaves_leaves]
    calc (distinctCensusExecution hfirstD).cfg.challenges.z ^ 4
        = (distinctCensusExecution hfirstD).cfg.challenges.z ^ 4 * 1 := by rw [mul_one]
      _ = (distinctCensusExecution hfirstD).cfg.challenges.z ^ 4 *
            (distinctCensusExecution hfirstD).cfg.challenges.z ^ 16 := by rw [h16]
      _ = (distinctCensusExecution hfirstD).cfg.challenges.z ^ 20 := by rw [← pow_add]
  · rw [fourLeaves_leaves, (distinctCensus_Lambda_and_order hfirstD).1]
    omega
  · intro hleaf
    have hΛ : (distinctCensusExecution hfirstD).Λ = 7 :=
      (distinctCensus_Lambda_and_order hfirstD).1
    have h20 : twentyLeaves.leaves = 20 := twentyLeaves_leaves hfirstD
    rw [h20, hΛ] at hleaf
    exact (Nat.not_le.mpr (by norm_num : 7 < 20)) hleaf

end F97

/-! ## §D. The `CanonicalCommitmentCheck` lead — wiring, and the one wire that is hard

`StrictCommitment.CanonicalCommitmentCheck p C` is
`∀ n ∈ commitmentNouns C, FieldEmbedding.BoundedBy p n ∧ n.leaves ≤ C.nounSizeBound`, and
`commitmentNouns C` enumerates exactly the *active* addresses of every committed compute row
(`.subject`, `.formula`, `.evaluation`, active `.dec`, active `.sub i slot`, active `.memRec`) plus
the memory rows.  Its second conjunct, restricted to the public triple and the active subformula
addresses, **is `RowLeafWindow C.nounSizeBound`** — the inactive subformula projections are the
literal `.atom 0`, which needs only `1 ≤ C.nounSizeBound`.  So this is a **wiring** shape and not a
new predicate, and `b140_rowLeafWindow_of_canonicalCommitmentCheck` compiles the wire.

The check is genuinely a check: seed-independent, decidable
(`StrictCommitment.instDecidableCanonicalCommitmentCheck`), a bounded quantification over one
explicit finite list, and non-vacuous at a concrete prime
(`StrictCommitment.sampleCommitment_canonical`).

**What it does not give, and this is where the work is.**

1. *It is held by no carrier in the census cone.*  `CanonicalCommitmentCheck` occurs only in
   `SkeletonCommitment.lean`, `ActiveFingerprintScan.lean`, `RawSemanticAssembly.lean`,
   `StrictRawStrategy.lean` and `Batch24`.  `CommitmentResidual` carries `commitment`, `scan`,
   `shapeMatch` and `rowFrame` but **not** the canonical check, and `HonestCommitment.Data` carries
   `nounSizeBound : ℕ` as a bare scalar with no property attached.  Adding the check would change
   `CommitmentResidual` (or `Data`), not `BuildableNockExecution`, `ResidualPremises` or
   `CensusRecordPremises`.
2. *The layers differ.*  `census` is stated over the **reconstruction**
   `skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)`; the check is over `C.skeleton`.
   Bridging them is the commitment-to-reconstruction identification, i.e. the A2 binding residual
   (`BindsAt` / `ExecTreeShapeMatchesAt` / `RowFrameChecksAt`), and it is the load-bearing wire.
3. *The scalars are untied.*  `C.nounSizeBound ≤ E.Λ` is needed and is stated nowhere.  At the
   assembled layer `GenericHonestData.censusAssemblyOf_nounSizeBound` pins
   `(censusAssemblyOf …).nounSizeBound = E.Λ` by `rfl`, but that is `CensusAssemblyPremises`'s
   scalar, not `SkeletonCommitment`'s.
4. *It does not subsume `RowCellIdentities`.*  The check bounds each `dec` slot individually, but the
   census compares `s.formula` against `.cell (d.f_h) (d.f_t)`, whose leaf count is the **sum**.
   So the paper's `cons` equations are still required, which is what
   `b140_census_of_canonicalCommitmentCheck` records.

**Verdict: a wiring task in shape, whose one hard wire is (2), the skeleton identification.**  Items
(1) and (3) are plumbing; (2) is a real obligation and is the same one the A2 residual already
names.  This is strictly better placed than a new carrier field, because the object is a check the
verifier can run rather than a hypothesis it must be handed. -/

section CommitmentWiring

open Nock.NockVMROM.Thm54.StrictCommitment

/-- **The wire.**  The deterministic, seed-independent, decidable pre-seed check supplies exactly
`RowLeafWindow` at its own committed bound, on every committed compute row.  No new predicate, no
carrier field, no seed. -/
theorem b140_rowLeafWindow_of_canonicalCommitmentCheck {p : ℕ} {C : SkeletonCommitment}
    (h : CanonicalCommitmentCheck p C) (hΛ : 1 ≤ C.nounSizeBound) :
    ∀ s ∈ computeSkeletonRows C.skeleton, RowLeafWindow C.nounSizeBound s := by
  intro s hs
  have key : ∀ a : ComputeSlotAddress, computeSlotActive s.state a = true →
      (computeSlotNoun s a).leaves ≤ C.nounSizeBound := fun a ha =>
    h.computeSlot_leaves hs ((mem_activeComputeSlotAddresses_iff _ _).2 ha)
  refine ⟨key .subject rfl, key .formula rfl, key .evaluation rfl, ?_⟩
  intro i slot
  by_cases hi : (i : ℕ) < ComputeTable.fanoutComp s.state
  · rw [P8Census.skeletonSubformula, dif_pos hi]
    have hk := key (.sub i slot) (by simp [computeSlotActive, hi])
    rwa [computeSlotNoun_sub_of_active hi slot] at hk
  · rw [P8Census.skeletonSubformula, dif_neg hi]
    simpa [Noun.leaves] using hΛ

/-- **`census` at the committed skeleton, from a check the verifier can already run plus the paper's
`cons` equations.**  `RowCellIdentities` is *not* subsumed by the check and remains: the check bounds
each `dec` slot individually, while the census compares the formula against their `cons` cell, whose
leaf count is the sum.

Still not an inhabitation of the `CensusRecordPremises` field: this is `C.skeleton` at
`C.nounSizeBound`, and the field is the reconstruction at `E.Λ`. -/
theorem b140_census_of_canonicalCommitmentCheck {p : ℕ} {C : SkeletonCommitment}
    (h : CanonicalCommitmentCheck p C) (hΛ : 1 ≤ C.nounSizeBound)
    (hc : ∀ s ∈ computeSkeletonRows C.skeleton, RowCellIdentities s) :
    EdgeComparisonCensus.CombinedSkeletonCensus K C.skeleton C.nounSizeBound :=
  census_of_leafWindow _ _ hΛ hc (b140_rowLeafWindow_of_canonicalCommitmentCheck h hΛ)

/-- The remaining wire, named as an explicit hypothesis so it is not mistaken for free: with the
commitment's rows identified with the reconstruction's and its scalar bound inside `E.Λ`, the check
discharges `RowLeafWindow` at the layer `CensusRecordPremises` quantifies over. -/
theorem b140_reconstruction_window_of_check_and_identification
    {p : ℕ} {C : SkeletonCommitment} (E : BuildableNockExecution F K)
    (P : ResidualPremises E) (M : MemoryRecordPremises E)
    (h : CanonicalCommitmentCheck p C) (hΛ : 1 ≤ C.nounSizeBound)
    (hbound : C.nounSizeBound ≤ E.Λ)
    (hident : ∀ s ∈ computeSkeletonRows
        (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)),
      s ∈ computeSkeletonRows C.skeleton) :
    ∀ s ∈ computeSkeletonRows
        (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)),
      RowLeafWindow E.Λ s := by
  intro s hs
  obtain ⟨h1, h2, h3, h4⟩ :=
    b140_rowLeafWindow_of_canonicalCommitmentCheck h hΛ s (hident s hs)
  exact ⟨h1.trans hbound, h2.trans hbound, h3.trans hbound,
    fun i slot => (h4 i slot).trans hbound⟩

end CommitmentWiring

/-! ## §C. Nothing moved -/

/-- The five census extras are still five named fields. -/
theorem b140_censusRecordPremises_still_five {E : BuildableNockExecution F K}
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

/-- `ResidualPremises` is still four named fields. -/
theorem b140_residualPremises_still_four {E : BuildableNockExecution F K}
    (P : ResidualPremises E) :
    P =
      { axisAtoms := P.axisAtoms
        inactiveDec := P.inactiveDec
        q_eq_ringChar := P.q_eq_ringChar } := by
  cases P
  rfl

#print axioms b140_census_does_not_imply_rowLeafWindow
#print axioms s3WindowSkeleton_computeRows
#print axioms s3WindowRow_subformula_result
#print axioms b140_distinctCensus_reconstruction_states
#print axioms b140_s5_third_subformula_is_atom
#print axioms b140_distinctCensus_rowLeafWindow_residual
#print axioms b140_distinctCensus_censusRecordPremises_of_triples_and_op5
#print axioms twentyLeaves_leaves
#print axioms b140_f97_size_coordinate_cannot_enforce_the_window
#print axioms b140_rowLeafWindow_of_canonicalCommitmentCheck
#print axioms b140_census_of_canonicalCommitmentCheck
#print axioms b140_reconstruction_window_of_check_and_identification
#print axioms b140_censusRecordPremises_still_five
#print axioms b140_residualPremises_still_four

end

end Nock.RedTeam.Batch140
