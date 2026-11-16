import Nock.NockVMROM.Thm54.RoundFibredSoundness

/-!
# The production failure union as one round-indexed cylinder union

`RoundFibredSoundness.lean` proved the general round-indexed union bound
(`RoundFibred.roundUnion_card_le`, `:376`) and identified each of the five `FailureUnion`
summands as a single-coordinate cylinder over strictly-earlier coordinates
(`liftSeed_eq_cylinder` `:722`, `zeroSeedFailureEvent_eq_cylinder` `:784`,
`guardedAxisFailureEvent_eq_cylinder` `:838`, `specializedTopologyFailureEvent_eq_cylinder`
`:915`).  What it did **not** do — recorded as the open seam in `IZ` §6 — is compose them end to
end: each summand's existing bound was re-derived individually, and the aggregate still came from
the hand-written `card_union_le` chain in
`ProductionP8Containment.failureUnion_card_le` (`ProductionP8Containment.lean:825`).

This module closes that seam **for the union bound**, which is the half that lives on the four
`JointCoins` coins.  It exhibits `FailureUnion` as *one* `RoundFibred.roundUnion` over the
coordinate set `{γ, αM, z} = {1, 2, 3}` of `jointChronology = ![3, 2, 1, 0]`, and re-derives

from `roundUnion_card_le_of_chronology` alone.  Same conclusion, same hypotheses, no new axioms;
`failureUnion_card_le` itself is untouched, and so is `FailureUnion` and `workload` — this is an
alternative derivation, not a replacement.

## The structural wrinkle, and how it is handled

`FailureUnion` has **five summands over only three distinct coordinates**: `zeroSeedFailureEvent`,
`collisionFailureEvent` and `SizeWindowFailure` all restrict the seed `z` (all three are
`liftSeed` of a challenge-independent `Finset K`), while `guardedAxisFailureEvent` restricts `αM`
and `specializedTopologyFailureEvent` restricts `γ`.  `roundUnion` takes **one** bad set per
coordinate, so the three seed summands are combined into a single seed bad set
`seedBad T C = {0} ∪ C.census.badSeeds ∪ sizeWindowFailureSeeds T.skeleton` — a `Finset K` union,
*not* three separate `roundUnion`s added afterwards.  `liftSeed_union` (`liftSeed` commutes with
`∪` on the seed axis) makes the identification `Finset`-exact rather than an inequality, and
`seedBad_readsOn_empty` gives its `ReadsOn (priorCoords jointChronology 3) = ReadsOn ∅`:
`seedBad` is literally constant in the challenge vector, which is what "committed before any coin
is sampled" means here.  Its cardinality bound `seedBad_card_le` is the sum of the three original
per-summand numerators, so the total `workload` is reproduced exactly and not weakened.

`αC` (coordinate `0`) is restricted by no summand; it carries the empty bad set and is left out of
the index set `s`, matching `RoundFibred`'s disclosure that its chronology position is not forced
by the construction.

## Scope

`{F K : Type}` at universe 0, inherited from `ProductionP8Containment`'s `variable {F K : Type}`
(`ProductionP8Containment.lean:30`) — a pre-existing pin, not introduced here.  The only fixed
value read from a hypothesis is `(2 : K) ≠ 0` on `h2`, verbatim from the target theorem, where it
is consumed by `production_guarded_axis_cardinal` (`ProductionAxisStructureVerifier.lean:410`).
Nothing here is specialized to a program, a skeleton, a field size or a characteristic.
-/

namespace Nock.NockVMROM.Thm54.ProductionRoundChronology

open scoped Classical BigOperators
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.RoundFibred
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness
open Nock.NockVMROM.Thm54.TemplateAxisCounting
open Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier
open Nock.NockVMROM.Thm54.SizeWindowCounting

set_option linter.unusedSectionVars false

noncomputable section

/-! ## 1. The union form of `roundUnion` at the three restricted coordinates -/

section Triple

variable {C : Type*} [Fintype C] [DecidableEq C]
variable {K : Type*} [Fintype K] [DecidableEq K]

/-- `roundUnion` over `{1, 2, 3}` *is* the union of the three single-coordinate cylinders.
`RoundFibred.roundUnion_subset_biUnion` (`:361`) only gives `⊆`; the reverse inclusion is what
lets `FailureUnion` be identified with a `roundUnion` as a `Finset` equality. -/
theorem roundUnion_triple (bad : Fin 4 → (Fin 4 → C) → Finset C) :
    roundUnion ({1, 2, 3} : Finset (Fin 4)) bad
      = (cylinder 1 (bad 1) ∪ cylinder 2 (bad 2)) ∪ cylinder 3 (bad 3) := by
  ext x
  simp only [roundUnion, cylinder, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, exists_eq_or_imp,
    exists_eq_left]
  tauto

/-- `liftSeed` commutes with union on the seed axis.  This is the exactness that makes the
three-seed-summand combination an identification rather than a weakening. -/
theorem liftSeed_union (A B : Finset K) :
    liftSeed A ∪ liftSeed B = liftSeed (A ∪ B) := by
  ext ω
  simp [Finset.mem_union]

end Triple

/-! ## 2. The combined seed bad set -/

section Production

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [Fintype K] [DecidableEq K]
variable [charRing : CharP K (ringChar K)]
variable {Λ : ℕ}

/-- **The three seed summands' bad sets, combined.**  `zeroSeedFailureEvent` contributes `{0}`
(`JointSoundness.lean:601`), `collisionFailureEvent` the census's `badSeeds`
(`JointSoundness.lean:615`), and `SizeWindowFailure` the window filter
(`SizeWindowCounting.lean:60`).  All three are `liftSeed` of a `Finset K` that mentions no
challenge, so their union is again such a set and the seed coordinate keeps exactly one bad
set. -/
def seedBad (T : ProductionStrategy F K)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus K T.skeleton Λ) : Finset K :=
  (({0} : Finset K) ∪ C.census.badSeeds (K := K)) ∪
    sizeWindowFailureSeeds (K := K) T.skeleton

/-- The combined seed bad set reads **no** coordinate: it is constant in the challenge vector.
`priorCoords jointChronology 3 = ∅` (`RoundFibred.seed_coord_prior`), so this is the strongest
form of the dependence hypothesis at the first-sampled coordinate. -/
theorem seedBad_readsOn_empty (T : ProductionStrategy F K)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus K T.skeleton Λ) :
    ReadsOn (C := K) (n := 4) (priorCoords jointChronology (3 : Fin 4))
      (fun _ : Fin 4 → K => seedBad T C) := fun _ _ _ => rfl

/-- The three seed summands of `FailureUnion` are exactly `liftSeed (seedBad T C)`. -/
theorem seedSummands_eq_liftSeed_seedBad (T : ProductionStrategy F K)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus K T.skeleton Λ) :
    ((zeroSeedFailureEvent : Finset (JointCoins K)) ∪
        collisionFailureEvent C.census) ∪ SizeWindowFailure (K := K) T.skeleton
      = liftSeed (seedBad T C) := by
  rw [zeroSeedFailureEvent, collisionFailureEvent, SizeWindowFailure,
    liftSeed_union, liftSeed_union]
  rfl

/-- The combined seed bound is the **sum of the three original numerators**: `1` from
`zeroSeedFailureEvent_card`, `(3 + 19·rows)·(2Λ−1)` from `collisionFailureEvent_card_le` composed
with `CombinedSkeletonCensus.count_le`, and `sizeWindowRootBound Λ` from
`sizeWindowFailureSeeds_card_le`.  Nothing is lost by combining them. -/
theorem seedBad_card_le (T : ProductionStrategy F K)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus K T.skeleton Λ)
    (hwindowBound : SizeWindowNounsBoundedBy T.skeleton Λ) :
    (seedBad T C).card ≤
      1 + (3 + 19 * (SemanticStrategy.computeSkeletonRows T.skeleton).length) * (2 * Λ - 1)
        + sizeWindowRootBound Λ := by
  have h1 : (({0} : Finset K) ∪ C.census.badSeeds (K := K)).card
      ≤ 1 + (3 + 19 * (SemanticStrategy.computeSkeletonRows T.skeleton).length)
              * (2 * Λ - 1) := by
    refine (Finset.card_union_le _ _).trans ?_
    have hb := (C.census.badSeeds_card_le (K := K)).trans
      (Nat.mul_le_mul_right (2 * Λ - 1) C.count_le)
    simpa using Nat.add_le_add_left hb 1
  refine (Finset.card_union_le _ _).trans ?_
  exact Nat.add_le_add h1 (sizeWindowFailureSeeds_card_le T.skeleton Λ hwindowBound)

/-! ## 3. The one bad-set family on the four `JointCoins` coordinates -/

/-- **The production verifier's round-indexed bad-set family.**  Coordinate `0` is `αC`, which no
summand restricts; `1` is `γ`, restricted by the topology event through a bad set reading `(z, αM)`;
`2` is `αM`, restricted by the guarded-axis event through a bad set reading `z`; `3` is `z`,
restricted by the combined seed bad set, which reads nothing.  This is the object `IZ` §6 said was
missing — a chronology for the *production* verifier on the four coins, as opposed to
`Staged.StagedTable`'s six challenges over three rounds. -/
def jointBad (T : ProductionStrategy F K)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus K T.skeleton Λ) (lmb : K) :
    Fin 4 → (Fin 4 → K) → Finset K :=
  ![ fun _ => ∅,
     fun x => topologyBad T.verifier.raw lmb (x 3) (x 2),
     fun x => guardedAxisBad T lmb (x 3),
     fun _ => seedBad T C ]

@[simp] theorem jointBad_zero (T : ProductionStrategy F K)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus K T.skeleton Λ) (lmb : K) :
    jointBad T C lmb 0 = fun _ => (∅ : Finset K) := rfl

@[simp] theorem jointBad_one (T : ProductionStrategy F K)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus K T.skeleton Λ) (lmb : K) :
    jointBad T C lmb 1 = fun x : Fin 4 → K => topologyBad T.verifier.raw lmb (x 3) (x 2) := rfl

@[simp] theorem jointBad_two (T : ProductionStrategy F K)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus K T.skeleton Λ) (lmb : K) :
    jointBad T C lmb 2 = fun x : Fin 4 → K => guardedAxisBad T lmb (x 3) := rfl

@[simp] theorem jointBad_three (T : ProductionStrategy F K)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus K T.skeleton Λ) (lmb : K) :
    jointBad T C lmb 3 = fun _ : Fin 4 → K => seedBad T C := rfl

/-- **`FailureUnion` is one `roundUnion`.**  A `Finset` equality, not an inclusion: the five
summands reassociate into the three coordinate blocks and each block is the corresponding
cylinder.  `Λ`, `T` and `C` are threaded; nothing is quantified independently. -/
theorem failureUnion_eq_roundUnion (T : ProductionStrategy F K) (lmb : K)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus K T.skeleton Λ) :
    ProductionP8Containment.FailureUnion T C lmb
      = (roundUnion ({1, 2, 3} : Finset (Fin 4)) (jointBad T C lmb)).map
          jointVecEquiv.toEmbedding := by
  haveI : Nonempty K := ⟨0⟩
  have hblocks :
      ProductionP8Containment.FailureUnion T C lmb
        = (specializedTopologyFailureEvent T.verifier.raw lmb ∪ guardedAxisFailureEvent T lmb)
            ∪ liftSeed (seedBad T C) := by
    rw [← seedSummands_eq_liftSeed_seedBad T C]
    ext ω
    simp only [ProductionP8Containment.FailureUnion, Finset.mem_union]
    tauto
  rw [hblocks, roundUnion_triple, jointBad_one, jointBad_two, jointBad_three,
    Finset.map_union, Finset.map_union,
    ← specializedTopologyFailureEvent_eq_cylinder T.verifier.raw lmb,
    ← guardedAxisFailureEvent_eq_cylinder T lmb,
    ← liftSeed_eq_cylinder (seedBad T C)]

/-! ## 4. The bound, re-derived from the general principle -/

/-- **The target, re-derived.**  Same conclusion and same hypotheses as
`ProductionP8Containment.failureUnion_card_le` (`ProductionP8Containment.lean:825`), but obtained
from `RoundFibred.roundUnion_card_le_of_chronology` (`RoundFibredSoundness.lean:388`) applied once
to `jointBad`, rather than from five per-summand `have`s and a `Finset.card_union_le` chain.

The `* Fintype.card K ^ 3` in the target and the general bound's `Fintype.card C ^ (n - 1)` are
the *same* factor: `n = 4` is the number of `JointCoins` coins, so `|K|^{4-1} = |K|³`.  That is
the content of the exercise — the existing per-summand `· |K|³` is not five coincidences but one
free-coordinate count.

The three bad-set cardinality bounds fed in are `topologyBadGammas_card_le`
(`RawTopologyRAP.lean:351`) with `htopology`, `production_guarded_axis_cardinal`
(`ProductionAxisStructureVerifier.lean:410`) with `h2` and `haxis`, and `seedBad_card_le` with
`hwindowBound`.  The three dependence facts are `topologyBad_readsOn_prior`
(`RoundFibredSoundness.lean:904`), `guardedAxisBad_readsOn_prior`
(`RoundFibredSoundness.lean:825`) and `seedBad_readsOn_empty`, all stated against
`priorCoords jointChronology`. -/
theorem failureUnion_card_le_of_roundUnion
    (h2 : (2 : K) ≠ 0)
    (T : ProductionStrategy F K) (lmb : K)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus K T.skeleton Λ)
    (topologyBound axisWorkload : ℕ)
    (hwindowBound : SizeWindowNounsBoundedBy T.skeleton Λ)
    (htopology :
      ∀ z (hz : z ≠ 0) α lmb,
        topologyWorkload
          (T.verifier.raw.afterAlphaM z hz α lmb).familyData.base ≤ topologyBound)
    (haxis :
      ∀ z (hz : z ≠ 0),
        templateAxisWorkload (committedTemplate T.verifier z hz) ≤ axisWorkload) :
    (ProductionP8Containment.FailureUnion T C lmb).card ≤
      ProductionP8Containment.workload T Λ topologyBound axisWorkload * Fintype.card K ^ 3 := by
  haveI : Nonempty K := ⟨0⟩
  -- the per-coordinate numerators
  set seedBound : ℕ :=
    1 + (3 + 19 * (SemanticStrategy.computeSkeletonRows T.skeleton).length) * (2 * Λ - 1)
      + sizeWindowRootBound Λ with hseedBound
  set B : Fin 4 → ℕ := ![0, topologyBound, axisWorkload, seedBound] with hB
  -- dependence: each coordinate's bad set reads only strictly-earlier coordinates
  have hdep : ∀ i ∈ ({1, 2, 3} : Finset (Fin 4)),
      ReadsOn (C := K) (priorCoords jointChronology i) (jointBad T C lmb i) := by
    intro i hi
    fin_cases hi
    · exact jointBad_one T C lmb ▸ topologyBad_readsOn_prior T.verifier.raw lmb
    · exact jointBad_two T C lmb ▸ guardedAxisBad_readsOn_prior T lmb
    · exact jointBad_three T C lmb ▸ seedBad_readsOn_empty T C
  -- cardinality: each coordinate's bad set is small, uniformly in the earlier coordinates
  have hcard : ∀ (i : Fin 4) (x : Fin 4 → K), (jointBad T C lmb i x).card ≤ B i := by
    intro i x
    fin_cases i
    · simp [hB]
    · show (topologyBad T.verifier.raw lmb (x 3) (x 2)).card ≤ topologyBound
      by_cases hz : x 3 ≠ 0
      · simp only [topologyBad, dif_pos hz]
        exact (topologyBadGammas_card_le _).trans (htopology (x 3) hz (x 2) lmb)
      · simp only [ne_eq, not_not] at hz
        simp [topologyBad, hz]
    · show (guardedAxisBad T lmb (x 3)).card ≤ axisWorkload
      by_cases hz : x 3 ≠ 0
      · simp only [guardedAxisBad, dif_pos hz]
        exact (production_guarded_axis_cardinal h2 T.verifier (x 3) hz lmb).trans
          (haxis (x 3) hz)
      · simp only [ne_eq, not_not] at hz
        simp [guardedAxisBad, hz]
    · show (seedBad T C).card ≤ seedBound
      exact seedBad_card_le T C hwindowBound
  -- one application of the general principle
  have hgen := roundUnion_card_le_of_chronology (C := K) jointChronology
    ({1, 2, 3} : Finset (Fin 4)) (jointBad T C lmb) hdep B hcard
  rw [failureUnion_eq_roundUnion T lmb C, Finset.card_map]
  refine hgen.trans ?_
  -- `|K|^{4-1} = |K|³`, and the three numerators sum to `workload`
  have hsum : ∑ i ∈ ({1, 2, 3} : Finset (Fin 4)), Fintype.card K ^ (4 - 1) * B i
      ≤ ProductionP8Containment.workload T Λ topologyBound axisWorkload * Fintype.card K ^ 3 := by
    rw [show ({1, 2, 3} : Finset (Fin 4)) = insert 1 (insert 2 {3}) from rfl,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
    show Fintype.card K ^ (4 - 1) * topologyBound
        + (Fintype.card K ^ (4 - 1) * axisWorkload
          + Fintype.card K ^ (4 - 1) * seedBound)
      ≤ ProductionP8Containment.workload T Λ topologyBound axisWorkload * Fintype.card K ^ 3
    -- thirtieth move: `workload` also carries the Form R λ-event summand, which no
    -- `JointCoins` coordinate reads; it is slack here.  So is the thirty-third move's pair
    -- summand `reqPairWorkload T Λ` (it is priced on the lifted event, not on this union).
    have hw : ProductionP8Containment.workload T Λ topologyBound axisWorkload *
        Fintype.card K ^ 3 =
        Fintype.card K ^ (4 - 1) * topologyBound
          + (Fintype.card K ^ (4 - 1) * axisWorkload
            + Fintype.card K ^ (4 - 1) * seedBound)
          + ProductionP8Containment.formRUniformWorkload T * Fintype.card K ^ 3
          + ProductionP8Containment.reqPairWorkload T Λ * Fintype.card K ^ 3 := by
      simp only [ProductionP8Containment.workload, hseedBound]
      ring
    omega
  exact hsum

end Production

end

end Nock.NockVMROM.Thm54.ProductionRoundChronology

#print axioms Nock.NockVMROM.Thm54.ProductionRoundChronology.roundUnion_triple
#print axioms Nock.NockVMROM.Thm54.ProductionRoundChronology.liftSeed_union
#print axioms Nock.NockVMROM.Thm54.ProductionRoundChronology.seedBad_readsOn_empty
#print axioms Nock.NockVMROM.Thm54.ProductionRoundChronology.seedSummands_eq_liftSeed_seedBad
#print axioms Nock.NockVMROM.Thm54.ProductionRoundChronology.seedBad_card_le
#print axioms Nock.NockVMROM.Thm54.ProductionRoundChronology.failureUnion_eq_roundUnion
#print axioms Nock.NockVMROM.Thm54.ProductionRoundChronology.failureUnion_card_le_of_roundUnion
