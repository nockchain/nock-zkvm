/-
  Nock/NockVMROM/Thm54/TraceGen/GenGoodSeedExists.lean

  **A good NPR seed exists, so the compiler chooses it instead of the caller supplying it.**

  `nockCompiles_of_rom` (`GenNockCompiles.lean:383`) carries three hypotheses about the NPR seed
  `z`:

  * `hz   : z ≠ 0`,
  * `hbad : z ∉ (genSkeletonP8Census …).census.badSeeds`,
  * `hout : z ∉ SizeWindowCounting.sizeWindowFailureSeeds …`,

  and `GenCombinedCensusGood.not_mem_failureUnion_of_seed` discharges three of `FailureUnion`'s
  five summands from exactly those three.  So the three together say "this seed is outside the
  seed-axis part of the failure union".

  **This module adds no security property and no soundness error.**  The bad seeds are already
  excluded, and already *priced*, by the capstone's `complete_false_acceptance_bound`; this module
  is a **second consumer of the same counting**, used for **non-vacuity**: without some good seed
  the honest witness cannot be exhibited and `containment` holds vacuously.  No new failure event,
  no new summand and no new probability is introduced here, and the soundness bound is neither
  re-derived nor restated.

  ## Why this is a pigeonhole and not a fixed-point problem

  The three sets are stated at `mf := genMemoryForest z α (memInputs z) t`, which itself mentions
  `z`, so `∃ z, z ∉ Bad z` reads circular.  It is not: **neither set reads the memory forest.**

  * `EqualityOperandCensus.census_ignores_memoryForest` (`EqualityOperandCensus.lean:593`) already
    records this for `combinedSkeletonPairs`, by `rfl`; the same holds of its first summand
    `BoundSemanticTrace.skeletonPairs` (`BoundSemanticTrace.lean:100`), and
    `ComparisonCensus.badSeeds` (`JointSoundness.lean:274`) reads only `count` and `pair`, which
    `ofPairList` takes from the pair list alone.
  * `SizeWindowCounting.skeletonSizeWindowNouns` (`SizeWindowCounting.lean:33`) is
    `(computeSkeletonRows S).flatMap requiredSizeWindowNouns`, and `computeSkeletonRows` is the BFS
    of `S.computeTree`.

  So both are functions of the compute tree alone, `z` does not occur in them, and the argument is
  the plain union bound.  The three numerators are the ones the production counting already uses —
  `1` for the zero seed, `count · (2Λ−1)` for the collision census, and `sizeWindowRootBound Λ = ∑_{d=1}^{Λ} d` for
  the size-window roots (`SizeWindowCounting.sizeWindowFailureSeeds_card_le`).  Compare
  `ProductionRoundChronology.seedBad_card_le` (`ProductionRoundChronology.lean:141`), which sums
  the same three at the *combined* census; the p8 census used here has the smaller count bound
  `3 + 10 · rows` (`SkeletonP8Census.count_le`) because `hbad` is stated at the p8 census.

  ## The side condition

  At Tier A
  (`Λ = 22`, `rows = 8`, `|𝕂| = 769³`) it reads `3823 < 454756609`
  (`Batch261Thm54GoodSeedAtTierA.lean`).

  **Not claimed.**  `nockCompiles_of_rom`'s other seed-mentioning hypotheses — `hseed : SeedGood z
  t`, `hcoins : ComputeCoinsGeneric …`, and the forest-length capacity bounds — are *not* retired
  here; the corollary in §5 states them at the chosen seed.  `SeedGood` has its own counting
  (`GenDyckBadSeed.seedBad_card_le`) and a second pigeonhole over it is a separate piece of work.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompiles
import Nock.NockVMROM.Thm54.BelowDefs.TraceGen.GenGoodSeedExists
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.TraceGen.GoodSeed

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SizeWindowCounting
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace

noncomputable section

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

variable {lmb : K}

/-! ## 1. The budget and the pigeonhole

`seedBudget` is the sum of the three numerators the production counting already spends on the
seed axis.  Nothing new is counted. -/

theorem rows_lt_card_of_seedBudget {Λ rows : ℕ} [Fintype K] (hΛ : 1 ≤ Λ)
    (h : seedBudget Λ rows < Fintype.card K) : rows < Fintype.card K :=
  lt_trans (seedBudget_gt_rows hΛ) h

/-- **The counting, at a bare skeleton.**  The three bad sets together miss `seedBudget`-many
seeds at most, so a seed outside all three exists as soon as the carrier is bigger than that. -/
theorem exists_seed_outside_counted_events
    {S : SemanticSkeleton} {Λ : ℕ}
    (C : BoundSemanticTrace.SkeletonP8Census K S Λ)
    (hwin : SizeWindowNounsBoundedBy S Λ)
    (hcard : seedBudget Λ (computeSkeletonRows S).length < Fintype.card K) :
    ∃ z : K, z ≠ 0
      ∧ z ∉ C.census.badSeeds (K := K)
      ∧ z ∉ sizeWindowFailureSeeds (K := K) S := by
  classical
  have hb :
      ((({0} : Finset K) ∪ C.census.badSeeds (K := K)) ∪
        sizeWindowFailureSeeds (K := K) S).card < Fintype.card K := by
    refine lt_of_le_of_lt ?_ hcard
    have h1 : (({0} : Finset K) ∪ C.census.badSeeds (K := K)).card
        ≤ 1 + (3 + 10 * (computeSkeletonRows S).length) * (2 * Λ - 1) := by
      refine (Finset.card_union_le _ _).trans ?_
      have hcen := (C.census.badSeeds_card_le (K := K)).trans
        (Nat.mul_le_mul_right (2 * Λ - 1) C.count_le)
      simpa using Nat.add_le_add_left hcen 1
    refine (Finset.card_union_le _ _).trans ?_
    exact Nat.add_le_add h1 (sizeWindowFailureSeeds_card_le S Λ hwin)
  obtain ⟨z, hz⟩ := exists_notMem_of_card_lt hb
  simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hz
  exact ⟨z, hz.1.1, hz.1.2, hz.2⟩

/-! ## 2. Neither counted set reads the memory forest

These are the facts that make the existential non-circular: the forest that the seed itself
generates is invisible to both bad sets.  All four are `rfl` — the definitions simply do not
mention `SemanticSkeleton.memoryForest`.  `EqualityOperandCensus.census_ignores_memoryForest`
(`EqualityOperandCensus.lean:593`) is the same observation for `combinedSkeletonPairs`. -/

/-- The p8 pair list is a function of the compute tree alone. -/
theorem skeletonPairs_memoryForest_irrelevant (u : NTree (GenComputeRow K))
    (mf₁ mf₂ : List (NTree (GenMemoryRow K))) :
    BoundSemanticTrace.skeletonPairs K (genSemanticSkeleton u mf₁)
      = BoundSemanticTrace.skeletonPairs K (genSemanticSkeleton u mf₂) := rfl

/-- And so is its leaf-bound premise. -/
theorem sizeWindowNounsBoundedBy_memoryForest_irrelevant {Λ : ℕ}
    (u : NTree (GenComputeRow K)) (mf₁ mf₂ : List (NTree (GenMemoryRow K))) :
    SizeWindowNounsBoundedBy (genSemanticSkeleton u mf₁) Λ
      ↔ SizeWindowNounsBoundedBy (genSemanticSkeleton u mf₂) Λ := Iff.rfl

/-! ## 3. Over the program -/

/-- **A good seed exists for every accepted program.**  The conclusion is stated at the very forest
the chosen seed generates, `genMemoryForest z α (memInputs z) t`, so it plugs straight into
`nockCompiles_of_accepted`'s `hz`/`hbad`/`hout`. -/
theorem exists_good_seed_of_accepted {Λ : ℕ} (hΛ : 1 ≤ Λ)
    {fuel : ℕ} {subject formula : Noun} {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hconf : TraceConfined Λ (airReorder t))
    (α : K)
    (hwin : SizeWindowNounsBoundedBy
      (genSemanticSkeleton (bfsAssign (airReorder t))
        ([] : List (NTree (GenMemoryRow K)))) Λ)
    (hcard : seedBudget Λ (bfsForest [bfsAssign (airReorder t)]).length < Fintype.card K) :
    ∃ z : K, z ≠ 0
      ∧ z ∉ (genSkeletonP8Census (K := K) hΛ h hconf
              (genMemoryForest z α lmb (memInputs z) t)).census.badSeeds
      ∧ z ∉ sizeWindowFailureSeeds (K := K)
              (genSemanticSkeleton (bfsAssign (airReorder t))
                (genMemoryForest z α lmb (memInputs z) t)) := by
  obtain ⟨z, hz0, hbad, hout⟩ :=
    exists_seed_outside_counted_events
      (genSkeletonP8Census (K := K) hΛ h hconf ([] : List (NTree (GenMemoryRow K))))
      hwin (by rwa [computeSkeletonRows_length])
  refine ⟨z, hz0, ?_, ?_⟩
  · rw [badSeeds_memoryForest_irrelevant
      (genSkeletonP8Census (K := K) hΛ h hconf (genMemoryForest z α lmb (memInputs z) t))
      (genSkeletonP8Census (K := K) hΛ h hconf ([] : List (NTree (GenMemoryRow K))))]
    exact hbad
  · rw [sizeWindowFailureSeeds_memoryForest_irrelevant (bfsAssign (airReorder t))
      (genMemoryForest z α lmb (memInputs z) t) ([] : List (NTree (GenMemoryRow K)))]
    exact hout

/-- The same, under the paper's ROM restriction, at the tree
`GenRomComplete.romTree` produces. -/
theorem exists_good_seed_of_rom {Λ : ℕ} (hΛ : 1 ≤ Λ)
    {fuel : ℕ} {subject formula result : Noun}
    (hrom : evalRom fuel subject formula = some result)
    (hconf : TraceConfined Λ (airReorder (romTree (K := K) hrom)))
    (α : K)
    (hwin : SizeWindowNounsBoundedBy
      (genSemanticSkeleton (bfsAssign (airReorder (romTree (K := K) hrom)))
        ([] : List (NTree (GenMemoryRow K)))) Λ)
    (hcard : seedBudget Λ
      (bfsForest [bfsAssign (airReorder (romTree (K := K) hrom))]).length < Fintype.card K) :
    ∃ z : K, z ≠ 0
      ∧ z ∉ (genSkeletonP8Census (K := K) hΛ (romTree_spec (K := K) hrom) hconf
              (genMemoryForest z α lmb (memInputs z) (romTree (K := K) hrom))).census.badSeeds
      ∧ z ∉ sizeWindowFailureSeeds (K := K)
              (genSemanticSkeleton (bfsAssign (airReorder (romTree (K := K) hrom)))
                (genMemoryForest z α lmb (memInputs z) (romTree (K := K) hrom))) :=
  exists_good_seed_of_accepted hΛ (romTree_spec (K := K) hrom) hconf α hwin hcard

/-! ## 3b. The census does not read `λ`

Both
counted bad sets are functions of the compute tree alone (§2, by `rfl`), so they are the same set
at every `λ`: the compiler's seed census is **λ-irrelevant**, and the seed it picks is good at
whatever `λ` is later drawn.  Hence `romSeed` takes no `λ` and the compiler chooses none. -/

/-- **λ-irrelevance of the compiler's collision census.**  At any two Form R `λ`, `λ'`, the p8
bad-seed set of the generated skeleton is the same `Finset`. -/
theorem badSeeds_lambda_irrelevant {Λ : ℕ} (u : NTree (GenComputeRow K))
    (z α lmb₁ lmb₂ : K) (inp : MemoryTable.Inputs K) (t : NTree (GenComputeRow K))
    (C₁ : BoundSemanticTrace.SkeletonP8Census K
      (genSemanticSkeleton u (genMemoryForest z α lmb₁ inp t)) Λ)
    (C₂ : BoundSemanticTrace.SkeletonP8Census K
      (genSemanticSkeleton u (genMemoryForest z α lmb₂ inp t)) Λ) :
    C₁.census.badSeeds (K := K) = C₂.census.badSeeds (K := K) :=
  badSeeds_memoryForest_irrelevant C₁ C₂

/-- **λ-irrelevance of the size-window failure set.** -/
theorem sizeWindowFailureSeeds_lambda_irrelevant (u : NTree (GenComputeRow K))
    (z α lmb₁ lmb₂ : K) (inp : MemoryTable.Inputs K) (t : NTree (GenComputeRow K)) :
    sizeWindowFailureSeeds (K := K) (genSemanticSkeleton u (genMemoryForest z α lmb₁ inp t))
      = sizeWindowFailureSeeds (K := K) (genSemanticSkeleton u (genMemoryForest z α lmb₂ inp t)) :=
  sizeWindowFailureSeeds_memoryForest_irrelevant u _ _

/-- The λ-free form of `exists_good_seed_of_rom`: the census at the empty forest, which by §2 is
the census at every generated forest, at every `λ`. -/
theorem exists_good_seed_of_rom_lambdaFree {Λ : ℕ} (hΛ : 1 ≤ Λ)
    {fuel : ℕ} {subject formula result : Noun}
    (hrom : evalRom fuel subject formula = some result)
    (hconf : TraceConfined Λ (airReorder (romTree (K := K) hrom)))
    (hwin : SizeWindowNounsBoundedBy
      (genSemanticSkeleton (bfsAssign (airReorder (romTree (K := K) hrom)))
        ([] : List (NTree (GenMemoryRow K)))) Λ)
    (hcard : seedBudget Λ
      (bfsForest [bfsAssign (airReorder (romTree (K := K) hrom))]).length < Fintype.card K) :
    ∃ z : K, z ≠ 0
      ∧ z ∉ (genSkeletonP8Census (K := K) hΛ (romTree_spec (K := K) hrom) hconf
              ([] : List (NTree (GenMemoryRow K)))).census.badSeeds
      ∧ z ∉ sizeWindowFailureSeeds (K := K)
              (genSemanticSkeleton (bfsAssign (airReorder (romTree (K := K) hrom)))
                ([] : List (NTree (GenMemoryRow K)))) :=
  exists_seed_outside_counted_events
    (genSkeletonP8Census (K := K) hΛ (romTree_spec (K := K) hrom) hconf
      ([] : List (NTree (GenMemoryRow K))))
    hwin (by rwa [computeSkeletonRows_length])

/-! ## 4. The seed the compiler chooses

A name for the witness, so the three hypotheses can be discharged rather than relocated.  This is
`Classical.choose`, i.e. `Classical.choice` — already in the sanctioned axiom set. -/

/-- **The compiler's NPR seed** for a ROM-terminating program. -/
def romSeed {Λ : ℕ} (hΛ : 1 ≤ Λ)
    {fuel : ℕ} {subject formula result : Noun}
    (hrom : evalRom fuel subject formula = some result)
    (hconf : TraceConfined Λ (airReorder (romTree (K := K) hrom)))
    (α : K)
    (hwin : SizeWindowNounsBoundedBy
      (genSemanticSkeleton (bfsAssign (airReorder (romTree (K := K) hrom)))
        ([] : List (NTree (GenMemoryRow K)))) Λ)
    (hcard : seedBudget Λ
      (bfsForest [bfsAssign (airReorder (romTree (K := K) hrom))]).length < Fintype.card K) :
    K :=
  (exists_good_seed_of_rom_lambdaFree (K := K) hΛ hrom hconf hwin hcard).choose

theorem romSeed_ne_zero {Λ : ℕ} (hΛ : 1 ≤ Λ)
    {fuel : ℕ} {subject formula result : Noun}
    (hrom : evalRom fuel subject formula = some result)
    (hconf : TraceConfined Λ (airReorder (romTree (K := K) hrom)))
    (α : K)
    (hwin : SizeWindowNounsBoundedBy
      (genSemanticSkeleton (bfsAssign (airReorder (romTree (K := K) hrom)))
        ([] : List (NTree (GenMemoryRow K)))) Λ)
    (hcard : seedBudget Λ
      (bfsForest [bfsAssign (airReorder (romTree (K := K) hrom))]).length < Fintype.card K) :
    romSeed hΛ hrom hconf α hwin hcard ≠ 0 :=
  (exists_good_seed_of_rom_lambdaFree (K := K) hΛ hrom hconf hwin hcard).choose_spec.1

theorem romSeed_notMem_badSeeds {Λ : ℕ} (hΛ : 1 ≤ Λ)
    {fuel : ℕ} {subject formula result : Noun}
    (hrom : evalRom fuel subject formula = some result)
    (hconf : TraceConfined Λ (airReorder (romTree (K := K) hrom)))
    (α : K)
    (hwin : SizeWindowNounsBoundedBy
      (genSemanticSkeleton (bfsAssign (airReorder (romTree (K := K) hrom)))
        ([] : List (NTree (GenMemoryRow K)))) Λ)
    (hcard : seedBudget Λ
      (bfsForest [bfsAssign (airReorder (romTree (K := K) hrom))]).length < Fintype.card K) :
    romSeed hΛ hrom hconf α hwin hcard ∉
      (genSkeletonP8Census (K := K) hΛ (romTree_spec (K := K) hrom) hconf
        (genMemoryForest (romSeed hΛ hrom hconf α hwin hcard) α lmb
          (memInputs (romSeed hΛ hrom hconf α hwin hcard))
          (romTree (K := K) hrom))).census.badSeeds := by
  rw [badSeeds_memoryForest_irrelevant _
    (genSkeletonP8Census (K := K) hΛ (romTree_spec (K := K) hrom) hconf
      ([] : List (NTree (GenMemoryRow K))))]
  exact (exists_good_seed_of_rom_lambdaFree (K := K) hΛ hrom hconf hwin hcard).choose_spec.2.1

theorem romSeed_notMem_sizeWindowFailureSeeds {Λ : ℕ} (hΛ : 1 ≤ Λ)
    {fuel : ℕ} {subject formula result : Noun}
    (hrom : evalRom fuel subject formula = some result)
    (hconf : TraceConfined Λ (airReorder (romTree (K := K) hrom)))
    (α : K)
    (hwin : SizeWindowNounsBoundedBy
      (genSemanticSkeleton (bfsAssign (airReorder (romTree (K := K) hrom)))
        ([] : List (NTree (GenMemoryRow K)))) Λ)
    (hcard : seedBudget Λ
      (bfsForest [bfsAssign (airReorder (romTree (K := K) hrom))]).length < Fintype.card K) :
    romSeed hΛ hrom hconf α hwin hcard ∉
      sizeWindowFailureSeeds (K := K)
        (genSemanticSkeleton (bfsAssign (airReorder (romTree (K := K) hrom)))
          (genMemoryForest (romSeed hΛ hrom hconf α hwin hcard) α lmb
            (memInputs (romSeed hΛ hrom hconf α hwin hcard))
            (romTree (K := K) hrom))) := by
  rw [sizeWindowFailureSeeds_memoryForest_irrelevant _ _ ([] : List (NTree (GenMemoryRow K)))]
  exact (exists_good_seed_of_rom_lambdaFree (K := K) hΛ hrom hconf hwin hcard).choose_spec.2.2

section Package

open Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.BuildablePackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.Framework.Thm54

variable {F : Type} [Field F] [Algebra F K] [FiniteDimensional F K]
variable [Fintype F] [DecidableEq F] [CharP K (ringChar K)]

/-! ## 5. `nockCompiles_of_rom` with the three seed hypotheses discharged

`nockCompiles_of_rom` (`GenNockCompiles.lean:383`) with `z`, `hz`, `hbad` and `hout` **gone** from
the binder list: the seed is `romSeed`, the compiler's own choice, and the three conditions are
supplied by §4 rather than assumed.  The two binders that replace them, `hwinNouns` and
`hseedcard`, are program measurements (a leaf bound and a row-count inequality), not seed
conditions.

The remaining seed-mentioning binders — `hinp`, `hmi`, `hseed`, `hcoins`, and the forest-length
bounds — now read at `romSeed`. -/
theorem nockCompiles_of_rom_atRomSeed {q Λ : ℕ}
    (α : K) (htwo : (2 : K) ≠ 0) (a b c : K)
    {fuel : ℕ} {subject formula : Noun}
    {result : Noun}
    (hrom : evalRom fuel subject formula = some result)
    (hΛ : 1 ≤ Λ) (hconf : TraceConfined Λ (airReorder (romTree (K := K) hrom)))
    (hwinNouns : SizeWindowNounsBoundedBy
      (genSemanticSkeleton (bfsAssign (airReorder (romTree (K := K) hrom)))
        ([] : List (NTree (GenMemoryRow K)))) Λ)
    (hseedcard : seedBudget Λ
      (bfsForest [bfsAssign (airReorder (romTree (K := K) hrom))]).length < Fintype.card K)
    (chal : ChallengeVector K)
    (hinp : chal.computeInputs = ⟨α, (romSeed hΛ hrom hconf α hwinNouns hseedcard), a, b, c⟩)
    (hmi : chal.memoryInputs = memInputs (romSeed hΛ hrom hconf α hwinNouns hseedcard))
    (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (hseed : SeedGood (romSeed hΛ hrom hconf α hwinNouns hseedcard) (romTree (K := K) hrom))
    (hcoins : ComputeCoinsGeneric (romSeed hΛ hrom hconf α hwinNouns hseedcard) α a b c
      (airReorder (romTree (K := K) hrom)))
    (hmempos : 0 < (bfsForest (genMemoryForest (romSeed hΛ hrom hconf α hwinNouns hseedcard) α chal.lam (memInputs (romSeed hΛ hrom hconf α hwinNouns hseedcard)) (romTree (K := K) hrom))).length)
    (hcomp : (bfsForest [genComputeRows (romSeed hΛ hrom hconf α hwinNouns hseedcard) α (romTree (K := K) hrom)]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemoryForest (romSeed hΛ hrom hconf α hwinNouns hseedcard) α chal.lam (memInputs (romSeed hΛ hrom hconf α hwinNouns hseedcard)) (romTree (K := K) hrom))).length ≤ 2 ^ orbit.h)
    (B : ℕ) (hB : B ≤ orderOf α)
    (hwin : accAt (airReorder (romTree (K := K) hrom)) (bfsRows (airReorder (romTree (K := K) hrom))).length + 3 < B)
    (hKsz : accAt (airReorder (romTree (K := K) hrom)) (bfsRows (airReorder (romTree (K := K) hrom))).length ≤ Ksz)
    (hKsz2 : 2 * (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows (romSeed hΛ hrom hconf α hwinNouns hseedcard) α (romTree (K := K) hrom))
      (genMemoryForest (romSeed hΛ hrom hconf α hwinNouns hseedcard) α chal.lam (memInputs (romSeed hΛ hrom hconf α hwinNouns hseedcard)) (romTree (K := K) hrom)) hmempos hcomp hmem).kMem ≤ Ksz)
    (hb : (genSemanticSkeleton (bfsAssign (airReorder (romTree (K := K) hrom)))
      (genMemoryForest (romSeed hΛ hrom hconf α hwinNouns hseedcard) α chal.lam (memInputs (romSeed hΛ hrom hconf α hwinNouns hseedcard)) (romTree (K := K) hrom))).BoundedBy q)
    (hq : 11 < q) (hchar : q = ringChar K)
    (haxis : SkeletonAxisRange q (genSemanticSkeleton (bfsAssign (airReorder (romTree (K := K) hrom)))
      (genMemoryForest (romSeed hΛ hrom hconf α hwinNouns hseedcard) α chal.lam (memInputs (romSeed hΛ hrom hconf α hwinNouns hseedcard)) (romTree (K := K) hrom))))
    (hKszChar : Ksz < ringChar K)
    (hprogCap : accAt (airReorder (romTree (K := K) hrom)) (bfsRows (airReorder (romTree (K := K) hrom))).length + 1 ≤ 2 ^ orbit.h)
    (hmemCap : (bfsForest (genMemoryForest (romSeed hΛ hrom hconf α hwinNouns hseedcard) α chal.lam (memInputs (romSeed hΛ hrom hconf α hwinNouns hseedcard)) (romTree (K := K) hrom))).length + 1 ≤ 2 ^ orbit.h)
    (hfirst : ∀ n, InTree (bfsAssign (airReorder (romTree (K := K) hrom))) n →
        ∀ r ∈ extractNodeReqs n.label, r.axis < ringChar K)
    (hmore : BuildableAxisWitness.LaterSeedZeros
      (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
        (romSeed hΛ hrom hconf α hwinNouns hseedcard) α
        (romSeed_ne_zero hΛ hrom hconf α hwinNouns hseedcard) htwo a b c chal hinp hmi
        Ksz orbit horb (romTree_spec (K := K) hrom) hseed hcoins hΛ hconf hmempos hcomp hmem
        B hB hwin hKsz hKsz2 hb hq hchar haxis
        (romSeed_notMem_badSeeds (lmb := chal.lam) hΛ hrom hconf α hwinNouns hseedcard)
        (romSeed_notMem_sizeWindowFailureSeeds (lmb := chal.lam) hΛ hrom hconf α hwinNouns hseedcard)
        hKszChar hprogCap hmemCap hfirst))
    {hOrb : ℕ}
    (stc : NodeEncoding.StateTagChar K)
    (bas : Module.Basis (Fin 3) F K)
    (packageOrbit : StrictOrbitDomain F 3 hOrb)
    (hcap : 2 ^ orbit.h ≤ 2 ^ hOrb)
    (n : ℕ)
    (hreqn : accAt (airReorder (romTree (K := K) hrom)) (bfsRows (airReorder (romTree (K := K) hrom))).length ≤ n)
    (hrespn : (bfsForest (genMemoryForest (romSeed hΛ hrom hconf α hwinNouns hseedcard) α chal.lam (memInputs (romSeed hΛ hrom hconf α hwinNouns hseedcard)) (romTree (K := K) hrom))).length ≤ n)
    (hcard : RecordCarrier.honestIOBound n n (Fintype.card K) < Fintype.card (K × K))
    (computeWalkAlpha memoryWalkAlpha walkGamma : K)
    (memoryScalarChallenge : Fin 4 → F) (memoryExtensionFold : K)
    (hord : 2 ≤
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
          (romSeed hΛ hrom hconf α hwinNouns hseedcard) α
          (romSeed_ne_zero hΛ hrom hconf α hwinNouns hseedcard) htwo a b c chal hinp hmi
          Ksz orbit horb (romTree_spec (K := K) hrom) hseed hcoins hΛ hconf hmempos hcomp hmem
          B hB hwin hKsz hKsz2 hb hq hchar haxis
          (romSeed_notMem_badSeeds (lmb := chal.lam) hΛ hrom hconf α hwinNouns hseedcard)
          (romSeed_notMem_sizeWindowFailureSeeds (lmb := chal.lam) hΛ hrom hconf α hwinNouns hseedcard)
          hKszChar hprogCap hmemCap hfirst).cfg.compRows →
      (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
          (romSeed hΛ hrom hconf α hwinNouns hseedcard) α
          (romSeed_ne_zero hΛ hrom hconf α hwinNouns hseedcard) htwo a b c chal hinp hmi
          Ksz orbit horb (romTree_spec (K := K) hrom) hseed hcoins hΛ hconf hmempos hcomp hmem
          B hB hwin hKsz hKsz2 hb hq hchar haxis
          (romSeed_notMem_badSeeds (lmb := chal.lam) hΛ hrom hconf α hwinNouns hseedcard)
          (romSeed_notMem_sizeWindowFailureSeeds (lmb := chal.lam) hΛ hrom hconf α hwinNouns hseedcard)
          hKszChar hprogCap hmemCap hfirst).cfg.compRows ≤
        orderOf computeWalkAlpha)
    (hordM : 2 ≤
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
          (romSeed hΛ hrom hconf α hwinNouns hseedcard) α
          (romSeed_ne_zero hΛ hrom hconf α hwinNouns hseedcard) htwo a b c chal hinp hmi
          Ksz orbit horb (romTree_spec (K := K) hrom) hseed hcoins hΛ hconf hmempos hcomp hmem
          B hB hwin hKsz hKsz2 hb hq hchar haxis
          (romSeed_notMem_badSeeds (lmb := chal.lam) hΛ hrom hconf α hwinNouns hseedcard)
          (romSeed_notMem_sizeWindowFailureSeeds (lmb := chal.lam) hΛ hrom hconf α hwinNouns hseedcard)
          hKszChar hprogCap hmemCap hfirst).cfg.memRows →
      (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
          (romSeed hΛ hrom hconf α hwinNouns hseedcard) α
          (romSeed_ne_zero hΛ hrom hconf α hwinNouns hseedcard) htwo a b c chal hinp hmi
          Ksz orbit horb (romTree_spec (K := K) hrom) hseed hcoins hΛ hconf hmempos hcomp hmem
          B hB hwin hKsz hKsz2 hb hq hchar haxis
          (romSeed_notMem_badSeeds (lmb := chal.lam) hΛ hrom hconf α hwinNouns hseedcard)
          (romSeed_notMem_sizeWindowFailureSeeds (lmb := chal.lam) hΛ hrom hconf α hwinNouns hseedcard)
          hKszChar hprogCap hmemCap hfirst).cfg.memRows ≤
        orderOf memoryWalkAlpha)
    (hrows : 3 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
          (romSeed hΛ hrom hconf α hwinNouns hseedcard) α
          (romSeed_ne_zero hΛ hrom hconf α hwinNouns hseedcard) htwo a b c chal hinp hmi
          Ksz orbit horb (romTree_spec (K := K) hrom) hseed hcoins hΛ hconf hmempos hcomp hmem
          B hB hwin hKsz hKsz2 hb hq hchar haxis
          (romSeed_notMem_badSeeds (lmb := chal.lam) hΛ hrom hconf α hwinNouns hseedcard)
          (romSeed_notMem_sizeWindowFailureSeeds (lmb := chal.lam) hΛ hrom hconf α hwinNouns hseedcard)
          hKszChar hprogCap hmemCap hfirst).cfg.compRows < ringChar K ∧
      (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
          (romSeed hΛ hrom hconf α hwinNouns hseedcard) α
          (romSeed_ne_zero hΛ hrom hconf α hwinNouns hseedcard) htwo a b c chal hinp hmi
          Ksz orbit horb (romTree_spec (K := K) hrom) hseed hcoins hΛ hconf hmempos hcomp hmem
          B hB hwin hKsz hKsz2 hb hq hchar haxis
          (romSeed_notMem_badSeeds (lmb := chal.lam) hΛ hrom hconf α hwinNouns hseedcard)
          (romSeed_notMem_sizeWindowFailureSeeds (lmb := chal.lam) hΛ hrom hconf α hwinNouns hseedcard)
          hKszChar hprogCap hmemCap hfirst).cfg.memRows < ringChar K)
    {fuelG : ℕ} {rG : Noun} (hG : FieldEmbedding.evalGBy q fuelG subject formula = some rG)
    (hF : GeneratedField.PrimeFieldElems F)
    (hax : FormRAxisBound
      (buildFullPackage
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) (romSeed hΛ hrom hconf α hwinNouns hseedcard) α
          (romSeed_ne_zero hΛ hrom hconf α hwinNouns hseedcard) htwo a b c chal hinp hmi
          Ksz orbit horb (romTree_spec (K := K) hrom) hseed hcoins hΛ hconf hmempos hcomp hmem
          B hB hwin hKsz hKsz2 hb hq hchar haxis
          (romSeed_notMem_badSeeds (lmb := chal.lam) hΛ hrom hconf α hwinNouns hseedcard)
          (romSeed_notMem_sizeWindowFailureSeeds (lmb := chal.lam) hΛ hrom hconf α hwinNouns hseedcard) hKszChar hprogCap hmemCap hfirst)
        (inputsOfCarrier
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) (romSeed hΛ hrom hconf α hwinNouns hseedcard) α
            (romSeed_ne_zero hΛ hrom hconf α hwinNouns hseedcard) htwo a b c chal hinp hmi
            Ksz orbit horb (romTree_spec (K := K) hrom) hseed hcoins hΛ hconf hmempos hcomp hmem
            B hB hwin hKsz hKsz2 hb hq hchar haxis
          (romSeed_notMem_badSeeds (lmb := chal.lam) hΛ hrom hconf α hwinNouns hseedcard)
          (romSeed_notMem_sizeWindowFailureSeeds (lmb := chal.lam) hΛ hrom hconf α hwinNouns hseedcard) hKszChar hprogCap hmemCap hfirst)
          stc bas packageOrbit hcap n
          (genExactExecution_requestIO_le (F := F) (romSeed hΛ hrom hconf α hwinNouns hseedcard) α chal Ksz orbit horb a b c
            (romTree (K := K) hrom) (genMemoryForest (romSeed hΛ hrom hconf α hwinNouns hseedcard) α chal.lam (memInputs (romSeed hΛ hrom hconf α hwinNouns hseedcard)) (romTree (K := K) hrom))
            hmempos hcomp hmem n hreqn)
          (genExactExecution_responseIO_le (F := F) chal Ksz orbit horb a b c
            (genComputeRows (romSeed hΛ hrom hconf α hwinNouns hseedcard) α (romTree (K := K) hrom))
            (genMemoryForest (romSeed hΛ hrom hconf α hwinNouns hseedcard) α chal.lam (memInputs (romSeed hΛ hrom hconf α hwinNouns hseedcard)) (romTree (K := K) hrom))
            hmempos hcomp hmem n hrespn)
          hcard computeWalkAlpha memoryWalkAlpha walkGamma memoryScalarChallenge
          memoryExtensionFold (interCard_of_unionBound _ (by
            change (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) (romSeed hΛ hrom hconf α hwinNouns hseedcard) α
                (romSeed_ne_zero hΛ hrom hconf α hwinNouns hseedcard) htwo a b c chal hinp hmi
                Ksz orbit horb (romTree_spec (K := K) hrom) hseed hcoins hΛ hconf hmempos hcomp hmem
                B hB hwin hKsz hKsz2 hb hq hchar haxis
          (romSeed_notMem_badSeeds (lmb := chal.lam) hΛ hrom hconf α hwinNouns hseedcard)
          (romSeed_notMem_sizeWindowFailureSeeds (lmb := chal.lam) hΛ hrom hconf α hwinNouns hseedcard) hKszChar hprogCap hmemCap hfirst).cfg.memRows ≤ n
            exact hrespn) hcard) (genBuildableOfProgram_honestVer (F := F) (q := q) (Λ := Λ) (romSeed hΛ hrom hconf α hwinNouns hseedcard) α
            (romSeed_ne_zero hΛ hrom hconf α hwinNouns hseedcard) htwo a b c chal hinp hmi
            Ksz orbit horb (romTree_spec (K := K) hrom) hseed hcoins hΛ hconf hmempos hcomp hmem
            B hB hwin hKsz hKsz2 hb hq hchar haxis
          (romSeed_notMem_badSeeds (lmb := chal.lam) hΛ hrom hconf α hwinNouns hseedcard)
          (romSeed_notMem_sizeWindowFailureSeeds (lmb := chal.lam) hΛ hrom hconf α hwinNouns hseedcard) hKszChar hprogCap hmemCap hfirst))
        (commitmentResidualOfZero
          (genDataOfProgram (F := F) (q := q) (Λ := Λ) (romSeed hΛ hrom hconf α hwinNouns hseedcard) α
            (romSeed_ne_zero hΛ hrom hconf α hwinNouns hseedcard) htwo a b c chal hinp hmi
            Ksz orbit horb (romTree_spec (K := K) hrom) hseed hcoins hΛ hconf hmempos hcomp hmem
            B hB hwin hKsz hKsz2 hb hq hchar haxis
          (romSeed_notMem_badSeeds (lmb := chal.lam) hΛ hrom hconf α hwinNouns hseedcard)
          (romSeed_notMem_sizeWindowFailureSeeds (lmb := chal.lam) hΛ hrom hconf α hwinNouns hseedcard) hKszChar hprogCap hmemCap hfirst))
        (inputsOfCarrier_challenges
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) (romSeed hΛ hrom hconf α hwinNouns hseedcard) α
            (romSeed_ne_zero hΛ hrom hconf α hwinNouns hseedcard) htwo a b c chal hinp hmi
            Ksz orbit horb (romTree_spec (K := K) hrom) hseed hcoins hΛ hconf hmempos hcomp hmem
            B hB hwin hKsz hKsz2 hb hq hchar haxis
          (romSeed_notMem_badSeeds (lmb := chal.lam) hΛ hrom hconf α hwinNouns hseedcard)
          (romSeed_notMem_sizeWindowFailureSeeds (lmb := chal.lam) hΛ hrom hconf α hwinNouns hseedcard) hKszChar hprogCap hmemCap hfirst)
          stc bas packageOrbit hcap n
          (genExactExecution_requestIO_le (F := F) (romSeed hΛ hrom hconf α hwinNouns hseedcard) α chal Ksz orbit horb a b c
            (romTree (K := K) hrom) (genMemoryForest (romSeed hΛ hrom hconf α hwinNouns hseedcard) α chal.lam (memInputs (romSeed hΛ hrom hconf α hwinNouns hseedcard)) (romTree (K := K) hrom))
            hmempos hcomp hmem n hreqn)
          (genExactExecution_responseIO_le (F := F) chal Ksz orbit horb a b c
            (genComputeRows (romSeed hΛ hrom hconf α hwinNouns hseedcard) α (romTree (K := K) hrom))
            (genMemoryForest (romSeed hΛ hrom hconf α hwinNouns hseedcard) α chal.lam (memInputs (romSeed hΛ hrom hconf α hwinNouns hseedcard)) (romTree (K := K) hrom))
            hmempos hcomp hmem n hrespn)
          hcard computeWalkAlpha memoryWalkAlpha walkGamma memoryScalarChallenge
          memoryExtensionFold (interCard_of_unionBound _ (by
            change (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) (romSeed hΛ hrom hconf α hwinNouns hseedcard) α
                (romSeed_ne_zero hΛ hrom hconf α hwinNouns hseedcard) htwo a b c chal hinp hmi
                Ksz orbit horb (romTree_spec (K := K) hrom) hseed hcoins hΛ hconf hmempos hcomp hmem
                B hB hwin hKsz hKsz2 hb hq hchar haxis
          (romSeed_notMem_badSeeds (lmb := chal.lam) hΛ hrom hconf α hwinNouns hseedcard)
          (romSeed_notMem_sizeWindowFailureSeeds (lmb := chal.lam) hΛ hrom hconf α hwinNouns hseedcard) hKszChar hprogCap hmemCap hfirst).cfg.memRows ≤ n
            exact hrespn) hcard) (genBuildableOfProgram_honestVer (F := F) (q := q) (Λ := Λ) (romSeed hΛ hrom hconf α hwinNouns hseedcard) α
            (romSeed_ne_zero hΛ hrom hconf α hwinNouns hseedcard) htwo a b c chal hinp hmi
            Ksz orbit horb (romTree_spec (K := K) hrom) hseed hcoins hΛ hconf hmempos hcomp hmem
            B hB hwin hKsz hKsz2 hb hq hchar haxis
          (romSeed_notMem_badSeeds (lmb := chal.lam) hΛ hrom hconf α hwinNouns hseedcard)
          (romSeed_notMem_sizeWindowFailureSeeds (lmb := chal.lam) hΛ hrom hconf α hwinNouns hseedcard) hKszChar hprogCap hmemCap hfirst))
        (genBuildableOfProgram_pairedRecordLayout (F := F) (q := q) (Λ := Λ) (romSeed hΛ hrom hconf α hwinNouns hseedcard) α (romSeed_ne_zero hΛ hrom hconf α hwinNouns hseedcard) htwo a b c chal
          hinp hmi Ksz orbit horb (romTree_spec (K := K) hrom) hseed hcoins hΛ hconf hmempos hcomp hmem
          B hB hwin hKsz hKsz2 hb hq hchar haxis
          (romSeed_notMem_badSeeds (lmb := chal.lam) hΛ hrom hconf α hwinNouns hseedcard)
          (romSeed_notMem_sizeWindowFailureSeeds (lmb := chal.lam) hΛ hrom hconf α hwinNouns hseedcard) hKszChar hprogCap hmemCap hfirst)
        hmore hord hordM hrows).optimized.sampled
      (buildFullPackage
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) (romSeed hΛ hrom hconf α hwinNouns hseedcard) α
          (romSeed_ne_zero hΛ hrom hconf α hwinNouns hseedcard) htwo a b c chal hinp hmi
          Ksz orbit horb (romTree_spec (K := K) hrom) hseed hcoins hΛ hconf hmempos hcomp hmem
          B hB hwin hKsz hKsz2 hb hq hchar haxis
          (romSeed_notMem_badSeeds (lmb := chal.lam) hΛ hrom hconf α hwinNouns hseedcard)
          (romSeed_notMem_sizeWindowFailureSeeds (lmb := chal.lam) hΛ hrom hconf α hwinNouns hseedcard) hKszChar hprogCap hmemCap hfirst)
        (inputsOfCarrier
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) (romSeed hΛ hrom hconf α hwinNouns hseedcard) α
            (romSeed_ne_zero hΛ hrom hconf α hwinNouns hseedcard) htwo a b c chal hinp hmi
            Ksz orbit horb (romTree_spec (K := K) hrom) hseed hcoins hΛ hconf hmempos hcomp hmem
            B hB hwin hKsz hKsz2 hb hq hchar haxis
          (romSeed_notMem_badSeeds (lmb := chal.lam) hΛ hrom hconf α hwinNouns hseedcard)
          (romSeed_notMem_sizeWindowFailureSeeds (lmb := chal.lam) hΛ hrom hconf α hwinNouns hseedcard) hKszChar hprogCap hmemCap hfirst)
          stc bas packageOrbit hcap n
          (genExactExecution_requestIO_le (F := F) (romSeed hΛ hrom hconf α hwinNouns hseedcard) α chal Ksz orbit horb a b c
            (romTree (K := K) hrom) (genMemoryForest (romSeed hΛ hrom hconf α hwinNouns hseedcard) α chal.lam (memInputs (romSeed hΛ hrom hconf α hwinNouns hseedcard)) (romTree (K := K) hrom))
            hmempos hcomp hmem n hreqn)
          (genExactExecution_responseIO_le (F := F) chal Ksz orbit horb a b c
            (genComputeRows (romSeed hΛ hrom hconf α hwinNouns hseedcard) α (romTree (K := K) hrom))
            (genMemoryForest (romSeed hΛ hrom hconf α hwinNouns hseedcard) α chal.lam (memInputs (romSeed hΛ hrom hconf α hwinNouns hseedcard)) (romTree (K := K) hrom))
            hmempos hcomp hmem n hrespn)
          hcard computeWalkAlpha memoryWalkAlpha walkGamma memoryScalarChallenge
          memoryExtensionFold (interCard_of_unionBound _ (by
            change (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) (romSeed hΛ hrom hconf α hwinNouns hseedcard) α
                (romSeed_ne_zero hΛ hrom hconf α hwinNouns hseedcard) htwo a b c chal hinp hmi
                Ksz orbit horb (romTree_spec (K := K) hrom) hseed hcoins hΛ hconf hmempos hcomp hmem
                B hB hwin hKsz hKsz2 hb hq hchar haxis
          (romSeed_notMem_badSeeds (lmb := chal.lam) hΛ hrom hconf α hwinNouns hseedcard)
          (romSeed_notMem_sizeWindowFailureSeeds (lmb := chal.lam) hΛ hrom hconf α hwinNouns hseedcard) hKszChar hprogCap hmemCap hfirst).cfg.memRows ≤ n
            exact hrespn) hcard) (genBuildableOfProgram_honestVer (F := F) (q := q) (Λ := Λ) (romSeed hΛ hrom hconf α hwinNouns hseedcard) α
            (romSeed_ne_zero hΛ hrom hconf α hwinNouns hseedcard) htwo a b c chal hinp hmi
            Ksz orbit horb (romTree_spec (K := K) hrom) hseed hcoins hΛ hconf hmempos hcomp hmem
            B hB hwin hKsz hKsz2 hb hq hchar haxis
          (romSeed_notMem_badSeeds (lmb := chal.lam) hΛ hrom hconf α hwinNouns hseedcard)
          (romSeed_notMem_sizeWindowFailureSeeds (lmb := chal.lam) hΛ hrom hconf α hwinNouns hseedcard) hKszChar hprogCap hmemCap hfirst))
        (commitmentResidualOfZero
          (genDataOfProgram (F := F) (q := q) (Λ := Λ) (romSeed hΛ hrom hconf α hwinNouns hseedcard) α
            (romSeed_ne_zero hΛ hrom hconf α hwinNouns hseedcard) htwo a b c chal hinp hmi
            Ksz orbit horb (romTree_spec (K := K) hrom) hseed hcoins hΛ hconf hmempos hcomp hmem
            B hB hwin hKsz hKsz2 hb hq hchar haxis
          (romSeed_notMem_badSeeds (lmb := chal.lam) hΛ hrom hconf α hwinNouns hseedcard)
          (romSeed_notMem_sizeWindowFailureSeeds (lmb := chal.lam) hΛ hrom hconf α hwinNouns hseedcard) hKszChar hprogCap hmemCap hfirst))
        (inputsOfCarrier_challenges
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) (romSeed hΛ hrom hconf α hwinNouns hseedcard) α
            (romSeed_ne_zero hΛ hrom hconf α hwinNouns hseedcard) htwo a b c chal hinp hmi
            Ksz orbit horb (romTree_spec (K := K) hrom) hseed hcoins hΛ hconf hmempos hcomp hmem
            B hB hwin hKsz hKsz2 hb hq hchar haxis
          (romSeed_notMem_badSeeds (lmb := chal.lam) hΛ hrom hconf α hwinNouns hseedcard)
          (romSeed_notMem_sizeWindowFailureSeeds (lmb := chal.lam) hΛ hrom hconf α hwinNouns hseedcard) hKszChar hprogCap hmemCap hfirst)
          stc bas packageOrbit hcap n
          (genExactExecution_requestIO_le (F := F) (romSeed hΛ hrom hconf α hwinNouns hseedcard) α chal Ksz orbit horb a b c
            (romTree (K := K) hrom) (genMemoryForest (romSeed hΛ hrom hconf α hwinNouns hseedcard) α chal.lam (memInputs (romSeed hΛ hrom hconf α hwinNouns hseedcard)) (romTree (K := K) hrom))
            hmempos hcomp hmem n hreqn)
          (genExactExecution_responseIO_le (F := F) chal Ksz orbit horb a b c
            (genComputeRows (romSeed hΛ hrom hconf α hwinNouns hseedcard) α (romTree (K := K) hrom))
            (genMemoryForest (romSeed hΛ hrom hconf α hwinNouns hseedcard) α chal.lam (memInputs (romSeed hΛ hrom hconf α hwinNouns hseedcard)) (romTree (K := K) hrom))
            hmempos hcomp hmem n hrespn)
          hcard computeWalkAlpha memoryWalkAlpha walkGamma memoryScalarChallenge
          memoryExtensionFold (interCard_of_unionBound _ (by
            change (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) (romSeed hΛ hrom hconf α hwinNouns hseedcard) α
                (romSeed_ne_zero hΛ hrom hconf α hwinNouns hseedcard) htwo a b c chal hinp hmi
                Ksz orbit horb (romTree_spec (K := K) hrom) hseed hcoins hΛ hconf hmempos hcomp hmem
                B hB hwin hKsz hKsz2 hb hq hchar haxis
          (romSeed_notMem_badSeeds (lmb := chal.lam) hΛ hrom hconf α hwinNouns hseedcard)
          (romSeed_notMem_sizeWindowFailureSeeds (lmb := chal.lam) hΛ hrom hconf α hwinNouns hseedcard) hKszChar hprogCap hmemCap hfirst).cfg.memRows ≤ n
            exact hrespn) hcard) (genBuildableOfProgram_honestVer (F := F) (q := q) (Λ := Λ) (romSeed hΛ hrom hconf α hwinNouns hseedcard) α
            (romSeed_ne_zero hΛ hrom hconf α hwinNouns hseedcard) htwo a b c chal hinp hmi
            Ksz orbit horb (romTree_spec (K := K) hrom) hseed hcoins hΛ hconf hmempos hcomp hmem
            B hB hwin hKsz hKsz2 hb hq hchar haxis
          (romSeed_notMem_badSeeds (lmb := chal.lam) hΛ hrom hconf α hwinNouns hseedcard)
          (romSeed_notMem_sizeWindowFailureSeeds (lmb := chal.lam) hΛ hrom hconf α hwinNouns hseedcard) hKszChar hprogCap hmemCap hfirst))
        (genBuildableOfProgram_pairedRecordLayout (F := F) (q := q) (Λ := Λ) (romSeed hΛ hrom hconf α hwinNouns hseedcard) α (romSeed_ne_zero hΛ hrom hconf α hwinNouns hseedcard) htwo a b c chal
          hinp hmi Ksz orbit horb (romTree_spec (K := K) hrom) hseed hcoins hΛ hconf hmempos hcomp hmem
          B hB hwin hKsz hKsz2 hb hq hchar haxis
          (romSeed_notMem_badSeeds (lmb := chal.lam) hΛ hrom hconf α hwinNouns hseedcard)
          (romSeed_notMem_sizeWindowFailureSeeds (lmb := chal.lam) hΛ hrom hconf α hwinNouns hseedcard) hKszChar hprogCap hmemCap hfirst)
        hmore hord hordM hrows).optimized.basis)
    (hbasis : FormRBasis bas)
    (hwidth : FormRWidth F) :
    ∃ package : OptimizedFullStrictNockVMROMPackage F K hOrb,
      OptimizedFullStrictThm54Statement package
        ∧ package.optimized.verifier.raw.claim = ⟨subject, formula, result⟩
        ∧ package.optimized.objects.cfg.challenges.lam = chal.lam :=
  nockCompiles_of_rom (romSeed hΛ hrom hconf α hwinNouns hseedcard) α
    (romSeed_ne_zero hΛ hrom hconf α hwinNouns hseedcard) htwo a b c chal hinp hmi
    Ksz orbit horb hrom hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
    hb hq hchar haxis
    (romSeed_notMem_badSeeds (lmb := chal.lam) hΛ hrom hconf α hwinNouns hseedcard)
    (romSeed_notMem_sizeWindowFailureSeeds (lmb := chal.lam) hΛ hrom hconf α hwinNouns hseedcard)
    hKszChar hprogCap hmemCap hfirst hmore stc bas packageOrbit hcap n hreqn hrespn hcard
    computeWalkAlpha memoryWalkAlpha walkGamma memoryScalarChallenge memoryExtensionFold
    hord hordM hrows hG hF hax hbasis hwidth

end Package

end

end Nock.NockVMROM.Thm54.TraceGen.GoodSeed

#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.exists_notMem_of_card_lt
#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.exists_seed_outside_counted_events
#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.skeletonPairs_memoryForest_irrelevant
#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.badSeeds_memoryForest_irrelevant
#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.sizeWindowFailureSeeds_memoryForest_irrelevant
#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.computeSkeletonRows_length
#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.exists_good_seed_of_accepted
#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.exists_good_seed_of_rom
#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.romSeed_ne_zero
#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.romSeed_notMem_badSeeds
#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.romSeed_notMem_sizeWindowFailureSeeds
#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_of_rom_atRomSeed
