/-
  Nock/NockVMROM/Thm54/BelowDefs/TraceGen/GenGoodSeedExists.lean

  The
  remaining declarations stay in `Nock/NockVMROM/Thm54/TraceGen/GenGoodSeedExists.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackageDefs` or the statement file, directly or transitively.
-/
import Nock.NockVMROM.Thm54.SizeWindowCounting
import Nock.NockVMROM.Thm54.TraceGen.Gen

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.TraceGen.GoodSeed

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SizeWindowCounting
open Nock.NockVMROM.Thm54.TraceGen

noncomputable section

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
variable {lmb : K}

/-- **The compiler's seed budget**: the zero seed, the collision census at the p8 count bound, and
the size-window roots.  Exactly `ProductionRoundChronology.seedBad_card_le`'s three summands, at
the p8 census's own count bound `3 + 10·rows` (`SkeletonP8Census.count_le`) rather than the
combined census's `3 + 19·rows`. -/
def seedBudget (Λ rows : ℕ) : ℕ :=
  1 + (3 + 10 * rows) * (2 * Λ - 1) + sizeWindowRootBound Λ

/-- The budget is strictly larger than the row count (`1 ≤ Λ`).  So `hseedcard` already
gives `rows < |K|`, the side condition `exists_computeCoinsGeneric` wants. -/
theorem seedBudget_gt_rows {Λ rows : ℕ} (hΛ : 1 ≤ Λ) : rows < seedBudget Λ rows := by
  have hmul : 1 ≤ 2 * Λ - 1 := by omega
  have hle : 3 + 10 * rows ≤ (3 + 10 * rows) * (2 * Λ - 1) := by
    simpa using Nat.mul_le_mul_left (3 + 10 * rows) hmul
  unfold seedBudget
  omega

/-- A finite set smaller than the carrier misses a point. -/
theorem exists_notMem_of_card_lt {s : Finset K} (h : s.card < Fintype.card K) :
    ∃ z : K, z ∉ s := by
  have hpos : 0 < sᶜ.card := by
    rw [Finset.card_compl]
    omega
  obtain ⟨z, hz⟩ := Finset.card_pos.mp hpos
  exact ⟨z, Finset.mem_compl.mp hz⟩

/-- Hence so is the collision bad-seed set: `ComparisonCensus.badSeeds` reads `count` and `pair`,
and `ofPairList` takes both from the pair list. -/
theorem badSeeds_memoryForest_irrelevant {Λ : ℕ} {u : NTree (GenComputeRow K)}
    {mf₁ mf₂ : List (NTree (GenMemoryRow K))}
    (C₁ : BoundSemanticTrace.SkeletonP8Census K (genSemanticSkeleton u mf₁) Λ)
    (C₂ : BoundSemanticTrace.SkeletonP8Census K (genSemanticSkeleton u mf₂) Λ) :
    C₁.census.badSeeds (K := K) = C₂.census.badSeeds (K := K) := rfl

/-- And so is the size-window failure set. -/
theorem sizeWindowFailureSeeds_memoryForest_irrelevant (u : NTree (GenComputeRow K))
    (mf₁ mf₂ : List (NTree (GenMemoryRow K))) :
    sizeWindowFailureSeeds (K := K) (genSemanticSkeleton u mf₁)
      = sizeWindowFailureSeeds (K := K) (genSemanticSkeleton u mf₂) := rfl

/-- The row count the budget is stated against is the compute tree's BFS length. -/
theorem computeSkeletonRows_length (u : NTree (GenComputeRow K))
    (mf : List (NTree (GenMemoryRow K))) :
    (computeSkeletonRows (genSemanticSkeleton u mf)).length = (bfsForest [u]).length := by
  have h : computeSkeletonRows (genSemanticSkeleton u mf)
      = computeSkeletonRows (genComputeSemanticSkeleton u) := rfl
  rw [h, computeSkeletonRows_genCompute, List.length_map]

end

end Nock.NockVMROM.Thm54.TraceGen.GoodSeed
