/-
  Nock/NockVMROM/Thm54/HostileWorkloadMajorant.lean

  `ProductionP8Containment.workload` (`ProductionP8Containment.lean::workload`) is consumed
  today at the package's `P.optimized.Λ` (the compiler's `programLeafBound`) and the honest
  skeleton's compute-row count.  A hostile prover commits what it likes, so the leaf window
  cannot be that compiler `Λ`: every leaf is a memory row, hence
  `Λ_hostile := M`, and the compute-row count is majorised by `N`.  Topology collapses to
  `24N + 8M` (`GenWorkloadBounds.lean::fixedTopologyWorkload_eq`); the axis product is
  `kMem · L ≤ M · 3N`.

  Figures below are
  **computed** from `p8WorkHostile`, not quoted from `123 / 122 / 120`.
-/
import Nock.NockVMROM.Thm54.RealProgramSoundness
import Nock.NockVMROM.Thm54.HostileRecordLists
import Nock.NockVMROM.Thm54.WalkForestPrefixAlphaEvents

set_option autoImplicit false
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54
namespace HostileWorkloadMajorant

open Nock
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.RealProgramSoundness
open Nock.NockVMROM.Thm54.SizeWindowCounting
open Nock.NockVMROM.Thm54.GoldilocksParameters
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.FiniteIO

noncomputable section

/-! ## 1. The closed-form majorant

`p8WorkHostile N M` is `p8Majorant` at compute rows `N`, memory rows `M`, leaf window
`Λ = M` and axis `A = 3·N·M` (the honest product `kMem · L` with both
factors a row count).  Expanded:

    1 + (3 + 19N)·(2M) + (24N + 8M) + 3NM + M²
-/

/-- `N` majorises compute rows, `M`
majorises memory rows and is the leaf window. -/
def p8WorkHostile (N M : ℕ) : ℕ :=
  p8Majorant N M M (3 * N * M)

theorem p8WorkHostile_eq (N M : ℕ) :
    p8WorkHostile N M =
      1 + (3 + 19 * N) * (2 * M) + (24 * N + 8 * M) + 3 * N * M + M * M := rfl

/-- At uniform size `S` the majorant is `42S² + 38S + 1`.  Compare
`p8Majorant_le_of_size`'s `39S² + 39S + 1` (axis `A ≤ S`) and
`p8Majorant_le_of_size_quadAxis`'s `43S² + 39S + 1` (axis `A ≤ 4S²`): the hostile
axis `3NM` costs `3S²`, not `4S²`. -/
theorem p8WorkHostile_le_of_size (S N M : ℕ) (hN : N ≤ S) (hM : M ≤ S) :
    p8WorkHostile N M ≤ 42 * (S * S) + 38 * S + 1 := by
  have a1 : (3 + 19 * N) * (2 * M) ≤ (3 + 19 * S) * (2 * S) :=
    Nat.mul_le_mul (by omega) (by omega)
  have a1' : (3 + 19 * S) * (2 * S) = 38 * (S * S) + 6 * S := by ring
  have a2 : M * M ≤ S * S := Nat.mul_le_mul hM hM
  have a3 : 3 * N * M ≤ 3 * (S * S) := by
    have hNM : N * M ≤ S * S := Nat.mul_le_mul hN hM
    calc 3 * N * M
        = 3 * (N * M) := by ring
      _ ≤ 3 * (S * S) := Nat.mul_le_mul_left 3 hNM
  have a4 : 24 * N + 8 * M ≤ 32 * S := by omega
  simp only [p8WorkHostile, p8Majorant]
  rw [a1'] at a1
  linarith

/-- The diagonal closed form, for the receipts. -/
theorem p8WorkHostile_diag (S : ℕ) :
    p8WorkHostile S S = 42 * (S * S) + 38 * S + 1 := by
  simp only [p8WorkHostile, p8Majorant]
  ring

/-! ## 2. `workload` is below the majorant

Topology has the exact helper `topology_majorant_of_rows`. -/

section Workload

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [Fintype K] [DecidableEq K] [CharP K (ringChar K)]

/-- **`workload T M (fixedTopology …) (fixedAxis …) ≤ p8WorkHostile N M + M·(3N + 130) + M·(2M − 1)`**
whenever the compute-row count is `≤ N`, the memory-row count is `≤ M`, and the three canonical
majorants sit under the closed forms `24N + 8M`, `3NM` and (thirtieth move, the Form R λ-event
summand in `workload`) `M·(3N + 130)`.  The last summand is the thirty-third move's request-indexed
pair summand `reqPairWorkload T M` at `Λ = M` (`Λg = M ⊔ M = M`). -/
theorem workload_le_p8WorkHostile
    (T : ProductionStrategy F K) (N M : ℕ)
    (hrows : (SemanticStrategy.computeSkeletonRows T.skeleton).length ≤ N)
    (htop : fixedTopologyWorkload T ≤ 24 * N + 8 * M)
    (hax : fixedAxisWorkload T ≤ 3 * N * M)
    (hformR : formRUniformWorkload T ≤ M * (3 * N + 130))
    (hmrows : (SemanticStrategy.memorySkeletonRows T.skeleton).length ≤ M) :
    workload T M (fixedTopologyWorkload T) (fixedAxisWorkload T) ≤
      p8WorkHostile N M + M * (3 * N + 130) + M * (2 * M - 1) := by
  have hpair : reqPairWorkload T M ≤ M * (2 * M - 1) := by
    unfold reqPairWorkload
    rw [max_eq_right hmrows]
    exact Nat.mul_le_mul_right _ hmrows
  have h := workload_le_p8Majorant T M (fixedTopologyWorkload T) (fixedAxisWorkload T)
    N M (3 * N * M + M * (3 * N + 130) + M * (2 * M - 1)) hrows htop (by omega)
  have he : p8Majorant N M M (3 * N * M + M * (3 * N + 130) + M * (2 * M - 1)) =
      p8WorkHostile N M + M * (3 * N + 130) + M * (2 * M - 1) := by
    simp only [p8WorkHostile, p8Majorant]; ring
  omega

/-- `workload` is at least its topology summand — the negative-control lower bound. -/
theorem workload_ge_topology
    (T : ProductionStrategy F K) (Λ topologyBound axisWorkload : ℕ) :
    topologyBound ≤ workload T Λ topologyBound axisWorkload := by
  simp only [workload]
  omega

end Workload

/-! ## 3. The consumed bound, restated at the majorant (not yet consumed)

This is a renaming of
`optimizedHostileProductionFailureProbabilityBound` at `p8Work := p8WorkHostile N M`. -/

/-- The hostile bound function at the row-count majorant: the consumed
`optimizedHostileProductionFailureProbabilityBound` with `p8Work := p8WorkHostile N M`.
Restatement, not a new summand. -/
def hostileBoundAtMajorant (cardK N M ioWork : ℕ) : ℚ :=
  (p8WorkHostile N M +
      OptimizedHostileTimestamps.timestampCollisionBound (3 * N) +
      pricedWalkWork N M : ℚ) / cardK +
    (ioWork : ℚ) / cardK ^ 2 +
    ((ioFailureUnionBound 10 M M cardK + cardK * M : ℕ) : ℚ) / cardK ^ 2

/-- **`hostile_bound_at_majorant`.**  At Goldilocks this *is*
`goldilocksHostileFailureBound (p8WorkHostile N M) ioWork N M`. -/
theorem hostile_bound_at_majorant (N M ioWork : ℕ) :
    goldilocksHostileFailureBound (p8WorkHostile N M) ioWork N M =
      hostileBoundAtMajorant cardKGold N M ioWork := by
  simp only [goldilocksHostileFailureBound_eq, hostileBoundAtMajorant]

theorem hostile_bound_at_majorant_generic (cardK N M ioWork : ℕ) :
    hostileBoundAtMajorant cardK N M ioWork =
      (p8WorkHostile N M +
          OptimizedHostileTimestamps.timestampCollisionBound (3 * N) +
          pricedWalkWork N M : ℚ) / cardK +
        (ioWork : ℚ) / cardK ^ 2 +
        ((ioFailureUnionBound 10 M M cardK + cardK * M : ℕ) : ℚ) / cardK ^ 2 :=
  rfl

/-- **`hostile_bound_eq`.**  The consumed bound function at `p8Work := p8WorkHostile N M`.
`cardF` is unused in the current body (no base-field summand). -/
theorem hostile_bound_eq (cardK cardF N M ioWork : ℕ) :
    optimizedHostileProductionFailureProbabilityBound cardK cardF
        (p8WorkHostile N M) ioWork N M =
      hostileBoundAtMajorant cardK N M ioWork :=
  rfl

/-! ## 4. `SizeWindowNounsBoundedBy` at `Λ_hostile := M`

Every size-window noun of the decoded skeleton
has `≤ M` leaves (every leaf is a memory row) -/

/-- **Generic inhabit.**  Any skeleton whose size-window nouns have `≤ M` leaves
satisfies the leaf window at `Λ_hostile := M`. -/
theorem sizeWindowNounsBoundedBy_of_leaves
    {K : Type} [Field K] [Fintype K] [DecidableEq K]
    (skel : SemanticStrategy.SemanticSkeleton) (M : ℕ)
    (h : ∀ n ∈ skeletonSizeWindowNouns (S := skel), Noun.leaves n ≤ M) :
    SizeWindowNounsBoundedBy (S := skel) M :=
  h

theorem sizeWindowNounsBoundedBy_iff
    {K : Type} [Field K] [Fintype K] [DecidableEq K]
    (skel : SemanticStrategy.SemanticSkeleton) (M : ℕ) :
    SizeWindowNounsBoundedBy (S := skel) M ↔
      ∀ n ∈ skeletonSizeWindowNouns (S := skel), Noun.leaves n ≤ M :=
  Iff.rfl

/-! ## 5. Recomputed figures at `p8WorkHostile`

Old figures, for the side-by-side: paper configuration **123**
(`GoldilocksParameters.hostile_soundness_at_paper_configuration`, `ioWork ≤ 16^65`),
real programs **122** at `2^31` / **120** at `2^32`
(`RealProgramSoundness.hostile_soundness_for_real_programs_at_two_pow_31/_32`).

The `16^65` ceiling still applies to the paper-configuration analogue — it is a
hypothesis on `ioWork`, independent of `p8Work`, and still fails of every real
execution at `N = 2^31` with two or more records per row
(`not_ioWork_le_at_two_records_per_row`). -/

/-- `p8WorkHostile` at the paper row counts, as a power of two. -/
theorem p8WorkHostile_at_two_pow_31 :
    p8WorkHostile (2 ^ 31) (2 ^ 31) ≤ 2 ^ 68 := by
  rw [p8WorkHostile_diag]
  norm_num

theorem p8WorkHostile_at_two_pow_31_ge :
    2 ^ 67 ≤ p8WorkHostile (2 ^ 31) (2 ^ 31) := by
  rw [p8WorkHostile_diag]
  norm_num

/-- **THE PAPER-CONFIGURATION FIGURE AT `p8WorkHostile` IS `122`.**  Old figure **123**. -/
theorem hostile_soundness_at_paper_configuration_majorant (ioWork : ℕ)
    (hio : ioWork ≤ 16 ^ 65) :
    goldilocksHostileFailureBound (p8WorkHostile (2 ^ 31) (2 ^ 31)) ioWork
        (2 ^ 31) (2 ^ 31)
      < 1 / (2 : ℚ) ^ 122 := by
  rw [goldilocksHostileFailureBound_eq]
  have hts := timestampCollisionBound_at_paper_configuration
  have hwr := walkAndTilingBound_at_paper_configuration
  have hp8 := p8WorkHostile_at_two_pow_31
  have hinter :
      ((ioFailureUnionBound 10 (2 ^ 31) (2 ^ 31) cardKGold
          + cardKGold * 2 ^ 31 : ℕ) : ℚ) / (cardKGold : ℚ) ^ 2
      = ((36 : ℚ) * 2 ^ 62 + 5 * 2 ^ 31) / (cardKGold : ℚ) := by
    rw [ioFailureUnionBound_ten]
    have hk : (cardKGold : ℚ) ≠ 0 := by norm_num
    field_simp
    ring
  have hmaj :
      ((2 : ℚ) ^ 68 + (2 : ℚ) ^ 65 + (2 : ℚ) ^ 36) / (cardKGold : ℚ)
        + ((16 : ℚ) ^ 65) / (cardKGold : ℚ) ^ 2
        + ((36 : ℚ) * 2 ^ 62 + 5 * 2 ^ 31) / (cardKGold : ℚ)
        < 1 / (2 : ℚ) ^ 122 := by
    norm_num
  have hp8' : (p8WorkHostile (2 ^ 31) (2 ^ 31) : ℚ) ≤ (2 : ℚ) ^ 68 := by
    exact_mod_cast hp8
  have hts' : (OptimizedHostileTimestamps.timestampCollisionBound (3 * 2 ^ 31) : ℚ)
      ≤ (2 : ℚ) ^ 65 := by exact_mod_cast hts
  have hwr' : (pricedWalkWork (2 ^ 31) (2 ^ 31) : ℚ) ≤ (2 : ℚ) ^ 36 := by
    exact_mod_cast hwr
  have hio' : (ioWork : ℚ) ≤ (16 : ℚ) ^ 65 := by exact_mod_cast hio
  have hsum :
      (p8WorkHostile (2 ^ 31) (2 ^ 31) : ℚ) +
        (OptimizedHostileTimestamps.timestampCollisionBound (3 * 2 ^ 31) : ℚ) +
        (pricedWalkWork (2 ^ 31) (2 ^ 31) : ℚ) ≤
      (2 : ℚ) ^ 68 + (2 : ℚ) ^ 65 + (2 : ℚ) ^ 36 := by
    linarith [hp8', hts', hwr']
  calc
    (p8WorkHostile (2 ^ 31) (2 ^ 31) +
          OptimizedHostileTimestamps.timestampCollisionBound (3 * 2 ^ 31) +
          pricedWalkWork (2 ^ 31) (2 ^ 31) : ℚ) /
          (cardKGold : ℚ)
        + (ioWork : ℚ) / (cardKGold : ℚ) ^ 2
        + ((ioFailureUnionBound 10 (2 ^ 31) (2 ^ 31) cardKGold
            + cardKGold * 2 ^ 31 : ℕ) : ℚ) / (cardKGold : ℚ) ^ 2
        = ((p8WorkHostile (2 ^ 31) (2 ^ 31) : ℚ) +
            (OptimizedHostileTimestamps.timestampCollisionBound (3 * 2 ^ 31) : ℚ) +
            (pricedWalkWork (2 ^ 31) (2 ^ 31) : ℚ)) /
            (cardKGold : ℚ)
          + (ioWork : ℚ) / (cardKGold : ℚ) ^ 2
          + ((36 : ℚ) * 2 ^ 62 + 5 * 2 ^ 31) / (cardKGold : ℚ) := by
            rw [hinter]
    _ ≤ ((2 : ℚ) ^ 68 + (2 : ℚ) ^ 65 + (2 : ℚ) ^ 36) / (cardKGold : ℚ)
          + ((16 : ℚ) ^ 65) / (cardKGold : ℚ) ^ 2
          + ((36 : ℚ) * 2 ^ 62 + 5 * 2 ^ 31) / (cardKGold : ℚ) := by
            gcongr
    _ < 1 / (2 : ℚ) ^ 122 := hmaj

/-- **Floor: `> 2^-125`.**  Old floor
`2^-128` was the α-summand; the majorant is now the larger term.  Together with
the `122` upper half, `122` is a figure and not a ceiling. -/
theorem hostile_lower_bound_at_paper_configuration_majorant (ioWork : ℕ) :
    1 / (2 : ℚ) ^ 125
      < goldilocksHostileFailureBound (p8WorkHostile (2 ^ 31) (2 ^ 31)) ioWork
          (2 ^ 31) (2 ^ 31) := by
  rw [goldilocksHostileFailureBound_eq]
  have h2 : (0 : ℚ) ≤ (ioWork : ℚ) / (cardKGold : ℚ) ^ 2 := by positivity
  have hinter0 : (0 : ℚ) ≤
      ((ioFailureUnionBound 10 (2 ^ 31) (2 ^ 31) cardKGold
          + cardKGold * 2 ^ 31 : ℕ) : ℚ) / (cardKGold : ℚ) ^ 2 := by positivity
  have hts0 : (0 : ℚ) ≤
      (OptimizedHostileTimestamps.timestampCollisionBound (3 * 2 ^ 31) : ℚ) := by
    positivity
  have hwr0 : (0 : ℚ) ≤ (pricedWalkWork (2 ^ 31) (2 ^ 31) : ℚ) := by
    positivity
  have hp8 := p8WorkHostile_at_two_pow_31_ge
  have hnumq : ((2 : ℕ) ^ 67 : ℚ) ≤ (p8WorkHostile (2 ^ 31) (2 ^ 31) : ℚ) := by
    exact_mod_cast hp8
  have h1 : 1 / (2 : ℚ) ^ 125
      < (p8WorkHostile (2 ^ 31) (2 ^ 31) +
          OptimizedHostileTimestamps.timestampCollisionBound (3 * 2 ^ 31) +
          pricedWalkWork (2 ^ 31) (2 ^ 31) : ℚ) /
          (cardKGold : ℚ) := by
    have hstep : 1 / (2 : ℚ) ^ 125 < ((2 : ℚ) ^ 67) / (cardKGold : ℚ) := by
      norm_num
    refine hstep.trans_le ?_
    refine div_le_div_of_nonneg_right ?_ (by norm_num)
    push_cast at hnumq ⊢
    linarith
  exact h1.trans_le
    ((le_add_of_nonneg_right h2).trans (le_add_of_nonneg_right hinter0))

/-- **`123` is lost at the paper configuration once `p8Work` is the majorant.**
At `ioWork = 16^65` the bound is not below `2^-123`.  Instrument: `norm_num` on
the exact closed form against `cardKGold`. -/
theorem not_123_at_paper_configuration_majorant :
    ¬ goldilocksHostileFailureBound (p8WorkHostile (2 ^ 31) (2 ^ 31)) (16 ^ 65)
        (2 ^ 31) (2 ^ 31)
      < 1 / (2 : ℚ) ^ 123 := by
  rw [goldilocksHostileFailureBound_eq]
  simp only [p8WorkHostile, p8Majorant,
    OptimizedHostileTimestamps.timestampCollisionBound, pricedWalkWork,
    ComputeWalkRootEvents.walkRootBound, ComputeWalkRootEvents.walkAlphaRootBound,
    ComputeWalkRootEvents.walkRootGammaBound,
    WalkTilingEvents.computeTilingBound, WalkTilingEvents.memoryTilingBound,
    WalkPrefixGammaEvents.computePrefixGammaBound,
    WalkPrefixGammaEvents.memoryPrefixGammaBound,
    WalkForestPrefixAlphaEvents.memoryForestAlphaBound, pwAccountingWork']
  rw [ioFailureUnionBound_ten]
  norm_num

/-! ### 5.1 Ceiling-free real programs at `p8WorkHostile`

`2 · hostileTotalWork (p8WorkHostile N M) N M ≤ 373S² + 112S + 28` at uniform size
`S`.  The bit
relation `2r + b = 184` is unchanged, so the ceiling-free figures
stay **122** at `2^31` and **120** at `2^32`. -/

/-- The pre-thirty-third form at `p8WorkHostile` alone (`453S² + 150S + 288`), kept for the
receipts that price the pair separately. -/
theorem two_hostileTotalWork_le_p8WorkHostile_prePair (S N M : ℕ)
    (hN : N ≤ S) (hM : M ≤ S) :
    2 * hostileTotalWork (p8WorkHostile N M) N M
      ≤ 453 * (S * S) + 150 * S + 288 := by
  have h1 : p8WorkHostile N M ≤ 42 * (S * S) + 38 * S + 1 :=
    p8WorkHostile_le_of_size S N M hN hM
  have h2 := OptimizedHostileTimestamps.two_mul_timestampCollisionBound_le (3 * N)
  have h3 : (3 * N + M) * (3 * N + M) ≤ (4 * S) * (4 * S) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h4 : (M + M) * (M + M) ≤ (2 * S) * (2 * S) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hwr : ComputeWalkRootEvents.walkRootBound N ≤ S + 9 := by
    rw [ComputeWalkRootEvents.walkRootBound_eq]; omega
  have htc : WalkTilingEvents.computeTilingBound N ≤ 2 * S + 2 := by
    simp only [WalkTilingEvents.computeTilingBound]; omega
  have htm : WalkTilingEvents.memoryTilingBound M ≤ 2 * S + 1 := by
    simp only [WalkTilingEvents.memoryTilingBound]; omega
  have hγc : WalkPrefixGammaEvents.computePrefixGammaBound N ≤ 9 * S := by
    simp only [WalkPrefixGammaEvents.computePrefixGammaBound]; omega
  have hγm : WalkPrefixGammaEvents.memoryPrefixGammaBound M ≤ 5 * S := by
    simp only [WalkPrefixGammaEvents.memoryPrefixGammaBound]; omega
  simp only [hostileTotalWork]
  have e1 : 2 * (p8WorkHostile N M +
      OptimizedHostileTimestamps.timestampCollisionBound (3 * N) +
      (9 * ((3 * N + M) * (3 * N + M)) + 2 * (3 * N + M)) +
      (9 * ((M + M) * (M + M)) + 2 * (M + M)) + M +
      pricedWalkWork N M)
      = 2 * p8WorkHostile N M +
        2 * OptimizedHostileTimestamps.timestampCollisionBound (3 * N) +
        18 * ((3 * N + M) * (3 * N + M)) + 4 * (3 * N + M) +
        18 * ((M + M) * (M + M)) + 4 * (M + M) + 2 * M +
        2 * pricedWalkWork N M := by ring
  rw [e1]
  have e2 : 453 * (S * S) + 150 * S + 288 =
      2 * (42 * (S * S) + 38 * S + 1) + (3 * S * (3 * S) + 2) +
        18 * ((4 * S) * (4 * S)) + 16 * S +
        18 * ((2 * S) * (2 * S)) + 8 * S + 2 * S +
        2 * (S + 9) + 2 * (2 * S + 2) + 2 * (2 * S + 1) +
        2 * (9 * S) + 2 * (5 * S) + 2 * S +
        2 * (4 * S + 130) := by ring
  rw [e2]
  have hp8 : 2 * p8WorkHostile N M ≤ 2 * (42 * (S * S) + 38 * S + 1) :=
    Nat.mul_le_mul_left 2 h1
  have h3N : (3 * N) * (3 * N) ≤ (3 * S) * (3 * S) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hts : 2 * OptimizedHostileTimestamps.timestampCollisionBound (3 * N)
      ≤ (3 * S) * (3 * S) + 2 :=
    le_trans h2 (Nat.add_le_add_right h3N 2)
  have hquad1 : 18 * ((3 * N + M) * (3 * N + M)) ≤ 18 * ((4 * S) * (4 * S)) :=
    Nat.mul_le_mul_left 18 h3
  have hquad2 : 18 * ((M + M) * (M + M)) ≤ 18 * ((2 * S) * (2 * S)) :=
    Nat.mul_le_mul_left 18 h4
  have hlin1 : 4 * (3 * N + M) ≤ 16 * S := by omega
  have hlin2 : 4 * (M + M) ≤ 8 * S := by omega
  have hlin3 : 2 * M ≤ 2 * S := by omega
  have hpw : pricedWalkWork N M ≤
      (S + 9) + (2 * S + 2) + (2 * S + 1) + 9 * S + 5 * S + S + (4 * S + 130) := by
    simp only [pricedWalkWork, WalkPrefixGammaEvents.computePrefixGammaBound,
      WalkPrefixGammaEvents.memoryPrefixGammaBound,
      WalkForestPrefixAlphaEvents.memoryForestAlphaBound, pwAccountingWork']
    omega
  have hlin4 : 2 * pricedWalkWork N M ≤
      2 * ((S + 9) + (2 * S + 2) + (2 * S + 1) + 9 * S + 5 * S + S + (4 * S + 130)) := by omega
  omega

/-- **** at the hostile majorant `Λ = M`, so the pair
summand is `M·(2M − 1) ≤ 2S²` and the doubled numerator is `457S² + 150S + 288` (was `453`). -/
theorem two_hostileTotalWork_le_p8WorkHostile (S N M : ℕ)
    (hN : N ≤ S) (hM : M ≤ S) :
    2 * hostileTotalWork (p8WorkHostile N M + M * (2 * M - 1)) N M
      ≤ 457 * (S * S) + 150 * S + 288 := by
  have h := two_hostileTotalWork_le_p8WorkHostile_prePair S N M hN hM
  have hW : hostileTotalWork (p8WorkHostile N M + M * (2 * M - 1)) N M =
      hostileTotalWork (p8WorkHostile N M) N M + M * (2 * M - 1) := by
    simp only [hostileTotalWork]; omega
  have hp : M * (2 * M - 1) ≤ 2 * (S * S) := by
    calc M * (2 * M - 1) ≤ S * (2 * S) := Nat.mul_le_mul hM (by omega)
      _ = 2 * (S * S) := by ring
  rw [hW]
  omega

/-- **The arithmetic core at the hostile majorant.**  `373` in place of §8's
`367`; the same `2r + b = 184`. -/
theorem hostileSizeWork_lt_cardK_majorant (r b : ℕ)
    (hr : 4 ≤ r) (hb : 2 * r + b = 184) :
    (457 * (2 ^ r * 2 ^ r) + 150 * 2 ^ r + 288) * 2 ^ b < 2 * cardKGold := by
  have h1 : (2 : ℕ) ^ r * 2 ^ r * 2 ^ b = 2 ^ 184 := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  have h2 : (2 : ℕ) ^ r * 2 ^ b ≤ 2 ^ 180 := by
    rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : (2 : ℕ) ^ b ≤ 2 ^ 176 := Nat.pow_le_pow_right (by norm_num) (by omega)
  calc (457 * (2 ^ r * 2 ^ r) + 150 * 2 ^ r + 288) * 2 ^ b
      = 457 * (2 ^ r * 2 ^ r * 2 ^ b) + 150 * (2 ^ r * 2 ^ b) + 288 * 2 ^ b := by
        ring
    _ ≤ 457 * 2 ^ 184 + 150 * 2 ^ 180 + 288 * 2 ^ 176 := by
        rw [h1]
        exact Nat.add_le_add
          (Nat.add_le_add_left (Nat.mul_le_mul_left 150 h2) _)
          (Nat.mul_le_mul_left 288 h3)
    _ < 2 * cardKGold := by norm_num

/-- **And `184 − 2r` is still the best:** `373 · 2^185 > 2·|K|`. -/
theorem hostileSizeWork_not_lt_cardK_majorant (r b : ℕ)
    (hb : 2 * r + b = 184) :
    ¬ ((457 * (2 ^ r * 2 ^ r) + 150 * 2 ^ r + 288) * 2 ^ (b + 1)
        < 2 * cardKGold) := by
  have h1 : (2 : ℕ) ^ r * 2 ^ r * 2 ^ (b + 1) = 2 ^ 185 := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  have hA : 457 * (2 ^ r * 2 ^ r)
      ≤ 457 * (2 ^ r * 2 ^ r) + 150 * 2 ^ r + 288 := by omega
  have hstep : 457 * (2 ^ r * 2 ^ r) * 2 ^ (b + 1)
      ≤ (457 * (2 ^ r * 2 ^ r) + 150 * 2 ^ r + 288) * 2 ^ (b + 1) :=
    Nat.mul_le_mul_right _ hA
  have heq : 457 * (2 ^ r * 2 ^ r) * 2 ^ (b + 1) = 457 * 2 ^ 185 := by
    rw [mul_assoc, h1]
  rw [heq] at hstep
  have hcard : 2 * cardKGold ≤ 457 * 2 ^ 185 := by norm_num
  exact Nat.not_lt.mpr (le_trans hcard hstep)

theorem hostile_soundness_at_row_budget_majorant (r b N M : ℕ)
    (hr : 4 ≤ r) (hb : 2 * r + b = 184)
    (hN : N ≤ 2 ^ r) (hM : M ≤ 2 ^ r) :
    goldilocksHostileFailureBound (p8WorkHostile N M + M * (2 * M - 1))
        (ioFailureUnionBound 10 (3 * N) M (Fintype.card Nock.Field.K)) N M
      < 1 / (2 : ℚ) ^ b := by
  refine hostileBound_lt_of_totalWork _ _ _ _ ?_
  have h := two_hostileTotalWork_le_p8WorkHostile (2 ^ r) N M hN hM
  have h' := hostileSizeWork_lt_cardK_majorant r b hr hb
  have : 2 * (hostileTotalWork (p8WorkHostile N M + M * (2 * M - 1)) N M * 2 ^ b)
      ≤ (457 * (2 ^ r * 2 ^ r) + 150 * 2 ^ r + 288) * 2 ^ b := by
    rw [← mul_assoc]; exact Nat.mul_le_mul_right _ h
  omega

/-- **122 bits for real programs at `2^31` rows — at `p8WorkHostile`.**  Old
figure **122**.  Ceiling-free; the `16^65` hypothesis is not used. -/
theorem hostile_soundness_for_real_programs_at_two_pow_31_majorant
    (N M : ℕ) (hN : N ≤ 2 ^ 31) (hM : M ≤ 2 ^ 31) :
    goldilocksHostileFailureBound (p8WorkHostile N M + M * (2 * M - 1))
        (ioFailureUnionBound 10 (3 * N) M (Fintype.card Nock.Field.K)) N M
      < 1 / (2 : ℚ) ^ 122 :=
  hostile_soundness_at_row_budget_majorant 31 122 N M
    (by norm_num) (by norm_num) hN hM

/-- **120 bits at the deployable maximum `2^32` rows — at `p8WorkHostile`.**  Old
figure **120**. -/
theorem hostile_soundness_for_real_programs_at_two_pow_32_majorant
    (N M : ℕ) (hN : N ≤ 2 ^ 32) (hM : M ≤ 2 ^ 32) :
    goldilocksHostileFailureBound (p8WorkHostile N M + M * (2 * M - 1))
        (ioFailureUnionBound 10 (3 * N) M (Fintype.card Nock.Field.K)) N M
      < 1 / (2 : ℚ) ^ 120 :=
  hostile_soundness_at_row_budget_majorant 32 120 N M
    (by norm_num) (by norm_num) hN hM

end

end HostileWorkloadMajorant
end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.HostileWorkloadMajorant.p8WorkHostile
#print axioms Nock.NockVMROM.Thm54.HostileWorkloadMajorant.workload_le_p8WorkHostile
#print axioms Nock.NockVMROM.Thm54.HostileWorkloadMajorant.hostile_bound_at_majorant
#print axioms Nock.NockVMROM.Thm54.HostileWorkloadMajorant.hostile_bound_eq
#print axioms Nock.NockVMROM.Thm54.HostileWorkloadMajorant.sizeWindowNounsBoundedBy_of_leaves
#print axioms Nock.NockVMROM.Thm54.HostileWorkloadMajorant.hostile_soundness_at_paper_configuration_majorant
#print axioms Nock.NockVMROM.Thm54.HostileWorkloadMajorant.hostile_lower_bound_at_paper_configuration_majorant
#print axioms Nock.NockVMROM.Thm54.HostileWorkloadMajorant.not_123_at_paper_configuration_majorant
#print axioms Nock.NockVMROM.Thm54.HostileWorkloadMajorant.hostile_soundness_for_real_programs_at_two_pow_31_majorant
#print axioms Nock.NockVMROM.Thm54.HostileWorkloadMajorant.hostile_soundness_for_real_programs_at_two_pow_32_majorant
