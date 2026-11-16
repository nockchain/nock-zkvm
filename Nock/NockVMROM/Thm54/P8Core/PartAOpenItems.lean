/-
  Nock/NockVMROM/Thm54/P8Core/PartAOpenItems.lean

  Sits below the statement half
.

  **(a) The memory residual columns `182..204` are round 0 under L1's map
  (`RepartitionedStaging.newMemoryColRound`), so `StagedTraces12` fixes them before every coin.**
  * `residual_round_zero`: every column `≥ 180` of the width-205 memory trace is round 0;
  * `canonicalFinalMemoryTrace_residual_zero`: the honest generator's final memory trace is the
    zero polynomial on every residual column, for EVERY challenge / public vector it is fed —
    the fill is coin-free;
  * `honest_residual_staged`: so any honest strategy `c ↦ canonicalFinalMemoryTrace … (cv c) (pv c)`
    is constant on the residual columns, which is exactly what `Staged12` asks of a round-0 column;
  * `memoryChipAt12_satisfies_residual_free`: the twelve-coin memory chip reads no residual column
    (acceptance depends on the first `182` columns only), so the residual fill cannot affect
    acceptance either.

  **(b) The event pinned at the 303-column truncation.**
  * `truncQc_eq_lt303`: the truncation keeps columns `0..302` verbatim, and the dropped columns
    are exactly the six walk limbs `303..308` (`dropped_eq_walkLimbs`);
  * `consumedFailureEvent309_congr_lt303`: the parallel package's consumed event reads the 309
    trace only through columns `< 303`.

  -- the paper
-/
import Nock.NockVMROM.Thm54.P8Core.PartAStaged12

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.PartAOpenItems

open scoped Polynomial
open Nock Nock.Framework
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedMemoryRAP
open Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction
open Nock.NockVMROM.Thm54.RepartitionedStaging
open Nock.NockVMROM.Thm54.PartA12
open Nock.NockVMROM.Thm54.PartAStaged
open Nock.NockVMROM.Thm54.StrictExtension

noncomputable section

/-! ## (a) The residual columns -/

/-- Every memory column `≥ 180` (atom `180`, `reqIdx` `181`, the residual `182..204`) is round 0
under L1's map. -/
theorem residual_round_zero (j : ℕ) (hj : 180 ≤ j) : newMemoryColRound j = 0 := by
  unfold newMemoryColRound
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

section Canonical

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [Fintype K] [DecidableEq K] [DecidableEq F]
variable {p : ℕ} [CharP K p]
variable {R : PlusIOSegmentedFamily F K}

/-- **The honest fill of the residual columns is coin-free**: whatever challenge vector `cv` and
public vector `pv` the generator is run at, the final canonical memory trace is the zero
polynomial on every column `≥ 182` (`rightPadTrace` pads with `0`). -/
theorem canonicalFinalMemoryTrace_residual_zero
    (A : SampledIOSameExecutionAssignment R p) (nodes : Fin R.problem.cfg.memRows → F)
    [FiniteDimensional F K] (b : Module.Basis (Fin 3) F K) (cv pv : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (j : Fin (namedFinalMemoryRAP R.problem.cfg.memRows_pos nodes b cv pv orbit
      R.problem.cfg.kMem).rap.w)
    (hj : 182 ≤ (j : ℕ)) :
    canonicalFinalMemoryTrace A nodes b cv pv orbit j = 0 := by
  unfold canonicalFinalMemoryTrace rightPadTrace
  obtain ⟨k, hk⟩ : ∃ k : Fin (RAPPadding.extraWidth (RAPPadding.firstRoundExtra
      (namedSourceMemoryRAP R.problem.cfg.memRows_pos nodes b cv pv orbit R.problem.cfg.kMem).rap
      (namedSourceMemoryRAP R.problem.cfg.memRows_pos nodes b cv pv orbit
        R.problem.cfg.kMem).rounds_pos (RAPPadding.memoryResidualColumns 3))),
      j = Fin.natAdd 182 k := by
    have hjw := j.isLt
    refine ⟨⟨(j : ℕ) - 182, ?_⟩, Fin.ext ?_⟩
    · rw [RAPPadding.extraWidth_firstRoundExtra]
      have : (namedFinalMemoryRAP R.problem.cfg.memRows_pos nodes b cv pv orbit
          R.problem.cfg.kMem).rap.w = 205 :=
        (finalMemoryRAP_fingerprint _ nodes b cv pv orbit _).1
      simp only [RAPPadding.memoryResidualColumns]
      omega
    · simp only [Fin.val_natAdd]
      omega
  rw [hk]
  exact Fin.addCases_right (m := 182) k

end Canonical

section Package

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- **(a), staged form**: any honest strategy that runs the generator at coin-dependent challenge
and public vectors `cv c`, `pv c` is constant in `c` on every residual column (the round-0
requirement of `Staged12`), because the fill is `0` at every coin. -/
theorem honest_residual_staged {ι : Type*}
    {R : PlusIOSegmentedFamily F K} {p : ℕ} [CharP K p]
    (A : SampledIOSameExecutionAssignment R p) (nodes : Fin R.problem.cfg.memRows → F)
    (b : Module.Basis (Fin 3) F K) (cv pv : ι → ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h) (x y : ι) (j : ℕ) (hj : 182 ≤ j)
    (hx : j < (namedFinalMemoryRAP R.problem.cfg.memRows_pos nodes b (cv x) (pv x) orbit
      R.problem.cfg.kMem).rap.w)
    (hy : j < (namedFinalMemoryRAP R.problem.cfg.memRows_pos nodes b (cv y) (pv y) orbit
      R.problem.cfg.kMem).rap.w) :
    canonicalFinalMemoryTrace A nodes b (cv x) (pv x) orbit ⟨j, hx⟩ =
      canonicalFinalMemoryTrace A nodes b (cv y) (pv y) orbit ⟨j, hy⟩ := by
  rw [canonicalFinalMemoryTrace_residual_zero _ _ _ _ _ _ _ hj,
    canonicalFinalMemoryTrace_residual_zero _ _ _ _ _ _ _ hj]

/-- **(a), acceptance**: the twelve-coin memory chip reads no residual column — two package traces
that agree on the first `182` columns are accepted at the same tuples. -/
theorem memoryChipAt12_satisfies_residual_free (c : OptimizedProductionChallengeTuple12 K F)
    (Qm Qm' : Fin P.memoryChip.rap.w → F[X])
    (hagree : ∀ j : Fin P.memoryChip.rap.w, (j : ℕ) < 182 → Qm j = Qm' j) :
    RAP.SatisfiesWithPreprocessing (Pkg12.memoryChipAt12 P c) (Pkg12.familyQm12 P c Qm) ↔
      RAP.SatisfiesWithPreprocessing (Pkg12.memoryChipAt12 P c) (Pkg12.familyQm12 P c Qm') := by
  unfold Pkg12.memoryChipAt12 DeployedChipFamily12.memoryChipAt12 namedFinalMemoryRAP12
  erw [RAPPadding.padFixedPreprocessing_satisfies_iff, RAPPadding.padFixedPreprocessing_satisfies_iff]
  have hproj : RAPPadding.projectTrace _ _ (Pkg12.familyQm12 P c Qm) =
      RAPPadding.projectTrace _ _ (Pkg12.familyQm12 P c Qm') := by
    funext i
    simp only [RAPPadding.projectTrace, RAPPadding.columnInclusion, Function.Embedding.coeFn_mk,
      Pkg12.familyQm12]
    apply hagree
    have aux : ∀ (m k m' : ℕ) (h : m + k = m') (j : Fin m), ((Fin.cast h (Fin.castAdd k j) : Fin m') : ℕ) = j := fun _ _ _ _ _ => rfl
    refine lt_of_eq_of_lt (aux _ _ _ _ i) ?_
    exact i.isLt
  rw [hproj]

/-! ## (b) The truncation -/

/-- **(b)**: the truncation keeps every column `< 303` verbatim. -/
theorem truncQc_eq_lt303 (Qc : Fin 309 → F[X]) (j : Fin P.computeChip.rap.w) :
    truncQc P Qc j = Qc ⟨j, by have h1 := j.isLt; have h2 := computeWidth303 P; omega⟩ := rfl

/-- **(b)**: the dropped columns are exactly the six walk limbs `W0 = 303..305`,
`W1 = 306..308` (`Unhosted309.walkLimb`). -/
theorem dropped_eq_walkLimbs :
    (Finset.univ.filter fun j : Fin 309 => 303 ≤ (j : ℕ)).image (fun j : Fin 309 => (j : ℕ)) =
      (Finset.univ : Finset (Fin 2 × Fin 3)).image (fun q => Unhosted309.walkLimb q.1 q.2) := by
  decide

/-- **(b)**: the parallel consumed event reads the 309 trace only through columns `< 303`. -/
theorem consumedFailureEvent309_congr_lt303 (Qc Qc' : Fin 309 → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (hagree : ∀ j : Fin 309, (j : ℕ) < 303 → Qc j = Qc' j) :
    consumedFailureEvent309 P Qc Qm = consumedFailureEvent309 P Qc' Qm := by
  have ht : truncQc P Qc = truncQc P Qc' := by
    funext j
    unfold truncQc
    apply hagree
    show (j : ℕ) < 303
    have h1 := j.isLt; have h2 := computeWidth303 P; omega
  unfold consumedFailureEvent309
  rw [ht]

end Package


end

end Nock.NockVMROM.Thm54.PartAOpenItems
