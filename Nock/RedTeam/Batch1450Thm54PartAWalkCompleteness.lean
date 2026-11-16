import Nock.NockVMROM.Thm54.P8Core.PartAReWalk
import Nock.NockVMROM.Thm54.P8Core.PartAStaged12
import Nock.NockVMROM.Thm54.P8Core.WalkQueueDeployed
import Nock.RedTeam.Batch1040Thm54EventFirstFigures
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-
  Nock/RedTeam/Batch1450Thm54PartAWalkCompleteness.lean

  **R-T steps 1-2 — the corrected walk
  completeness, its negative control, summand 15 and the figures at the new bound.**

  * §C the figures at the NEW bound, recomputed (Goldilocks `|𝕂| = p³`):
    the doubled numerator `463S² + 412S + 30` becomes `464S² + 412S + 32`
    (`2·(1 + M(M−1)/2) ≤ M² + 2`); **122 at `2^31`** (`fig15_122`), **120 at `2^32`**
    (`fig15_120`), 123 not reached at `2^31` (`fig15_not_123`), 121 not reached at `2^32`
    (`fig15_not_121`); **paper configuration 122** (`fig15_paper_122`), 123 lost there
    (`fig15_paper_not_123`); **123 under the `p8Work ≤ 2^60` ceiling** (`fig15_ceiling_123`).
    No figure drops.

  Scope: `repartitionedChronology` and the parallel package; nothing here states or implies
  `:966` soundness at `deployedChronology`
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 20000

namespace Nock.RedTeam.Batch1450

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.PartAReWalk
open Nock.NockVMROM.Thm54.PartA12
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.RealProgramSoundness
open Nock.NockVMROM.Thm54.GoldilocksParameters
open Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.P8EventEv
open Nock.RedTeam.Batch981
open Nock.RedTeam.Batch1040
open Nock.RedTeam.Batch881 (Crit)

/-! ## §A  The corrected walk completeness and its negative controls -/

section A

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

theorem receipt_walkCompleteness12 (cur : ℕ → K) (chld' : ℕ → ℕ → K) (fo : ℕ → ℕ) (α : K)
    (kMem M : ℕ) (hk : 1 ≤ kMem) (hkM : kMem ≤ M)
    (hbft : IsForestFullBFT cur chld' fo kMem M) (htile : kMem + Sf fo M = M)
    (hvalid : BFSValidF kMem fo M)
    (hα : α ∉ OptimizedHostileTimestamps.TimestampCollisionEvent M) (hα0 : α ≠ 0) :
    ∃ ln count acc inv : ℕ → K,
      WalkSatInGate cur chld' fo ln count acc α (α ^ kMem) kMem M ∧ acc M = 0 ∧
      (∀ i, 1 ≤ i → i < M → inv i * (count i - ln i) = 1) ∧ count M = ln M := by
  obtain ⟨ln, count, acc, inv, hw, h0, hq, ht, -⟩ :=
    walkCompleteness12 cur chld' fo α kMem M hk hkM hbft htile hvalid hα hα0
  exact ⟨ln, count, acc, inv, hw, h0, hq, ht⟩

/-- Negative control (abstract): without the order premise the queue gate fails at `α = 1`. -/
theorem control_queue_fails_at_one {cur : ℕ → K} {chld' : ℕ → ℕ → K} {fo : ℕ → ℕ}
    {ln count acc : ℕ → K} {kMem M : ℕ}
    (hw : WalkSatInGate cur chld' fo ln count acc 1 ((1 : K) ^ kMem) kMem M) (h2 : 2 ≤ M)
    (inv : ℕ → K) : ¬ (∀ i, 1 ≤ i → i < M → inv i * (count i - ln i) = 1) :=
  queue_gate_fails_at_one hw h2 inv

/-- The premise is exactly what fails there: `1 ∈ TimestampCollisionEvent M` for `2 ≤ M`. -/
theorem control_premise_fails_at_one (M : ℕ) (h2 : 2 ≤ M) :
    (1 : K) ∈ OptimizedHostileTimestamps.TimestampCollisionEvent M :=
  one_mem_collision M h2

end A

section Landed

open Nock.Framework
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.WrapMemoryConjuncts
open Nock.NockVMROM.Thm54.WalkQueueDeployed
open Nock.NockVMROM.Thm54.MemoryWalkDeployed
open scoped Polynomial

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qm : Fin (P.memoryChipAt c).rap.w → F[X])

theorem no_memory_acceptance_at_one (h1 : alphaM c.1 = 1) (h2 : 2 ≤ MemoryWalkDeployed.memRows P)
    (hchar : MemStateTagChar F) :
    ¬ RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm := by
  intro hsat
  have hw := deployed_walkSat P c Qm hsat hchar
  have hne := count_ne_ln_of_queue_memory P c Qm hsat ⟨0, by omega⟩ (by simp only; omega)
  have hcnt := WalkSatInGate.count_closed hw 1 le_rfl (by omega)
  have hln := WalkSatInGate.ln_closed hw 1 le_rfl (by omega)
  simp only [zero_add] at hne
  rw [hcnt, hln, h1] at hne
  simp at hne

end Landed

/-! ## §B  Summand 15 -/

section B

open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- Summand 15 is the walk-line collision at the timestamp coin, at the memory row count. -/
theorem receipt_mem_summand15 (c : OptimizedProductionChallengeTuple12 K F) :
    c ∈ Pkg12.summand15 P ↔
      alphaM c.1 ∈ OptimizedHostileTimestamps.TimestampCollisionEvent
        P.optimized.family.problem.cfg.memRows :=
  Pkg12.mem_summand15 P c

theorem receipt_summand15_card :
    (Pkg12.summand15 (F := F) P).card ≤
      Fintype.card K ^ 11 * (1 + P.optimized.family.problem.cfg.memRows *
        (P.optimized.family.problem.cfg.memRows - 1) / 2) :=
  Pkg12.summand15_card_le P

end B

/-- **The new bound in shift form**: the walk-line term rides in the `|𝕂|` numerator, so the new
function is the OLD function (not redefined) at `p8Work + (1 + M(M−1)/2)`. -/
theorem bound15_eq_shift (cardK cardF p8Work ioWork N M : ℕ) :
    optimizedHostileProductionFailureProbabilityBound15 cardK cardF p8Work ioWork N M =
      optimizedHostileProductionFailureProbabilityBound cardK cardF
        (p8Work + OptimizedHostileTimestamps.timestampCollisionBound M) ioWork N M := by
  simp only [optimizedHostileProductionFailureProbabilityBound15,
    optimizedHostileProductionFailureProbabilityBound]
  push_cast
  ring

/-! ## §C  The figures at the new bound -/

/-- The new bound with Goldilocks plugged in. -/
noncomputable def goldilocksBound15 (p8Work ioWork N M : ℕ) : ℚ :=
  optimizedHostileProductionFailureProbabilityBound15 (Fintype.card Nock.Field.K)
    (Fintype.card Nock.Field.Fp) p8Work ioWork N M

theorem goldilocksBound15_eq (p8Work ioWork N M : ℕ) :
    goldilocksBound15 p8Work ioWork N M =
      goldilocksHostileFailureBound (p8Work + OptimizedHostileTimestamps.timestampCollisionBound M)
        ioWork N M := by
  unfold goldilocksBound15 goldilocksHostileFailureBound
  exact bound15_eq_shift _ _ _ _ _ _

theorem hostileTotalWork_add (a b N M : ℕ) :
    hostileTotalWork (a + b) N M = hostileTotalWork a N M + b := by
  unfold hostileTotalWork; ring

theorem numerator15 (S R M Λ p8Work : ℕ) (hR : R ≤ S) (hM : M ≤ S) (hΛ : Λ ≤ S)
    (hp8 : p8Work ≤ p8WorkEv R M Λ + M * (3 * R + 130) +
      M * (2 * (M ⊔ Λ) - 1) + (2 * (M ⊔ Λ) - 1) + 1) :
    2 * hostileTotalWork (p8Work + OptimizedHostileTimestamps.timestampCollisionBound M) R M ≤
      464 * (S * S) + 412 * S + 32 := by
  rw [hostileTotalWork_add]
  have h := numerator_ev S R M Λ p8Work hR hM hΛ hp8
  have h15 := OptimizedHostileTimestamps.two_mul_timestampCollisionBound_le M
  have hMM : M * M ≤ S * S := Nat.mul_le_mul hM hM
  omega

theorem crit15_122 : Crit 464 412 32 31 122 := by unfold Crit; norm_num
theorem crit15_120 : Crit 464 412 32 32 120 := by unfold Crit; norm_num
theorem not_crit15_123 : ¬ Crit 464 412 32 31 123 := by unfold Crit; norm_num
theorem not_crit15_121 : ¬ Crit 464 412 32 32 121 := by unfold Crit; norm_num

/-- **122 bits at `2^31` rows at the new bound** (ceiling-free). -/
theorem fig15_122 (R M Λ p8Work : ℕ)
    (hR : R ≤ 2 ^ 31) (hM : M ≤ 2 ^ 31) (hΛ : Λ ≤ 2 ^ 31)
    (hp8 : p8Work ≤ p8WorkEv R M Λ + M * (3 * R + 130) +
      M * (2 * (M ⊔ Λ) - 1) + (2 * (M ⊔ Λ) - 1) + 1) :
    goldilocksBound15 p8Work (ioFailureUnionBound 10 (3 * R) M (Fintype.card Nock.Field.K)) R M
      < 1 / (2 : ℚ) ^ 122 := by
  rw [goldilocksBound15_eq]
  exact bound_of_numerator 464 412 32 31 122 R M _ crit15_122
    (numerator15 _ R M Λ p8Work hR hM hΛ hp8)

/-- **120 bits at `2^32` rows at the new bound.** -/
theorem fig15_120 (R M Λ p8Work : ℕ)
    (hR : R ≤ 2 ^ 32) (hM : M ≤ 2 ^ 32) (hΛ : Λ ≤ 2 ^ 32)
    (hp8 : p8Work ≤ p8WorkEv R M Λ + M * (3 * R + 130) +
      M * (2 * (M ⊔ Λ) - 1) + (2 * (M ⊔ Λ) - 1) + 1) :
    goldilocksBound15 p8Work (ioFailureUnionBound 10 (3 * R) M (Fintype.card Nock.Field.K)) R M
      < 1 / (2 : ℚ) ^ 120 := by
  rw [goldilocksBound15_eq]
  exact bound_of_numerator 464 412 32 32 120 R M _ crit15_120
    (numerator15 _ R M Λ p8Work hR hM hΛ hp8)

/-- The numerator method gives no more: `464S² + 412S + 32` reaches neither 123 at `2^31` nor
121 at `2^32` (the same ceiling as before summand 15). -/
theorem fig15_not_123 : ¬ Crit 464 412 32 31 123 := not_crit15_123
theorem fig15_not_121 : ¬ Crit 464 412 32 32 121 := not_crit15_121

/-- **122 at the paper configuration at the new bound** (`N = M = Λ = 2^31`, `ioWork = 16^65`). -/
theorem fig15_paper_122 :
    goldilocksBound15 evPaperWork (16 ^ 65) (2 ^ 31) (2 ^ 31) < 1 / (2 : ℚ) ^ 122 := by
  rw [goldilocksBound15_eq, goldilocksHostileFailureBound_eq]
  simp only [OptimizedHostileTimestamps.timestampCollisionBound, pricedWalkWork,
    ComputeWalkRootEvents.walkRootBound, ComputeWalkRootEvents.walkAlphaRootBound,
    ComputeWalkRootEvents.walkRootGammaBound,
    WalkTilingEvents.computeTilingBound, WalkTilingEvents.memoryTilingBound,
    WalkPrefixGammaEvents.computePrefixGammaBound,
    WalkPrefixGammaEvents.memoryPrefixGammaBound,
    WalkForestPrefixAlphaEvents.memoryForestAlphaBound]
  rw [ioFailureUnionBound_ten]
  unfold evPaperWork p8WorkEvNum
  norm_num

/-- 123 at the paper configuration stays lost (it was lost before summand 15). -/
theorem fig15_paper_not_123 :
    ¬ goldilocksBound15 evPaperWork (16 ^ 65) (2 ^ 31) (2 ^ 31) < 1 / (2 : ℚ) ^ 123 := by
  rw [goldilocksBound15_eq, goldilocksHostileFailureBound_eq]
  simp only [OptimizedHostileTimestamps.timestampCollisionBound, pricedWalkWork,
    ComputeWalkRootEvents.walkRootBound, ComputeWalkRootEvents.walkAlphaRootBound,
    ComputeWalkRootEvents.walkRootGammaBound,
    WalkTilingEvents.computeTilingBound, WalkTilingEvents.memoryTilingBound,
    WalkPrefixGammaEvents.computePrefixGammaBound,
    WalkPrefixGammaEvents.memoryPrefixGammaBound,
    WalkForestPrefixAlphaEvents.memoryForestAlphaBound]
  rw [ioFailureUnionBound_ten]
  unfold evPaperWork p8WorkEvNum
  norm_num

/-- **123 at the paper configuration under the standing `p8Work ≤ 2^60` ceiling, at the new
bound** (every other summand, summand 15 included, at its value). -/
theorem fig15_ceiling_123 :
    goldilocksBound15
        (2 ^ 60 + 2 ^ 31 * (3 * 2 ^ 31 + 130) + 2 ^ 31 * (2 * 2 ^ 31 - 1) + (2 * 2 ^ 31 - 1) + 1)
        (16 ^ 65) (2 ^ 31) (2 ^ 31)
      < 1 / (2 : ℚ) ^ 123 := by
  rw [goldilocksBound15_eq, goldilocksHostileFailureBound_eq]
  simp only [OptimizedHostileTimestamps.timestampCollisionBound, pricedWalkWork,
    ComputeWalkRootEvents.walkRootBound, ComputeWalkRootEvents.walkAlphaRootBound,
    ComputeWalkRootEvents.walkRootGammaBound,
    WalkTilingEvents.computeTilingBound, WalkTilingEvents.memoryTilingBound,
    WalkPrefixGammaEvents.computePrefixGammaBound,
    WalkPrefixGammaEvents.memoryPrefixGammaBound,
    WalkForestPrefixAlphaEvents.memoryForestAlphaBound]
  rw [ioFailureUnionBound_ten]
  norm_num

end Nock.RedTeam.Batch1450

#print axioms Nock.RedTeam.Batch1450.receipt_walkCompleteness12
#print axioms Nock.RedTeam.Batch1450.no_memory_acceptance_at_one
#print axioms Nock.RedTeam.Batch1450.bound15_eq_shift
#print axioms Nock.RedTeam.Batch1450.fig15_122
#print axioms Nock.RedTeam.Batch1450.fig15_120
#print axioms Nock.RedTeam.Batch1450.fig15_paper_122
#print axioms Nock.RedTeam.Batch1450.fig15_paper_not_123
#print axioms Nock.RedTeam.Batch1450.fig15_ceiling_123
