/-
  Nock/RedTeam/Batch1040Thm54EventFirstFigures.lean

  * **§A — the shares.**
  * **§B — the doubled numerator: `463S² + 412S + 30`** (`numerator_ev`): the redesign's
    `463S² + 406S + 30` plus the envelope's `6S`.  **122 at `2^31`, 120 at `2^32`**
    (`crit_463_412_*`, `hostile_soundness_ev_at_two_pow_31/_32`).
-/
import Nock.NockVMROM.Thm54.OptimizedFailureEventEv
import Nock.RedTeam.Batch981Thm54S3Figures
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch1040

open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.RealProgramSoundness
open Nock.NockVMROM.Thm54.GoldilocksParameters
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.HostileWorkloadMajorant
open Nock.NockVMROM.Thm54.SizeWindowCounting
open Nock.NockVMROM.Thm54.P8EventEv
open Nock.NockVMROM.Thm54.OptimizedFailureEventEv
open Nock.RedTeam.Batch981
open Nock.RedTeam.Batch881 (Crit)

/-! ## §A  The shares -/

theorem share_p8_ev (S R M Λ : ℕ) (hR : R ≤ S) (hM : M ≤ S) (hΛ : Λ ≤ S) :
    2 * p8WorkEv R M Λ ≤ 84 * (S * S) + 82 * S + 2 := by
  have a1 : (3 + 19 * R) * (2 * Λ - 1) ≤ (3 + 19 * S) * (2 * S) :=
    Nat.mul_le_mul (by omega) (by omega)
  have a1' : (3 + 19 * S) * (2 * S) = 38 * (S * S) + 6 * S := by ring
  have a2 : sizeWindowRootBound Λ ≤ S * S :=
    (sizeWindowRootBound_le_square Λ).trans (Nat.mul_le_mul hΛ hΛ)
  have a3 : axisUniformWorkload R M ≤ 3 * (S * S) + 3 * S := by
    unfold axisUniformWorkload
    have : M * (3 * R + 3) ≤ S * (3 * S + 3) := Nat.mul_le_mul hM (by omega)
    nlinarith
  have a4 : 24 * R + 8 * M ≤ 32 * S := by omega
  simp only [p8WorkEv]
  rw [a1'] at a1
  omega

/-- The root-result pair `2Λg − 1`: doubled `≤ 4S`. -/
theorem share_root (S M Λ : ℕ) (hM : M ≤ S) (hΛ : Λ ≤ S) :
    2 * (2 * (M ⊔ Λ) - 1) ≤ 4 * S := by
  have hmax : M ⊔ Λ ≤ S := max_le hM hΛ
  omega

/-! ## §B  The doubled numerator and the bits -/

theorem numerator_ev (S R M Λ p8Work : ℕ) (hR : R ≤ S) (hM : M ≤ S) (hΛ : Λ ≤ S)
    (hp8 : p8Work ≤ p8WorkEv R M Λ + M * (3 * R + 130) +
      M * (2 * (M ⊔ Λ) - 1) + (2 * (M ⊔ Λ) - 1) + 1) :
    2 * hostileTotalWork p8Work R M ≤ 463 * (S * S) + 412 * S + 30 := by
  have hc := two_hostileTotalWork_le_core S R M p8Work hR hM
  have h1 := share_p8_ev S R M Λ hR hM hΛ
  have h2 := share_formR S R M hR hM
  have h3 := share_pair S M Λ hM hΛ
  have h4 := share_root S M Λ hM hΛ
  omega

theorem crit_463_412_122 : Crit 463 412 30 31 122 := by unfold Crit; norm_num
theorem crit_463_412_120 : Crit 463 412 30 32 120 := by unfold Crit; norm_num

/-- The numerator is the best it gives: `463S² + 412S + 30` at `2^31` does not reach 123. -/
theorem not_crit_463_412_123 : ¬ Crit 463 412 30 31 123 := by unfold Crit; norm_num

/-- **122 bits at `2^31` rows** at the assembled event (ceiling-free). -/
theorem hostile_soundness_ev_at_two_pow_31 (R M Λ p8Work : ℕ)
    (hR : R ≤ 2 ^ 31) (hM : M ≤ 2 ^ 31) (hΛ : Λ ≤ 2 ^ 31)
    (hp8 : p8Work ≤ p8WorkEv R M Λ + M * (3 * R + 130) +
      M * (2 * (M ⊔ Λ) - 1) + (2 * (M ⊔ Λ) - 1) + 1) :
    goldilocksHostileFailureBound p8Work
        (ioFailureUnionBound 10 (3 * R) M (Fintype.card Nock.Field.K)) R M
      < 1 / (2 : ℚ) ^ 122 :=
  bound_of_numerator 463 412 30 31 122 R M p8Work crit_463_412_122
    (numerator_ev _ R M Λ p8Work hR hM hΛ hp8)

/-- **120 bits at `2^32` rows.** -/
theorem hostile_soundness_ev_at_two_pow_32 (R M Λ p8Work : ℕ)
    (hR : R ≤ 2 ^ 32) (hM : M ≤ 2 ^ 32) (hΛ : Λ ≤ 2 ^ 32)
    (hp8 : p8Work ≤ p8WorkEv R M Λ + M * (3 * R + 130) +
      M * (2 * (M ⊔ Λ) - 1) + (2 * (M ⊔ Λ) - 1) + 1) :
    goldilocksHostileFailureBound p8Work
        (ioFailureUnionBound 10 (3 * R) M (Fintype.card Nock.Field.K)) R M
      < 1 / (2 : ℚ) ^ 120 :=
  bound_of_numerator 463 412 30 32 120 R M p8Work crit_463_412_120
    (numerator_ev _ R M Λ p8Work hR hM hΛ hp8)

/-! ## §C  The paper configuration -/

def p8WorkEvNum (N M Λ : ℕ) : ℕ :=
  1 + (3 + 19 * N) * (2 * Λ) + (24 * N + 8 * M) + M * (3 * N + 3) + Λ * Λ

theorem p8WorkEv_le_num (N M Λ : ℕ) : p8WorkEv N M Λ ≤ p8WorkEvNum N M Λ := by
  unfold p8WorkEv p8WorkEvNum axisUniformWorkload
  have h1 : (3 + 19 * N) * (2 * Λ - 1) ≤ (3 + 19 * N) * (2 * Λ) :=
    Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have h2 := sizeWindowRootBound_le_square Λ
  omega

/-- The assembled numerator at the paper configuration (`N = M = Λ = 2^31`). -/
def evPaperWork : ℕ :=
  p8WorkEvNum (2 ^ 31) (2 ^ 31) (2 ^ 31) + 2 ^ 31 * (3 * 2 ^ 31 + 130) +
    2 ^ 31 * (2 * 2 ^ 31 - 1) + (2 * 2 ^ 31 - 1) + 1

/-- The bound is monotone in `p8Work`. -/
theorem bound_mono_p8 (a b ioWork N M : ℕ) (h : a ≤ b) :
    goldilocksHostileFailureBound a ioWork N M ≤ goldilocksHostileFailureBound b ioWork N M := by
  rw [goldilocksHostileFailureBound_eq, goldilocksHostileFailureBound_eq]
  have : (a : ℚ) ≤ (b : ℚ) := by exact_mod_cast h
  gcongr

/-- **122 at the paper configuration** at the assembled event. -/
theorem ev_paper_122 :
    goldilocksHostileFailureBound evPaperWork (16 ^ 65) (2 ^ 31) (2 ^ 31) < 1 / (2 : ℚ) ^ 122 := by
  rw [goldilocksHostileFailureBound_eq]
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

theorem ev_paper_not_123 :
    ¬ goldilocksHostileFailureBound evPaperWork (16 ^ 65) (2 ^ 31) (2 ^ 31) < 1 / (2 : ℚ) ^ 123 := by
  rw [goldilocksHostileFailureBound_eq]
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

theorem ev_ceiling_paper_123 :
    goldilocksHostileFailureBound
        (2 ^ 60 + 2 ^ 31 * (3 * 2 ^ 31 + 130) + 2 ^ 31 * (2 * 2 ^ 31 - 1) + (2 * 2 ^ 31 - 1) + 1)
        (16 ^ 65) (2 ^ 31) (2 ^ 31)
      < 1 / (2 : ℚ) ^ 123 := by
  rw [goldilocksHostileFailureBound_eq]
  simp only [OptimizedHostileTimestamps.timestampCollisionBound, pricedWalkWork,
    ComputeWalkRootEvents.walkRootBound, ComputeWalkRootEvents.walkAlphaRootBound,
    ComputeWalkRootEvents.walkRootGammaBound,
    WalkTilingEvents.computeTilingBound, WalkTilingEvents.memoryTilingBound,
    WalkPrefixGammaEvents.computePrefixGammaBound,
    WalkPrefixGammaEvents.memoryPrefixGammaBound,
    WalkForestPrefixAlphaEvents.memoryForestAlphaBound]
  rw [ioFailureUnionBound_ten]
  norm_num

/-! ## §D  At `P`: the assembled numerator is below the numeric majorant -/

section AtP

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

theorem formRUniformWorkload_eq :
    ProductionP8Containment.formRUniformWorkload P.strategy =
      DecodedLambdaEvent.formRUniformWorkloadOf (FormRAxisEvent.formRN K) (N P) (M P) := by
  have hcfg : P.optimized.family.problem.cfg =
      P.strategy.specializedCfg P.honestSeed P.honestSeed_ne P.honestAlpha
        P.optimized.objects.cfg.challenges.lam := by
    rw [P.optimized.family_cfg]
    exact (congrArg (fun x => x.cfg) P.honest_specialization).symm
  have hN : P.optimized.family.problem.cfg.compRows =
      (SemanticStrategy.computeSkeletonRows P.strategy.skeleton).length := by
    rw [hcfg]
    have h := (P.optimized.strategy_bindsAll P.honestSeed P.honestSeed_ne P.honestAlpha
      P.optimized.objects.cfg.challenges.lam).computeRows.length_eq
    rw [ExactExecution.computeRows_length] at h
    exact h.symm
  have hM : P.optimized.family.problem.cfg.memRows =
      (SemanticStrategy.memorySkeletonRows P.strategy.skeleton).length := by
    rw [hcfg]
    have h := (P.optimized.strategy_bindsAll P.honestSeed P.honestSeed_ne P.honestAlpha
      P.optimized.objects.cfg.challenges.lam).memoryRows.length_eq
    rw [ExactExecution.memoryRows_length] at h
    exact h.symm
  unfold ProductionP8Containment.formRUniformWorkload DecodedLambdaEvent.formRUniformWorkloadOf
  show _ = P.optimized.family.problem.cfg.memRows *
    (3 * P.optimized.family.problem.cfg.compRows + 67 + (FormRAxisEvent.formRN K - 1))
  rw [hN, hM]

/-- **`workloadEv P Λ` is below the numeric majorant the figures use**, at chip width
(`formRN K ≤ 64`, `FormRWidth`'s first conjunct). -/
theorem workloadEv_le_numeral (hn : FormRAxisEvent.formRN K ≤ 64) (Λ : ℕ) :
    workloadEv P Λ ≤ p8WorkEv (N P) (M P) Λ + M P * (3 * N P + 130) +
      M P * (2 * (M P ⊔ Λ) - 1) + (2 * (M P ⊔ Λ) - 1) + 1 := by
  unfold workloadEv
  rw [formRUniformWorkload_eq P]
  have := DecodedLambdaEvent.formRUniformWorkloadOf_le_of_width hn (N P) (M P)
  omega

end AtP

end Nock.RedTeam.Batch1040

#print axioms Nock.RedTeam.Batch1040.hostile_soundness_ev_at_two_pow_31
#print axioms Nock.RedTeam.Batch1040.hostile_soundness_ev_at_two_pow_32
#print axioms Nock.RedTeam.Batch1040.ev_paper_122
#print axioms Nock.RedTeam.Batch1040.ev_paper_not_123
#print axioms Nock.RedTeam.Batch1040.ev_ceiling_paper_123
#print axioms Nock.RedTeam.Batch1040.workloadEv_le_numeral
