/-
  Nock/RedTeam/Batch981Thm54S3Figures.lean

  Every numerator below is DERIVED from the
  definitions (`RealProgramSoundness.hostileTotalWork`, `p8Majorant`, the λ / pair / S3 summands),
  not quoted:

  * **§A — the core.**
  * **§B — the four numerators.**
    - **+ S3 (2b-ii's summand, `k = 3`): `481S² + 398S + 28`** (`numerator_s3`, the name of the new
      doubled numerator: `doubledNumeratorS3`);
  * **§C — the bits.**  `b = 184 − 2r` for all four (`122` at `2^31`, `120` at `2^32`), and it is the
    best each numerator gives (`…_not_more`).  Ceiling: `511` (`512S²` loses 122).
  * **§D — the paper configuration.**
-/
import Nock.NockVMROM.Thm54.S3PairEvent
import Nock.NockVMROM.Thm54.HostileWorkloadMajorant
import Nock.RedTeam.Batch915Thm54Part2bS3Figures

set_option autoImplicit false
set_option maxRecDepth 20000

namespace Nock.RedTeam.Batch981

open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.RealProgramSoundness
open Nock.NockVMROM.Thm54.GoldilocksParameters
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.HostileWorkloadMajorant
open Nock.NockVMROM.Thm54.S3PairEvent

/-! ## §A  The core and the shares -/

theorem two_hostileTotalWork_le_core (S R M p8Work : ℕ) (hR : R ≤ S) (hM : M ≤ S) :
    2 * hostileTotalWork p8Work R M ≤ 2 * p8Work + (369 * (S * S) + 66 * S + 26) := by
  have h2 := OptimizedHostileTimestamps.two_mul_timestampCollisionBound_le (3 * R)
  have h3N : (3 * R) * (3 * R) ≤ (3 * S) * (3 * S) := Nat.mul_le_mul (by omega) (by omega)
  have h3 : (3 * R + M) * (3 * R + M) ≤ (4 * S) * (4 * S) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h4 : (M + M) * (M + M) ≤ (2 * S) * (2 * S) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hpw : pricedWalkWork R M ≤ (S + 9) + (2 * S + 2) + (2 * S + 1) + 9 * S + 5 * S + S := by
    simp only [pricedWalkWork, ComputeWalkRootEvents.walkRootBound_eq,
      WalkTilingEvents.computeTilingBound, WalkTilingEvents.memoryTilingBound,
      WalkPrefixGammaEvents.computePrefixGammaBound,
      WalkPrefixGammaEvents.memoryPrefixGammaBound,
      WalkForestPrefixAlphaEvents.memoryForestAlphaBound]
    omega
  have e3 : (4 * S) * (4 * S) = 16 * (S * S) := by ring
  have e4 : (2 * S) * (2 * S) = 4 * (S * S) := by ring
  have e5 : (3 * S) * (3 * S) = 9 * (S * S) := by ring
  rw [e3] at h3
  rw [e4] at h4
  rw [e5] at h3N
  simp only [hostileTotalWork]
  omega

theorem share_p8_package (S R M Λ A : ℕ) (hR : R ≤ S) (hM : M ≤ S) (hΛ : Λ ≤ S) (hA : A ≤ S) :
    2 * p8Majorant R M Λ A ≤ 78 * (S * S) + 78 * S + 2 := by
  have := p8Majorant_le_of_size S R M Λ A hR hM hΛ hA
  omega

theorem share_p8_built (S R M Λ : ℕ) (hR : R ≤ S) (hM : M ≤ S) (hΛ : Λ ≤ S) :
    2 * p8Majorant R M Λ (3 * R * M) ≤ 84 * (S * S) + 76 * S + 2 := by
  have a1 : (3 + 19 * R) * (2 * Λ) ≤ (3 + 19 * S) * (2 * S) :=
    Nat.mul_le_mul (by omega) (by omega)
  have a1' : (3 + 19 * S) * (2 * S) = 38 * (S * S) + 6 * S := by ring
  have a2 : Λ * Λ ≤ S * S := Nat.mul_le_mul hΛ hΛ
  have a3 : 3 * R * M ≤ 3 * (S * S) := by
    have : R * M ≤ S * S := Nat.mul_le_mul hR hM
    calc 3 * R * M = 3 * (R * M) := by ring
      _ ≤ 3 * (S * S) := Nat.mul_le_mul_left 3 this
  rw [a1'] at a1
  simp only [p8Majorant]
  omega

/-- The λ-event `M(3N + 130)`: doubled share `6S² + 260S`. -/
theorem share_formR (S R M : ℕ) (hR : R ≤ S) (hM : M ≤ S) :
    2 * (M * (3 * R + 130)) ≤ 6 * (S * S) + 260 * S := by
  have : M * (3 * R + 130) ≤ S * (3 * S + 130) := Nat.mul_le_mul hM (by omega)
  nlinarith

theorem share_pair (S M Λ : ℕ) (hM : M ≤ S) (hΛ : Λ ≤ S) :
    2 * (M * (2 * (M ⊔ Λ) - 1)) ≤ 4 * (S * S) := by
  have hmax : M ⊔ Λ ≤ S := max_le hM hΛ
  have : M * (2 * (M ⊔ Λ) - 1) ≤ S * (2 * S) := Nat.mul_le_mul hM (by omega)
  nlinarith

/-- **The S3 term `3N·(2·s3Window M Λ − 1)`: doubled share `24S² − 6S`** (as `+ 6S ≤ 24S²`). -/
theorem share_s3 (S R M Λ : ℕ) (hR : R ≤ S) (hM : M ≤ S) (hΛ : Λ ≤ S) :
    2 * (3 * R * (2 * s3Window M Λ - 1)) + 6 * S ≤ 24 * (S * S) := by
  have hW := s3Window_le_two_mul hM hΛ
  have h1 : 2 * s3Window M Λ - 1 ≤ 4 * S - 1 := by omega
  have h2 : 3 * R * (2 * s3Window M Λ - 1) ≤ 3 * S * (4 * S - 1) :=
    Nat.mul_le_mul (by omega) h1
  rcases Nat.eq_zero_or_pos S with h0 | hpos
  · subst h0
    have : R = 0 := by omega
    subst this
    simp
  · have e : 3 * S * (4 * S - 1) = 12 * (S * S) - 3 * S := by
      rw [Nat.mul_sub, mul_one]
      ring_nf
    have h3S : 3 * S ≤ 12 * (S * S) := by nlinarith
    omega

/-- **The S3 share is exact on the diagonal** `R = M = Λ = S`. -/
theorem s3_share_diag (S : ℕ) :
    2 * (3 * S * (2 * s3Window S S - 1)) + 6 * S = 24 * (S * S) := by
  unfold s3Window
  rw [max_self]
  rcases Nat.eq_zero_or_pos S with h0 | hpos
  · subst h0; simp
  · have e : 2 * (S + S) - 1 = 4 * S - 1 := by omega
    rw [e]
    have e2 : 3 * S * (4 * S - 1) = 12 * (S * S) - 3 * S := by
      rw [Nat.mul_sub, mul_one]; ring_nf
    rw [e2]
    have h3S : 3 * S ≤ 12 * (S * S) := by nlinarith
    omega

/-! ## §B  The four numerators -/

/-- The new doubled numerator with the S3 summand. -/
def doubledNumeratorS3 (S : ℕ) : ℕ := 481 * (S * S) + 398 * S + 28

theorem numerator_base (S R M Λ A p8Work : ℕ) (hR : R ≤ S) (hM : M ≤ S) (hΛ : Λ ≤ S)
    (hA : A ≤ S)
    (hp8 : p8Work ≤ p8Majorant R M Λ A + M * (3 * R + 130) + M * (2 * (M ⊔ Λ) - 1)) :
    2 * hostileTotalWork p8Work R M ≤ 457 * (S * S) + 404 * S + 28 := by
  have hc := two_hostileTotalWork_le_core S R M p8Work hR hM
  have h1 := share_p8_package S R M Λ A hR hM hΛ hA
  have h2 := share_formR S R M hR hM
  have h3 := share_pair S M Λ hM hΛ
  omega

/-- **The S3 numerator (2b-ii's `workload` + `s3Work`): `481S² + 398S + 28`.** -/
theorem numerator_s3 (S R M Λ A p8Work : ℕ) (hR : R ≤ S) (hM : M ≤ S) (hΛ : Λ ≤ S)
    (hA : A ≤ S)
    (hp8 : p8Work ≤ p8Majorant R M Λ A + M * (3 * R + 130) + M * (2 * (M ⊔ Λ) - 1) +
      3 * R * (2 * s3Window M Λ - 1)) :
    2 * hostileTotalWork p8Work R M ≤ doubledNumeratorS3 S := by
  have hc := two_hostileTotalWork_le_core S R M p8Work hR hM
  have h1 := share_p8_package S R M Λ A hR hM hΛ hA
  have h2 := share_formR S R M hR hM
  have h3 := share_pair S M Λ hM hΛ
  have h4 := share_s3 S R M Λ hR hM hΛ
  unfold doubledNumeratorS3
  omega

theorem numerator_F8 (S R M Λ p8Work : ℕ) (hR : R ≤ S) (hM : M ≤ S) (hΛ : Λ ≤ S)
    (hp8 : p8Work ≤ p8Majorant R M Λ (3 * R * M) + M * (3 * R + 130) +
      M * (2 * (M ⊔ Λ) - 1)) :
    2 * hostileTotalWork p8Work R M ≤ 463 * (S * S) + 402 * S + 28 := by
  have hc := two_hostileTotalWork_le_core S R M p8Work hR hM
  have h1 := share_p8_built S R M Λ hR hM hΛ
  have h2 := share_formR S R M hR hM
  have h3 := share_pair S M Λ hM hΛ
  omega

/-- F8 is the baseline plus exactly the axis share: `463 − 457 = 6 = 2·3` (`A ≤ 3NM` at `S²`) and
`402 − 404 = −2` (the dropped `A ≤ S`); and `p8WorkHostile` (`Λ := M`) is an instance. -/
theorem F8_is_baseline_plus_axis (S : ℕ) :
    463 * (S * S) + 402 * S + 28 + 2 * S = 457 * (S * S) + 404 * S + 28 + 6 * (S * S) := by ring

theorem F8_at_p8WorkHostile (S N M : ℕ) (hN : N ≤ S) (hM : M ≤ S) :
    2 * hostileTotalWork (p8WorkHostile N M + M * (3 * N + 130) + M * (2 * M - 1)) N M ≤
      463 * (S * S) + 402 * S + 28 := by
  refine numerator_F8 S N M M _ hN hM hM ?_
  rw [max_self]
  simp only [p8WorkHostile]
  exact le_refl _

theorem numerator_builtS3 (S R M Λ p8Work : ℕ) (hR : R ≤ S) (hM : M ≤ S) (hΛ : Λ ≤ S)
    (hp8 : p8Work ≤ p8Majorant R M Λ (3 * R * M) + M * (3 * R + 130) +
      M * (2 * (M ⊔ Λ) - 1) + 3 * R * (2 * s3Window M Λ - 1)) :
    2 * hostileTotalWork p8Work R M ≤ 487 * (S * S) + 396 * S + 28 := by
  have hc := two_hostileTotalWork_le_core S R M p8Work hR hM
  have h1 := share_p8_built S R M Λ hR hM hΛ
  have h2 := share_formR S R M hR hM
  have h3 := share_pair S M Λ hM hΛ
  have h4 := share_s3 S R M Λ hR hM hΛ
  omega

/-! ## §C  The bits -/

open Nock.RedTeam.Batch881 (Crit)

/-- And no more: `c·2^185 ≥ 2|𝕂|` kills `b + 1`. -/
theorem size_not_more (c l k r b : ℕ) (hb : 2 * r + b = 184) (hc : 2 * cardKGold ≤ c * 2 ^ 185) :
    ¬ ((c * (2 ^ r * 2 ^ r) + l * 2 ^ r + k) * 2 ^ (b + 1) < 2 * cardKGold) := by
  have h1 : (2 : ℕ) ^ r * 2 ^ r * 2 ^ (b + 1) = 2 ^ 185 := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  have hstep : c * (2 ^ r * 2 ^ r) * 2 ^ (b + 1)
      ≤ (c * (2 ^ r * 2 ^ r) + l * 2 ^ r + k) * 2 ^ (b + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  have heq : c * (2 ^ r * 2 ^ r) * 2 ^ (b + 1) = c * 2 ^ 185 := by rw [mul_assoc, h1]
  rw [heq] at hstep
  exact Nat.not_lt.mpr (le_trans hc hstep)

/-- From a doubled numerator to the bound (`Crit c l k r b` is `Batch881`'s criterion:
`(c·S² + l·S + k)·2^b < 2|𝕂|` at `S = 2^r`). -/
theorem bound_of_numerator (c l k r b R M p8Work : ℕ) (hck : Crit c l k r b)
    (h : 2 * hostileTotalWork p8Work R M ≤ c * (2 ^ r * 2 ^ r) + l * 2 ^ r + k) :
    goldilocksHostileFailureBound p8Work
        (ioFailureUnionBound 10 (3 * R) M (Fintype.card Nock.Field.K)) R M
      < 1 / (2 : ℚ) ^ b := by
  refine hostileBound_lt_of_totalWork _ _ _ _ ?_
  unfold Crit at hck
  have : 2 * (hostileTotalWork p8Work R M * 2 ^ b) ≤ (c * (2 ^ r * 2 ^ r) + l * 2 ^ r + k) * 2 ^ b := by
    rw [← mul_assoc]; exact Nat.mul_le_mul_right _ h
  omega

theorem crit_481_122 : Crit 481 398 28 31 122 := by unfold Crit; norm_num
theorem crit_481_120 : Crit 481 398 28 32 120 := by unfold Crit; norm_num
theorem crit_463_122 : Crit 463 402 28 31 122 := by unfold Crit; norm_num
theorem crit_463_120 : Crit 463 402 28 32 120 := by unfold Crit; norm_num
theorem crit_487_122 : Crit 487 396 28 31 122 := by unfold Crit; norm_num
theorem crit_487_120 : Crit 487 396 28 32 120 := by unfold Crit; norm_num
theorem crit_511_122 : Crit 511 404 28 31 122 := by unfold Crit; norm_num
theorem not_crit_512_122 : ¬ Crit 512 0 0 31 122 := by unfold Crit; norm_num
theorem builtS3_k6_122 : Crit 511 390 28 31 122 := by unfold Crit; norm_num
theorem builtS3_k7_not_122 : ¬ Crit 519 388 28 31 122 := by unfold Crit; norm_num

/-- **122 bits at `2^31` rows with the S3 summand** (2b-ii's `workload` + `s3Work`). -/
theorem hostile_soundness_s3_at_two_pow_31 (R M Λ A p8Work : ℕ)
    (hR : R ≤ 2 ^ 31) (hM : M ≤ 2 ^ 31) (hΛ : Λ ≤ 2 ^ 31) (hA : A ≤ 2 ^ 31)
    (hp8 : p8Work ≤ p8Majorant R M Λ A + M * (3 * R + 130) + M * (2 * (M ⊔ Λ) - 1) +
      3 * R * (2 * s3Window M Λ - 1)) :
    goldilocksHostileFailureBound p8Work
        (ioFailureUnionBound 10 (3 * R) M (Fintype.card Nock.Field.K)) R M
      < 1 / (2 : ℚ) ^ 122 :=
  bound_of_numerator 481 398 28 31 122 R M p8Work crit_481_122
    (numerator_s3 _ R M Λ A p8Work hR hM hΛ hA hp8)

/-- **120 bits at `2^32` rows with the S3 summand.** -/
theorem hostile_soundness_s3_at_two_pow_32 (R M Λ A p8Work : ℕ)
    (hR : R ≤ 2 ^ 32) (hM : M ≤ 2 ^ 32) (hΛ : Λ ≤ 2 ^ 32) (hA : A ≤ 2 ^ 32)
    (hp8 : p8Work ≤ p8Majorant R M Λ A + M * (3 * R + 130) + M * (2 * (M ⊔ Λ) - 1) +
      3 * R * (2 * s3Window M Λ - 1)) :
    goldilocksHostileFailureBound p8Work
        (ioFailureUnionBound 10 (3 * R) M (Fintype.card Nock.Field.K)) R M
      < 1 / (2 : ℚ) ^ 120 :=
  bound_of_numerator 481 398 28 32 120 R M p8Work crit_481_120
    (numerator_s3 _ R M Λ A p8Work hR hM hΛ hA hp8)

/-- And `184 − 2r` is the best `481S²+398S+28` gives. -/
theorem s3_numerator_not_more (r b : ℕ) (hb : 2 * r + b = 184) :
    ¬ ((481 * (2 ^ r * 2 ^ r) + 398 * 2 ^ r + 28) * 2 ^ (b + 1) < 2 * cardKGold) :=
  size_not_more 481 398 28 r b hb (by norm_num)

/-- F8: 122 / 120. -/
theorem F8_122 (R M Λ p8Work : ℕ) (hR : R ≤ 2 ^ 31) (hM : M ≤ 2 ^ 31) (hΛ : Λ ≤ 2 ^ 31)
    (hp8 : p8Work ≤ p8Majorant R M Λ (3 * R * M) + M * (3 * R + 130) +
      M * (2 * (M ⊔ Λ) - 1)) :
    goldilocksHostileFailureBound p8Work
        (ioFailureUnionBound 10 (3 * R) M (Fintype.card Nock.Field.K)) R M
      < 1 / (2 : ℚ) ^ 122 :=
  bound_of_numerator 463 402 28 31 122 R M p8Work crit_463_122
    (numerator_F8 _ R M Λ p8Work hR hM hΛ hp8)

theorem F8_120 (R M Λ p8Work : ℕ) (hR : R ≤ 2 ^ 32) (hM : M ≤ 2 ^ 32) (hΛ : Λ ≤ 2 ^ 32)
    (hp8 : p8Work ≤ p8Majorant R M Λ (3 * R * M) + M * (3 * R + 130) +
      M * (2 * (M ⊔ Λ) - 1)) :
    goldilocksHostileFailureBound p8Work
        (ioFailureUnionBound 10 (3 * R) M (Fintype.card Nock.Field.K)) R M
      < 1 / (2 : ℚ) ^ 120 :=
  bound_of_numerator 463 402 28 32 120 R M p8Work crit_463_120
    (numerator_F8 _ R M Λ p8Work hR hM hΛ hp8)

theorem builtS3_122 (R M Λ p8Work : ℕ) (hR : R ≤ 2 ^ 31) (hM : M ≤ 2 ^ 31) (hΛ : Λ ≤ 2 ^ 31)
    (hp8 : p8Work ≤ p8Majorant R M Λ (3 * R * M) + M * (3 * R + 130) +
      M * (2 * (M ⊔ Λ) - 1) + 3 * R * (2 * s3Window M Λ - 1)) :
    goldilocksHostileFailureBound p8Work
        (ioFailureUnionBound 10 (3 * R) M (Fintype.card Nock.Field.K)) R M
      < 1 / (2 : ℚ) ^ 122 :=
  bound_of_numerator 487 396 28 31 122 R M p8Work crit_487_122
    (numerator_builtS3 _ R M Λ p8Work hR hM hΛ hp8)

theorem builtS3_120 (R M Λ p8Work : ℕ) (hR : R ≤ 2 ^ 32) (hM : M ≤ 2 ^ 32) (hΛ : Λ ≤ 2 ^ 32)
    (hp8 : p8Work ≤ p8Majorant R M Λ (3 * R * M) + M * (3 * R + 130) +
      M * (2 * (M ⊔ Λ) - 1) + 3 * R * (2 * s3Window M Λ - 1)) :
    goldilocksHostileFailureBound p8Work
        (ioFailureUnionBound 10 (3 * R) M (Fintype.card Nock.Field.K)) R M
      < 1 / (2 : ℚ) ^ 120 :=
  bound_of_numerator 487 396 28 32 120 R M p8Work crit_487_120
    (numerator_builtS3 _ R M Λ p8Work hR hM hΛ hp8)

/-! ## §D  The paper configuration -/

/-- The S3 term at its value at `N = M = Λ = 2^31` is below `2^66`. -/
theorem s3_term_paper : 3 * 2 ^ 31 * (2 * s3Window (2 ^ 31) (2 ^ 31) - 1) ≤ 2 ^ 66 := by
  unfold s3Window; norm_num

/-- The pair term at its value is below `2^63`. -/
theorem pair_term_paper : 2 ^ 31 * (2 * ((2 : ℕ) ^ 31 ⊔ 2 ^ 31) - 1) ≤ 2 ^ 63 := by
  norm_num

/-- **123 at the paper configuration, with the S3 and pair terms AT THEIR VALUES** (under the
`p8Work ≤ 2^60` and `ioWork ≤ 16^65` ceilings). -/
theorem hostile_soundness_s3_at_paper_configuration (p8Work ioWork : ℕ)
    (hp8 : p8Work ≤ 2 ^ 60) (hio : ioWork ≤ 16 ^ 65) :
    goldilocksHostileFailureBound
        (p8Work + (2 ^ 31 * (2 * ((2 : ℕ) ^ 31 ⊔ 2 ^ 31) - 1) +
          3 * 2 ^ 31 * (2 * s3Window (2 ^ 31) (2 ^ 31) - 1)))
        ioWork (2 ^ 31) (2 ^ 31)
      < 1 / (2 : ℚ) ^ 123 :=
  Batch915.hostile_soundness_S3_at_paper_configuration p8Work ioWork _ _ hp8 hio
    pair_term_paper s3_term_paper

def builtS3PaperWork : ℕ :=
  p8WorkHostile (2 ^ 31) (2 ^ 31) + 2 ^ 31 * (3 * 2 ^ 31 + 130) + 2 ^ 31 * (2 * 2 ^ 31 - 1) +
    3 * 2 ^ 31 * (2 * s3Window (2 ^ 31) (2 ^ 31) - 1)

theorem builtS3PaperWork_eq : builtS3PaperWork = 272089475439403204609 := by
  unfold builtS3PaperWork
  rw [p8WorkHostile_diag]
  unfold s3Window
  norm_num

theorem bound_mono_io (p8Work ioWork N M : ℕ) (hio : ioWork ≤ 16 ^ 65) :
    goldilocksHostileFailureBound p8Work ioWork N M ≤
      goldilocksHostileFailureBound p8Work (16 ^ 65) N M := by
  rw [goldilocksHostileFailureBound_eq, goldilocksHostileFailureBound_eq]
  have : (ioWork : ℚ) ≤ ((16 ^ 65 : ℕ) : ℚ) := by exact_mod_cast hio
  gcongr

theorem builtS3_paper_122 (ioWork : ℕ) (hio : ioWork ≤ 16 ^ 65) :
    goldilocksHostileFailureBound builtS3PaperWork ioWork (2 ^ 31) (2 ^ 31)
      < 1 / (2 : ℚ) ^ 122 := by
  refine lt_of_le_of_lt (bound_mono_io _ _ _ _ hio) ?_
  rw [goldilocksHostileFailureBound_eq]
  rw [builtS3PaperWork_eq]
  simp only [OptimizedHostileTimestamps.timestampCollisionBound, pricedWalkWork,
    ComputeWalkRootEvents.walkRootBound, ComputeWalkRootEvents.walkAlphaRootBound,
    ComputeWalkRootEvents.walkRootGammaBound,
    WalkTilingEvents.computeTilingBound, WalkTilingEvents.memoryTilingBound,
    WalkPrefixGammaEvents.computePrefixGammaBound,
    WalkPrefixGammaEvents.memoryPrefixGammaBound,
    WalkForestPrefixAlphaEvents.memoryForestAlphaBound]
  rw [ioFailureUnionBound_ten]
  norm_num

/-- **And `123` is lost there** (at `ioWork = 16^65`). -/
theorem builtS3_paper_not_123 :
    ¬ goldilocksHostileFailureBound builtS3PaperWork (16 ^ 65) (2 ^ 31) (2 ^ 31)
      < 1 / (2 : ℚ) ^ 123 := by
  rw [goldilocksHostileFailureBound_eq]
  rw [builtS3PaperWork_eq]
  simp only [OptimizedHostileTimestamps.timestampCollisionBound, pricedWalkWork,
    ComputeWalkRootEvents.walkRootBound, ComputeWalkRootEvents.walkAlphaRootBound,
    ComputeWalkRootEvents.walkRootGammaBound,
    WalkTilingEvents.computeTilingBound, WalkTilingEvents.memoryTilingBound,
    WalkPrefixGammaEvents.computePrefixGammaBound,
    WalkPrefixGammaEvents.memoryPrefixGammaBound,
    WalkForestPrefixAlphaEvents.memoryForestAlphaBound]
  rw [ioFailureUnionBound_ten]
  norm_num

end Nock.RedTeam.Batch981

#print axioms Nock.RedTeam.Batch981.numerator_s3
#print axioms Nock.RedTeam.Batch981.numerator_F8
#print axioms Nock.RedTeam.Batch981.numerator_builtS3
#print axioms Nock.RedTeam.Batch981.hostile_soundness_s3_at_two_pow_31
#print axioms Nock.RedTeam.Batch981.hostile_soundness_s3_at_two_pow_32
#print axioms Nock.RedTeam.Batch981.F8_122
#print axioms Nock.RedTeam.Batch981.F8_120
#print axioms Nock.RedTeam.Batch981.builtS3_122
#print axioms Nock.RedTeam.Batch981.builtS3_120
#print axioms Nock.RedTeam.Batch981.hostile_soundness_s3_at_paper_configuration
#print axioms Nock.RedTeam.Batch981.builtS3_paper_122
#print axioms Nock.RedTeam.Batch981.builtS3_paper_not_123
