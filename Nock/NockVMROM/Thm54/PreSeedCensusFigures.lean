/-
  Nock/NockVMROM/Thm54/PreSeedCensusFigures.lean

  **The figures with the fixed-pair summand.  Recomputed, not quoted.

  * **Positional census (`#pairs = M`, `PreSeedCensus.zipPairs`): the figures do not move.**
    `2·(hostileTotalWork + M(2Λ − 1)) ≤ 457S² + 404S + 28` (was `453S² + 404S + 28`), and
    `457·2^184 + 404·2^180 + 28·2^176 < 2|𝕂|`, so `b = 184 − 2r` holds: **122** at `2^31`,
    **120** at `2^32` (`…_pair_at_two_pow_31/_32`), tight for this numerator
    (`pairSizeWork_not_lt_cardK`).  Paper configuration (`p8Work ≤ 2^60`, `ioWork ≤ 16^65`,
    pair summand `≤ 2^63`): **123** (`hostile_soundness_at_paper_configuration_pair`).
  * **All-pairs census, worst case (`#pairs ≤ M²`, `Λ_hostile = M`): the figures BREAK.**
    The summand `M²(2M − 1)/|𝕂|` alone is above `2^-98` at `M = 2^31` and above `2^-95` at
    `M = 2^32` (`allPairs_floor_at_two_pow_31/_32`); with it the bound is below `2^-97` / `2^-94`
    (`…_allPairs_at_two_pow_31/_32`).  So **97 at `2^31`, 94 at `2^32`** (from 122 / 120).
-/
import Nock.NockVMROM.Thm54.RealProgramSoundness

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Nock.NockVMROM.Thm54.PreSeedCensusFigures

open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.GoldilocksParameters
open Nock.NockVMROM.Thm54.RealProgramSoundness
open Nock.NockVMROM.Thm54.OptimizedStrictPackage

/-- The positional census's pair summand numerator: `M` pairs, `2Λ − 1` seeds each. -/
def pairWork (M Λ : ℕ) : ℕ := M * (2 * Λ - 1)

/-- The all-pairs census's pair summand numerator: `M²` pairs, `2Λ − 1` seeds each. -/
def allPairWork (M Λ : ℕ) : ℕ := M * M * (2 * Λ - 1)

/-- Adding a `|𝕂|`-numerator summand to the consumed hostile bound. -/
theorem hostileBound_add_lt_of_totalWork (p8Work N M w b : ℕ)
    (h : (hostileTotalWork p8Work N M + w) * 2 ^ b < cardKGold) :
    goldilocksHostileFailureBound p8Work
        (ioFailureUnionBound 10 (3 * N) M (Fintype.card Nock.Field.K)) N M
        + (w : ℚ) / (cardKGold : ℚ)
      < 1 / (2 : ℚ) ^ b := by
  rw [hostileBound_at_majorants, ← add_div]
  rw [div_lt_div_iff₀ (by norm_num) (by positivity)]
  have hq : (((hostileTotalWork p8Work N M + w) * 2 ^ b : ℕ) : ℚ) < ((cardKGold : ℕ) : ℚ) := by
    exact_mod_cast h
  push_cast at hq ⊢
  linarith

/-! ### The positional census: `#pairs = M` -/

theorem two_hostileTotalWork_pair_le_of_size (S R M Λ A p8Work : ℕ)
    (hR : R ≤ S) (hM : M ≤ S) (hΛ : Λ ≤ S) (hA : A ≤ S)
    (hp8 : p8Work ≤ p8Majorant R M Λ A + M * (3 * R + 130)) :
    2 * (hostileTotalWork p8Work R M + pairWork M Λ) ≤ 457 * (S * S) + 404 * S + 28 := by
  have h := two_hostileTotalWork_le_of_size_formR_prePair S R M Λ A p8Work hR hM hΛ hA hp8
  have hp : pairWork M Λ ≤ S * (2 * S) := by
    unfold pairWork
    exact Nat.mul_le_mul hM (by omega)
  nlinarith

theorem pairSizeWork_lt_cardK (r b : ℕ) (hr : 4 ≤ r) (hb : 2 * r + b = 184) :
    (457 * (2 ^ r * 2 ^ r) + 404 * 2 ^ r + 28) * 2 ^ b < 2 * cardKGold := by
  have h1 : (2 : ℕ) ^ r * 2 ^ r * 2 ^ b = 2 ^ 184 := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  have h2 : (2 : ℕ) ^ r * 2 ^ b ≤ 2 ^ 180 := by
    rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : (2 : ℕ) ^ b ≤ 2 ^ 176 := Nat.pow_le_pow_right (by norm_num) (by omega)
  calc (457 * (2 ^ r * 2 ^ r) + 404 * 2 ^ r + 28) * 2 ^ b
      = 457 * (2 ^ r * 2 ^ r * 2 ^ b) + 404 * (2 ^ r * 2 ^ b) + 28 * 2 ^ b := by ring
    _ ≤ 457 * 2 ^ 184 + 404 * 2 ^ 180 + 28 * 2 ^ 176 := by
        rw [h1]
        exact Nat.add_le_add
          (Nat.add_le_add_left (Nat.mul_le_mul_left 404 h2) _)
          (Nat.mul_le_mul_left 28 h3)
    _ < 2 * cardKGold := by norm_num

/-- `184 − 2r` is the best this numerator gives (`457·2^185 > 2|𝕂|`). -/
theorem pairSizeWork_not_lt_cardK (r b : ℕ) (hb : 2 * r + b = 184) :
    ¬ ((457 * (2 ^ r * 2 ^ r) + 404 * 2 ^ r + 28) * 2 ^ (b + 1) < 2 * cardKGold) := by
  have h1 : (2 : ℕ) ^ r * 2 ^ r * 2 ^ (b + 1) = 2 ^ 185 := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  have hstep : 457 * (2 ^ r * 2 ^ r) * 2 ^ (b + 1)
      ≤ (457 * (2 ^ r * 2 ^ r) + 404 * 2 ^ r + 28) * 2 ^ (b + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  have heq : 457 * (2 ^ r * 2 ^ r) * 2 ^ (b + 1) = 457 * 2 ^ 185 := by
    rw [mul_assoc, h1]
  have hbig : 2 * cardKGold ≤ 457 * 2 ^ 185 := by norm_num
  omega

/-- **The parametric figure with the positional pair summand: `b = 184 − 2r`.** -/
theorem hostile_soundness_formR_pair_at_row_budget (r b R M Λ A p8Work : ℕ)
    (hr : 4 ≤ r) (hb : 2 * r + b = 184)
    (hR : R ≤ 2 ^ r) (hM : M ≤ 2 ^ r) (hΛ : Λ ≤ 2 ^ r) (hA : A ≤ 2 ^ r)
    (hp8 : p8Work ≤ p8Majorant R M Λ A + M * (3 * R + 130)) :
    goldilocksHostileFailureBound p8Work
        (ioFailureUnionBound 10 (3 * R) M (Fintype.card Nock.Field.K)) R M
        + (pairWork M Λ : ℚ) / (cardKGold : ℚ)
      < 1 / (2 : ℚ) ^ b := by
  refine hostileBound_add_lt_of_totalWork _ _ _ _ _ ?_
  have h := two_hostileTotalWork_pair_le_of_size (2 ^ r) R M Λ A p8Work hR hM hΛ hA hp8
  have h' := pairSizeWork_lt_cardK r b hr hb
  have : 2 * ((hostileTotalWork p8Work R M + pairWork M Λ) * 2 ^ b)
      ≤ (457 * (2 ^ r * 2 ^ r) + 404 * 2 ^ r + 28) * 2 ^ b := by
    rw [← mul_assoc]; exact Nat.mul_le_mul_right _ h
  omega

theorem hostile_soundness_formR_pair_at_two_pow_31 (R M Λ A p8Work : ℕ)
    (hR : R ≤ 2 ^ 31) (hM : M ≤ 2 ^ 31) (hΛ : Λ ≤ 2 ^ 31) (hA : A ≤ 2 ^ 31)
    (hp8 : p8Work ≤ p8Majorant R M Λ A + M * (3 * R + 130)) :
    goldilocksHostileFailureBound p8Work
        (ioFailureUnionBound 10 (3 * R) M (Fintype.card Nock.Field.K)) R M
        + (pairWork M Λ : ℚ) / (cardKGold : ℚ)
      < 1 / (2 : ℚ) ^ 122 :=
  hostile_soundness_formR_pair_at_row_budget 31 122 R M Λ A p8Work (by norm_num) (by norm_num)
    hR hM hΛ hA hp8

theorem hostile_soundness_formR_pair_at_two_pow_32 (R M Λ A p8Work : ℕ)
    (hR : R ≤ 2 ^ 32) (hM : M ≤ 2 ^ 32) (hΛ : Λ ≤ 2 ^ 32) (hA : A ≤ 2 ^ 32)
    (hp8 : p8Work ≤ p8Majorant R M Λ A + M * (3 * R + 130)) :
    goldilocksHostileFailureBound p8Work
        (ioFailureUnionBound 10 (3 * R) M (Fintype.card Nock.Field.K)) R M
        + (pairWork M Λ : ℚ) / (cardKGold : ℚ)
      < 1 / (2 : ℚ) ^ 120 :=
  hostile_soundness_formR_pair_at_row_budget 32 120 R M Λ A p8Work (by norm_num) (by norm_num)
    hR hM hΛ hA hp8

/-- The positional summand at the paper configuration is below `2^63`. -/
theorem pairWork_at_paper_configuration : pairWork (2 ^ 31) (2 ^ 31) ≤ 2 ^ 63 := by
  unfold pairWork; norm_num

theorem hostile_soundness_at_paper_configuration_pair (p8Work ioWork pw : ℕ)
    (hp8 : p8Work ≤ 2 ^ 60) (hio : ioWork ≤ 16 ^ 65) (hpw : pw ≤ 2 ^ 63) :
    goldilocksHostileFailureBound p8Work ioWork (2 ^ 31) (2 ^ 31) + (pw : ℚ) / (cardKGold : ℚ)
      < 1 / (2 : ℚ) ^ 123 := by
  rw [goldilocksHostileFailureBound_eq]
  have hts := timestampCollisionBound_at_paper_configuration
  have hwr := walkAndTilingBound_at_paper_configuration
  have hinter :
      ((FiniteIO.ioFailureUnionBound 10 (2 ^ 31) (2 ^ 31) cardKGold
          + cardKGold * 2 ^ 31 : ℕ) : ℚ) / (cardKGold : ℚ) ^ 2
      = ((9 : ℚ) * 2 ^ 64 + 2 ^ 33 + 2 ^ 31) / (cardKGold : ℚ) := by
    rw [ioFailureUnionBound_ten]
    have hnat : 36 * 2 ^ 31 * 2 ^ 31 + 4 * 2 ^ 31 = 9 * 2 ^ 64 + 2 ^ 33 := by norm_num
    rw [hnat]
    have hk : (cardKGold : ℚ) ≠ 0 := by norm_num
    field_simp
    ring
  have hmaj :
      ((2 : ℚ) ^ 60 + (2 : ℚ) ^ 65 + (2 : ℚ) ^ 36) / (cardKGold : ℚ)
        + ((16 : ℚ) ^ 65) / (cardKGold : ℚ) ^ 2
        + ((9 : ℚ) * 2 ^ 64 + 2 ^ 33 + 2 ^ 31) / (cardKGold : ℚ)
        + (2 : ℚ) ^ 63 / (cardKGold : ℚ)
        < 1 / (2 : ℚ) ^ 123 := by
    norm_num
  have hp8' : (p8Work : ℚ) ≤ (2 : ℚ) ^ 60 := by exact_mod_cast hp8
  have hts' : (OptimizedHostileTimestamps.timestampCollisionBound (3 * 2 ^ 31) : ℚ)
      ≤ (2 : ℚ) ^ 65 := by exact_mod_cast hts
  have hwr' : (pricedWalkWork (2 ^ 31) (2 ^ 31) : ℚ) ≤ (2 : ℚ) ^ 36 := by
    exact_mod_cast hwr
  have hio' : (ioWork : ℚ) ≤ (16 : ℚ) ^ 65 := by exact_mod_cast hio
  have hpw' : (pw : ℚ) ≤ (2 : ℚ) ^ 63 := by exact_mod_cast hpw
  calc
    (p8Work + OptimizedHostileTimestamps.timestampCollisionBound (3 * 2 ^ 31) +
          pricedWalkWork (2 ^ 31) (2 ^ 31) : ℚ) /
          (cardKGold : ℚ)
        + (ioWork : ℚ) / (cardKGold : ℚ) ^ 2
        + ((FiniteIO.ioFailureUnionBound 10 (2 ^ 31) (2 ^ 31) cardKGold
            + cardKGold * 2 ^ 31 : ℕ) : ℚ) / (cardKGold : ℚ) ^ 2
        + (pw : ℚ) / (cardKGold : ℚ)
        = ((p8Work : ℚ) +
            (OptimizedHostileTimestamps.timestampCollisionBound (3 * 2 ^ 31) : ℚ) +
            (pricedWalkWork (2 ^ 31) (2 ^ 31) : ℚ)) /
            (cardKGold : ℚ)
          + (ioWork : ℚ) / (cardKGold : ℚ) ^ 2
          + ((9 : ℚ) * 2 ^ 64 + 2 ^ 33 + 2 ^ 31) / (cardKGold : ℚ)
          + (pw : ℚ) / (cardKGold : ℚ) := by
            rw [hinter]
    _ ≤ ((2 : ℚ) ^ 60 + (2 : ℚ) ^ 65 + (2 : ℚ) ^ 36) / (cardKGold : ℚ)
          + ((16 : ℚ) ^ 65) / (cardKGold : ℚ) ^ 2
          + ((9 : ℚ) * 2 ^ 64 + 2 ^ 33 + 2 ^ 31) / (cardKGold : ℚ)
          + (2 : ℚ) ^ 63 / (cardKGold : ℚ) := by
            gcongr
    _ < 1 / (2 : ℚ) ^ 123 := hmaj

/-! ### The all-pairs census, worst case: `#pairs ≤ M²`, `Λ_hostile = M` -/

theorem two_hostileTotalWork_allPairs_le_of_size (S R M Λ A p8Work : ℕ)
    (hR : R ≤ S) (hM : M ≤ S) (hΛ : Λ ≤ S) (hA : A ≤ S)
    (hp8 : p8Work ≤ p8Majorant R M Λ A + M * (3 * R + 130)) :
    2 * (hostileTotalWork p8Work R M + allPairWork M Λ)
      ≤ 4 * (S * S * S) + 453 * (S * S) + 404 * S + 28 := by
  have h := two_hostileTotalWork_le_of_size_formR_prePair S R M Λ A p8Work hR hM hΛ hA hp8
  have hp : allPairWork M Λ ≤ S * S * (2 * S) := by
    unfold allPairWork
    exact Nat.mul_le_mul (Nat.mul_le_mul hM hM) (by omega)
  nlinarith

/-- **97 bits at `2^31` rows with the all-pairs summand** (was 122). -/
theorem hostile_soundness_formR_allPairs_at_two_pow_31 (R M Λ A p8Work : ℕ)
    (hR : R ≤ 2 ^ 31) (hM : M ≤ 2 ^ 31) (hΛ : Λ ≤ 2 ^ 31) (hA : A ≤ 2 ^ 31)
    (hp8 : p8Work ≤ p8Majorant R M Λ A + M * (3 * R + 130)) :
    goldilocksHostileFailureBound p8Work
        (ioFailureUnionBound 10 (3 * R) M (Fintype.card Nock.Field.K)) R M
        + (allPairWork M Λ : ℚ) / (cardKGold : ℚ)
      < 1 / (2 : ℚ) ^ 97 := by
  refine hostileBound_add_lt_of_totalWork _ _ _ _ _ ?_
  have h := two_hostileTotalWork_allPairs_le_of_size (2 ^ 31) R M Λ A p8Work hR hM hΛ hA hp8
  have h' : (4 * (2 ^ 31 * 2 ^ 31 * 2 ^ 31) + 453 * (2 ^ 31 * 2 ^ 31) + 404 * 2 ^ 31 + 28)
      * 2 ^ 97 < 2 * cardKGold := by norm_num
  have : 2 * ((hostileTotalWork p8Work R M + allPairWork M Λ) * 2 ^ 97)
      ≤ (4 * (2 ^ 31 * 2 ^ 31 * 2 ^ 31) + 453 * (2 ^ 31 * 2 ^ 31) + 404 * 2 ^ 31 + 28)
        * 2 ^ 97 := by
    rw [← mul_assoc]; exact Nat.mul_le_mul_right _ h
  exact Nat.lt_of_mul_lt_mul_left (lt_of_le_of_lt this h')

/-- **94 bits at `2^32` rows with the all-pairs summand** (was 120). -/
theorem hostile_soundness_formR_allPairs_at_two_pow_32 (R M Λ A p8Work : ℕ)
    (hR : R ≤ 2 ^ 32) (hM : M ≤ 2 ^ 32) (hΛ : Λ ≤ 2 ^ 32) (hA : A ≤ 2 ^ 32)
    (hp8 : p8Work ≤ p8Majorant R M Λ A + M * (3 * R + 130)) :
    goldilocksHostileFailureBound p8Work
        (ioFailureUnionBound 10 (3 * R) M (Fintype.card Nock.Field.K)) R M
        + (allPairWork M Λ : ℚ) / (cardKGold : ℚ)
      < 1 / (2 : ℚ) ^ 94 := by
  refine hostileBound_add_lt_of_totalWork _ _ _ _ _ ?_
  have h := two_hostileTotalWork_allPairs_le_of_size (2 ^ 32) R M Λ A p8Work hR hM hΛ hA hp8
  have h' : (4 * (2 ^ 32 * 2 ^ 32 * 2 ^ 32) + 453 * (2 ^ 32 * 2 ^ 32) + 404 * 2 ^ 32 + 28)
      * 2 ^ 94 < 2 * cardKGold := by norm_num
  have : 2 * ((hostileTotalWork p8Work R M + allPairWork M Λ) * 2 ^ 94)
      ≤ (4 * (2 ^ 32 * 2 ^ 32 * 2 ^ 32) + 453 * (2 ^ 32 * 2 ^ 32) + 404 * 2 ^ 32 + 28)
        * 2 ^ 94 := by
    rw [← mul_assoc]; exact Nat.mul_le_mul_right _ h
  exact Nat.lt_of_mul_lt_mul_left (lt_of_le_of_lt this h')

/-- **Floor**: the all-pairs summand ALONE is above `2^-98` at `M = Λ = 2^31`, so 97 is the
figure, not a ceiling artefact. -/
theorem allPairs_floor_at_two_pow_31 :
    1 / (2 : ℚ) ^ 98 < (allPairWork (2 ^ 31) (2 ^ 31) : ℚ) / (cardKGold : ℚ) := by
  unfold allPairWork
  rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
  norm_num

/-- **Floor**: above `2^-95` at `M = Λ = 2^32`. -/
theorem allPairs_floor_at_two_pow_32 :
    1 / (2 : ℚ) ^ 95 < (allPairWork (2 ^ 32) (2 ^ 32) : ℚ) / (cardKGold : ℚ) := by
  unfold allPairWork
  rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
  norm_num

end Nock.NockVMROM.Thm54.PreSeedCensusFigures
