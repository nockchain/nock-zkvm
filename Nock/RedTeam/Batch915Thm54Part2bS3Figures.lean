/-
  Nock/RedTeam/Batch915Thm54Part2bS3Figures.lean

  Nothing consumes this.

  S3 (the pre-`z` collision census of the built skeleton, `hbind`'s `hfaith` / `hwin` / `hke` /
  `hcondE`) has the compiled shape `PreSeedCensus.pairBadSeeds (window3 M Λ) pairs` with
  `pairBadSeeds_card_le : card ≤ |pairs| · (2·window3 − 1)` at every `(Qc, Qm)` (no premise) and
  `window3 M Λ = M + max M Λ ≤ 2S` (`ComputedWindow.window3_le_two_mul`).  Under served decomposition
  the pairs per compute row are the OP5 equality-operand pair, `formulaCons`, `tailCons` (and possibly a
  branch tail): `k ≤ 3` (or `4`) per row, `≤ k·N` in all.  The prose figure `463S²+402S+28` of the wiped
  `s3-scope` scratch is NOT reproduced here; this receipt brackets it from above: 122 / 120 hold up to
  `k = 6`, and 123 at the paper configuration holds with an S3 ceiling of `2^66` (`k ≤ 4`) and fails at `2^67`.
-/
import Nock.RedTeam.Batch881Thm54Part2aFamIOAtQD
import Nock.RedTeam.Batch818Thm54H13ConsumeFigures

namespace Nock.RedTeam.Batch915

open Nock.RedTeam.Batch881 (Crit)
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.GoldilocksParameters
open Nock.NockVMROM.Thm54.OptimizedStrictPackage

/-- Baseline (2a tip): `457S²+404S+28` → 122 / 120 (re-checked). -/
theorem base_122 : Crit 457 404 28 31 122 := by unfold Crit; norm_num
theorem base_120 : Crit 457 404 28 32 120 := by unfold Crit; norm_num

/-- S3 additive, `k = 1` pair per row: `465S²+402S+28` → 122 / 120. -/
theorem s3_k1_122 : Crit 465 402 28 31 122 := by unfold Crit; norm_num
theorem s3_k1_120 : Crit 465 402 28 32 120 := by unfold Crit; norm_num

/-- S3 additive, `k = 3` pairs per row (served decomposition): `481S²+398S+28` → 122 / 120. -/
theorem s3_k3_122 : Crit 481 398 28 31 122 := by unfold Crit; norm_num
theorem s3_k3_120 : Crit 481 398 28 32 120 := by unfold Crit; norm_num

/-- S3 additive, `k = 4` pairs per row: `489S²+396S+28` → 122 / 120. -/
theorem s3_k4_122 : Crit 489 396 28 31 122 := by unfold Crit; norm_num
theorem s3_k4_120 : Crit 489 396 28 32 120 := by unfold Crit; norm_num

/-- The ceiling: `k = 7` (`513S²`) is PAST the `S²` ceiling 511 at `r = 31` / 122 bits. -/
theorem s3_k7_not_122 : ¬ Crit 513 390 28 31 122 := by unfold Crit; norm_num
/-- `k = 6` (`505S²+392S+28`) still holds. -/
theorem s3_k6_122 : Crit 505 392 28 31 122 := by unfold Crit; norm_num

/-- The S3 term at the paper configuration `N = M = Λ = 2^31`, `k = 4` pairs per row, is below
`2^66`. -/
theorem s3_paper_ceiling :
    4 * 2 ^ 31 * (2 * (2 ^ 31 + max (2 ^ 31) (2 ^ 31)) - 1) < 2 ^ 66 := by norm_num

theorem hostile_soundness_S3_at_paper_configuration (p8Work ioWork pw s3 : ℕ)
    (hp8 : p8Work ≤ 2 ^ 60) (hio : ioWork ≤ 16 ^ 65) (hpw : pw ≤ 2 ^ 63) (hs3 : s3 ≤ 2 ^ 66) :
    goldilocksHostileFailureBound (p8Work + (pw + s3)) ioWork (2 ^ 31) (2 ^ 31)
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
      ((2 : ℚ) ^ 60 + (2 : ℚ) ^ 63 + (2 : ℚ) ^ 66 + (2 : ℚ) ^ 65 + (2 : ℚ) ^ 36) / (cardKGold : ℚ)
        + ((16 : ℚ) ^ 65) / (cardKGold : ℚ) ^ 2
        + ((9 : ℚ) * 2 ^ 64 + 2 ^ 33 + 2 ^ 31) / (cardKGold : ℚ)
        < 1 / (2 : ℚ) ^ 123 := by
    norm_num
  have hp8' : (p8Work : ℚ) ≤ (2 : ℚ) ^ 60 := by exact_mod_cast hp8
  have hpw' : (pw : ℚ) ≤ (2 : ℚ) ^ 63 := by exact_mod_cast hpw
  have hs3' : (s3 : ℚ) ≤ (2 : ℚ) ^ 66 := by exact_mod_cast hs3
  have hts' : (OptimizedHostileTimestamps.timestampCollisionBound (3 * 2 ^ 31) : ℚ)
      ≤ (2 : ℚ) ^ 65 := by exact_mod_cast hts
  have hwr' : (pricedWalkWork (2 ^ 31) (2 ^ 31) : ℚ) ≤ (2 : ℚ) ^ 36 := by
    exact_mod_cast hwr
  have hio' : (ioWork : ℚ) ≤ (16 : ℚ) ^ 65 := by exact_mod_cast hio
  have hsum :
      ((p8Work + (pw + s3) : ℕ) : ℚ) +
        (OptimizedHostileTimestamps.timestampCollisionBound (3 * 2 ^ 31) : ℚ) +
        (pricedWalkWork (2 ^ 31) (2 ^ 31) : ℚ) ≤
      (2 : ℚ) ^ 60 + (2 : ℚ) ^ 63 + (2 : ℚ) ^ 66 + (2 : ℚ) ^ 65 + (2 : ℚ) ^ 36 := by
    have h1 : ((p8Work + (pw + s3) : ℕ) : ℚ) ≤ (2 : ℚ) ^ 60 + (2 : ℚ) ^ 63 + (2 : ℚ) ^ 66 := by
      push_cast; linarith [hp8', hpw', hs3']
    linarith [h1, hts', hwr']
  have hk : (0 : ℚ) < (cardKGold : ℚ) := by norm_num
  calc
    (((p8Work + (pw + s3) : ℕ) : ℚ) +
          (OptimizedHostileTimestamps.timestampCollisionBound (3 * 2 ^ 31) : ℚ) +
          (pricedWalkWork (2 ^ 31) (2 ^ 31) : ℚ)) /
          (cardKGold : ℚ)
        + (ioWork : ℚ) / (cardKGold : ℚ) ^ 2
        + ((FiniteIO.ioFailureUnionBound 10 (2 ^ 31) (2 ^ 31) cardKGold
            + cardKGold * 2 ^ 31 : ℕ) : ℚ) / (cardKGold : ℚ) ^ 2
        = (((p8Work + (pw + s3) : ℕ) : ℚ) +
            (OptimizedHostileTimestamps.timestampCollisionBound (3 * 2 ^ 31) : ℚ) +
            (pricedWalkWork (2 ^ 31) (2 ^ 31) : ℚ)) /
            (cardKGold : ℚ)
          + (ioWork : ℚ) / (cardKGold : ℚ) ^ 2
          + ((9 : ℚ) * 2 ^ 64 + 2 ^ 33 + 2 ^ 31) / (cardKGold : ℚ) := by
            rw [hinter]
    _ ≤ ((2 : ℚ) ^ 60 + (2 : ℚ) ^ 63 + (2 : ℚ) ^ 66 + (2 : ℚ) ^ 65 + (2 : ℚ) ^ 36) / (cardKGold : ℚ)
          + ((16 : ℚ) ^ 65) / (cardKGold : ℚ) ^ 2
          + ((9 : ℚ) * 2 ^ 64 + 2 ^ 33 + 2 ^ 31) / (cardKGold : ℚ) := by
            gcongr
    _ < 1 / (2 : ℚ) ^ 123 := hmaj

/-- The margin: an S3 ceiling of `2^67` (`k ≥ 5` pairs per row at `window3 = 2S`) is PAST the
paper-configuration budget — the same numeral sum with `2^67` in place of `2^66` is NOT below
`1/2^123`. -/
theorem s3_paper_ceiling_2_67_fails :
    ¬ (((2 : ℚ) ^ 60 + (2 : ℚ) ^ 63 + (2 : ℚ) ^ 67 + (2 : ℚ) ^ 65 + (2 : ℚ) ^ 36) / (cardKGold : ℚ)
        + ((16 : ℚ) ^ 65) / (cardKGold : ℚ) ^ 2
        + ((9 : ℚ) * 2 ^ 64 + 2 ^ 33 + 2 ^ 31) / (cardKGold : ℚ)
        < 1 / (2 : ℚ) ^ 123) := by
  norm_num

end Nock.RedTeam.Batch915
