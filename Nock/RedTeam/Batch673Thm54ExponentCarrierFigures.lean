/-
  Nock/RedTeam/Batch673Thm54ExponentCarrierFigures.lean

  **C5 of the THIRTY-FIRST move (lane `exponent-carrier`): the figures at the new IO
  factor.**

  The IO and `intermediate` record RLCs are now over ten slots, so `IORLCCollisionEvent_card_le`'s
  per-pair factor is `m − 1 = 9` (was `8`).

  * `ioFailureUnionBound_ten`: `ioFailureUnionBound 10 n n |𝕂| = |𝕂|·(36n² + 4n)`
    (`GoldilocksParameters.ioFailureUnionBound_ten`).
  * **Doubled numerator `453S² + 404S + 28`** (`two_hostileTotalWork_le_453`): the thirtieth's
    `413S² + 404S + 28` plus `2·((4S)² + (2S)²) = 40S²` (`numerator_ten`, against the CONSUMED
    bound `hostileTotalWork`, whose two IO masses now carry the factor `9`).
  * **122 / 120 hold** (`figure_122`, `figure_120`: `hostile_soundness_formR_at_two_pow_31/_32`
    re-proved at `ioFailureUnionBound 10`); the arithmetic `(453·2^{62} + 404·2^{31} + 28)·2^{122}
    < 2|𝕂|` and its `2^{32}` row (`figure_122_arith`, `figure_120_arith`); tightness
    `453·2^{185} > 2|𝕂|` (`figure_tight`).
  * **123 holds** at the paper configuration (`figure_123`): the inter term at `M = 2^{31}` grows by
    `(9 − 8)·(2^{32})²/|𝕂|² = 2^{64}/|𝕂|²` (`inter_ten_negligible`, `< 2^{−127}`), re-proved inside
    `GoldilocksParameters.hostile_soundness_at_paper_configuration` at `ioFailureUnionBound_ten`.
-/
import Nock.NockVMROM.Thm54.RealProgramSoundness
import Nock.NockVMROM.Thm54.GoldilocksParameters
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesCarrier

set_option autoImplicit false

namespace Nock.RedTeam.Batch673

open Nock
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.RealProgramSoundness
open Nock.NockVMROM.Thm54.GoldilocksParameters
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.FiniteIO

/-- The consumed bound's inter summand reads `ioFailureUnionBound 10` (byte-identical, `rfl`). -/
theorem byte_identical_ten (cardK cardF p8Work ioWork N M : ℕ) :
    optimizedHostileProductionFailureProbabilityBound cardK cardF p8Work ioWork N M =
      (p8Work +
        OptimizedHostileTimestamps.timestampCollisionBound (3 * N) +
        pricedWalkWork N M : ℚ) / cardK +
      (ioWork : ℚ) / cardK ^ 2 +
      ((ioFailureUnionBound 10 M M cardK + cardK * M : ℕ) : ℚ) / cardK ^ 2 :=
  optimizedHostileProductionFailureProbabilityBound_byte_identical cardK cardF p8Work ioWork N M

/-- `ioFailureUnionBound_ten`. -/
theorem ioFailureUnionBound_ten (n cardK : ℕ) :
    ioFailureUnionBound 10 n n cardK = cardK * (36 * n * n + 4 * n) :=
  GoldilocksParameters.ioFailureUnionBound_ten n cardK

/-- The factor is `m − 1`: `8` at nine slots, `9` at ten. -/
theorem rlc_factor : (9 : ℕ) - 1 = 8 ∧ (10 : ℕ) - 1 = 9 := by norm_num

/-- The doubled-numerator identity: the thirtieth's `413S² + 404S + 28` plus the factor-`9`
growth `2·((4S)² + (2S)²) = 40S²`. -/
theorem numerator_ten (S : ℕ) :
    413 * (S * S) + 404 * S + 28 + 2 * ((4 * S) * (4 * S) + (2 * S) * (2 * S)) =
      453 * (S * S) + 404 * S + 28 := by ring

/-- **The doubled numerator of the consumed bound at uniform size `S`, at the new IO factor.** -/
theorem two_hostileTotalWork_le_453 (S R M Λ A p8Work : ℕ)
    (hR : R ≤ S) (hM : M ≤ S) (hΛ : Λ ≤ S) (hA : A ≤ S)
    (hp8 : p8Work ≤ p8Majorant R M Λ A + M * (3 * R + 130)) :
    2 * hostileTotalWork p8Work R M ≤ 453 * (S * S) + 404 * S + 28 :=
  two_hostileTotalWork_le_of_size_formR_prePair S R M Λ A p8Work hR hM hΛ hA hp8

theorem figure_122_arith : (453 * 2 ^ 62 + 404 * 2 ^ 31 + 28) * 2 ^ 122 < 2 * cardKGold := by
  norm_num [cardKGold]

theorem figure_120_arith : (453 * 2 ^ 64 + 404 * 2 ^ 32 + 28) * 2 ^ 120 < 2 * cardKGold := by
  norm_num [cardKGold]

/-- **122 bits at `2^31` rows**, at `ioFailureUnionBound 10`. -/
theorem figure_122 (R M Λ A p8Work : ℕ)
    (hR : R ≤ 2 ^ 31) (hM : M ≤ 2 ^ 31) (hΛ : Λ ≤ 2 ^ 31) (hA : A ≤ 2 ^ 31)
    (hp8 : p8Work ≤ p8Majorant R M Λ A + M * (3 * R + 130)) :
    goldilocksHostileFailureBound p8Work
        (ioFailureUnionBound 10 (3 * R) M (Fintype.card Nock.Field.K)) R M
      < 1 / (2 : ℚ) ^ 122 :=
  hostile_soundness_formR_at_two_pow_31 R M Λ A p8Work hR hM hΛ hA
    (hp8.trans (Nat.le_add_right _ _))

/-- **120 bits at `2^32` rows**, at `ioFailureUnionBound 10`. -/
theorem figure_120 (R M Λ A p8Work : ℕ)
    (hR : R ≤ 2 ^ 32) (hM : M ≤ 2 ^ 32) (hΛ : Λ ≤ 2 ^ 32) (hA : A ≤ 2 ^ 32)
    (hp8 : p8Work ≤ p8Majorant R M Λ A + M * (3 * R + 130)) :
    goldilocksHostileFailureBound p8Work
        (ioFailureUnionBound 10 (3 * R) M (Fintype.card Nock.Field.K)) R M
      < 1 / (2 : ℚ) ^ 120 :=
  hostile_soundness_formR_at_two_pow_32 R M Λ A p8Work hR hM hΛ hA
    (hp8.trans (Nat.le_add_right _ _))

/-- The figure is tight for this numerator: one more bit fails at every `r`. -/
theorem figure_tight (r b : ℕ) (hb : 2 * r + b = 184) :
    ¬ ((453 * (2 ^ r * 2 ^ r) + 404 * 2 ^ r + 28) * 2 ^ (b + 1) < 2 * cardKGold) :=
  hostileSizeWorkFormR_not_lt_cardK_prePair r b hb

/-- The inter term's growth at the paper configuration is below `2^{−127}`. -/
theorem inter_ten_negligible : ((2 : ℚ) ^ 64) / ((cardKGold : ℚ) ^ 2) < 1 / (2 : ℚ) ^ 127 := by
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  norm_num [cardKGold]

/-- **123 at the paper configuration**, re-proved at `ioFailureUnionBound 10`. -/
theorem figure_123 (p8Work ioWork : ℕ) (hp8 : p8Work ≤ 2 ^ 60) (hio : ioWork ≤ 16 ^ 65) :
    goldilocksHostileFailureBound p8Work ioWork (2 ^ 31) (2 ^ 31) < 1 / (2 : ℚ) ^ 123 :=
  hostile_soundness_at_paper_configuration p8Work ioWork hp8 hio

/-- The honest-side budget, closed form. -/
theorem honest_budget (n cardK : ℕ) :
    RecordCarrier.honestIOBound n n cardK = cardK * (68 * n * n + 8 * n) :=
  RecordCarrier.honestIOBound_eq n cardK

/-- The honest-side arithmetic behind `hcard_of_hF_hK` (no new binder on `nockCompiles`). -/
theorem honest_cubic (k : ℕ) (hk : 2 ≤ k) : 68 * k * k + 8 * k < (3 * k + 1) ^ 3 :=
  TraceGen.hcard_cubic_arith_honest k hk

end Nock.RedTeam.Batch673

#print axioms Nock.RedTeam.Batch673.two_hostileTotalWork_le_453
#print axioms Nock.RedTeam.Batch673.figure_122
#print axioms Nock.RedTeam.Batch673.figure_120
#print axioms Nock.RedTeam.Batch673.figure_123
#print axioms Nock.RedTeam.Batch673.figure_tight
#print axioms Nock.RedTeam.Batch673.inter_ten_negligible
