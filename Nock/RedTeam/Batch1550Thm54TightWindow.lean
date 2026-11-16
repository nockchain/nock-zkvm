/-
  Nock/RedTeam/Batch1550Thm54TightWindow.lean

  **Receipts for the tight window.**

  * §A axioms of `TightWindow` (`leafBound_ge_tower`, `hLp_hp64_exclude`,
    `lowOrderRootSeeds_card_le_divisors`, `hLambdaK_of_hΛp`, `hLambdaK*_goldilocks`, `p8WorkEvK_le`);
  * §B the 122 / 120 figures with `p8WorkEvK` in place of `p8WorkEv` (same `numerator_ev`, since
    `p8WorkEvK ≤ p8WorkEv`);
  * §C negative controls: `hLambdaK` is FALSE at a window beyond the field, `p8WorkEvK` is STRICTLY
    below `p8WorkEv` at a concrete point (so the repricing is not the identity), and the tower
    receipt is instantiated at `k = 64`.
-/
import Nock.NockVMROM.Thm54.TightWindow
import Nock.RedTeam.Batch1040Thm54EventFirstFigures

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch1550

open Nock.NockVMROM.Thm54
open Nock Nock.Walk Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.TightWindow
open Nock.NockVMROM.Thm54.RealProgramSoundness
open Nock.NockVMROM.Thm54.GoldilocksParameters
open Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.P8EventEv
open Nock.RedTeam.Batch1040

/-! ## §B Figures at the repriced slot -/

theorem hostile_soundness_evK_at_two_pow_31 (q R M Λ p8Work : ℕ)
    (hR : R ≤ 2 ^ 31) (hM : M ≤ 2 ^ 31) (hΛ : Λ ≤ 2 ^ 31)
    (hp8 : p8Work ≤ p8WorkEvK q R M Λ + M * (3 * R + 130) +
      M * (2 * (M ⊔ Λ) - 1) + (2 * (M ⊔ Λ) - 1) + 1) :
    goldilocksHostileFailureBound p8Work
        (ioFailureUnionBound 10 (3 * R) M (Fintype.card Nock.Field.K)) R M
      < 1 / (2 : ℚ) ^ 122 :=
  hostile_soundness_ev_at_two_pow_31 R M Λ p8Work hR hM hΛ
    (hp8.trans (by have := p8WorkEvK_le q R M Λ; omega))

/-- **120 bits at `2^32` rows**, same. -/
theorem hostile_soundness_evK_at_two_pow_32 (q R M Λ p8Work : ℕ)
    (hR : R ≤ 2 ^ 32) (hM : M ≤ 2 ^ 32) (hΛ : Λ ≤ 2 ^ 32)
    (hp8 : p8Work ≤ p8WorkEvK q R M Λ + M * (3 * R + 130) +
      M * (2 * (M ⊔ Λ) - 1) + (2 * (M ⊔ Λ) - 1) + 1) :
    goldilocksHostileFailureBound p8Work
        (ioFailureUnionBound 10 (3 * R) M (Fintype.card Nock.Field.K)) R M
      < 1 / (2 : ℚ) ^ 120 :=
  hostile_soundness_ev_at_two_pow_32 R M Λ p8Work hR hM hΛ
    (hp8.trans (by have := p8WorkEvK_le q R M Λ; omega))

/-- At the Goldilocks cube `q = p³ − 1`. -/
theorem hostile_soundness_evK_122_goldilocks (R M Λ p8Work : ℕ)
    (hR : R ≤ 2 ^ 31) (hM : M ≤ 2 ^ 31) (hΛ : Λ ≤ 2 ^ 31)
    (hp8 : p8Work ≤ p8WorkEvK (pG ^ 3 - 1) R M Λ + M * (3 * R + 130) +
      M * (2 * (M ⊔ Λ) - 1) + (2 * (M ⊔ Λ) - 1) + 1) :
    goldilocksHostileFailureBound p8Work
        (ioFailureUnionBound 10 (3 * R) M (Fintype.card Nock.Field.K)) R M
      < 1 / (2 : ℚ) ^ 122 :=
  hostile_soundness_evK_at_two_pow_31 _ R M Λ p8Work hR hM hΛ hp8

/-! ## §C Negative controls -/

/-- `hΛK` is not vacuous-true: a window past the field fails it (`p = 5`, `e = 1`, `Λ = 10`). -/
theorem hLambdaK_fails_beyond_field : ¬ hLambdaK 5 1 0 10 := by
  unfold hLambdaK; decide

/-- The repricing is strictly below the old slot at a concrete point (`q = 4`, `Λ = 10`:
`1 + 2 + 4 = 7 < 55`). -/
theorem p8WorkEvK_strict : p8WorkEvK 4 0 0 10 < p8WorkEv 0 0 10 := by
  unfold p8WorkEvK p8WorkEv SizeWindowCounting.sizeWindowRootBound axisUniformWorkload
  decide

/-- The old hypotheses give `hΛK` at a concrete point (`p = 29`, `R = 1`, `Λ = 2`). -/
theorem hLambdaK_of_hΛp_concrete : hLambdaK 29 3 1 2 :=
  hLambdaK_of_hΛp (by norm_num) (by norm_num) (by norm_num)

/-- The tower receipt at `k = 64`: `hΛp` with any `p < 2^64` is refuted (`Field := ZMod 3`). -/
theorem tower_excludes_hp64 (p : ℕ)
    (h : programLeafBound (airReorder (romTree (K := ZMod 3) (evalRom_zero 64))) < p) :
    ¬ p < 2 ^ 64 :=
  hLp_hp64_exclude 64 p le_rfl (evalRom_zero 64) h

end Nock.RedTeam.Batch1550

#print axioms Nock.NockVMROM.Thm54.TightWindow.leafBound_ge_tower
#print axioms Nock.NockVMROM.Thm54.TightWindow.hLp_hp64_exclude
#print axioms Nock.NockVMROM.Thm54.TightWindow.lowOrderRootSeeds_card_le_divisors
#print axioms Nock.NockVMROM.Thm54.TightWindow.hLambdaK_of_hΛp
#print axioms Nock.NockVMROM.Thm54.TightWindow.hLambdaK_of_hΛp_pow
#print axioms Nock.NockVMROM.Thm54.TightWindow.hLambdaK6_goldilocks
#print axioms Nock.NockVMROM.Thm54.TightWindow.hLambdaK3_goldilocks
#print axioms Nock.NockVMROM.Thm54.TightWindow.hLambdaK3_goldilocks_hΛK
#print axioms Nock.NockVMROM.Thm54.TightWindow.hLambdaK6_goldilocks_hΛK
#print axioms Nock.NockVMROM.Thm54.TightWindow.p8WorkEvK_le
#print axioms Nock.RedTeam.Batch1550.hostile_soundness_evK_at_two_pow_31
#print axioms Nock.RedTeam.Batch1550.hostile_soundness_evK_at_two_pow_32
#print axioms Nock.RedTeam.Batch1550.hostile_soundness_evK_122_goldilocks
#print axioms Nock.RedTeam.Batch1550.hLambdaK_fails_beyond_field
#print axioms Nock.RedTeam.Batch1550.p8WorkEvK_strict
#print axioms Nock.RedTeam.Batch1550.hLambdaK_of_hΛp_concrete
#print axioms Nock.RedTeam.Batch1550.tower_excludes_hp64
