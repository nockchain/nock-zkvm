/-
  Nock/RedTeam/Batch1720Thm54TowerSeedWindow.lean

  **Receipts.**

  * §A axioms of `GenTowerSeed` (`{propext, Classical.choice, Quot.sound}`; the generator-level
    theorems do not list `Nock.Field.goldilocks_prime`: they use only the numeral `pG` and the proved
    divisor counts);
  * §B negative controls: `hΛK` is refuted at `Λ = p⁶` (the window must be a genuine bound); two
    distinct tower seeds are distinct elements (the coordinates are not collapsed).
-/
import Nock.NockVMROM.Thm54.TraceGen.GenTowerSeed
import Nock.Primality.GoldilocksCore

set_option autoImplicit false

namespace Nock.RedTeam.Batch1720

open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.TightWindow
open Nock.NockVMROM.Thm54.TraceGen.GenTowerSeed

#print axioms encC_towerSeed
#print axioms ofFP_encC_towerSeed
#print axioms renderNode_s0_f_t_tower
#print axioms renderNode_s9_f_th_tower
#print axioms hLambdaK_mono
#print axioms hLambdaK_generator
#print axioms towerSeedBudget_lt_card
#print axioms towerSeedBudget_generator

/-- NEGATIVE: `hΛK` is not vacuous: the window `Λ = p⁶` is refuted. -/
theorem hLambdaK_refuted_at_card : ¬ hLambdaK pG 6 0 (pG ^ 6) := by
  have h : 0 < pG ^ 6 := by unfold pG; positivity
  unfold hLambdaK
  intro hh
  omega

/-- NEGATIVE: distinct coordinates give distinct tower seeds. -/
theorem towerSeed_ne {K : Type} [Field K] (δ : K) [Fact (¬ IsSquare δ)] {a b : K} (h : a ≠ b) :
    towerSeed δ a 0 ≠ towerSeed δ b 0 := by
  intro hh
  have := towerSeed_injective δ (a₁ := (a, 0)) (a₂ := (b, 0)) hh
  exact h (congrArg Prod.fst this)

/-! ## The leaf prime module -/

#print axioms Nock.Primality.goldilocks_prime_nat

/-- The numeral-form leaf theorem and `goldilocks_prime_thm` are one proposition. -/
theorem prime_nat_eq_thm :
    Nock.Primality.goldilocks_prime_nat = Nock.Primality.goldilocks_prime_thm := rfl

end Nock.RedTeam.Batch1720
