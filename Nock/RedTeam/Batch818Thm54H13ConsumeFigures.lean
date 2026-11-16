/-
  Nock/RedTeam/Batch818Thm54H13ConsumeFigures.lean

  * Option W (summand inside the `p8Work` slot): doubled numerator `457S² + 404S + 28` at the row
    budget (`two_hostileTotalWork_W_le_of_size`), **122** at `2^31` / **120** at `2^32`
    (`hostile_soundness_W_at_two_pow_31/_32`), hostile-majorant form `457S² + 150S + 288`
    (`two_hostileTotalWork_W_le_p8WorkHostile`), **123** at the paper configuration with the pair
    term `≤ 2^63` riding beside the `2^60` ceiling (`hostile_soundness_W_at_paper_configuration`);
    `pricedWalkWork` and `walkAndTilingBound_at_paper_configuration ≤ 2^36` are untouched.
  * Option P (summand in `pricedWalkWork`): the paper-configuration walk numeral restates to
    `≤ 2^63 + 2^36` (`walkAndPair_paper_P`); the row-budget figures are `PreSeedCensusFigures`'
    `hostile_soundness_formR_pair_at_two_pow_31/_32` at `Λ := M ⊔ Λ`.
-/
import Lean
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.NockVMROM.Thm54.PreZCensusCore
import Nock.NockVMROM.Thm54.PreSeedCensusFigures
import Nock.NockVMROM.Thm54.HostileWorkloadMajorant
import Nock.RedTeam.Batch742Thm54RouteBCensus
import Nock.RedTeam.Batch752Thm54PreZCensusCoreLift
import Nock.RedTeam.Batch747Thm54Gate32ndAuthorization
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

open Lean Elab Command

namespace Nock.RedTeam.Batch818

open Nock
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.PreSeedCensus
open Nock.NockVMROM.Thm54.RealProgramSoundness
open Nock.NockVMROM.Thm54.GoldilocksParameters
open Nock.NockVMROM.Thm54.PreSeedCensusFigures
open Nock.NockVMROM.Thm54.HostileWorkloadMajorant
open Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.SizeWindowCounting
open Nock.Reified
open Nock.NockVMROM.Thm54.OptimizedMemoryCollisionAccounting
open Nock.NockVMROM.Thm54.OptimizedComputeCollisionBound

noncomputable section

/-! ## D. Figures at live -/

theorem p8Majorant_mono_Λ (R M Λ Λ' A : ℕ) (h : Λ ≤ Λ') :
    p8Majorant R M Λ A ≤ p8Majorant R M Λ' A := by
  simp only [p8Majorant]
  have h1 : (3 + 19 * R) * (2 * Λ) ≤ (3 + 19 * R) * (2 * Λ') :=
    Nat.mul_le_mul_left _ (by omega)
  have h2 : Λ * Λ ≤ Λ' * Λ' := Nat.mul_le_mul h h
  omega

/-- **Row budget, Option W (summand inside `p8Work`):** `457S² + 404S + 28`. -/
theorem two_hostileTotalWork_W_le_of_size (S R M Λ A p8Work : ℕ)
    (hR : R ≤ S) (hM : M ≤ S) (hΛ : Λ ≤ S) (hA : A ≤ S)
    (hp8 : p8Work ≤ p8Majorant R M Λ A + M * (3 * R + 130)) :
    2 * hostileTotalWork (p8Work + M * (2 * (M ⊔ Λ) - 1)) R M ≤
      457 * (S * S) + 404 * S + 28 := by
  have hW : hostileTotalWork (p8Work + M * (2 * (M ⊔ Λ) - 1)) R M =
      hostileTotalWork p8Work R M + pairWork M (M ⊔ Λ) := by
    simp only [hostileTotalWork, pairWork]; omega
  rw [hW]
  exact two_hostileTotalWork_pair_le_of_size S R M (M ⊔ Λ) A p8Work hR hM (max_le hM hΛ) hA
    (hp8.trans (Nat.add_le_add_right (p8Majorant_mono_Λ R M Λ (M ⊔ Λ) A (le_max_right _ _)) _))

theorem hostile_soundness_W_at_row_budget (r b R M Λ A p8Work : ℕ)
    (hr : 4 ≤ r) (hb : 2 * r + b = 184)
    (hR : R ≤ 2 ^ r) (hM : M ≤ 2 ^ r) (hΛ : Λ ≤ 2 ^ r) (hA : A ≤ 2 ^ r)
    (hp8 : p8Work ≤ p8Majorant R M Λ A + M * (3 * R + 130)) :
    goldilocksHostileFailureBound (p8Work + M * (2 * (M ⊔ Λ) - 1))
        (ioFailureUnionBound 10 (3 * R) M (Fintype.card Nock.Field.K)) R M
      < 1 / (2 : ℚ) ^ b := by
  rw [hostileBound_at_majorants]
  rw [div_lt_div_iff₀ (by norm_num) (by positivity)]
  have h := two_hostileTotalWork_W_le_of_size (2 ^ r) R M Λ A p8Work hR hM hΛ hA hp8
  have h' := pairSizeWork_lt_cardK r b hr hb
  have hnat : (hostileTotalWork (p8Work + M * (2 * (M ⊔ Λ) - 1)) R M) * 2 ^ b < cardKGold := by
    have : 2 * ((hostileTotalWork (p8Work + M * (2 * (M ⊔ Λ) - 1)) R M) * 2 ^ b)
        ≤ (457 * (2 ^ r * 2 ^ r) + 404 * 2 ^ r + 28) * 2 ^ b := by
      rw [← mul_assoc]; exact Nat.mul_le_mul_right _ h
    omega
  have hq : (((hostileTotalWork (p8Work + M * (2 * (M ⊔ Λ) - 1)) R M) * 2 ^ b : ℕ) : ℚ)
      < ((cardKGold : ℕ) : ℚ) := by exact_mod_cast hnat
  push_cast at hq ⊢
  linarith

/-- **122 at `2^31`, Option W.** -/
theorem hostile_soundness_W_at_two_pow_31 (R M Λ A p8Work : ℕ)
    (hR : R ≤ 2 ^ 31) (hM : M ≤ 2 ^ 31) (hΛ : Λ ≤ 2 ^ 31) (hA : A ≤ 2 ^ 31)
    (hp8 : p8Work ≤ p8Majorant R M Λ A + M * (3 * R + 130)) :
    goldilocksHostileFailureBound (p8Work + M * (2 * (M ⊔ Λ) - 1))
        (ioFailureUnionBound 10 (3 * R) M (Fintype.card Nock.Field.K)) R M
      < 1 / (2 : ℚ) ^ 122 :=
  hostile_soundness_W_at_row_budget 31 122 R M Λ A p8Work (by norm_num) (by norm_num)
    hR hM hΛ hA hp8

/-- **120 at `2^32`, Option W.** -/
theorem hostile_soundness_W_at_two_pow_32 (R M Λ A p8Work : ℕ)
    (hR : R ≤ 2 ^ 32) (hM : M ≤ 2 ^ 32) (hΛ : Λ ≤ 2 ^ 32) (hA : A ≤ 2 ^ 32)
    (hp8 : p8Work ≤ p8Majorant R M Λ A + M * (3 * R + 130)) :
    goldilocksHostileFailureBound (p8Work + M * (2 * (M ⊔ Λ) - 1))
        (ioFailureUnionBound 10 (3 * R) M (Fintype.card Nock.Field.K)) R M
      < 1 / (2 : ℚ) ^ 120 :=
  hostile_soundness_W_at_row_budget 32 120 R M Λ A p8Work (by norm_num) (by norm_num)
    hR hM hΛ hA hp8

/-- **Hostile majorant form:** `453S² + 150S + 288 → 457S² + 150S + 288`
(`two_hostileTotalWork_le_p8WorkHostile` re-proved with the pair summand; `Λ_hostile = M`
there, so `Λg = M ⊔ Λ ≤ S` either way). -/
theorem two_hostileTotalWork_W_le_p8WorkHostile (S N M Λ : ℕ)
    (hN : N ≤ S) (hM : M ≤ S) (hΛ : Λ ≤ S) :
    2 * hostileTotalWork (p8WorkHostile N M + M * (2 * (M ⊔ Λ) - 1)) N M
      ≤ 457 * (S * S) + 150 * S + 288 := by
  have h := two_hostileTotalWork_le_p8WorkHostile_prePair S N M hN hM
  have hW : hostileTotalWork (p8WorkHostile N M + M * (2 * (M ⊔ Λ) - 1)) N M =
      hostileTotalWork (p8WorkHostile N M) N M + M * (2 * (M ⊔ Λ) - 1) := by
    simp only [hostileTotalWork]; omega
  have hp : M * (2 * (M ⊔ Λ) - 1) ≤ 2 * (S * S) := by
    have hmax : M ⊔ Λ ≤ S := max_le hM hΛ
    calc M * (2 * (M ⊔ Λ) - 1) ≤ S * (2 * S) := Nat.mul_le_mul hM (by omega)
      _ = 2 * (S * S) := by ring
  rw [hW]
  linarith

/-- The bound is linear in the `p8Work` slot. -/
theorem goldilocksHostileFailureBound_add_p8 (a w ioWork N M : ℕ) :
    goldilocksHostileFailureBound (a + w) ioWork N M =
      goldilocksHostileFailureBound a ioWork N M + (w : ℚ) / (cardKGold : ℚ) := by
  rw [goldilocksHostileFailureBound_eq, goldilocksHostileFailureBound_eq]
  push_cast
  ring

/-- **123 at the paper configuration, Option W**: the pair summand `≤ 2^63` rides in the
`p8Work` slot beside the `2^60` ceiling; `pricedWalkWork` is untouched (still `≤ 2^36`). -/
theorem hostile_soundness_W_at_paper_configuration (p8Work ioWork pw : ℕ)
    (hp8 : p8Work ≤ 2 ^ 60) (hio : ioWork ≤ 16 ^ 65) (hpw : pw ≤ 2 ^ 63) :
    goldilocksHostileFailureBound (p8Work + pw) ioWork (2 ^ 31) (2 ^ 31) < 1 / (2 : ℚ) ^ 123 := by
  rw [goldilocksHostileFailureBound_add_p8]
  exact hostile_soundness_at_paper_configuration_pair p8Work ioWork pw hp8 hio hpw

theorem pairWork_paper_W : pairWork (2 ^ 31) (2 ^ 31 ⊔ 2 ^ 31) ≤ 2 ^ 63 := by
  simp only [pairWork, max_self]; norm_num

/-- Option P's restated walk numeral, for the record: `≤ 2^63 + 2^36`. -/
theorem walkAndPair_paper_P :
    pricedWalkWork (2 ^ 31) (2 ^ 31) + pairWork (2 ^ 31) (2 ^ 31) ≤ 2 ^ 63 + 2 ^ 36 := by
  have h1 := walkAndTilingBound_at_paper_configuration
  have h2 := pairWork_at_paper_configuration
  omega


/-- The joint receipts of the gate exist at live and say what the text cites. -/
theorem joint_cited : (457 * 2 ^ 62 + 404 * 2 ^ 31 + 28) * 2 ^ 122 < 2 * cardKGold ∧
    (457 * 2 ^ 64 + 404 * 2 ^ 32 + 28) * 2 ^ 120 < 2 * cardKGold :=
  ⟨Batch747.joint_122, Batch747.joint_120⟩

end

end Nock.RedTeam.Batch818

#print axioms Nock.RedTeam.Batch818.hostile_soundness_W_at_two_pow_31
#print axioms Nock.RedTeam.Batch818.hostile_soundness_W_at_two_pow_32
#print axioms Nock.RedTeam.Batch818.two_hostileTotalWork_W_le_p8WorkHostile
#print axioms Nock.RedTeam.Batch818.hostile_soundness_W_at_paper_configuration
#print axioms Nock.RedTeam.Batch818.walkAndPair_paper_P
#print axioms Nock.RedTeam.Batch818.joint_cited
