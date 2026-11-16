/-
  Nock/RedTeam/Batch291Thm54P5FieldChoice.lean

  The 2×2 matmul generator is hard-committed to
  `F = ZMod 65537`, `K = GaloisField 65537 3`.  `nockCompiles_p64`'s residual
  `packageOrbit : StrictOrbitDomain F 3 hOrb` wants a base-field element of
  exact order `e · 2^h = 3 · 2^hOrb`.  That order does not divide `|𝔽_65537^*| = 2^16`, nor
  `|K^*|`.  This batch compiles the obstruction and stops: it does not invent
  an orbit and it does not retarget the matmul.

  Positive control: the four residuals discharge at `DotConfig769`, and
  `Batch289.b289_nockCompiles_literal` is already the fully-concrete §1
  instance at Tier A (not at matmul).

  Candidate that would host *both* the strict RAP orbit and the 30936-row
  forest: Goldilocks `p = 2^64 − 2^32 + 1`.  769 cannot:
  `v₂(p−1) = v₂(|K|−1) = 8`, and `401 > 2^8`, `30936 > 2^8`.
-/
import Nock.Field
import Nock.NockVMROM.Thm54.CoordinateBasis
import Nock.NockVMROM.Thm54.ExtensionField
import Nock.NockVMROM.Thm54.GoldilocksOrbit
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulConfig
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesBounded
import Nock.NockVMROM.Thm54.TraceGen.GenTierAConfig769
import Nock.NockVMROM.Thm54.TraceGen.GenTierAInputsPrep
import Nock.RedTeam.Batch289Thm54P64SeedConcretization
import Mathlib.FieldTheory.Finite.Basic
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Nock.RedTeam.Batch291

open Nock
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.BuildableAxisWitness
open Nock.RedTeam
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.Framework.Thm54

/-! ## 1. The matmul fixture is `ZMod 65537`. -/

abbrev MF := TraceGen.MatmulConfig65537.F
abbrev MK := TraceGen.MatmulConfig65537.K

theorem b291_matmul_is_65537 : MF = ZMod 65537 ∧ MK = GaloisField 65537 3 :=
  ⟨rfl, rfl⟩

theorem b291_matmul_finrank : Module.finrank MF MK = 3 :=
  TraceGen.MatmulConfig65537.finrank_cubic

/-- `bas` discharges at 65537: the cubic has a 3-element `F`-basis. -/
noncomputable def b291_matmul_basis : Module.Basis (Fin 3) MF MK :=
  stdCoordBasis MF MK 3 b291_matmul_finrank

theorem b291_matmul_executionOrbit_order :
    orderOf TraceGen.MatmulConfig65537.executionOrbit.ω = 2 ^ 16 := by
  simpa [TraceGen.MatmulConfig65537.executionOrbit] using
    TraceGen.MatmulConfig65537.omega_order

theorem b291_matmul_row_counts :
    (TraceGen.MatmulConfig65537.exec
        TraceGen.MatmulConfig65537.seedZ
        TraceGen.MatmulConfig65537.alphaA).computeRows.length = 401 ∧
      (TraceGen.MatmulConfig65537.exec
        TraceGen.MatmulConfig65537.seedZ
        TraceGen.MatmulConfig65537.alphaA).memoryRows.length = 30936 :=
  TraceGen.MatmulConfig65537.exec_row_counts

theorem b291_matmul_hmempos (z α : MK) :
    TraceGen.MatmulConfig65537.memoryForest z α ≠ [] :=
  TraceGen.MatmulConfig65537.memoryForest_nonempty z α

theorem b291_matmul_hcard_arith :
    28 * 30936 * 30936 + 4 * 30936 < 65537 ^ 3 := by
  norm_num

/-! ## 2. `packageOrbit` cannot inhabit `ZMod 65537` -/

theorem b291_three_not_dvd_65536 : ¬ 3 ∣ (65537 - 1 : ℕ) := by
  norm_num

theorem b291_three_mul_two_pow_not_dvd (h : ℕ) :
    ¬ 3 * 2 ^ h ∣ (65537 - 1 : ℕ) := by
  intro hdvd
  exact b291_three_not_dvd_65536 (dvd_trans ⟨2 ^ h, rfl⟩ hdvd)

theorem b291_no_order_three_mul_two_pow {h : ℕ} (ω : ZMod 65537) :
    orderOf ω ≠ 3 * 2 ^ h := by
  intro heq
  have hpos : 0 < 3 * 2 ^ h :=
    Nat.mul_pos (by norm_num) (Nat.two_pow_pos h)
  by_cases h0 : ω = 0
  · have hpow := pow_orderOf_eq_one ω
    rw [heq, h0, zero_pow (Nat.pos_iff_ne_zero.mp hpos)] at hpow
    exact zero_ne_one hpow
  · have hpow := FiniteField.pow_card_sub_one_eq_one ω h0
    have hdvd := orderOf_dvd_of_pow_eq_one hpow
    rw [heq, ZMod.card] at hdvd
    exact b291_three_mul_two_pow_not_dvd h hdvd

/-- **The finding.**  No `StrictOrbitDomain (ZMod 65537) 3 h` exists. -/
theorem b291_no_strictOrbit (h : ℕ) :
    StrictOrbitDomain (ZMod 65537) 3 h → False := by
  intro o
  exact b291_no_order_three_mul_two_pow o.ω o.order_ω

/-- The cubic table field is no escape: `3 ∤ |K| − 1` either. -/
theorem b291_three_not_dvd_cubic_units : ¬ 3 ∣ (65537 ^ 3 - 1 : ℕ) := by
  norm_num

noncomputable instance : Fintype MK := Fintype.ofFinite _

theorem b291_card_MK : Fintype.card MK = 65537 ^ 3 := by
  rw [Fintype.card_eq_nat_card]
  exact GaloisField.card 65537 3 (by norm_num)

theorem b291_no_order_three_mul_two_pow_cubic {h : ℕ} (ω : MK) :
    orderOf ω ≠ 3 * 2 ^ h := by
  intro heq
  have hpos : 0 < 3 * 2 ^ h :=
    Nat.mul_pos (by norm_num) (Nat.two_pow_pos h)
  by_cases h0 : ω = 0
  · have hpow := pow_orderOf_eq_one ω
    rw [heq, h0, zero_pow (Nat.pos_iff_ne_zero.mp hpos)] at hpow
    exact zero_ne_one hpow
  · have hpow := FiniteField.pow_card_sub_one_eq_one ω h0
    have hdvd := orderOf_dvd_of_pow_eq_one hpow
    rw [heq, b291_card_MK] at hdvd
    exact b291_three_not_dvd_cubic_units (dvd_trans ⟨2 ^ h, rfl⟩ hdvd)

/-! ## 3. 769 hosts `packageOrbit` but cannot host the matmul forest. -/

theorem b291_769_strict_dvd : 3 * 2 ^ 8 ∣ (769 - 1 : ℕ) := by
  norm_num

theorem b291_769_strictOrbit_order :
    orderOf TraceGen.DotConfig769.strictOrbit.ω = 3 * 2 ^ 8 := by
  simpa [TraceGen.DotConfig769.strictOrbit] using
    TraceGen.DotConfig769.strictOmega_order

theorem b291_769_finrank :
    Module.finrank TraceGen.DotConfig769.F TraceGen.DotConfig769.K = 3 :=
  TraceGen.DotConfig769.finrank_cubic

/-- Compute 401 and memory 30936 both exceed the 769 2-power orbit `2^8 = 256`. -/
theorem b291_769_cannot_host_matmul_rows :
    ¬ 401 ≤ 2 ^ 8 ∧ ¬ 30936 ≤ 2 ^ 8 := by
  constructor <;> norm_num

theorem b291_two_pow_9_not_dvd_768 : ¬ 2 ^ 9 ∣ (769 - 1 : ℕ) := by
  norm_num

theorem b291_two_pow_9_not_dvd_cubic_769 : ¬ 2 ^ 9 ∣ (769 ^ 3 - 1 : ℕ) := by
  norm_num

/-! ## 4. Goldilocks hosts both constraints -/

theorem b291_goldilocks_strict_dvd_16 :
    3 * 2 ^ 16 ∣ Field.p - 1 :=
  GoldilocksOrbit.three_mul_two_pow_dvd_p_sub_one 16 (by norm_num)

theorem b291_goldilocks_hosts_matmul_rows :
    401 ≤ 2 ^ 16 ∧ 30936 ≤ 2 ^ 16 := by
  constructor <;> norm_num

/-- A Goldilocks strict RAP orbit of the height the matmul execution orbit uses. -/
noncomputable def b291_goldilocks_packageOrbit :
    StrictOrbitDomain Field.Fp 3 16 :=
  GoldilocksOrbit.goldilocksStrictOrbit 16 (by norm_num) (by norm_num)

theorem b291_goldilocks_packageOrbit_order :
    orderOf b291_goldilocks_packageOrbit.ω = 3 * 2 ^ 16 :=
  GoldilocksOrbit.goldilocksStrictGenerator_order 16 (by norm_num)

/-! ## 5. Fallback: §1 already instantiates at Tier A / 769, not at matmul. -/

abbrev DK := TraceGen.DotConfig769.K
abbrev DF := TraceGen.DotConfig769.F

local instance charRingDK : CharP DK (ringChar DK) := ringChar.charP DK
noncomputable local instance : Fintype DK := Fintype.ofFinite _
noncomputable local instance : DecidableEq DK := Classical.decEq _




noncomputable def b291_nockCompiles_at_tierA :=
  Batch289.b289_nockCompiles_literal

end Nock.RedTeam.Batch291

#print axioms Nock.RedTeam.Batch291.b291_three_not_dvd_65536
#print axioms Nock.RedTeam.Batch291.b291_no_strictOrbit
#print axioms Nock.RedTeam.Batch291.b291_no_order_three_mul_two_pow_cubic
#print axioms Nock.RedTeam.Batch291.b291_matmul_hcard_arith
#print axioms Nock.RedTeam.Batch291.b291_769_cannot_host_matmul_rows
#print axioms Nock.RedTeam.Batch291.b291_goldilocks_strict_dvd_16
#print axioms Nock.RedTeam.Batch291.b291_goldilocks_packageOrbit_order
#print axioms Nock.RedTeam.Batch291.b291_nockCompiles_at_tierA
