/-
  Nock/NockVMROM/Thm54/TraceGen/GenFibConfigGoldilocks.lean

  Goldilocks carrier for the Peano-fib program, same shape
  as `GenMatmulConfigGoldilocks.lean`: `F = Field.Fp`, `K = Field.K`,
  `seedZ = φ goldilocksSeedBase` (order `2^32`), execution orbit `2^16`.
-/
import Nock.Field
import Nock.Framework.Thm54.OrbitDomain
import Nock.NockVMROM.Thm54.CoordinateBasis
import Nock.NockVMROM.Thm54.Execution
import Nock.NockVMROM.Thm54.ExtensionField
import Nock.NockVMROM.Thm54.GoldilocksOrbit
import Nock.NockVMROM.Thm54.TraceGen.GenFibSize
import Mathlib.FieldTheory.Finite.GaloisField

namespace Nock.NockVMROM.Thm54.TraceGen.FibConfigGoldilocks

open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.GoldilocksOrbit
open Nock.Framework.Thm54

abbrev F : Type := Field.Fp
abbrev K : Type := Field.K

instance : CharP K (ringChar K) := ringChar.charP K

noncomputable abbrev φ : F →+* K := algebraMap F K
theorem φ_injective : Function.Injective φ := RingHom.injective φ

theorem finrank_cubic : Module.finrank F K = 3 :=
  GaloisField.finrank Field.p (by norm_num)

noncomputable def basis : Module.Basis (Fin 3) F K :=
  stdCoordBasis F K 3 finrank_cubic

noncomputable def executionOrbit : OrbitDomain K :=
  goldilocksExecutionOrbit 16 (by norm_num) (by norm_num)

noncomputable def packageOrbit : StrictOrbitDomain F 3 16 :=
  goldilocksStrictOrbit 16 (by norm_num) (by norm_num)

theorem executionOrbit_h : executionOrbit.h = 16 := rfl

theorem executionOrbit_order :
    orderOf executionOrbit.ω = 2 ^ 16 :=
  goldilocksExecutionGenerator_order 16 (by norm_num)

theorem packageOrbit_order :
    orderOf packageOrbit.ω = 3 * 2 ^ 16 :=
  goldilocksStrictGenerator_order 16 (by norm_num)

theorem horb : 1 ≤ executionOrbit.h := by
  norm_num [executionOrbit, goldilocksExecutionOrbit]

theorem hcap : 2 ^ executionOrbit.h ≤ 2 ^ (16 : ℕ) := by
  simp [executionOrbit_h]

noncomputable section

def seedZ : K := φ goldilocksSeedBase
def alphaA : K := executionOrbit.ω

theorem seedZ_ne_zero : seedZ ≠ 0 := by
  intro h
  exact goldilocksSeedBase_ne_zero (φ_injective (by simpa [seedZ] using h))

theorem seedZ_order : orderOf seedZ = 2 ^ 32 := by
  have h := orderOf_injective φ.toMonoidHom φ_injective goldilocksSeedBase
  rw [goldilocksSeedBase_order] at h
  simpa [seedZ] using h

theorem seedZ_order_gt (Λ : ℕ) (hΛ : Λ < 2 ^ 32) : Λ < orderOf seedZ := by
  rw [seedZ_order]; exact hΛ

theorem alphaA_order : orderOf alphaA = 2 ^ 16 :=
  executionOrbit_order

theorem alphaA_ne_zero : alphaA ≠ 0 := by
  intro h
  have hpow := pow_orderOf_eq_one alphaA
  rw [alphaA_order, h, zero_pow (by norm_num : (2 ^ 16 : ℕ) ≠ 0)] at hpow
  exact one_ne_zero (hpow.symm)

theorem ringChar_K : ringChar K = Field.p := by
  rw [← Algebra.ringChar_eq F K, ZMod.ringChar_zmod_n]

theorem two_ne_zero : (2 : K) ≠ 0 := by
  have h2 : 2 < Field.p := by
    simp only [Field.p]; norm_num
  exact CharP.cast_eq_zero_iff K (ringChar K) 2 |>.not.mpr (by
    rw [ringChar_K]
    exact Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) h2)

theorem hq : 11 < Field.p := by
  simp only [Field.p]; norm_num

theorem hchar : Field.p = ringChar K :=
  ringChar_K.symm

/-- Compute rows of the compiled n = 4 tree. -/
theorem fib_compute_rows : (fibTree (K := K)).size = 33 :=
  fibTree_size

end

#print axioms Nock.NockVMROM.Thm54.TraceGen.FibConfigGoldilocks.seedZ_order
#print axioms Nock.NockVMROM.Thm54.TraceGen.FibConfigGoldilocks.fib_compute_rows

end Nock.NockVMROM.Thm54.TraceGen.FibConfigGoldilocks
