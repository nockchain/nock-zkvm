import Nock.Field
import Nock.NockVMROM.Thm54.StrictActiveDomains
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

/-!
# Goldilocks strict and execution orbits

For `1 ≤ hRap ≤ 32`, the Goldilocks base field contains a strict cubic RAP generator of exact
order `3 * 2^hRap`.  Independently, `hExec` selects an execution/evaluation generator in the cubic
extension of exact order `2^hExec`, obtained by cubing a strict base-field generator and applying
the injective algebra map.  The two exponents are intentionally distinct parameters.
-/

namespace Nock.NockVMROM.Thm54
namespace GoldilocksOrbit

open Nock
open Nock.Framework.Thm54
open StrictExtension

noncomputable section

/-! ## Goldilocks arithmetic -/

/-- Goldilocks factorization used to select every supported strict cubic orbit. -/
theorem p_sub_one_factorization :
    Field.p - 1 = 2 ^ 32 * (2 ^ 32 - 1) := by
  norm_num [Field.p]

/-- Three divides the Goldilocks unit-group order. -/
theorem three_dvd_p_sub_one : 3 ∣ Field.p - 1 := by
  norm_num [Field.p]

/-- Every `3 * 2^h`, for `h ≤ 32`, divides the Goldilocks unit-group order. -/
theorem three_mul_two_pow_dvd_p_sub_one (h : ℕ) (hle : h ≤ 32) :
    3 * 2 ^ h ∣ Field.p - 1 := by
  rw [p_sub_one_factorization]
  have htwo : 2 ^ h ∣ 2 ^ 32 := Nat.pow_dvd_pow 2 hle
  have hthree : 3 ∣ 2 ^ 32 - 1 := by norm_num
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
    Nat.mul_dvd_mul htwo hthree

/-! ## Named base-field kernels (`orderOf_eq_prime_pow`)

All arithmetic is in `ZMod p`.  The two kernels of `orderOf_eq_prime_pow` are
`x ^ p ^ n ≠ 1` and `x ^ p ^ (n + 1) = 1`.  Nothing here reduces in `GaloisField`. -/

theorem two_ne_zero_fp : (2 : Field.Fp) ≠ 0 := by
  have h2 : 2 < Field.p := by simp only [Field.p]; norm_num
  exact (CharP.cast_eq_zero_iff Field.Fp Field.p 2).not.mpr
    (Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) h2)

theorem seven_ne_zero_fp : (7 : Field.Fp) ≠ 0 := by
  have h7 : 7 < Field.p := by simp only [Field.p]; norm_num
  exact (CharP.cast_eq_zero_iff Field.Fp Field.p 7).not.mpr
    (Nat.not_dvd_of_pos_of_lt (by decide : 0 < 7) h7)

theorem eight_ne_zero_fp : (8 : Field.Fp) ≠ 0 := by
  have h8 : 8 < Field.p := by simp only [Field.p]; norm_num
  exact (CharP.cast_eq_zero_iff Field.Fp Field.p 8).not.mpr
    (Nat.not_dvd_of_pos_of_lt (by decide : 0 < 8) h8)

theorem neg_one_ne_one_fp : (-1 : Field.Fp) ≠ 1 := by
  intro h
  apply two_ne_zero_fp
  apply_fun (fun x => x + 1) at h
  have : (1 + 1 : Field.Fp) = 2 := by norm_num
  rw [this] at h
  simpa using h.symm

/-- `2^64 ≡ 2^32 − 1 (mod p)` because `p = 2^64 − 2^32 + 1`. -/
theorem two_pow_64_mod_p : (2 : Field.Fp) ^ 64 = (2 : Field.Fp) ^ 32 - 1 := by
  have hnat : (2 : ℕ) ^ 64 = Field.p + (2 : ℕ) ^ 32 - 1 := by
    simp only [Field.p]; norm_num
  have hsub : 1 ≤ Field.p + (2 : ℕ) ^ 32 := by
    simp only [Field.p]; norm_num
  change ((2 : ℕ) : Field.Fp) ^ 64 = ((2 : ℕ) : Field.Fp) ^ 32 - 1
  rw [← Nat.cast_pow, hnat, Nat.cast_sub hsub, Nat.cast_add, ZMod.natCast_self,
    zero_add, Nat.cast_pow, Nat.cast_one]

/-- Kernel 1 for `8`: `8^(2^5) = −1 ≠ 1`. -/
theorem eight_pow_32 : (8 : Field.Fp) ^ 32 = -1 := by
  have h8 : (8 : Field.Fp) = (2 : Field.Fp) ^ 3 := by norm_num
  have hsplit : (2 : Field.Fp) ^ 96 = (2 : Field.Fp) ^ 32 * (2 : Field.Fp) ^ 64 :=
    (pow_add (2 : Field.Fp) 32 64).symm
  rw [h8, ← pow_mul]
  change (2 : Field.Fp) ^ 96 = -1
  rw [hsplit, two_pow_64_mod_p]
  have hmul : (2 : Field.Fp) ^ 32 * ((2 : Field.Fp) ^ 32 - 1) =
      (2 : Field.Fp) ^ 64 - (2 : Field.Fp) ^ 32 := by ring
  rw [hmul, two_pow_64_mod_p]
  ring

/-- Kernel 2 for `8`: `8^(2^6) = 1`. -/
theorem eight_pow_64 : (8 : Field.Fp) ^ 64 = 1 := by
  have h : (8 : Field.Fp) ^ 64 = ((8 : Field.Fp) ^ 32) ^ 2 :=
    (pow_mul (8 : Field.Fp) 32 2).symm
  rw [h, eight_pow_32, neg_one_sq]

/-- `orderOf (8 : 𝔽_p) = 64 = 2^6`.  The two kernels are `eight_pow_32` and `eight_pow_64`. -/
theorem eight_order : orderOf (8 : Field.Fp) = 64 := by
  have hnot : ¬ (8 : Field.Fp) ^ (2 ^ 5) = 1 := by
    change ¬ (8 : Field.Fp) ^ 32 = 1
    rw [eight_pow_32]
    exact neg_one_ne_one_fp
  have hfin : (8 : Field.Fp) ^ (2 ^ 6) = 1 := by
    change (8 : Field.Fp) ^ 64 = 1
    exact eight_pow_64
  simpa using (orderOf_eq_prime_pow (p := 2) (n := 5) hnot hfin)

local instance fact_prime_seven : Fact (Nat.Prime 7) := ⟨by decide⟩

theorem p_mod_four : Field.p % 4 = 1 := by
  simp only [Field.p]; norm_num

theorem p_mod_seven : Field.p % 7 = 6 := by
  simp only [Field.p]; norm_num

/-- `7` is a quadratic non-residue mod Goldilocks (`(7/p) = −1`). -/
theorem goldilocks_legendre_seven : legendreSym Field.p (7 : ℤ) = -1 := by
  have hq2 : (7 : ℕ) ≠ 2 := by decide
  have hqr : legendreSym (7 : ℕ) Field.p = legendreSym Field.p (7 : ℕ) :=
    legendreSym.quadratic_reciprocity_one_mod_four (p := Field.p) (q := 7)
      p_mod_four hq2
  have hswap : legendreSym Field.p (7 : ℤ) = legendreSym 7 (Field.p : ℤ) := by
    simpa using hqr.symm
  rw [hswap]
  have hmod : legendreSym 7 (Field.p : ℤ) = legendreSym 7 ((Field.p : ℤ) % 7) :=
    legendreSym.mod 7 (Field.p : ℤ)
  have hp7 : ((Field.p : ℤ) % 7) = 6 := by
    trans (↑(Field.p % 7) : ℤ)
    · exact Int.natCast_emod Field.p 7
    · rw [p_mod_seven]; norm_num
  rw [hmod, hp7]
  have hns : ¬ IsSquare (6 : ZMod 7) := by decide
  exact (legendreSym.eq_neg_one_iff' (p := 7) (a := 6)).mpr hns

/-- Euler's criterion: `7^((p−1)/2) = −1`. -/
theorem seven_pow_half : (7 : Field.Fp) ^ (Field.p / 2) = -1 := by
  have heq := legendreSym.eq_pow (p := Field.p) (7 : ℤ)
  have hcast : ((7 : ℤ) : Field.Fp) = (7 : Field.Fp) := by norm_cast
  have hleg : (legendreSym Field.p 7 : Field.Fp) = -1 := by
    rw [goldilocks_legendre_seven]; norm_num
  rw [← hcast, ← heq, hleg]

/-- The NPR seed in the base field: `7^(2^32 − 1)`, of exact order `2^32`. -/
def goldilocksSeedBase : Field.Fp := (7 : Field.Fp) ^ (2 ^ 32 - 1)

/-- Kernel 2 for the seed: `a^(2^32) = 7^(p−1) = 1` (Fermat). -/
theorem goldilocksSeedBase_pow_two_pow_32 :
    goldilocksSeedBase ^ (2 ^ 32) = 1 := by
  unfold goldilocksSeedBase
  rw [← pow_mul]
  have hmul : (2 ^ 32 - 1) * 2 ^ 32 = Field.p - 1 := by
    simp only [Field.p]; norm_num
  rw [hmul]
  exact ZMod.pow_card_sub_one_eq_one seven_ne_zero_fp

/-- Kernel 1 for the seed: `a^(2^31) = 7^((p−1)/2) = −1 ≠ 1`. -/
theorem goldilocksSeedBase_pow_two_pow_31 :
    goldilocksSeedBase ^ (2 ^ 31) = -1 := by
  unfold goldilocksSeedBase
  rw [← pow_mul]
  have hmul : (2 ^ 32 - 1) * 2 ^ 31 = Field.p / 2 := by
    simp only [Field.p]; norm_num
  rw [hmul]
  exact seven_pow_half

/-- `orderOf (7^(2^32−1)) = 2^32`.  The two kernels are
    `goldilocksSeedBase_pow_two_pow_31` and `goldilocksSeedBase_pow_two_pow_32`. -/
theorem goldilocksSeedBase_order : orderOf goldilocksSeedBase = 2 ^ 32 := by
  have hnot : ¬ goldilocksSeedBase ^ (2 ^ 31) = 1 := by
    rw [goldilocksSeedBase_pow_two_pow_31]
    exact neg_one_ne_one_fp
  have hfin : goldilocksSeedBase ^ (2 ^ (31 + 1)) = 1 := by
    change goldilocksSeedBase ^ (2 ^ 32) = 1
    exact goldilocksSeedBase_pow_two_pow_32
  exact orderOf_eq_prime_pow (p := 2) (n := 31) hnot hfin

theorem goldilocksSeedBase_ne_zero : goldilocksSeedBase ≠ 0 := by
  intro h
  have hpow := pow_orderOf_eq_one goldilocksSeedBase
  rw [goldilocksSeedBase_order, h, zero_pow (by norm_num : (2 ^ 32 : ℕ) ≠ 0)] at hpow
  exact one_ne_zero hpow.symm

/-! `7` is a generator of `(𝔽_p)ˣ` (user-computed).  The live seed only consumes
the 2-power quotient `7^(2^32−1)`; the remaining prime-factor kernels of
`p − 1 = 2^32 · 3 · 5 · 17 · 257 · 65537` are not needed for `hout`. -/

/-! ## Fixed strict base-field orbit -/

/-- A chosen Goldilocks base-field generator of exact order `3 * 2^h`. -/
def goldilocksStrictGenerator (h : ℕ) (hle : h ≤ 32) : Field.Fp :=
  Classical.choose
    (exists_zmod_generator_of_dvd_sub_one Field.p (3 * 2 ^ h)
      (three_mul_two_pow_dvd_p_sub_one h hle))

theorem goldilocksStrictGenerator_order (h : ℕ) (hle : h ≤ 32) :
    orderOf (goldilocksStrictGenerator h hle) = 3 * 2 ^ h :=
  Classical.choose_spec
    (exists_zmod_generator_of_dvd_sub_one Field.p (3 * 2 ^ h)
      (three_mul_two_pow_dvd_p_sub_one h hle))

/-- Fixed Goldilocks strict RAP orbit.  The supported range retains the structure's required
`1 ≤ h ≤ 32`. -/
def goldilocksStrictOrbit (h : ℕ) (hpos : 1 ≤ h) (hle : h ≤ 32) :
    StrictOrbitDomain Field.Fp 3 h where
  ω := goldilocksStrictGenerator h hle
  βcoset := 1
  e_pos := by norm_num
  h_pos := hpos
  order_ω := goldilocksStrictGenerator_order h hle
  βcoset_ne_zero := one_ne_zero

/-! ## Cubic extraction and execution orbit -/

/-- Cubing an element of exact order `3 * 2^h` extracts exact order `2^h`. -/
theorem orderOf_cube_of_order_three_mul_two_pow
    {F : Type*} [Field F] {h : ℕ} (ω : F)
    (horder : orderOf ω = 3 * 2 ^ h) :
    orderOf (ω ^ 3) = 2 ^ h := by
  have hω : ω ≠ 0 := by
    intro hz
    simp [hz] at horder
  let u : Fˣ := Units.mk0 ω hω
  have huorder : orderOf u = 3 * 2 ^ h := by
    rw [← orderOf_units]
    simpa [u] using horder
  have hne : orderOf u ≠ 0 := by
    rw [huorder]
    exact Nat.mul_ne_zero (by norm_num) (pow_ne_zero _ (by norm_num))
  have hdvd : 2 ^ h ∣ orderOf u := by
    rw [huorder]
    refine ⟨3, ?_⟩
    omega
  have hdiv : orderOf u / 2 ^ h = 3 := by
    rw [huorder]
    rw [Nat.mul_comm]
    exact Nat.mul_div_cancel_left 3 (Nat.two_pow_pos h)
  have hexact := orderOf_pow_orderOf_div hne hdvd
  rw [hdiv] at hexact
  change orderOf (((u ^ 3 : Fˣ) : F)) = 2 ^ h
  rw [orderOf_units]
  exact hexact

/-- The execution generator in the cubic extension, obtained by cubing in `Field.Fp` and then
injecting into `Field.K`. -/
def goldilocksExecutionGenerator (hExec : ℕ) (hle : hExec ≤ 32) : Field.K :=
  algebraMap Field.Fp Field.K ((goldilocksStrictGenerator hExec hle) ^ 3)

theorem goldilocksExecutionGenerator_order (hExec : ℕ) (hle : hExec ≤ 32) :
    orderOf (goldilocksExecutionGenerator hExec hle) = 2 ^ hExec := by
  change orderOf
    ((algebraMap Field.Fp Field.K).toMonoidHom
      ((goldilocksStrictGenerator hExec hle) ^ 3)) = 2 ^ hExec
  exact
    (orderOf_injective (algebraMap Field.Fp Field.K).toMonoidHom
      (algebraMap Field.Fp Field.K).injective
      ((goldilocksStrictGenerator hExec hle) ^ 3)).trans
        (orderOf_cube_of_order_three_mul_two_pow
          (goldilocksStrictGenerator hExec hle)
          (goldilocksStrictGenerator_order hExec hle))

/-- Execution/evaluation orbit in `Field.K` of exact order `2^hExec`. -/
def goldilocksExecutionOrbit (hExec : ℕ) (_hpos : 1 ≤ hExec) (hle : hExec ≤ 32) :
    OrbitDomain Field.K where
  h := hExec
  ω := goldilocksExecutionGenerator hExec hle
  βcoset := 1
  βcoset_ne_zero := one_ne_zero
  order_ω := goldilocksExecutionGenerator_order hExec hle

/-- The two independent orbit choices used by later universal builders.  No equality between
`hExec` and `hRap` is imposed. -/
structure GoldilocksOrbitPair (hExec hRap : ℕ) where
  execution : OrbitDomain Field.K
  strictRAP : StrictOrbitDomain Field.Fp 3 hRap

/-- Construct execution and RAP orbits at explicitly separate exponents. -/
def goldilocksOrbitPair (hExec hRap : ℕ)
    (hExecPos : 1 ≤ hExec) (hExecLe : hExec ≤ 32)
    (hRapPos : 1 ≤ hRap) (hRapLe : hRap ≤ 32) :
    GoldilocksOrbitPair hExec hRap where
  execution := goldilocksExecutionOrbit hExec hExecPos hExecLe
  strictRAP := goldilocksStrictOrbit hRap hRapPos hRapLe

/-! ## Concrete non-vacuity -/

/-- At supported height one, both orbit kinds exist and their first nontrivial two-point prefixes
are injective and cardinality-correct. -/
theorem height_one_nonvacuous :
    Nonempty (StrictOrbitDomain Field.Fp 3 1) ∧
      Nonempty (OrbitDomain Field.K) ∧
      (strictRowDomain (goldilocksStrictOrbit 1 (by norm_num) (by norm_num)) 2).card = 2 ∧
      Function.Injective
        (fun i : Fin 2 =>
          strictOrbitPoint (goldilocksStrictOrbit 1 (by norm_num) (by norm_num)) i) ∧
      ((goldilocksExecutionOrbit 1 (by norm_num) (by norm_num)).rowDomain 2).card = 2 ∧
      Function.Injective
        (fun i : Fin 2 =>
          (goldilocksExecutionOrbit 1 (by norm_num) (by norm_num)).orbitPoint i) := by
  let strict := goldilocksStrictOrbit 1 (by norm_num) (by norm_num)
  let execution := goldilocksExecutionOrbit 1 (by norm_num) (by norm_num)
  refine ⟨⟨strict⟩, ⟨execution⟩, ?_, ?_, ?_, ?_⟩
  · exact strictRowDomain_card strict (by norm_num)
  · exact strictOrbitPoint_injective strict (by norm_num)
  · apply execution.rowDomain_card
    change 2 ≤ 2 ^ 1
    norm_num
  · apply execution.orbitPoint_injective
    change 2 ≤ 2 ^ 1
    norm_num

end

end GoldilocksOrbit
end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.GoldilocksOrbit.p_sub_one_factorization
#print axioms Nock.NockVMROM.Thm54.GoldilocksOrbit.three_mul_two_pow_dvd_p_sub_one
#print axioms Nock.NockVMROM.Thm54.GoldilocksOrbit.orderOf_cube_of_order_three_mul_two_pow
#print axioms Nock.NockVMROM.Thm54.GoldilocksOrbit.goldilocksStrictOrbit
#print axioms Nock.NockVMROM.Thm54.GoldilocksOrbit.goldilocksExecutionOrbit
#print axioms Nock.NockVMROM.Thm54.GoldilocksOrbit.height_one_nonvacuous
#print axioms Nock.NockVMROM.Thm54.GoldilocksOrbit.eight_order
#print axioms Nock.NockVMROM.Thm54.GoldilocksOrbit.goldilocksSeedBase_order
#print axioms Nock.NockVMROM.Thm54.GoldilocksOrbit.seven_pow_half
