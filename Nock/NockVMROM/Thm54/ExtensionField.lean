/-
  Nock/NockVMROM/Thm54/ExtensionField.lean

  Packet 1 of the Theorem 5.4 north star: the extension-field API parameterized by a fixed
  operational degree `e ≥ 1`, and the strict orbit domain of exact order `e·2^h`.

  * **Extension degree `e` is a real field parameter, not width metadata.**  `ExtensionFieldAt e q n`
    is the degree-`e` Galois extension of `𝔽_{q n}`; its cardinality is `(q n)^e`
    (`extensionFieldAt_card`), its characteristic is `q n` (`extensionFieldAt_charP`), and its
    `𝔽_{q n}`-dimension is `e` (`extensionFieldAt_finrank`).  This is orthogonal to `ExactConfig.eDeg`
    (which stays `1` as a coordinate-width datum).

  * **The RAP orbit really has order `e·2^h`, not `2^h`.**  `StrictOrbitDomain F e h` bundles an
    element `ω : F` of exact multiplicative order `e·2^h`.

  The `e = 3` production family (`ExactPrimeFamily.FieldAt = GaloisField (p …) 3`) is recovered as the
  `e := 3` specialization (`extensionFieldAt_three_eq_prodField`), and any fixed prime is the
  degenerate constant family.
-/

import Nock.NockVMROM.Thm54.ExactAsymptotic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finite.Basic

namespace Nock.NockVMROM.Thm54
namespace StrictExtension

open scoped Classical

noncomputable section

/-! ## Generic degree-`e` extension field over a prime family -/

section Generic

variable (e : ℕ) (q : ℕ → ℕ) [hq : ∀ n, Fact (Nat.Prime (q n))]

/-- The degree-`e` Galois extension of the base field `𝔽_{q n}` at security parameter `n`. -/
abbrev ExtensionFieldAt (n : ℕ) : Type := GaloisField (q n) e

noncomputable instance extensionFieldAt_field (n : ℕ) : Field (ExtensionFieldAt e q n) :=
  inferInstance

noncomputable instance extensionFieldAt_fintype (n : ℕ) : Fintype (ExtensionFieldAt e q n) :=
  Fintype.ofFinite _

noncomputable instance extensionFieldAt_algebra (n : ℕ) :
    Algebra (ZMod (q n)) (ExtensionFieldAt e q n) :=
  inferInstance

/-- **Cardinality of the extension field is `(q n)^e`.** -/
theorem extensionFieldAt_card (he : e ≠ 0) (n : ℕ) :
    Fintype.card (ExtensionFieldAt e q n) = (q n) ^ e := by
  rw [Fintype.card_eq_nat_card]
  exact GaloisField.card _ _ he

/-- **Characteristic of the extension field is the base prime `q n`.** -/
theorem extensionFieldAt_charP (n : ℕ) : CharP (ExtensionFieldAt e q n) (q n) :=
  inferInstance

/-- **The base-field dimension of the extension is exactly `e`.**  This is the operational extension
degree, distinct from `ExactConfig.eDeg`. -/
theorem extensionFieldAt_finrank (he : e ≠ 0) (n : ℕ) :
    Module.finrank (ZMod (q n)) (ExtensionFieldAt e q n) = e :=
  GaloisField.finrank _ he

end Generic

/-- The `e = 3` specialization is definitionally the production cubic family. -/
theorem extensionFieldAt_three_eq_prodField
    (Ksz h : ℕ → ℕ) (kroots : ℕ) (n : ℕ) :
    ExtensionFieldAt 3 (ExactPrimeFamily.p Ksz h kroots) n
      = ExactPrimeFamily.FieldAt Ksz h kroots n := rfl

/-! ## The strict orbit domain of order `e·2^h` -/

/-- A **strict orbit domain**: a field element of *exact* multiplicative order `e·2^h`, together with
a nonzero coset representative. -/
structure StrictOrbitDomain (F : Type*) [Field F] (e h : ℕ) where
  /-- The generator. -/
  ω : F
  /-- The coset representative `β`. -/
  βcoset : F
  /-- The operational extension degree is at least one. -/
  e_pos : 1 ≤ e
  /-- The orbit height is at least one. -/
  h_pos : 1 ≤ h
  /-- `ω` has *exact* order `e·2^h`. -/
  order_ω : orderOf ω = e * 2 ^ h
  /-- The coset representative is a unit. -/
  βcoset_ne_zero : βcoset ≠ 0

/-! ### Generic extraction of an exact-order element from a prime field -/

/-- A divisor `m` of the unit-group order of a prime field occurs as the exact order of a
field element.  This is the fixed-prime form of the cyclic-unit construction used by the varying
strict family below. -/
theorem exists_zmod_generator_of_dvd_sub_one
    (q m : ℕ) [Fact (Nat.Prime q)] (hm : m ∣ q - 1) :
    ∃ ω : ZMod q, orderOf ω = m := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod q)ˣ)
  have hcard : Nat.card (ZMod q)ˣ = q - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime (Fact.out : Nat.Prime q)]
  rw [hcard] at hg
  have hne : orderOf g ≠ 0 := by
    rw [hg]
    have hq_one : 1 < q := (Fact.out : Nat.Prime q).one_lt
    omega
  have hdvd : m ∣ orderOf g := by
    rw [hg]
    exact hm
  let ζ : ZMod q := ((g ^ (orderOf g / m) : (ZMod q)ˣ) : ZMod q)
  have hζ : orderOf ζ = m := by
    change orderOf (((g ^ (orderOf g / m) : (ZMod q)ˣ) : ZMod q)) = m
    rw [orderOf_units]
    exact orderOf_pow_orderOf_div hne hdvd
  exact ⟨ζ, hζ⟩

/-! ### A varying base-prime family congruent to `1 (mod e·2^h)` -/

section StrictFamily

variable (e : ℕ) [NeZero e] (Ksz h : ℕ → ℕ) (kroots : ℕ)

/-- The strict congruence modulus `e·2^h`. -/
def strictModulus (n : ℕ) : ℕ := e * 2 ^ h n

theorem strictModulus_ne_zero (n : ℕ) : strictModulus e h n ≠ 0 := by
  simp only [strictModulus]
  exact Nat.mul_ne_zero (NeZero.ne e) (pow_ne_zero _ (by norm_num))

theorem exists_strict_prime (n : ℕ) :
    ∃ p : ℕ, Nat.Prime p ∧ ExactPrimeFamily.selectionBound Ksz h kroots n < p ∧
      p ≡ 1 [MOD strictModulus e h n] :=
  Nat.exists_prime_gt_modEq_one (k := strictModulus e h n)
    (ExactPrimeFamily.selectionBound Ksz h kroots n) (strictModulus_ne_zero e h n)

/-- The chosen strict prime at security parameter `n`. -/
def pS (n : ℕ) : ℕ :=
  Nat.find
    (p := fun p =>
      Nat.Prime p ∧ ExactPrimeFamily.selectionBound Ksz h kroots n < p ∧
        p ≡ 1 [MOD strictModulus e h n])
    (exists_strict_prime e Ksz h kroots n)

theorem pS_spec (n : ℕ) :
    Nat.Prime (pS e Ksz h kroots n) ∧
      ExactPrimeFamily.selectionBound Ksz h kroots n < pS e Ksz h kroots n ∧
      pS e Ksz h kroots n ≡ 1 [MOD strictModulus e h n] :=
  Nat.find_spec (exists_strict_prime e Ksz h kroots n)

instance pS_fact_prime (n : ℕ) : Fact (Nat.Prime (pS e Ksz h kroots n)) :=
  ⟨(pS_spec e Ksz h kroots n).1⟩

/-- The strict base field `𝔽_{pS n}`. -/
abbrev StrictBaseField (n : ℕ) : Type := ZMod (pS e Ksz h kroots n)

/-- `e·2^h ∣ pS - 1`, the divisibility certificate for an order-`e·2^h` subgroup of the units. -/
theorem strictModulus_dvd_sub_one (n : ℕ) :
    strictModulus e h n ∣ pS e Ksz h kroots n - 1 := by
  have hmod := (pS_spec e Ksz h kroots n).2.2
  have hp : 0 < pS e Ksz h kroots n := (pS_spec e Ksz h kroots n).1.pos
  exact (Nat.modEq_iff_dvd' hp).mp hmod.symm

/-- A base-field element of *exact* order `e·2^h`. -/
theorem exists_strict_generator (n : ℕ) :
    ∃ ω : StrictBaseField e Ksz h kroots n, orderOf ω = strictModulus e h n := by
  exact exists_zmod_generator_of_dvd_sub_one
    (pS e Ksz h kroots n) (strictModulus e h n)
    (strictModulus_dvd_sub_one e Ksz h kroots n)

/-- A fixed chosen strict generator. -/
def strictGenerator (n : ℕ) : StrictBaseField e Ksz h kroots n :=
  Classical.choose (exists_strict_generator e Ksz h kroots n)

@[simp] theorem strictGenerator_order (n : ℕ) :
    orderOf (strictGenerator e Ksz h kroots n) = strictModulus e h n :=
  Classical.choose_spec (exists_strict_generator e Ksz h kroots n)

/-- **The strict orbit domain is inhabited over the varying base prime field.**  It carries an
element of *exact* order `e·2^h`, resolving the order-`2^h`-vs-`e·2^h` gap. -/
def strictOrbitDomain (n : ℕ) (hh : 1 ≤ h n) :
    StrictOrbitDomain (StrictBaseField e Ksz h kroots n) e (h n) where
  ω := strictGenerator e Ksz h kroots n
  βcoset := 1
  e_pos := Nat.one_le_iff_ne_zero.mpr (NeZero.ne e)
  h_pos := hh
  order_ω := by
    rw [strictGenerator_order]; rfl
  βcoset_ne_zero := one_ne_zero

/-- The strict extension field `𝔽_{(pS n)^e}` used on the `K` side of the strict family. -/
abbrev StrictExtensionField (n : ℕ) : Type :=
  ExtensionFieldAt e (pS e Ksz h kroots) n

theorem strictExtensionField_card (n : ℕ) :
    Fintype.card (StrictExtensionField e Ksz h kroots n) = (pS e Ksz h kroots n) ^ e :=
  extensionFieldAt_card e (pS e Ksz h kroots) (NeZero.ne e) n

end StrictFamily

end

end StrictExtension
end Nock.NockVMROM.Thm54
