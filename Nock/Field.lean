/-
  Nock/Field.lean

  The field layer for the Noun Polynomial Representation.

  Paper correspondence: the RAP is instantiated with
    1. `𝔽 ≡ 𝔽_p`, the **Goldilocks** prime field with `p = 2^64 − 2^32 + 1`;
    2. `K`, the degree-`e = 3` extension of `𝔽_p` (so `|K| = p^3 ≈ 2^192`).

  The operational `Nock.Noun` keeps `atom : Nat`.
  The field enters ONLY at the NPR layer, via the ring
  homomorphism `Nat → K` (`Nat.cast`).  Because `𝔽_p ↪ K` is a ring hom and the `Nat`
  cast is initial, `(Nat → 𝔽_p → K) = (Nat → K)`, so casting leaves directly into `K`
  is the same as the paper's "coefficients in `𝔽`, evaluate in `K`".

  CONSTRUCTION.  `K` is `GaloisField p 3`, Mathlib's canonical field of order `p^3`
  (the splitting field of `X^{p^3} − X`); no hand-rolled irreducible cubic is needed.
  `GaloisField.card` gives `|K| = p^3`.

  Primality of `p` is a kernel-checked theorem: a Pratt
  / Lucas certificate (`Nock.Primality.goldilocksCert`, `Nock/Primality/GoldilocksCore.lean`,
  imports `Pratt` and Mathlib only) is checked by `decide +kernel`, then `cert_prime`.  No
  `native_decide`, no `ofReduceBool`.  The field/NPR layer has no mathematical axiom left.
-/
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.SetTheory.Cardinal.Finite
import Nock.Primality.GoldilocksCore

namespace Nock
namespace Field

/-- The **Goldilocks prime** `p = 2^64 − 2^32 + 1`. -/
def p : ℕ := 2 ^ 64 - 2 ^ 32 + 1

/-- Sanity: the concrete decimal value of the Goldilocks prime. -/
theorem p_eq : p = 18446744069414584321 := by norm_num [p]

theorem goldilocks_prime : Nat.Prime p := by
  have h : (18446744069414584321 : ℕ) ∈ Nock.Primality.goldilocksCert.map Nock.Primality.Entry.n := by
    decide +kernel
  have := Nock.Primality.cert_prime h
  rwa [← p_eq] at this

instance : Fact (Nat.Prime p) := ⟨goldilocks_prime⟩

/-- The Goldilocks base field `𝔽 = 𝔽_p`.  A `Field` and `Fintype` by the
    `Fact p.Prime` instance above. -/
abbrev Fp : Type := ZMod p

/-- The degree-3 extension field `K` over `𝔽_p`, `|K| = p^3 ≈ 2^192`.
    Realized as Mathlib's `GaloisField p 3` (the field of order `p^3`); `K` is a `Field`
    and a `ZMod p`-algebra by Mathlib's instances, hence carries `𝔽_p ↪ K`. -/
abbrev K : Type := GaloisField p 3

noncomputable instance : Fintype K := Fintype.ofFinite _
noncomputable instance : DecidableEq K := Classical.decEq _

/-- **`|K| = p^3`.**  The degree-3 extension has `p^3` elements. -/
theorem card_K : Fintype.card K = p ^ 3 := by
  have h : Nat.card K = p ^ 3 := GaloisField.card p 3 (by norm_num)
  rwa [Nat.card_eq_fintype_card] at h

/-- `|K| ≈ 2^192`: the exact cardinality of `K`. -/
theorem card_K_value : Fintype.card K = 18446744069414584321 ^ 3 := by
  rw [card_K, p_eq]

end Field
end Nock
