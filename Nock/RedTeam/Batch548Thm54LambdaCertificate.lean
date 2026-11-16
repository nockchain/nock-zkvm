/-
  Nock/RedTeam/Batch548Thm54LambdaCertificate.lean

  **Item D: the axis-bit certificate is NOT unique mod `p` at `n = 64`.**

  D-λ certifies the OP0 axis on the compute chip by `n = 64` boolean columns with
  `Σ bᵢ·2ⁱ = axis` — an equation in `𝔽 = ℤ/p`.  On Goldilocks `p = 2^64 − 2^32 + 1 < 2^64`, so for
  every axis `a < 2^32 − 1` the bits of `a` AND the bits of `a + p` are both valid 64-bit
  certificates of `a` (`certificate_ambiguous`, `goldilocks_window`).  The second certificate's
  in-gate `a_λ = Σ bᵢλⁱ` is the λ-path polynomial of address `a + p`, so the memory chip then
  accepts a verify at relative address `a + p` (depth `63`) for a record whose compute-side axis
  is `a`: the forged lookup `/[a R] = /[a + p R]`, honest in every gate.  No depth bound excludes
  it ("no depth bound, no addresses, no wrap" is the design's own claim).

  The surviving form: `n = 63` bits with `a < 2^63 < p`, where the certificate is unique
  (`certificate_unique`, `goldilocks_63_below_p`) — at the price of a completeness side
  condition `axis < 2^63` on every OP0 of the program.
-/
import Mathlib.Data.ZMod.Basic
import Nock.Field

set_option autoImplicit false

namespace Nock.RedTeam.Batch548

/-- `Σ_{i<n} bᵢ·2ⁱ` of a boolean vector — the certificate's integer value. -/
def bitSum (b : ℕ → Bool) (n : ℕ) : ℕ := ∑ i ∈ Finset.range n, (b i).toNat * 2 ^ i

theorem bitSum_succ (b : ℕ → Bool) (n : ℕ) :
    bitSum b (n + 1) = bitSum b n + (b n).toNat * 2 ^ n := by
  simp [bitSum, Finset.sum_range_succ]

theorem bitSum_lt (b : ℕ → Bool) (n : ℕ) : bitSum b n < 2 ^ n := by
  induction n with
  | zero => simp [bitSum]
  | succ n ih =>
      rw [bitSum_succ, pow_succ]
      have : (b n).toNat ≤ 1 := Bool.toNat_le _
      nlinarith

/-- The binary digits of `m` are a certificate of `m` whenever `m < 2^n`. -/
theorem bitSum_testBit (n : ℕ) : ∀ m, m < 2 ^ n → bitSum (Nat.testBit m) n = m := by
  induction n with
  | zero => intro m hm; simp [bitSum]; omega
  | succ n ih =>
      intro m hm
      rw [bitSum, Finset.sum_range_succ']
      have h1 : ∀ i, (Nat.testBit m (i + 1)).toNat * 2 ^ (i + 1)
          = 2 * ((Nat.testBit (m / 2) i).toNat * 2 ^ i) := by
        intro i; rw [Nat.testBit_add_one, pow_succ]; ring
      simp only [h1, ← Finset.mul_sum]
      have hm2 : m / 2 < 2 ^ n := by
        rw [Nat.div_lt_iff_lt_mul (by norm_num)]; rw [pow_succ] at hm; exact hm
      have h2 := ih (m / 2) hm2
      rw [bitSum] at h2
      rw [h2, Nat.toNat_testBit]
      simp
      omega

/-- **Two distinct certificates of the same axis mod `p`** whenever `a + p < 2^n`: the bits of
`a` and the bits of `a + p`. -/
theorem certificate_ambiguous (p : ℕ) [NeZero p] (n a : ℕ) (h : a + p < 2 ^ n) :
    Nat.testBit a ≠ Nat.testBit (a + p)
    ∧ ((bitSum (Nat.testBit a) n : ℕ) : ZMod p) = (a : ZMod p)
    ∧ ((bitSum (Nat.testBit (a + p)) n : ℕ) : ZMod p) = (a : ZMod p) := by
  have ha : bitSum (Nat.testBit a) n = a := bitSum_testBit n a (by omega)
  have hap : bitSum (Nat.testBit (a + p)) n = a + p := bitSum_testBit n (a + p) h
  refine ⟨?_, by rw [ha], ?_⟩
  · intro heq
    have : a = a + p := by
      calc a = bitSum (Nat.testBit a) n := ha.symm
        _ = bitSum (Nat.testBit (a + p)) n := by rw [heq]
        _ = a + p := hap
    exact (NeZero.ne p) (by omega)
  · rw [hap]; push_cast; simp

/-- On Goldilocks, every axis below `2^32 − 1` has two 64-bit certificates. -/
theorem goldilocks_window (a : ℕ) (ha : a < 2 ^ 32 - 1) : a + Nock.Field.p < 2 ^ 64 := by
  have hp := Nock.Field.p_eq
  have h32 : (2 : ℕ) ^ 32 - 1 = 4294967295 := by norm_num
  have h64 : (2 : ℕ) ^ 64 = 18446744073709551616 := by norm_num
  omega

theorem goldilocks_axis_one_ambiguous :
    Nat.testBit 1 ≠ Nat.testBit (1 + Nock.Field.p)
    ∧ ((bitSum (Nat.testBit 1) 64 : ℕ) : ZMod Nock.Field.p) = 1
    ∧ ((bitSum (Nat.testBit (1 + Nock.Field.p)) 64 : ℕ) : ZMod Nock.Field.p) = 1 := by
  have h := certificate_ambiguous Nock.Field.p 64 1 (goldilocks_window 1 (by norm_num))
  simpa using h

/-! ## The surviving form: `n` bits with `2^n < p` -/

theorem bitSum_inj (n : ℕ) : ∀ b b' : ℕ → Bool, bitSum b n = bitSum b' n →
    ∀ i < n, b i = b' i := by
  induction n with
  | zero => intro _ _ _ i hi; omega
  | succ n ih =>
      intro b b' h i hi
      rw [bitSum_succ, bitSum_succ] at h
      have hb := bitSum_lt b n
      have hb' := bitSum_lt b' n
      have hbn : b n = b' n := by
        cases hbn : b n <;> cases hbn' : b' n <;> simp [hbn, hbn'] at h ⊢ <;>
          (generalize 2 ^ n = P at *; omega)
      rw [hbn] at h
      have h' : bitSum b n = bitSum b' n := by omega
      rcases Nat.lt_or_ge i n with hlt | hge
      · exact ih b b' h' i hlt
      · have : i = n := by omega
        subst this; exact hbn

/-- With `2^n < p` the certificate is unique: equal values in `ℤ/p` force equal bits. -/
theorem certificate_unique (p n : ℕ) [NeZero p] (hp : 2 ^ n < p) (b b' : ℕ → Bool)
    (h : ((bitSum b n : ℕ) : ZMod p) = ((bitSum b' n : ℕ) : ZMod p)) :
    ∀ i < n, b i = b' i := by
  apply bitSum_inj n b b'
  have hb := bitSum_lt b n
  have hb' := bitSum_lt b' n
  have := (ZMod.natCast_eq_natCast_iff' _ _ _).mp h
  rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this

theorem goldilocks_63_below_p : 2 ^ 63 < Nock.Field.p := by
  rw [Nock.Field.p_eq]; norm_num

end Nock.RedTeam.Batch548

#print axioms Nock.RedTeam.Batch548.certificate_ambiguous
#print axioms Nock.RedTeam.Batch548.goldilocks_axis_one_ambiguous
#print axioms Nock.RedTeam.Batch548.certificate_unique
