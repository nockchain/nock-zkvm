/-
  Nock/NockVMROM/Thm54/VclL/Chips/CertBound.lean

  Its soundness in a field of characteristic `p`:
  * `bits_sum_nat`: six (any `m`) boolean field values `bᵢ (bᵢ − 1) = 0` spell a natural number
    `s < 2^m` (`Σ 2^i bᵢ = (s : F)`);
  * `len_le_of_cert`: if the length is the natural `k` with `k + 1 < p` and `(k : F) + (s : F) = 62`
    with `s ≤ 63`, then `k ≤ 62` — the field equation cannot wrap upward: `k + s ≤ p + 61 < p + 62`;
  * `len_le_62_of_chip`: the two combined (bits as `Σ_{i<6} 2^i bᵢ` over `Finset.range`; relating it
    to the chip's `bitSum` `CoeffExpr` evaluation is part of the remaining bridge, unconfirmed).
  The hypothesis `k + 1 < p` is where `Checks.hcons` enters: `k ≤ P` (the edge count) and the export
  accumulator's consumer bound `3N + P < p` with `N ≥ 1` give `P + 3 < p`
  (`len_bound_of_hcons`).  Negative control: `cert_wraps_without_bound` — at `p = 31` with no length
  bound, `k = 31 + 62 = 93` meets the field equation with `s = 0` (`(93 : ZMod 31) = 62`).
-/
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.VclL.Chips.CertBound

open Finset

variable {F : Type} [Field F]

/-- A boolean field value is `0` or `1`. -/
theorem bool_cases {x : F} (h : x * (x - 1) = 0) : x = 0 ∨ x = 1 := by
  rcases mul_eq_zero.mp h with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

/-- **Boolean bits spell a natural number below `2^m`.** -/
theorem bits_sum_nat (b : ℕ → F) : ∀ m : ℕ, (∀ i < m, b i * (b i - 1) = 0) →
    ∃ s : ℕ, s < 2 ^ m ∧ (s : F) = ∑ i ∈ range m, (2 : F) ^ i * b i
  | 0, _ => ⟨0, by simp, by simp⟩
  | m + 1, hb => by
    obtain ⟨s, hs, hsum⟩ := bits_sum_nat b m (fun i hi => hb i (by omega))
    rw [sum_range_succ, ← hsum]
    rcases bool_cases (hb m (by omega)) with h0 | h1
    · refine ⟨s, by rw [pow_succ]; omega, by rw [h0]; ring⟩
    · refine ⟨s + 2 ^ m, by rw [pow_succ]; omega, by rw [h1]; push_cast; ring⟩

/-- **The certificate equation cannot wrap upward**: `(k : F) + (s : F) = 62`, `s ≤ 63`,
`k + 1 < p` give `k ≤ 62` (if `k + s ≥ 62` then `p ∣ k + s − 62 < p`, so `k + s = 62`). -/
theorem len_le_of_cert {p : ℕ} [CharP F p] {k s : ℕ} (hs : s ≤ 63) (hk : k + 1 < p)
    (h : (k : F) + (s : F) = 62) : k ≤ 62 := by
  have hc : ((k + s : ℕ) : F) = ((62 : ℕ) : F) := by push_cast; exact h
  rw [CharP.natCast_eq_natCast F p] at hc
  rcases le_or_gt 62 (k + s) with hge | hlt
  · have hdvd : p ∣ k + s - 62 := (Nat.modEq_iff_dvd' hge).mp hc.symm
    have h0 : k + s - 62 = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
    omega
  · omega

/-- **The chip form**: the length is the natural `k` (`k + 1 < p`), the six certificate columns are
boolean, and `len + Σ_{i<6} 2^i bᵢ − 62 = 0` on the chain's last row; then `k ≤ 62`. -/
theorem len_le_62_of_chip {p : ℕ} [CharP F p] (b : ℕ → F) (hb : ∀ i < 6, b i * (b i - 1) = 0)
    {k : ℕ} (hk : k + 1 < p) (hgate : (k : F) + ∑ i ∈ range 6, (2 : F) ^ i * b i - 62 = 0) :
    k ≤ 62 := by
  obtain ⟨s, hs, hsum⟩ := bits_sum_nat b 6 hb
  have : (k : F) + (s : F) = 62 := by rw [hsum]; linear_combination hgate
  exact len_le_of_cert (by norm_num at hs; omega) hk this

/-- Where `k + 1 < p` comes from: the chain length is at most the path rows `P`, and
`Checks.hcons` at the export accumulator is `3N + P < p` with `N ≥ 1`. -/
theorem len_bound_of_hcons {N P k p : ℕ} (hN : 1 ≤ N) (hkP : k ≤ P) (hcons : 3 * N + P < p) :
    k + 1 < p := by omega

/-- **Negative control**: without a length bound the certificate wraps (`p = 31`, `k = 93`,
`s = 0`: `(93 : ZMod 31) + 0 = 62`), and `93 > 62`. -/
theorem cert_wraps_without_bound : ((93 : ℕ) : ZMod 31) + ((0 : ℕ) : ZMod 31) = 62 ∧ ¬ (93 ≤ 62) :=
  ⟨by decide, by decide⟩

end Nock.NockVMROM.Thm54.VclL.Chips.CertBound
