/-
  Nock/RedTeam/Batch1252Thm54HonestReconCorrections.lean

  * It does not: `25` is not prime,
    and `nockCompiles_zmod` carries `[Fact p.Prime]`, so the floor `25 ≤ p` already means `26 ≤ p`
    (and under `hF`, `6 ∣ p − 1`, the smallest admissible prime is `31`).  So `hp : 25 ≤ p` stays, with or without `hS`.
  * **`hF` is open at general `F`.**  `Batch1250.hF_zmod` proves it at `F = ZMod p`; the general-`F`
    theorems of `Batch1250` carry it as an explicit premise.  It was listed as "discharged" there.
  * Only
    `Batch963`'s generated-package open list `{4, 11, 12}` is stale.
  * **The explicit `haxis` of `Batch1250.nonvacuous_generated_of_reconstruction` shadowed the
    generator's implicit `haxis : SkeletonAxisRange`.**  Renamed `haxisEv` in `Batch1250` (binder
    name only; statement and proof unchanged).
-/
import Nock.RedTeam.Batch1251Thm54HonestPairNotDiagonal

set_option autoImplicit false

namespace Nock.RedTeam.Batch1252

open Nock.RedTeam.Batch1251 Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SizeWindowCounting

def twoPairRoot (Λ rows M : ℕ) : ℕ :=
  seedBudgetPairB Λ rows M + M * (2 * (M ⊔ Λ) - 1) + (2 * (M ⊔ Λ) - 1)

theorem cubic_gap_two_26 {p : ℕ} (hp : 26 ≤ p) :
    6 * (1 + (3 + 13 * (p - 1)) * (2 * (p - 1) - 1)) + 3 * ((p - 1) * p) +
      4 * ((p - 1) * (2 * (p - 1) - 1)) + 6 * (2 * (p - 1) - 1) < 6 * p ^ 3 := by
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 26 := ⟨p - 26, by omega⟩
  have e1 : n + 26 - 1 = n + 25 := by omega
  have e2 : 2 * (n + 25) - 1 = 2 * n + 49 := by omega
  rw [e1, e2]
  ring_nf
  nlinarith [sq_nonneg n, Nat.zero_le n, Nat.zero_le (n ^ 3)]

/-- At `26 ≤ p`, the two-pair-plus-root budget is below `p³` under the §1 bounds. -/
theorem twoPairRoot_lt_pow {Λ rows M p : ℕ} (hrows : rows < p) (hΛp : Λ < p)
    (hM : 3 * M ≤ p - 1) (hp : 26 ≤ p) : twoPairRoot Λ rows M < p ^ 3 := by
  have hr : rows ≤ p - 1 := by omega
  have hL : Λ ≤ p - 1 := by omega
  have hMp : M ≤ p - 1 := by omega
  have hmx : 2 * (M ⊔ Λ) - 1 ≤ 2 * (p - 1) - 1 := by
    have : M ⊔ Λ ≤ p - 1 := sup_le hMp hL
    omega
  have hsw : sizeWindowRootBound Λ * 2 = Λ * (Λ + 1) := TraceGen.sizeWindowRootBound_mul_two Λ
  have hsw' : Λ * (Λ + 1) ≤ (p - 1) * p := Nat.mul_le_mul hL (by omega)
  have hb1 : (3 + 13 * rows) * (2 * Λ - 1) ≤ (3 + 13 * (p - 1)) * (2 * (p - 1) - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hb2 : 3 * (M * (2 * (M ⊔ Λ) - 1)) ≤ (p - 1) * (2 * (p - 1) - 1) := by
    calc 3 * (M * (2 * (M ⊔ Λ) - 1)) = (3 * M) * (2 * (M ⊔ Λ) - 1) := by ring
      _ ≤ (p - 1) * (2 * (p - 1) - 1) := Nat.mul_le_mul hM hmx
  have hgap := cubic_gap_two_26 hp
  have hexp : twoPairRoot Λ rows M =
      1 + (3 + 13 * rows) * (2 * Λ - 1) + sizeWindowRootBound Λ + M * (2 * (M ⊔ Λ) - 1)
        + M * (2 * (M ⊔ Λ) - 1) + (2 * (M ⊔ Λ) - 1) := by
    unfold twoPairRoot seedBudgetPairB TraceGen.GoodSeed.seedBudgetVcomp TraceGen.GoodSeed.seedBudget
    ring
  rw [hexp]
  nlinarith

/-- `25 ≤ p` with `p` prime already gives `26 ≤ p`. -/
theorem prime_ge_26 {p : ℕ} (hpr : p.Prime) (hp : 25 ≤ p) : 26 ≤ p := by
  rcases Nat.lt_or_ge p 26 with h | h
  · have : p = 25 := by omega
    subst this; exact absurd hpr (by norm_num)
  · exact h

theorem twoPairRoot_lt_pow_of_prime {Λ rows M p : ℕ} (hpr : p.Prime) (hrows : rows < p)
    (hΛp : Λ < p) (hM : 3 * M ≤ p - 1) (hp : 25 ≤ p) : twoPairRoot Λ rows M < p ^ 3 :=
  twoPairRoot_lt_pow hrows hΛp hM (prime_ge_26 hpr hp)

/-- The nat-level failure `Batch1251.seedBudgetTwoPair_fails_25` is at a non-prime. -/
theorem twentyFive_not_prime : ¬ (25 : ℕ).Prime := by norm_num

end Nock.RedTeam.Batch1252

#print axioms Nock.RedTeam.Batch1252.cubic_gap_two_26
#print axioms Nock.RedTeam.Batch1252.twoPairRoot_lt_pow
#print axioms Nock.RedTeam.Batch1252.prime_ge_26
#print axioms Nock.RedTeam.Batch1252.twoPairRoot_lt_pow_of_prime
#print axioms Nock.RedTeam.Batch1252.twentyFive_not_prime
