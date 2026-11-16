import Nock.NockVM
import Mathlib.NumberTheory.PrimesCongruentOne
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! Constructs, for each `n`, a prime `p_n` above explicit bounds with `2 ^ hgt n ∣ p_n - 1`, the resulting prime-field family, and an element of exact order `2 ^ hgt n` in it. These supply the characteristic, size and trace-domain hypotheses of the AIR soundness theorems. -/

namespace P9Spike

noncomputable section

variable (Ksz hgt : ℕ → ℕ)

/-- Lower bound: above `Ksz n + 2` and above `2^(n+1) + 12` (so `char > 11`, `Ksz n < p`). -/
def boundAt (n : ℕ) : ℕ := max (Ksz n + 2) (2 ^ (n + 1) + 12)

/-- Prime above the bound AND `≡ 1 mod 2^(hgt n)`: the special case of Dirichlet that IS in
    Mathlib (`Nat.exists_prime_gt_modEq_one`, via cyclotomic evaluation). -/
theorem exists_good_prime (n : ℕ) :
    ∃ p : ℕ, Nat.Prime p ∧ boundAt Ksz n < p ∧ p ≡ 1 [MOD 2 ^ hgt n] :=
  Nat.exists_prime_gt_modEq_one (boundAt Ksz n) (by positivity)

/-- The chosen prime, via `Nat.find`. -/
def pAt (n : ℕ) : ℕ :=
  Nat.find (p := fun p => Nat.Prime p ∧ boundAt Ksz n < p ∧ p ≡ 1 [MOD 2 ^ hgt n])
    (exists_good_prime Ksz hgt n)

theorem pAt_spec (n : ℕ) :
    Nat.Prime (pAt Ksz hgt n) ∧ boundAt Ksz n < pAt Ksz hgt n
      ∧ pAt Ksz hgt n ≡ 1 [MOD 2 ^ hgt n] :=
  Nat.find_spec (exists_good_prime Ksz hgt n)

instance factPrime (n : ℕ) : Fact (Nat.Prime (pAt Ksz hgt n)) := ⟨(pAt_spec Ksz hgt n).1⟩

/-- The varying-prime field family. -/
abbrev FieldAt (n : ℕ) : Type := ZMod (pAt Ksz hgt n)

instance : ∀ n, Field (FieldAt Ksz hgt n) := fun n => ZMod.instField _
instance : ∀ n, Fintype (FieldAt Ksz hgt n) := fun n => ZMod.fintype _
instance : ∀ n, DecidableEq (FieldAt Ksz hgt n) := fun n => ZMod.decidableEq _

theorem card_FieldAt (n : ℕ) : Fintype.card (FieldAt Ksz hgt n) = pAt Ksz hgt n :=
  ZMod.card _

/-- `char > 11`: the `computeAIR_sound_free` hypothesis. -/
theorem hchar (n : ℕ) : ∀ m : ℕ, m ≤ 11 → (m : FieldAt Ksz hgt n) = 1 → m = 1 := by
  intro m hm hcast
  have hp : 11 < pAt Ksz hgt n := by
    have h2 := (pAt_spec Ksz hgt n).2.1
    have : 2 ^ (n + 1) + 12 ≤ boundAt Ksz n := le_max_right _ _
    have hpow : 1 ≤ 2 ^ (n + 1) := Nat.one_le_two_pow
    omega
  have : ((m : ℕ) : ZMod (pAt Ksz hgt n)) = ((1 : ℕ) : ZMod (pAt Ksz hgt n)) := by
    simpa using hcast
  have := (ZMod.natCast_eq_natCast_iff' m 1 _).mp this
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  exact this

/-- `Ksz n < p_n`: the `fullAIR_entails_forest'` / `io_result_LIO` hypothesis. -/
theorem Ksz_lt (n : ℕ) : Ksz n < pAt Ksz hgt n := by
  have h2 := (pAt_spec Ksz hgt n).2.1
  have : Ksz n + 2 ≤ boundAt Ksz n := le_max_left _ _
  omega

/-- **The RAP-domain requirement.**  `2 ^ hgt n ∣ p_n - 1`, hence an order-`2^(hgt n)`
    multiplicative subgroup exists — the fact a plain "prime above a bound" family does NOT give. -/
theorem two_pow_dvd (n : ℕ) : 2 ^ hgt n ∣ pAt Ksz hgt n - 1 := by
  have h := (pAt_spec Ksz hgt n).2.2
  have hpos : 0 < pAt Ksz hgt n := (pAt_spec Ksz hgt n).1.pos
  exact (Nat.modEq_iff_dvd' hpos).mp h.symm

/-- **An element of exact order `2 ^ hgt n`** (the trace-subgroup generator / timestamp base). -/
theorem exists_traceStep (n : ℕ) :
    ∃ β : FieldAt Ksz hgt n, orderOf β = 2 ^ hgt n := by
  classical
  haveI : Fact (Nat.Prime (pAt Ksz hgt n)) := factPrime Ksz hgt n
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod (pAt Ksz hgt n))ˣ)
  have hcard : Nat.card (ZMod (pAt Ksz hgt n))ˣ = pAt Ksz hgt n - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime (pAt_spec Ksz hgt n).1]
  rw [hcard] at hg
  have hne : orderOf g ≠ 0 := by rw [hg]; have := (pAt_spec Ksz hgt n).2.1
                                 have : 1 < pAt Ksz hgt n := (pAt_spec Ksz hgt n).1.one_lt
                                 omega
  have hdvd : 2 ^ hgt n ∣ orderOf g := by rw [hg]; exact two_pow_dvd Ksz hgt n
  refine ⟨((g ^ (orderOf g / 2 ^ hgt n) : (ZMod (pAt Ksz hgt n))ˣ) : ZMod (pAt Ksz hgt n)), ?_⟩
  rw [orderOf_units]
  exact orderOf_pow_orderOf_div hne hdvd

end

end P9Spike

#print axioms P9Spike.exists_traceStep
#print axioms P9Spike.hchar
