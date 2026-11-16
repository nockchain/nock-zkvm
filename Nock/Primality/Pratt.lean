/-
  Nock/Primality/Pratt.lean

  A kernel-checkable Pratt /
  Lucas primality certificate checker, and a generic divisor-count lemma.  Additive; imports only
  Mathlib; no axiom beyond `{propext, Classical.choice, Quot.sound}`; no `native_decide`.

  A certificate is a list of entries `⟨n, a, fs⟩` read in order: `fs` is the full prime
  factorization of `n - 1`, every prime in `fs` is already certified (or is `2`), and `a` is a
  Lucas witness for `n`.  `checkAll` checks all entries; `checkAll_sound` turns a `true` into
  `Nat.Prime` for every `n` in the list via Mathlib's `lucas_primality`.
-/
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.NumberTheory.ArithmeticFunction.Misc

set_option autoImplicit false

namespace Nock.Primality

/-! ## Modular exponentiation by repeated squaring (kernel friendly) -/

/-- `b ^ e mod m`, by repeated squaring with explicit fuel (so the kernel reduces it with GMP
arithmetic and no well-founded recursion). -/
def powModAux : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, m => 1 % m
  | fuel + 1, b, e, m =>
    if e = 0 then 1 % m
    else
      let h := powModAux fuel (b * b % m) (e / 2) m
      if e % 2 = 1 then b * h % m else h

theorem powModAux_eq : ∀ (fuel b e m : ℕ), e < 2 ^ fuel → powModAux fuel b e m = b ^ e % m := by
  intro fuel
  induction fuel with
  | zero =>
    intro b e m he
    have : e = 0 := by simpa using he
    subst this
    simp [powModAux]
  | succ f ih =>
    intro b e m he
    by_cases h0 : e = 0
    · subst h0; simp [powModAux]
    · have hlt : e / 2 < 2 ^ f := by
        rw [pow_succ] at he; omega
      have key := ih (b * b % m) (e / 2) m hlt
      have h1 : (b * b % m) ^ (e / 2) % m = (b * b) ^ (e / 2) % m := (Nat.pow_mod (b * b) (e / 2) m).symm
      simp only [powModAux, h0, if_false, key, h1]
      by_cases hm : e % 2 = 1
      · simp only [hm, if_true]
        obtain ⟨k, hk⟩ : ∃ k, e = 2 * k + 1 := ⟨e / 2, by omega⟩
        have hk2 : e / 2 = k := by omega
        have hpow : b ^ e = b * (b * b) ^ k := by rw [hk, pow_succ, pow_mul, sq]; ring
        rw [hk2, hpow, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
      · simp only [hm, if_false]
        obtain ⟨k, hk⟩ : ∃ k, e = 2 * k := ⟨e / 2, by omega⟩
        have hk2 : e / 2 = k := by omega
        rw [hk2, hk, pow_mul, sq]

/-- `b ^ e mod m` for exponents below `2 ^ 128`. -/
def powMod (b e m : ℕ) : ℕ := powModAux 128 b e m

theorem powMod_eq {b e m : ℕ} (he : e < 2 ^ 128) : powMod b e m = b ^ e % m :=
  powModAux_eq 128 b e m he

/-! ## Certificates -/

/-- One certificate line: `n`, a Lucas witness `a`, and the prime factorization `∏ f ^ k` of
`n - 1`. -/
structure Entry where
  n : ℕ
  a : ℕ
  fs : List (ℕ × ℕ)

/-- `∏ f ^ k` over a factorization list. -/
def prodPow (fs : List (ℕ × ℕ)) : ℕ := fs.foldr (fun x acc => x.1 ^ x.2 * acc) 1

def checkEntry (known : List ℕ) (E : Entry) : Bool :=
  decide (2 ≤ E.n) && decide (E.n < 2 ^ 128) &&
  E.fs.all (fun x => known.contains x.1) &&
  (prodPow E.fs == E.n - 1) &&
  (powMod E.a (E.n - 1) E.n == 1) &&
  E.fs.all (fun x => powMod E.a ((E.n - 1) / x.1) E.n != 1)

def checkAll : List Entry → List ℕ → Bool
  | [], _ => true
  | E :: t, known => checkEntry known E && checkAll t (E.n :: known)

theorem prime_dvd_prodPow {q : ℕ} (hq : q.Prime) :
    ∀ fs : List (ℕ × ℕ), q ∣ prodPow fs → ∃ x ∈ fs, q ∣ x.1 ^ x.2
  | [], h => by
    simp only [prodPow, List.foldr_nil] at h
    exact absurd (Nat.dvd_one.mp h) hq.ne_one
  | x :: t, h => by
    simp only [prodPow, List.foldr_cons] at h
    rcases (Nat.Prime.dvd_mul hq).mp h with h | h
    · exact ⟨x, List.mem_cons_self, h⟩
    · obtain ⟨y, hy, hy'⟩ := prime_dvd_prodPow hq t h
      exact ⟨y, List.mem_cons_of_mem _ hy, hy'⟩

theorem cast_pow_eq_one_iff {n a k : ℕ} (hn : 2 ≤ n) :
    ((a : ZMod n) ^ k = 1) ↔ a ^ k % n = 1 := by
  have h1 : 1 % n = 1 := Nat.mod_eq_of_lt (by omega)
  have : ((a : ZMod n) ^ k = 1) ↔ ((a ^ k : ℕ) : ZMod n) = ((1 : ℕ) : ZMod n) := by
    push_cast; rfl
  rw [this, ZMod.natCast_eq_natCast_iff', h1]

theorem checkEntry_sound {known : List ℕ} (hk : ∀ x ∈ known, x.Prime) {E : Entry}
    (h : checkEntry known E = true) : E.n.Prime := by
  simp only [checkEntry, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    beq_iff_eq, bne_iff_ne, ne_eq, List.contains_iff_mem] at h
  obtain ⟨⟨⟨⟨⟨h2, h128⟩, hmem⟩, hprod⟩, hpow⟩, hne⟩ := h
  have hlt : E.n - 1 < 2 ^ 128 := by omega
  apply lucas_primality E.n (E.a : ZMod E.n)
  · rw [cast_pow_eq_one_iff h2, ← powMod_eq hlt]; exact hpow
  · intro q hq hdvd
    rw [← hprod] at hdvd
    obtain ⟨x, hx, hxq⟩ := prime_dvd_prodPow hq E.fs hdvd
    have hxp : x.1.Prime := hk _ (hmem x hx)
    have hqx : q ∣ x.1 := hq.dvd_of_dvd_pow hxq
    have hq1 : q = x.1 := (Nat.prime_dvd_prime_iff_eq hq hxp).mp hqx
    rw [hq1, Ne, cast_pow_eq_one_iff h2]
    have hlt2 : (E.n - 1) / x.1 < 2 ^ 128 := lt_of_le_of_lt (Nat.div_le_self _ _) hlt
    rw [← powMod_eq hlt2]
    exact hne x hx

theorem checkAll_sound : ∀ (cert : List Entry) (known : List ℕ),
    checkAll cert known = true → (∀ x ∈ known, x.Prime) → ∀ E ∈ cert, E.n.Prime
  | [], _, _, _, E, hE => absurd hE List.not_mem_nil
  | E0 :: t, known, h, hk, E, hE => by
    simp only [checkAll, Bool.and_eq_true] at h
    have h0 := checkEntry_sound hk h.1
    rcases List.mem_cons.mp hE with rfl | hE
    · exact h0
    · exact checkAll_sound t (E0.n :: known) h.2
        (fun x hx => by
          rcases List.mem_cons.mp hx with rfl | hx
          · exact h0
          · exact hk x hx) E hE

/-- Soundness, packaged: a passing certificate (with `2` the only assumed prime) certifies
every `n` it lists. -/
theorem prime_of_cert {cert : List Entry} (h : checkAll cert [2] = true) {n : ℕ}
    (hn : n ∈ cert.map Entry.n) : n.Prime := by
  obtain ⟨E, hE, rfl⟩ := List.mem_map.mp hn
  exact checkAll_sound cert [2] h (by simp [Nat.prime_two]) E hE

/-! ## Divisor count of a factored number -/

theorem coprime_prodPow {f : ℕ} (hf : f.Prime) :
    ∀ fs : List (ℕ × ℕ), (∀ x ∈ fs, x.1.Prime) → (∀ x ∈ fs, x.1 ≠ f) → Nat.Coprime f (prodPow fs)
  | [], _, _ => by simp [prodPow]
  | x :: t, hp, hne => by
    simp only [prodPow, List.foldr_cons]
    refine Nat.Coprime.mul_right ?_ ?_
    · exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hf (hp x List.mem_cons_self)).mpr
        (fun h => hne x List.mem_cons_self h.symm))
    · exact coprime_prodPow hf t (fun y hy => hp y (List.mem_cons_of_mem _ hy))
        (fun y hy => hne y (List.mem_cons_of_mem _ hy))

/-- `τ(∏ fᵢ^kᵢ) = ∏ (kᵢ + 1)` for distinct primes `fᵢ`. -/
theorem card_divisors_prodPow :
    ∀ fs : List (ℕ × ℕ), (∀ x ∈ fs, x.1.Prime) → (fs.map Prod.fst).Nodup →
      (prodPow fs).divisors.card = (fs.map fun x => x.2 + 1).prod
  | [], _, _ => by simp [prodPow]
  | x :: t, hp, hnd => by
    have hxp : x.1.Prime := hp x List.mem_cons_self
    have hnd' : (x.1 :: t.map Prod.fst).Nodup := hnd
    have hcop : Nat.Coprime (x.1 ^ x.2) (prodPow t) := by
      refine Nat.Coprime.pow_left _ (coprime_prodPow hxp t
        (fun y hy => hp y (List.mem_cons_of_mem _ hy)) ?_)
      intro y hy hyx
      exact (List.nodup_cons.mp hnd').1 (List.mem_map.mpr ⟨y, hy, hyx⟩)
    have ht : (t.map Prod.fst).Nodup := (List.nodup_cons.mp hnd').2
    have e : prodPow (x :: t) = x.1 ^ x.2 * prodPow t := rfl
    rw [e, Nat.Coprime.card_divisors_mul hcop,
      card_divisors_prodPow t (fun y hy => hp y (List.mem_cons_of_mem _ hy)) ht,
      ← ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply_prime_pow hxp]
    simp

/-! ## Crude divisor bound -/

/-- `τ(n) ≤ 2 √n`: divisors above `√n` map injectively (`d ↦ n / d`) to divisors `≤ √n`. -/
theorem card_divisors_le_two_mul_sqrt (n : ℕ) : n.divisors.card ≤ 2 * Nat.sqrt n := by
  classical
  by_cases hn : n = 0
  · subst hn; simp
  set s := Nat.sqrt n with hs
  have hsq : n < (s + 1) * (s + 1) := Nat.lt_succ_sqrt n
  have hD1 : (n.divisors.filter (· ≤ s)).card ≤ s := by
    calc (n.divisors.filter (· ≤ s)).card ≤ (Finset.Icc 1 s).card := by
          apply Finset.card_le_card
          intro d hd
          simp only [Finset.mem_filter, Nat.mem_divisors] at hd
          simp only [Finset.mem_Icc]
          exact ⟨Nat.pos_of_dvd_of_pos hd.1.1 (Nat.pos_of_ne_zero hn), hd.2⟩
      _ = s := by simp
  have hD2 : (n.divisors.filter (fun d => ¬ d ≤ s)).card ≤ s := by
    calc (n.divisors.filter (fun d => ¬ d ≤ s)).card
        ≤ (n.divisors.filter (· ≤ s)).card := by
          apply Finset.card_le_card_of_injOn (fun d => n / d)
          · intro d hd
            simp only [Finset.coe_filter, Nat.mem_divisors, Set.mem_setOf_eq] at hd ⊢
            obtain ⟨⟨hdn, _⟩, hds⟩ := hd
            refine ⟨⟨Nat.div_dvd_of_dvd hdn, hn⟩, ?_⟩
            by_contra hc
            push Not at hc
            obtain ⟨c, hc'⟩ := hdn
            have hdpos : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hc'; exact hn hc')
            have : n / d = c := by rw [hc']; exact Nat.mul_div_cancel_left c hdpos
            rw [this] at hc
            have h1 : (s + 1) * (s + 1) ≤ d * c := Nat.mul_le_mul (by omega) (by omega)
            omega
          · intro d hd e he hde
            simp only [Finset.coe_filter, Nat.mem_divisors, Set.mem_setOf_eq] at hd he
            have := Nat.div_div_self hd.1.1 hn
            have h2 := Nat.div_div_self he.1.1 hn
            simp only at hde
            rw [← this, ← h2, hde]
      _ ≤ s := hD1
  have := Finset.card_filter_add_card_filter_not (s := n.divisors) (· ≤ s)
  omega

end Nock.Primality

