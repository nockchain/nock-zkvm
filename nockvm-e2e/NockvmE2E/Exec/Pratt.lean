/-
  NockvmE2E/Exec/Pratt.lean

  Source: the nockvm library, Nock/Primality/Pratt.lean (lines up to "Divisor count", unchanged) and
  Nock/Primality/GoldilocksCore.lean (certificate + `goldilocks_prime_nat`), merged into one module, namespace
  renamed.  Kernel-checked Pratt/Lucas certificate for the Goldilocks prime (`decide +kernel`, no `native_decide`).
-/
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.NumberTheory.ArithmeticFunction.Misc

set_option autoImplicit false

namespace NockvmE2E.Exec.Primality

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
      simp only [powModAux, h0, ite_false, key, h1]
      by_cases hm : e % 2 = 1
      · simp only [hm, ite_true]
        obtain ⟨k, hk⟩ : ∃ k, e = 2 * k + 1 := ⟨e / 2, by omega⟩
        have hk2 : e / 2 = k := by omega
        have hpow : b ^ e = b * (b * b) ^ k := by rw [hk, pow_succ, pow_mul, sq]; ring
        rw [hk2, hpow, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
      · simp only [hm, ite_false]
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

def goldilocksCert : List Entry := [
  ⟨3, 2, [(2, 1)]⟩,
  ⟨5, 2, [(2, 2)]⟩,
  ⟨17, 3, [(2, 4)]⟩,
  ⟨257, 3, [(2, 8)]⟩,
  ⟨65537, 3, [(2, 16)]⟩,
  ⟨18446744069414584321, 7, [(2, 32), (3, 1), (5, 1), (17, 1), (257, 1), (65537, 1)]⟩,
  ⟨13, 2, [(2, 2), (3, 1)]⟩,
  ⟨937, 5, [(2, 3), (3, 2), (13, 1)]⟩,
  ⟨7, 3, [(2, 1), (3, 1)]⟩,
  ⟨43, 3, [(2, 1), (3, 1), (7, 1)]⟩,
  ⟨53, 2, [(2, 2), (13, 1)]⟩,
  ⟨724723, 2, [(2, 1), (3, 1), (43, 1), (53, 2)]⟩,
  ⟨97, 5, [(2, 5), (3, 1)]⟩,
  ⟨5821, 6, [(2, 2), (3, 1), (5, 1), (97, 1)]⟩,
  ⟨37, 2, [(2, 2), (3, 2)]⟩,
  ⟨14431, 3, [(2, 1), (3, 1), (5, 1), (13, 1), (37, 1)]⟩,
  ⟨1039033, 10, [(2, 3), (3, 2), (14431, 1)]⟩,
  ⟨19, 2, [(2, 1), (3, 2)]⟩,
  ⟨113, 3, [(2, 4), (7, 1)]⟩,
  ⟨227, 2, [(2, 1), (113, 1)]⟩,
  ⟨8627, 2, [(2, 1), (19, 1), (227, 1)]⟩,
  ⟨11, 2, [(2, 1), (5, 1)]⟩,
  ⟨73, 5, [(2, 3), (3, 2)]⟩,
  ⟨107, 2, [(2, 1), (53, 1)]⟩,
  ⟨29, 2, [(2, 2), (7, 1)]⟩,
  ⟨233, 3, [(2, 3), (29, 1)]⟩,
  ⟨467, 2, [(2, 1), (233, 1)]⟩,
  ⟨3852010273, 5, [(2, 5), (3, 1), (11, 1), (73, 1), (107, 1), (467, 1)]⟩,
  ⟨11365102077808483, 3, [(2, 1), (3, 2), (19, 1), (8627, 1), (3852010273, 1)]⟩,
  ⟨167034643597991036904547663171, 2, [(2, 1), (3, 5), (5, 1), (5821, 1), (1039033, 1), (11365102077808483, 1)]⟩]


theorem goldilocksCert_ok : checkAll goldilocksCert [2] = true := by decide +kernel

theorem cert_prime {n : ℕ} (hn : n ∈ goldilocksCert.map Entry.n) : n.Prime :=
  prime_of_cert goldilocksCert_ok hn

/-- **`2^64 - 2^32 + 1` is prime**, in the kernel, numeral form (no `Nock.Field`). -/
theorem goldilocks_prime_nat : Nat.Prime (2 ^ 64 - 2 ^ 32 + 1) := by
  have h : (18446744069414584321 : ℕ) ∈ goldilocksCert.map Entry.n := by decide +kernel
  have := cert_prime h
  norm_num
  exact this
end NockvmE2E.Exec.Primality
