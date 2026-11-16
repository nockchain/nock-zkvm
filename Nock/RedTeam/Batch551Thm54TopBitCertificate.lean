/-
  Nock/RedTeam/Batch551Thm54TopBitCertificate.lean

  **Items B / B' / B3: the top-bit certificate is sound in both realizations; the
  completeness side condition `axis < 2^63` is NEW (not given by `hs`/`hf`/`hΛp`).**

  With boolean bits exactly one term survives: `T = λ^m` at the top set bit
  (`Tcert_top`), `T = 0` when `a = 0` (`Tcert_zero`); `a_λ = λ^m + Σ_{i<m} bᵢλⁱ` (`aCert_top`).

  (i') one-hot activation: `Σ tᵢ = 1`, `tᵢ(1−tᵢ) = 0`, `tᵢ(1−bᵢ) = 0`, `bᵢ·Σ_{j<i} tⱼ = 0`.
  `oneHot_forces` proves on the COMMITTED columns: `t` is the one-hot of a top index `m`,
  `b_m = 1`, `b_{>m} = 0` — under the one arithmetic condition the gates need, that a sum of at
  most `n` ones is nonzero in `𝔽` (`char 𝔽 > n`; Goldilocks at `n ≤ 63`).  `Σ tᵢ = 1` then forces
  `a ≥ 2^m ≥ 1`: `a = 0` is rejected OUTRIGHT (`oneHot_axis_pos`), unlike (i) where `T = 0`.
  Every gate of (i') has degree ≤ 2 (`Σ tᵢ − 1`: 1; the three products: 2).

  B3: `slot_bound` — a resolvable axis satisfies `a < 2^{depth(subject)+1}`, so `depth ≤ 62`
  gives `a < 2^63` (`axis_lt_two_pow_63_of_depth`).
-/
import Mathlib.Data.ZMod.Basic
import Nock.Field
import Nock.Reference
import Nock.FieldEmbedding
import Nock.RedTeam.Batch548Thm54LambdaCertificate

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch551

open scoped Classical

variable {K : Type*} [Field K]

/-! ## (i) — suffix helpers and `T = Σ λⁱ bᵢ sᵢ` -/

/-- `sᵢ = Π_{i<j<n} (1 − bⱼ)`: "no bit above `i` is set". -/
def sProd (b : ℕ → K) (n i : ℕ) : K := ∏ j ∈ Finset.Ico (i + 1) n, (1 - b j)

/-- The certified top-bit power `T = Σ_{i<n} λⁱ·bᵢ·sᵢ`. -/
def Tcert (l : K) (b : ℕ → K) (n : ℕ) : K := ∑ i ∈ Finset.range n, l ^ i * b i * sProd b n i

/-- The in-gate certified axis `a_λ = Σ_{i<n} bᵢ·λⁱ`. -/
def aCert (l : K) (b : ℕ → K) (n : ℕ) : K := ∑ i ∈ Finset.range n, b i * l ^ i

theorem sProd_top (b : ℕ → K) (n : ℕ) : sProd b n n = 1 := by
  simp [sProd, Finset.Ico_eq_empty_of_le]

/-- One chain step (`s_i = (1 − b_{i+1})·s_{i+1}`). -/
theorem sProd_step (b : ℕ → K) (n i : ℕ) (h : i + 1 < n) :
    sProd b n i = (1 - b (i + 1)) * sProd b n (i + 1) := by
  unfold sProd
  rw [Finset.prod_eq_prod_Ico_succ_bot h]

/-- The brief's 3-stepped committed chain is three chain steps. -/
theorem chain3 (b : ℕ → K) (n k : ℕ) (h : 3 * k + 3 < n) :
    sProd b n (3 * k)
      = (1 - b (3 * k + 1)) * (1 - b (3 * k + 2)) * (1 - b (3 * k + 3)) * sProd b n (3 * k + 3) := by
  rw [sProd_step b n (3 * k) (by omega), sProd_step b n (3 * k + 1) (by omega),
    sProd_step b n (3 * k + 2) (by omega)]
  ring

theorem sProd_of_zero_above (b : ℕ → K) (n i : ℕ) (h : ∀ j, i < j → j < n → b j = 0) :
    sProd b n i = 1 := by
  unfold sProd
  apply Finset.prod_eq_one
  intro j hj
  rw [Finset.mem_Ico] at hj
  rw [h j (by omega) hj.2]; ring

theorem sProd_of_one_above (b : ℕ → K) (n i j : ℕ) (hij : i < j) (hj : j < n) (hbj : b j = 1) :
    sProd b n i = 0 := by
  unfold sProd
  apply Finset.prod_eq_zero (i := j)
  · rw [Finset.mem_Ico]; omega
  · rw [hbj]; ring

/-- **`T = λ^m`** when `b_m = 1` and every higher bit is `0` (boolean bits). -/
theorem Tcert_top (l : K) (b : ℕ → K) (n m : ℕ)
    (hm : m < n) (hbm : b m = 1) (habove : ∀ j, m < j → j < n → b j = 0) :
    Tcert l b n = l ^ m := by
  unfold Tcert
  rw [Finset.sum_eq_single m]
  · rw [hbm, sProd_of_zero_above b n m habove]; ring
  · intro i hi hne
    rw [Finset.mem_range] at hi
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · rw [sProd_of_one_above b n i m h hm hbm]; ring
    · rw [habove i h hi]; ring
  · intro h; exact absurd (Finset.mem_range.mpr hm) h

/-- `a = 0` gives `T = 0`. -/
theorem Tcert_zero (l : K) (b : ℕ → K) (n : ℕ) (h0 : ∀ i < n, b i = 0) : Tcert l b n = 0 := by
  unfold Tcert
  apply Finset.sum_eq_zero
  intro i hi
  rw [h0 i (Finset.mem_range.mp hi)]; ring

/-- `a_λ = λ^m + Σ_{i<m} bᵢλⁱ` under the same hypotheses. -/
theorem aCert_top (l : K) (b : ℕ → K) (n m : ℕ)
    (hm : m < n) (hbm : b m = 1) (habove : ∀ j, m < j → j < n → b j = 0) :
    aCert l b n = l ^ m + ∑ i ∈ Finset.range m, b i * l ^ i := by
  unfold aCert
  rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le m) hm.le,
    Finset.sum_eq_sum_Ico_succ_bot hm, hbm, ← Finset.range_eq_Ico]
  have : ∑ i ∈ Finset.Ico (m + 1) n, b i * l ^ i = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_Ico] at hi
    rw [habove i (by omega) hi.2]; ring
  rw [this]; ring

/-- Booleanity on a committed column is exactly `b ∈ {0, 1}`. -/
theorem booleanity_iff (x : K) : x * (1 - x) = 0 ↔ x = 0 ∨ x = 1 := by
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h).symm
  · rintro (rfl | rfl) <;> ring

/-! ## (i') — one-hot activation -/

/-- The four gates of variant (i') plus the bit booleanity of (i), on committed columns
`b`, `t` over `Fin n`. -/
structure OneHot (n : ℕ) (b t : ℕ → K) : Prop where
  bBool : ∀ i < n, b i * (1 - b i) = 0
  tBool : ∀ i < n, t i * (1 - t i) = 0
  tSum : ∑ i ∈ Finset.range n, t i = 1
  tImp : ∀ i < n, t i * (1 - b i) = 0
  bAbove : ∀ i < n, b i * ∑ j ∈ Finset.range i, t j = 0

/-- A sum of boolean values is the cast of a count. -/
theorem sum_bool_eq_card (t : ℕ → K) (s : Finset ℕ) (ht : ∀ i ∈ s, t i = 0 ∨ t i = 1) :
    ∑ i ∈ s, t i = ((s.filter fun i => t i = 1).card : K) := by
  rw [← Finset.sum_boole]
  apply Finset.sum_congr rfl
  intro i hi
  rcases ht i hi with h | h
  · rw [h]; simp
  · rw [h]; simp

/-- **B': the four gates force the one-hot of the top set bit on the committed columns.**
Arithmetic condition: a nonzero count of at most `n` ones is nonzero in `𝔽`
(`hcast`; true whenever `char 𝔽 > n`). -/
theorem oneHot_forces (n : ℕ) (b t : ℕ → K) (h : OneHot n b t)
    (hcast : ∀ k ≤ n, (k : K) = 0 → k = 0) :
    ∃ m < n, t m = 1 ∧ (∀ i < n, i ≠ m → t i = 0) ∧ b m = 1
      ∧ ∀ i, m < i → i < n → b i = 0 := by
  have htb : ∀ i < n, t i = 0 ∨ t i = 1 := fun i hi => (booleanity_iff _).mp (h.tBool i hi)
  have hbb : ∀ i < n, b i = 0 ∨ b i = 1 := fun i hi => (booleanity_iff _).mp (h.bBool i hi)
  -- a `t = 1` forces `b = 1` there
  have himp : ∀ i < n, t i = 1 → b i = 1 := by
    intro i hi hti
    have := h.tImp i hi
    rw [hti, one_mul] at this
    exact (sub_eq_zero.mp this).symm
  -- a set `t` below `i` forces `b i = 0`
  have hbelow : ∀ i < n, ∀ j < i, t j = 1 → b i = 0 := by
    intro i hi j hj htj
    have hsum := h.bAbove i hi
    rw [sum_bool_eq_card t (Finset.range i) (fun k hk =>
      htb k (lt_trans (Finset.mem_range.mp hk) hi))] at hsum
    rcases mul_eq_zero.mp hsum with hb0 | hc
    · exact hb0
    · exfalso
      set S := (Finset.range i).filter (fun k => t k = 1) with hS
      have hle : S.card ≤ n := le_trans (Finset.card_filter_le _ _)
        (by rw [Finset.card_range]; exact hi.le)
      have hcard : S.card = 0 := hcast S.card hle (by exact_mod_cast hc)
      have hmem : j ∈ S := by
        rw [hS, Finset.mem_filter, Finset.mem_range]; exact ⟨hj, htj⟩
      rw [Finset.card_eq_zero] at hcard
      rw [hcard] at hmem
      exact absurd hmem (Finset.notMem_empty j)
  -- existence of a set `t`
  have hex : ∃ m < n, t m = 1 := by
    by_contra hno
    have h0 : ∀ i < n, t i = 0 := fun i hi =>
      (htb i hi).resolve_right (fun h1 => hno ⟨i, hi, h1⟩)
    have := h.tSum
    rw [Finset.sum_eq_zero (fun i hi => h0 i (Finset.mem_range.mp hi))] at this
    exact zero_ne_one this
  obtain ⟨m, hm, htm⟩ := hex
  refine ⟨m, hm, htm, ?_, himp m hm htm, ?_⟩
  · -- uniqueness: two set `t`'s contradict `bAbove` at the higher one
    intro i hi hne
    rcases htb i hi with h0 | h1
    · exact h0
    · exfalso
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      · have := hbelow m hm i hlt h1
        rw [himp m hm htm] at this
        exact one_ne_zero this
      · have := hbelow i hi m hgt htm
        rw [himp i hi h1] at this
        exact one_ne_zero this
  · intro i hmi hi
    exact hbelow i hi m hmi htm

/-- (i') `T = Σ λⁱ tᵢ = λ^m` and `a_λ = λ^m + Σ_{i<m} bᵢλⁱ`. -/
theorem oneHot_T (l : K) (n : ℕ) (b t : ℕ → K) (h : OneHot n b t)
    (hcast : ∀ k ≤ n, (k : K) = 0 → k = 0) :
    ∃ m < n, (∑ i ∈ Finset.range n, l ^ i * t i) = l ^ m
      ∧ aCert l b n = l ^ m + ∑ i ∈ Finset.range m, b i * l ^ i := by
  obtain ⟨m, hm, htm, huniq, hbm, habove⟩ := oneHot_forces n b t h hcast
  refine ⟨m, hm, ?_, aCert_top l b n m hm hbm habove⟩
  rw [Finset.sum_eq_single m]
  · rw [htm, mul_one]
  · intro i hi hne
    rw [huniq i (Finset.mem_range.mp hi) hne, mul_zero]
  · intro h; exact absurd (Finset.mem_range.mpr hm) h

/-- (i') rejects `a = 0` outright: the certified integer is at least `2^m ≥ 1`, so with
`2^n ≤ p` its residue is nonzero. -/
theorem oneHot_axis_pos (n : ℕ) (b t : ℕ → K) (h : OneHot n b t)
    (hcast : ∀ k ≤ n, (k : K) = 0 → k = 0) :
    ∃ m < n, 2 ^ m ≤ Batch548.bitSum (fun i => decide (b i = 1)) n := by
  obtain ⟨m, hm, _, _, hbm, _⟩ := oneHot_forces n b t h hcast
  refine ⟨m, hm, ?_⟩
  unfold Batch548.bitSum
  calc 2 ^ m = (decide (b m = 1)).toNat * 2 ^ m := by rw [hbm]; simp
    _ ≤ ∑ i ∈ Finset.range n, (decide (b i = 1)).toNat * 2 ^ i :=
        Finset.single_le_sum (f := fun i => (decide (b i = 1)).toNat * 2 ^ i)
          (fun i _ => Nat.zero_le _) (Finset.mem_range.mpr hm)

/-- On Goldilocks the arithmetic condition holds for `n ≤ 63` (indeed for `n < p`). -/
theorem goldilocks_cast_condition (n : ℕ) (hn : n < Nock.Field.p) :
    ∀ k ≤ n, ((k : ℕ) : ZMod Nock.Field.p) = 0 → k = 0 := by
  intro k hk h0
  haveI : NeZero Nock.Field.p := ⟨by rw [Nock.Field.p_eq]; norm_num⟩
  rw [ZMod.natCast_eq_zero_iff] at h0
  exact Nat.eq_zero_of_dvd_of_lt h0 (by omega)

/-! ## B3 — the completeness side condition `a < 2^63` -/

/-- Depth of a noun (atoms have depth `0`). -/
def depth : Noun → ℕ
  | .atom _ => 0
  | .cell l r => max (depth l) (depth r) + 1

/-- A resolvable axis is bounded by the subject's depth: `(a + 1)·2^{depth x} ≤ 2^{depth s + 1}`
whenever `slot a s = some x`. -/
theorem slot_depth_bound (a : ℕ) :
    ∀ (s x : Noun), Noun.slot a s = some x → (a + 1) * 2 ^ depth x ≤ 2 ^ (depth s + 1) := by
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    intro s x hsx
    match a, hsx with
    | 0, h => simp [Noun.slot] at h
    | 1, h =>
        simp only [Noun.slot, Option.some.injEq] at h
        subst h; rw [pow_succ]; omega
    | k + 2, h =>
        rw [Noun.slot] at h
        rcases hq : Noun.slot ((k + 2) / 2) s with _ | q
        · rw [hq] at h; simp at h
        · rw [hq] at h
          cases q with
          | atom _ => simp at h
          | cell l r =>
              simp only [Option.some.injEq] at h
              have hih := ih ((k + 2) / 2) (by omega) s (Noun.cell l r) hq
              simp only [depth] at hih
              have hdl : 2 ^ (depth l + 1) ≤ 2 ^ (max (depth l) (depth r) + 1) :=
                Nat.pow_le_pow_right (by norm_num) (by omega)
              have hdr : 2 ^ (depth r + 1) ≤ 2 ^ (max (depth l) (depth r) + 1) :=
                Nat.pow_le_pow_right (by norm_num) (by omega)
              have hq2 : k + 2 + 1 ≤ 2 * ((k + 2) / 2 + 1) := by omega
              split_ifs at h with hpar
              · subst h
                calc (k + 2 + 1) * 2 ^ depth l
                    ≤ 2 * ((k + 2) / 2 + 1) * 2 ^ depth l := Nat.mul_le_mul_right _ hq2
                  _ = ((k + 2) / 2 + 1) * 2 ^ (depth l + 1) := by rw [pow_succ]; ring
                  _ ≤ ((k + 2) / 2 + 1) * 2 ^ (max (depth l) (depth r) + 1) :=
                      Nat.mul_le_mul_left _ hdl
                  _ ≤ 2 ^ (depth s + 1) := hih
              · subst h
                calc (k + 2 + 1) * 2 ^ depth r
                    ≤ 2 * ((k + 2) / 2 + 1) * 2 ^ depth r := Nat.mul_le_mul_right _ hq2
                  _ = ((k + 2) / 2 + 1) * 2 ^ (depth r + 1) := by rw [pow_succ]; ring
                  _ ≤ ((k + 2) / 2 + 1) * 2 ^ (max (depth l) (depth r) + 1) :=
                      Nat.mul_le_mul_left _ hdr
                  _ ≤ 2 ^ (depth s + 1) := hih

/-- `slot a s = some x → a < 2^{depth s + 1}`. -/
theorem slot_bound (a : ℕ) (s x : Noun) (h : Noun.slot a s = some x) :
    a < 2 ^ (depth s + 1) := by
  have := slot_depth_bound a s x h
  have h1 : (a + 1) * 1 ≤ (a + 1) * 2 ^ depth x :=
    Nat.mul_le_mul_left _ (Nat.one_le_two_pow)
  omega

/-- Subjects of depth `≤ 62` make every resolvable axis a `63`-bit integer. -/
theorem axis_lt_two_pow_63_of_depth (a : ℕ) (s x : Noun) (h : Noun.slot a s = some x)
    (hd : depth s ≤ 62) : a < 2 ^ 63 :=
  lt_of_lt_of_le (slot_bound a s x h) (Nat.pow_le_pow_right (by norm_num) (by omega))

/-- The tree's noun bound `BoundedBy p` (`hs`/`hf`) does NOT give it: `2^63` itself is an
admissible atom below Goldilocks `p`. -/
theorem boundedBy_does_not_give_63 :
    Nock.FieldEmbedding.BoundedBy Nock.Field.p (Noun.atom (2 ^ 63)) ∧ ¬ (2 ^ 63 < 2 ^ 63) := by
  refine ⟨?_, lt_irrefl _⟩
  show 2 ^ 63 < Nock.Field.p
  exact Batch548.goldilocks_63_below_p

end Nock.RedTeam.Batch551

#print axioms Nock.RedTeam.Batch551.Tcert_top
#print axioms Nock.RedTeam.Batch551.Tcert_zero
#print axioms Nock.RedTeam.Batch551.chain3
#print axioms Nock.RedTeam.Batch551.oneHot_forces
#print axioms Nock.RedTeam.Batch551.oneHot_T
#print axioms Nock.RedTeam.Batch551.oneHot_axis_pos
#print axioms Nock.RedTeam.Batch551.slot_bound
#print axioms Nock.RedTeam.Batch551.boundedBy_does_not_give_63
