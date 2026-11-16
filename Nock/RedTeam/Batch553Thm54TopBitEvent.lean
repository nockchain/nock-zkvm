/-
  Nock/RedTeam/Batch553Thm54TopBitEvent.lean

  **Item E (the bad `(α, λ)` set of the many-record identity) and the `a = 0` hole of
  the cheaper reversed alternative.**

  Item E.  If some `Q_{k₀} ≠ 0` as a
  polynomial in `λ` then `#{(α, λ) : F(α, λ) = 0} ≤ |𝕂|·(deg Q_{k₀} + E)` with `E` the largest
  exponent (`bad_card_le`): the `λ` with `Q_{k₀}(λ) = 0` are at most `deg Q_{k₀}` (times all `α`),
  and at every other `λ` the polynomial `F(·, λ)` is nonzero of degree `≤ E`.  Probability
  `≤ (deg Q + E)/|𝕂|` with `deg Q ≤ depth + n` and `E ≤ 3N + 3`.  Conversely `F = 0` as a
  bivariate polynomial iff every `Q_k = 0` (`forest_zero_iff`), which is item D record by record.

  The reversed alternative (`ind` kept, read wrapper `(−ã·ts, −ts)`, `ã` the bit-REVERSED
  certificate, no `T`, no `E`) is also sound record by record
  (`Batch552.identity_forces_ancestry_reversed`) and exact per root (`rev_honest_exact`) — but
  `a = 0` (`ã = 0`) is NOT self-rejecting there: a verify at a node whose RIGHT child carries the
  read wrapper has both boundaries identically zero (`rev_zero_axis_accepted`).
-/
import Nock.RedTeam.Batch548Thm54LambdaCertificate
import Nock.RedTeam.Batch552Thm54TopBitAncestry

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch553

open Nock
open Nock.AxisBatching
open Nock.AxisBatching.MTree
open Nock.RedTeam.Batch550 (embed revAddr)
open Polynomial

/-! ## Item E — the bad set of `F(α, λ) = Σ_k α^{e_k}·Q_k(λ)` -/

section Event

variable {K : Type*} [Field K] {ι : Type*} [DecidableEq ι]

/-- The forest identity at the coins `(α, λ)`. -/
noncomputable def forestF (s : Finset ι) (e : ι → ℕ) (Q : ι → K[X]) (α l : K) : K :=
  ∑ k ∈ s, α ^ e k * (Q k).eval l

/-- `F(·, λ)` as a polynomial in `α`. -/
noncomputable def alphaPoly (s : Finset ι) (e : ι → ℕ) (Q : ι → K[X]) (l : K) : K[X] :=
  ∑ k ∈ s, C ((Q k).eval l) * X ^ e k

theorem alphaPoly_eval (s : Finset ι) (e : ι → ℕ) (Q : ι → K[X]) (l α : K) :
    (alphaPoly s e Q l).eval α = forestF s e Q α l := by
  unfold alphaPoly forestF
  rw [eval_finset_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [eval_mul, eval_C, eval_pow, eval_X, mul_comm]

/-- With distinct exponents the `α^{e_k}` coefficient of `F(·, λ)` is `Q_k(λ)`. -/
theorem alphaPoly_coeff (s : Finset ι) (e : ι → ℕ) (Q : ι → K[X]) (l : K)
    (hinj : Set.InjOn e s) (k₀ : ι) (hk₀ : k₀ ∈ s) :
    (alphaPoly s e Q l).coeff (e k₀) = (Q k₀).eval l := by
  simp only [alphaPoly, finsetSum_coeff, coeff_C_mul, coeff_X_pow]
  rw [Finset.sum_eq_single k₀]
  · simp
  · intro k hk hne
    have : e k₀ ≠ e k := fun h => hne (hinj hk hk₀ h.symm)
    simp [this]
  · intro h; exact absurd hk₀ h

theorem alphaPoly_natDegree_le (s : Finset ι) (e : ι → ℕ) (Q : ι → K[X]) (l : K) (E : ℕ)
    (hE : ∀ k ∈ s, e k ≤ E) : (alphaPoly s e Q l).natDegree ≤ E := by
  unfold alphaPoly
  apply natDegree_sum_le_of_forall_le
  intro k hk
  exact le_trans (natDegree_C_mul_X_pow_le _ _) (hE k hk)

/-- `F = 0` as a bivariate polynomial iff every record's `Q_k = 0`: with distinct exponents the
records do not interfere (grouping by timestamp is exact). -/
theorem forest_zero_iff (s : Finset ι) (e : ι → ℕ) (Q : ι → K[X]) (hinj : Set.InjOn e s) :
    (∀ l : K, alphaPoly s e Q l = 0) ↔ ∀ k ∈ s, ∀ l : K, (Q k).eval l = 0 := by
  constructor
  · intro h k hk l
    rw [← alphaPoly_coeff s e Q l hinj k hk, h l, coeff_zero]
  · intro h l
    unfold alphaPoly
    apply Finset.sum_eq_zero
    intro k hk
    rw [h k hk l, C_0, zero_mul]

variable [Fintype K] [DecidableEq K]

/-- **The bad set.**  If some `Q_{k₀} ≠ 0` then at most `|𝕂|·(deg Q_{k₀} + E)` coin pairs
`(α, λ)` satisfy the forest identity. -/
theorem bad_card_le (s : Finset ι) (e : ι → ℕ) (Q : ι → K[X]) (E : ℕ)
    (hinj : Set.InjOn e s) (hE : ∀ k ∈ s, e k ≤ E)
    (k₀ : ι) (hk₀ : k₀ ∈ s) (hQ : Q k₀ ≠ 0) :
    (Finset.univ.filter fun p : K × K => forestF s e Q p.1 p.2 = 0).card
      ≤ Fintype.card K * ((Q k₀).natDegree + E) := by
  set bad := Finset.univ.filter fun p : K × K => forestF s e Q p.1 p.2 = 0 with hbad
  -- split by whether `Q_{k₀}(λ) = 0`
  have hsplit : bad ⊆ (Finset.univ ×ˢ (Q k₀).roots.toFinset)
      ∪ (Finset.univ : Finset K).biUnion
          (fun l => ((alphaPoly s e Q l).roots.toFinset).image (fun α => (α, l))) := by
    intro p hp
    rw [hbad, Finset.mem_filter] at hp
    obtain ⟨_, hF⟩ := hp
    rw [Finset.mem_union]
    by_cases hz : (Q k₀).eval p.2 = 0
    · left
      rw [Finset.mem_product, Multiset.mem_toFinset, mem_roots hQ]
      exact ⟨Finset.mem_univ _, hz⟩
    · right
      rw [Finset.mem_biUnion]
      refine ⟨p.2, Finset.mem_univ _, ?_⟩
      rw [Finset.mem_image]
      refine ⟨p.1, ?_, rfl⟩
      have hne : alphaPoly s e Q p.2 ≠ 0 := by
        intro h0
        apply hz
        rw [← alphaPoly_coeff s e Q p.2 hinj k₀ hk₀, h0, coeff_zero]
      rw [Multiset.mem_toFinset, mem_roots hne, IsRoot.def, alphaPoly_eval]
      exact hF
  calc bad.card
      ≤ ((Finset.univ ×ˢ (Q k₀).roots.toFinset)
          ∪ (Finset.univ : Finset K).biUnion
              (fun l => ((alphaPoly s e Q l).roots.toFinset).image (fun α => (α, l)))).card :=
        Finset.card_le_card hsplit
    _ ≤ (Finset.univ ×ˢ (Q k₀).roots.toFinset).card
          + ((Finset.univ : Finset K).biUnion
              (fun l => ((alphaPoly s e Q l).roots.toFinset).image (fun α => (α, l)))).card :=
        Finset.card_union_le _ _
    _ ≤ Fintype.card K * (Q k₀).natDegree + Fintype.card K * E := by
        apply Nat.add_le_add
        · rw [Finset.card_product, Finset.card_univ]
          apply Nat.mul_le_mul_left
          exact le_trans (Multiset.toFinset_card_le _) (card_roots' _)
        · calc ((Finset.univ : Finset K).biUnion
                (fun l => ((alphaPoly s e Q l).roots.toFinset).image (fun α => (α, l)))).card
              ≤ ∑ l ∈ (Finset.univ : Finset K),
                  (((alphaPoly s e Q l).roots.toFinset).image (fun α => (α, l))).card :=
                Finset.card_biUnion_le
            _ ≤ ∑ _l ∈ (Finset.univ : Finset K), E := by
                apply Finset.sum_le_sum
                intro l _
                exact le_trans Finset.card_image_le
                  (le_trans (Multiset.toFinset_card_le _)
                    (le_trans (card_roots' _) (alphaPoly_natDegree_le s e Q l E hE)))
            _ = Fintype.card K * E := by simp [Finset.card_univ]
    _ = Fintype.card K * ((Q k₀).natDegree + E) := by ring

end Event

/-! ## The reversed alternative: sound per record, exact per root, but `a = 0` is accepted -/

section Reversed

variable {K : Type*} [Field K]

/-- The reversed alternative on `MTree`: the paper's `ind` (verify `+ts`, read `−ts`), the
ascending `counts_P = λ·(counts_L + counts_R) + ind_R`, the verify adds `ts`, the read wrapper
subtracts `ã·ts` (`ã` keyed by the exponent). -/
noncomputable def countsR (l : K) (A : ℕ → K) : MTree K → K[X]
  | .halt => 0
  | .decompose L R => C l * (countsR l A L + countsR l A R) + indP R
  | .read e c => countsR l A c - C (A e) * X ^ e
  | .verify e _ c => countsR l A c + X ^ e

theorem indP_embed (p : List Bool) (t : MTree K) : indP (embed p t) = indP t := by
  induction p with
  | nil => rfl
  | cons e p ih =>
      cases e <;> simp [embed, indP, ih, pwScale, MemoryTable.pwScaleExp]

theorem countsR_embed (l : K) (A : ℕ → K) (p : List Bool) (t : MTree K) :
    countsR l A (embed p t)
      = C (l ^ p.length) * countsR l A t + C (revAddr l p - l ^ p.length) * indP t := by
  induction p with
  | nil => simp [embed, revAddr]
  | cons e p ih =>
      cases e
      · simp only [embed, countsR, indP, ih, revAddr, List.length_cons, pwScale,
          MemoryTable.pwScaleExp]
        simp only [Bool.false_eq_true, if_false, add_zero, C_mul, C_sub, C_pow, pow_succ, C_1]
        ring
      · simp only [embed, countsR, ih, revAddr, List.length_cons, indP_embed]
        simp only [if_true, C_mul, C_sub, C_add, C_pow, C_1, pow_succ]
        ring

/-- Exact per root for every `λ`: read wrapper at path `q`, verify at `q ++ p` below it,
`ã = revAddr p` (the reversed certificate of the relative path). -/
theorem rev_honest_exact (l : K) (e : ℕ) (a : K) (q p : List Bool) :
    countsR l (fun _ => revAddr l p) (embed q (.read e (embed p (.verify e a .halt)))) = 0
    ∧ indP (embed q (.read e (embed p (.verify e a .halt)))) = 0 := by
  have h1 : countsR l (fun _ => revAddr l p) (.read e (embed p (.verify e a .halt))) = 0 := by
    simp only [countsR, countsR_embed, indP, C_sub, C_pow, pwScale, MemoryTable.pwScaleExp, C_1]; ring
  have h2 : indP (.read e (embed p (.verify e a .halt))) = 0 := by
    simp only [indP, indP_embed, pwScale, MemoryTable.pwScaleExp, C_1]; ring
  rw [countsR_embed, indP_embed, h1, h2]; simp

/-- **`a = 0` is accepted by the reversed alternative.**  A `verify_child` at a node whose right
child is the `read_root` wrapper (the read one edge BELOW its verify), `ã = 0`: both boundaries
are identically zero. -/
theorem rev_zero_axis_accepted (l : K) (e : ℕ) (a : K) :
    countsR l (fun _ => 0) (.verify e a (.decompose .halt (.read e .halt))) = 0
    ∧ indP (.verify e a (.decompose .halt (.read e .halt))) = 0 := by
  constructor
  · simp [countsR, indP, C_0, pwScale, MemoryTable.pwScaleExp, C_pow, one_pow, C_1]
  · simp [indP, pwScale, MemoryTable.pwScaleExp, C_pow, one_pow, C_1]

/-- Its shape is not nested (the read's subtree holds no verify). -/
theorem rev_zero_axis_not_nested (e : ℕ) (a : K) :
    ¬ Nock.AxisBridge.ReadVerifyNested (.verify e a (.decompose .halt (.read e .halt))) := by
  intro h
  simp [Nock.AxisBridge.ReadVerifyNested, verifyCount] at h

end Reversed

/-! ## Variant (i'') — left-aligned bits + certified shift: the Laurent step and the gadgets -/

section LeftAligned

variable {K : Type*} [Field K]

/-- **The Laurent step.**  Multiply the per-record bracket by `λ^{n−1}`: the standard part
`Q` (a polynomial: `P_V − λ^m(P_R − 1) − λ^m − Σ_{j≤m} c_jλ^{m−j}`) lands on exponents
`≥ n − 1`, the padding bits `c_j`, `m < j < n`, on the DISTINCT exponents `n − 1 + m − j < n − 1`.
So the identity forces every padding bit to `0` and then `Q = 0`. -/
theorem laurent_padding_forced (n m : ℕ) (hm : m < n) (Q : K[X]) (c : ℕ → K)
    (h : X ^ (n - 1) * Q = ∑ j ∈ Finset.Ioo m n, C (c j) * X ^ (n - 1 + m - j)) :
    (∀ j, m < j → j < n → c j = 0) ∧ Q = 0 := by
  have hpad : ∀ j, m < j → j < n → c j = 0 := by
    intro j₀ hj₀m hj₀n
    have hk := congrArg (fun p : K[X] => p.coeff (n - 1 + m - j₀)) h
    simp only [finsetSum_coeff, coeff_C_mul, coeff_X_pow, coeff_X_pow_mul'] at hk
    rw [if_neg (by omega)] at hk
    rw [Finset.sum_eq_single j₀] at hk
    · simpa using hk.symm
    · intro j hj hne
      rw [Finset.mem_Ioo] at hj
      have : n - 1 + m - j₀ ≠ n - 1 + m - j := by omega
      simp [this]
    · intro habs; exact absurd (Finset.mem_Ioo.mpr ⟨hj₀m, hj₀n⟩) habs
  refine ⟨hpad, ?_⟩
  have h0 : X ^ (n - 1) * Q = 0 := by
    rw [h]
    apply Finset.sum_eq_zero
    intro j hj
    rw [Finset.mem_Ioo] at hj
    rw [hpad j hj.1 hj.2, C_0, zero_mul]
  rcases mul_eq_zero.mp h0 with hX | hQ
  · exact absurd hX (pow_ne_zero _ X_ne_zero)
  · exact hQ

open Classical in
/-- **The power gadget.**  With boolean `mₖ`, `Π_{k<r} (1 + mₖ(x^{2^k} − 1)) = x^{Σ mₖ2^k}`
(`T = λ^m` at `x = λ`, `t = 2^m` at `x = 2`). -/
theorem power_gadget (x : K) (m : ℕ → K) (r : ℕ) (hb : ∀ k < r, m k = 0 ∨ m k = 1) :
    ∏ k ∈ Finset.range r, (1 + m k * (x ^ (2 ^ k) - 1))
      = x ^ (∑ k ∈ Finset.range r, if m k = 1 then 2 ^ k else 0) := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Finset.prod_range_succ, Finset.sum_range_succ, ih (fun k hk => hb k (by omega)),
        pow_add]
      rcases hb r (Nat.lt_succ_self r) with h | h
      · rw [h, if_neg zero_ne_one]; simp
      · rw [h, if_pos rfl]; simp

/-- The certified integer `2^m + Σ_{1≤j≤m} c_j 2^{m−j}` (as `bitSum` of the LSB-first bits
`bᵢ = c_{m−i}`, `b_m = c_0 = 1`) lies in `[2^m, 2^{m+1})`; so `m ≤ 62` reads it exactly below
`2^63 < p`, and `a ≥ 1` always (item B''(4)). -/
theorem left_aligned_value_bounds (m : ℕ) (b : ℕ → Bool) (hb : b m = true) :
    2 ^ m ≤ Batch548.bitSum b (m + 1) ∧ Batch548.bitSum b (m + 1) < 2 ^ (m + 1) := by
  refine ⟨?_, Batch548.bitSum_lt b (m + 1)⟩
  unfold Batch548.bitSum
  calc 2 ^ m = (b m).toNat * 2 ^ m := by rw [hb]; simp
    _ ≤ ∑ i ∈ Finset.range (m + 1), (b i).toNat * 2 ^ i :=
        Finset.single_le_sum (f := fun i => (b i).toNat * 2 ^ i)
          (fun i _ => Nat.zero_le _) (Finset.mem_range.mpr (Nat.lt_succ_self m))

end LeftAligned

end Nock.RedTeam.Batch553

#print axioms Nock.RedTeam.Batch553.bad_card_le
#print axioms Nock.RedTeam.Batch553.forest_zero_iff
#print axioms Nock.RedTeam.Batch553.rev_honest_exact
#print axioms Nock.RedTeam.Batch553.rev_zero_axis_accepted
#print axioms Nock.RedTeam.Batch553.laurent_padding_forced
#print axioms Nock.RedTeam.Batch553.power_gadget
#print axioms Nock.RedTeam.Batch553.left_aligned_value_bounds
