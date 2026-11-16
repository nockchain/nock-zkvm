/-
  Nock/NockVMROM/Thm54/P8Core/SVFrame/WeightedIO.lean

  * **The weighted provider side.**  Providers are `(record, weight)` pairs with the weight a field
    value (the B0 multiplicity column, unbounded); consumers keep unit weight.  The LogUp identity
    at the sampled pole is `Σ_j 1/(ρ + RLC(a_j)) = Σ_i w_i/(ρ + RLC(b_i))`.
  * `IOFailureEventW reqs provs`: the three counted events of `FiniteIO.IOFailureEvent` at the
    weighted records — the RLC collision and the pole hit are the EXISTING events at
    `⟨reqs, provs.map Prod.fst⟩`; the log-derivative event is at the weighted difference
    polynomial `ioQPW` (scalar numerators `C wᵢ`, degree `≤ k₁ + k₂`).
  * **`finiteIO_lookup_sound_weighted`**: outside the RLC-collision and weighted log-derivative
    events, with nonzero denominators and the sampled-pole identity, and the CONSUMER COUNT below the
    characteristic, every consumed record is a provided record.  The step beyond the unit-weight
    `finiteIO_sound_of_identity` is partial-fraction uniqueness with distinct poles (in-tree:
    `SetEq.frac_eq_iff_coeff`; the probe's standalone form `partial_fraction_unique` is ported as a
    receipt): at a consumed key `v`, `#{j : a_j = v} = Σ_{b_i = v} w_i` in `𝕂`, and an empty
    provider fibre would force a nonzero count `< p` to vanish.
  * `nearP_count_ne` (receipt): a weight `≡ −1` matches a count only at `count ≡ −1 (mod p)`.
-/
import Nock.NockVMROM.Thm54.FiniteFieldIOSoundness

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.FiniteIO

open Nock
open Polynomial
open scoped BigOperators

noncomputable section

/-! ## 1. Weighted clearing identities -/

/-- Clearing all denominators of a weighted sum of reciprocals. -/
theorem sum_w_inv_mul_prod {L : Type*} [Field L] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d w : ι → L) (hd : ∀ i, d i ≠ 0) :
    (∑ i, w i * (d i)⁻¹) * (∏ i, d i) = ∑ i, w i * ∏ i' ∈ Finset.univ.erase i, d i' := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.mul_prod_erase Finset.univ d (Finset.mem_univ i), mul_assoc,
    inv_mul_cancel_left₀ (hd i)]

variable {K : Type*} [Field K] {m : ℕ}

/-- `Σᵢ wᵢ ∏_{i'≠i} (X + b_{i'})`, the cleared numerator of a weighted log-derivative sum. -/
def numerPW {n : ℕ} (b w : Fin n → K) : K[X] :=
  ∑ i, C (w i) * ∏ i' ∈ Finset.univ.erase i, (X + C (b i'))

theorem numerPW_natDegree_le {n : ℕ} (b w : Fin n → K) : (numerPW b w).natDegree ≤ n := by
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun i _ => ?_)
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  refine le_trans (Polynomial.natDegree_prod_le _ _) ?_
  calc (∑ i' ∈ Finset.univ.erase i, (X + C (b i')).natDegree)
      = ∑ _i' ∈ Finset.univ.erase i, 1 :=
        Finset.sum_congr rfl (fun i' _ => Polynomial.natDegree_X_add_C (b i'))
    _ = (Finset.univ.erase i).card := by simp
    _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_card (Finset.erase_subset _ _)
    _ = n := by simp

theorem numerPW_eval {n : ℕ} (b w : Fin n → K) (z : K) :
    (numerPW b w).eval z = ∑ i, w i * ∏ i' ∈ Finset.univ.erase i, (z + b i') := by
  simp [numerPW, Polynomial.eval_finsetSum, Polynomial.eval_prod]

theorem sum_w_inv_eval {n : ℕ} (b w : Fin n → K) (z : K) (hz : ∀ i, z + b i ≠ 0) :
    (∑ i, w i * (z + b i)⁻¹) * (denomP b).eval z = (numerPW b w).eval z := by
  rw [denomP_eval, numerPW_eval]
  exact sum_w_inv_mul_prod (fun i => z + b i) w hz

theorem frac_wsum_mul_denom {n : ℕ} (b w : Fin n → K) :
    (∑ i, w i • SetEq.frac (b i)) * algebraMap K[X] (RatFunc K) (denomP b)
      = algebraMap K[X] (RatFunc K) (numerPW b w) := by
  have hd : algebraMap K[X] (RatFunc K) (denomP b)
      = ∏ i, algebraMap K[X] (RatFunc K) (X + C (b i)) := by
    rw [denomP]; exact map_prod _ _ _
  have hn : algebraMap K[X] (RatFunc K) (numerPW b w)
      = ∑ i, algebraMap K[X] (RatFunc K) (C (w i)) *
          ∏ i' ∈ Finset.univ.erase i, algebraMap K[X] (RatFunc K) (X + C (b i')) := by
    rw [numerPW, map_sum]
    exact Finset.sum_congr rfl (fun i _ => by rw [map_mul, map_prod])
  have hs : ∀ i, w i • SetEq.frac (b i)
      = algebraMap K[X] (RatFunc K) (C (w i)) * (algebraMap K[X] (RatFunc K) (X + C (b i)))⁻¹ :=
    fun i => by rw [SetEq.smul_frac]; rfl
  simp_rw [hs]
  rw [hd, hn]
  exact sum_w_inv_mul_prod (fun i => algebraMap K[X] (RatFunc K) (X + C (b i)))
    (fun i => algebraMap K[X] (RatFunc K) (C (w i))) (fun i => SetEq.algebraMap_poleP_ne_zero (b i))

/-! ## 2. The weighted records, the difference polynomial and the event -/

/-- The record lists the weighted event's RLC / pole-hit components read: consumers and the
providers' records (weights dropped). -/
def recordsW (reqs : List (Fin m → K)) (provs : List ((Fin m → K) × K)) : PreChallengeRecords K m :=
  ⟨reqs, provs.map Prod.fst⟩

/-- The compressed consumer values. -/
def consVals (reqs : List (Fin m → K)) (γ : K) : Fin reqs.length → K :=
  fun i => Walk.rlc γ (reqs.get i)

/-- The compressed provider values. -/
def provVals (provs : List ((Fin m → K) × K)) (γ : K) : Fin provs.length → K :=
  fun j => Walk.rlc γ (provs.get j).1

/-- The provider weights. -/
def provWts (provs : List ((Fin m → K) × K)) : Fin provs.length → K :=
  fun j => (provs.get j).2

/-- **The weighted log-derivative difference polynomial**: `Σ 1/(X + a) − Σ w/(X + b)`, cleared. -/
def ioQPW (reqs : List (Fin m → K)) (provs : List ((Fin m → K) × K)) (γ : K) : K[X] :=
  numerP (consVals reqs γ) * denomP (provVals provs γ)
    - numerPW (provVals provs γ) (provWts provs) * denomP (consVals reqs γ)

theorem ioQPW_natDegree_le (reqs : List (Fin m → K)) (provs : List ((Fin m → K) × K)) (γ : K) :
    (ioQPW reqs provs γ).natDegree ≤ reqs.length + provs.length := by
  refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
  rw [max_le_iff]
  constructor
  · exact le_trans (Polynomial.natDegree_mul_le)
      (Nat.add_le_add (numerP_natDegree_le _) (denomP_natDegree_le _))
  · exact le_trans (Polynomial.natDegree_mul_le)
      (le_trans (Nat.add_le_add (numerPW_natDegree_le _ _) (denomP_natDegree_le _)) (by omega))

variable [Fintype K] [DecidableEq K]

open Classical in
/-- **The weighted log-derivative event**: `ioQPW ≠ 0` yet it vanishes at the sampled pole. -/
def IOLogDerivEventW (reqs : List (Fin m → K)) (provs : List ((Fin m → K) × K)) (γ : K) :
    Finset K :=
  Finset.univ.filter (fun z => ioQPW reqs provs γ ≠ 0 ∧ (ioQPW reqs provs γ).eval z = 0)

theorem IOLogDerivEventW_card_le (reqs : List (Fin m → K)) (provs : List ((Fin m → K) × K))
    (γ : K) : (IOLogDerivEventW reqs provs γ).card ≤ reqs.length + provs.length := by
  classical
  by_cases hQ : ioQPW reqs provs γ = 0
  · have hzero : (IOLogDerivEventW reqs provs γ).card = 0 := by
      rw [Finset.card_eq_zero, IOLogDerivEventW, Finset.filter_eq_empty_iff]
      intro z _
      rintro ⟨hne, -⟩
      exact hne hQ
    omega
  · refine le_trans (Finset.card_le_card (?_ : IOLogDerivEventW reqs provs γ ⊆
        Finset.univ.filter (fun z : K => (ioQPW reqs provs γ).eval z = 0))) ?_
    · intro z hz
      simp only [IOLogDerivEventW, Finset.mem_filter, Finset.mem_univ, true_and] at hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hz.2
    · exact le_trans (Walk.card_roots_le _ hQ) (ioQPW_natDegree_le reqs provs γ)

open Classical in
/-- **The weighted joint failure event** on the `(gamma, pole)` coin pair. -/
def IOFailureEventW (reqs : List (Fin m → K)) (provs : List ((Fin m → K) × K)) : Finset (K × K) :=
  Finset.univ.filter (fun q => q.1 ∈ IORLCCollisionEvent (recordsW reqs provs)
    ∨ q.2 ∈ IOPoleHitEvent (recordsW reqs provs) q.1 ∨ q.2 ∈ IOLogDerivEventW reqs provs q.1)

theorem mem_IOFailureEventW_iff {reqs : List (Fin m → K)} {provs : List ((Fin m → K) × K)}
    {γ pole : K} :
    (γ, pole) ∈ IOFailureEventW reqs provs ↔
      γ ∈ IORLCCollisionEvent (recordsW reqs provs) ∨
      pole ∈ IOPoleHitEvent (recordsW reqs provs) γ ∨
      pole ∈ IOLogDerivEventW reqs provs γ := by
  simp [IOFailureEventW]

/-- **The weighted joint failure bound: the same numeral as `IOFailureEvent_card_le`.** -/
theorem IOFailureEventW_card_le (reqs : List (Fin m → K)) (provs : List ((Fin m → K) × K)) :
    (IOFailureEventW reqs provs).card
      ≤ ioFailureUnionBound m reqs.length provs.length (Fintype.card K) := by
  classical
  set k₁ := reqs.length with hk₁
  set k₂ := provs.length with hk₂
  have hlen : (recordsW reqs provs).requests.length + (recordsW reqs provs).responses.length
      = k₁ + k₂ := by simp [recordsW, hk₁, hk₂]
  set S : Finset (K × K) := (IORLCCollisionEvent (recordsW reqs provs)) ×ˢ Finset.univ with hS
  set T : Finset (K × K) := Finset.univ.biUnion (fun γ : K =>
    ({γ} : Finset K) ×ˢ (IOPoleHitEvent (recordsW reqs provs) γ ∪ IOLogDerivEventW reqs provs γ))
    with hT
  have hsub : IOFailureEventW reqs provs ⊆ S ∪ T := by
    intro q hq
    simp only [IOFailureEventW, Finset.mem_filter, Finset.mem_univ, true_and] at hq
    rcases hq with h1 | h2 | h3
    · exact Finset.mem_union_left _ (by simp only [hS, Finset.mem_product]; exact ⟨h1, by simp⟩)
    · refine Finset.mem_union_right _ ?_
      refine Finset.mem_biUnion.mpr ⟨q.1, Finset.mem_univ _, ?_⟩
      simp only [Finset.mem_product, Finset.mem_singleton, Finset.mem_union]
      exact ⟨trivial, Or.inl h2⟩
    · refine Finset.mem_union_right _ ?_
      refine Finset.mem_biUnion.mpr ⟨q.1, Finset.mem_univ _, ?_⟩
      simp only [Finset.mem_product, Finset.mem_singleton, Finset.mem_union]
      exact ⟨trivial, Or.inr h3⟩
  have hScard : S.card ≤ (k₁ + k₂) * (k₁ + k₂) * (m - 1) * Fintype.card K := by
    rw [hS, Finset.card_product, Finset.card_univ]
    have := IORLCCollisionEvent_card_le (recordsW reqs provs)
    rw [hlen] at this
    exact Nat.mul_le_mul_right _ this
  have hTcard : T.card ≤ Fintype.card K * (2 * (k₁ + k₂)) := by
    refine le_trans Finset.card_biUnion_le ?_
    refine le_trans (Finset.sum_le_sum (g := fun _ : K => 2 * (k₁ + k₂))
      (fun γ (_ : γ ∈ Finset.univ) => ?_)) ?_
    · rw [Finset.card_product, Finset.card_singleton, one_mul]
      refine le_trans (Finset.card_union_le _ _) ?_
      have h1 := IOPoleHitEvent_card_le (recordsW reqs provs) γ
      rw [hlen] at h1
      have h2 := IOLogDerivEventW_card_le reqs provs γ
      omega
    · rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  calc (IOFailureEventW reqs provs).card ≤ (S ∪ T).card := Finset.card_le_card hsub
    _ ≤ S.card + T.card := Finset.card_union_le _ _
    _ ≤ (k₁ + k₂) * (k₁ + k₂) * (m - 1) * Fintype.card K
          + Fintype.card K * (2 * (k₁ + k₂)) := Nat.add_le_add hScard hTcard
    _ = ioFailureUnionBound m k₁ k₂ (Fintype.card K) := rfl

/-! ## 3. Weighted lookup soundness -/

omit [Fintype K] [DecidableEq K] in
theorem list_sum_map_eq_fin {α : Type*} (l : List α) (g : α → K) :
    (l.map g).sum = ∑ i : Fin l.length, g (l.get i) := by
  rw [← List.ofFn_getElem_eq_map, List.sum_ofFn]
  rfl

/-- **`finiteIO_lookup_sound_weighted` — the (m1) lookup soundness.**  Weighted providers
`(bᵢ, wᵢ)` (any field weights), unit-weight consumers `aⱼ`.  Outside the RLC-collision event and
the weighted log-derivative event, with nonzero denominators, the sampled-pole identity
`Σⱼ 1/(ρ + RLC aⱼ) = Σᵢ wᵢ/(ρ + RLC bᵢ)` and the consumer count `< p`, every consumed record is a
provided record.  No bound on the weights, no `Nodup`, no provider-count bound. -/
theorem finiteIO_lookup_sound_weighted {p : ℕ} [CharP K p] (reqs : List (Fin m → K))
    (provs : List ((Fin m → K) × K)) (coins : IOCoins K)
    (hdA : ∀ r ∈ reqs, compress coins r ≠ 0)
    (hdB : ∀ q ∈ provs, compress coins q.1 ≠ 0)
    (hsum : (reqs.map fun r => (compress coins r)⁻¹).sum =
      (provs.map fun q => q.2 * (compress coins q.1)⁻¹).sum)
    (hcount : reqs.length < p)
    (hγ : coins.gamma ∉ IORLCCollisionEvent (recordsW reqs provs))
    (hpole : coins.pole ∉ IOLogDerivEventW reqs provs coins.gamma) :
    ∀ r ∈ reqs, r ∈ provs.map Prod.fst := by
  classical
  set A := consVals reqs coins.gamma with hA
  set B := provVals provs coins.gamma with hB
  set w := provWts provs with hw
  have hdA' : ∀ i, coins.pole + A i ≠ 0 := fun i => hdA _ (List.get_mem _ _)
  have hdB' : ∀ j, coins.pole + B j ≠ 0 := fun j => hdB _ (List.get_mem _ _)
  have hend : (∑ i, (coins.pole + A i)⁻¹) = ∑ j, w j * (coins.pole + B j)⁻¹ := by
    have h1 := list_sum_map_eq_fin reqs (fun r => (compress coins r)⁻¹)
    have h2 := list_sum_map_eq_fin provs (fun q => q.2 * (compress coins q.1)⁻¹)
    rw [h1, h2] at hsum
    exact hsum
  -- the difference polynomial vanishes at the pole
  have hQeval : (ioQPW reqs provs coins.gamma).eval coins.pole = 0 := by
    have hSA := sum_inv_eval A coins.pole hdA'
    have hSB := sum_w_inv_eval B w coins.pole hdB'
    simp only [ioQPW, Polynomial.eval_sub, Polynomial.eval_mul, ← hA, ← hB, ← hw]
    rw [← hSA, ← hSB, hend]
    ring
  have hQ : ioQPW reqs provs coins.gamma = 0 := by
    by_contra hQ0
    exact hpole (by
      simp only [IOLogDerivEventW, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hQ0, hQeval⟩)
  have hQ' : numerP A * denomP B = numerPW B w * denomP A := by
    have hh := hQ
    unfold ioQPW at hh
    rw [← hA, ← hB, ← hw, sub_eq_zero] at hh
    exact hh
  -- the symbolic weighted identity
  have hmapQ : algebraMap K[X] (RatFunc K) (numerP A) * algebraMap K[X] (RatFunc K) (denomP B)
      = algebraMap K[X] (RatFunc K) (numerPW B w) * algebraMap K[X] (RatFunc K) (denomP A) := by
    rw [← map_mul, ← map_mul, hQ']
  have hdAne : algebraMap K[X] (RatFunc K) (denomP A) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (RatFunc.algebraMap_injective K)]
    exact denomP_ne_zero A
  have hdBne : algebraMap K[X] (RatFunc K) (denomP B) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (RatFunc.algebraMap_injective K)]
    exact denomP_ne_zero B
  have hfrac : (∑ i, (1 : K) • SetEq.frac (A i)) = ∑ j, w j • SetEq.frac (B j) := by
    have hA' := frac_sum_mul_denom A
    have hB' := frac_wsum_mul_denom B w
    simp only [one_smul]
    have hkey : (∑ i, SetEq.frac (A i))
          * (algebraMap K[X] (RatFunc K) (denomP A) * algebraMap K[X] (RatFunc K) (denomP B))
        = (∑ j, w j • SetEq.frac (B j))
          * (algebraMap K[X] (RatFunc K) (denomP A) * algebraMap K[X] (RatFunc K) (denomP B)) := by
      calc (∑ i, SetEq.frac (A i))
            * (algebraMap K[X] (RatFunc K) (denomP A) * algebraMap K[X] (RatFunc K) (denomP B))
          = ((∑ i, SetEq.frac (A i)) * algebraMap K[X] (RatFunc K) (denomP A))
              * algebraMap K[X] (RatFunc K) (denomP B) := by ring
        _ = algebraMap K[X] (RatFunc K) (numerP A) * algebraMap K[X] (RatFunc K) (denomP B) := by
              rw [hA']
        _ = algebraMap K[X] (RatFunc K) (numerPW B w) * algebraMap K[X] (RatFunc K) (denomP A) :=
              hmapQ
        _ = ((∑ j, w j • SetEq.frac (B j)) * algebraMap K[X] (RatFunc K) (denomP B))
              * algebraMap K[X] (RatFunc K) (denomP A) := by rw [hB']
        _ = (∑ j, w j • SetEq.frac (B j))
              * (algebraMap K[X] (RatFunc K) (denomP A)
                  * algebraMap K[X] (RatFunc K) (denomP B)) := by ring
    exact mul_right_cancel₀ (mul_ne_zero hdAne hdBne) hkey
  -- partial-fraction uniqueness: fibre sums agree at every pole
  have hco := (SetEq.frac_eq_iff_coeff A (fun _ => (1 : K)) B w).mp hfrac
  intro r hr
  obtain ⟨i, hi⟩ := List.get_of_mem hr
  by_contra hnot
  have hmem : A i ∈ (Finset.univ.image A ∪ Finset.univ.image B) :=
    Finset.mem_union_left _ (Finset.mem_image_of_mem A (Finset.mem_univ i))
  have hc0 := hco (A i) (by convert hmem)
  have hc : (∑ i' ∈ Finset.univ.filter (fun i' => A i' = A i), (1 : K)) =
      ∑ j ∈ Finset.univ.filter (fun j => B j = A i), w j := by convert hc0
  have hempty : Finset.univ.filter (fun j => B j = A i) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro j _ hj
    apply hnot
    have hrec : (provs.get j).1 = reqs.get i :=
      rlc_inj_of_not_collision hγ
        (List.mem_append_right _ (List.mem_map_of_mem (List.get_mem _ _)))
        (List.mem_append_left _ (List.get_mem _ _)) hj
    rw [← hi, ← hrec]
    exact List.mem_map_of_mem (List.get_mem _ _)
  rw [hempty, Finset.sum_empty, Finset.sum_const, nsmul_eq_mul, mul_one] at hc
  set c := (Finset.univ.filter (fun i' => A i' = A i)).card with hcdef
  have hpos : 0 < c := Finset.card_pos.mpr ⟨i, by simp⟩
  have hle : c ≤ reqs.length := by
    have := Finset.card_le_univ (Finset.univ.filter (fun i' => A i' = A i))
    simpa using this
  rw [CharP.cast_eq_zero_iff K p] at hc
  have := Nat.le_of_dvd hpos hc
  omega

end

/-! ## 4. Receipts ported from the probe (`ProbeEps.lean`) -/

section Receipts

variable {L : Type*} [Field L]

/-- **Uniqueness of partial fractions with distinct poles** (the probe's standalone form). -/
theorem partial_fraction_unique {n : ℕ} (a c : Fin n → L) (ha : Function.Injective a)
    (h : (∑ i, Polynomial.C (c i) * ∏ j ∈ Finset.univ.erase i, (Polynomial.X + Polynomial.C (a j)))
      = (0 : Polynomial L)) :
    ∀ k, c k = 0 := by
  intro k
  have hev := congrArg (Polynomial.eval (-a k)) h
  rw [eval_finsetSum, eval_zero] at hev
  rw [Finset.sum_eq_single k] at hev
  · rw [eval_mul, eval_C, eval_prod] at hev
    have hprod : (∏ j ∈ Finset.univ.erase k,
        Polynomial.eval (-a k) (Polynomial.X + Polynomial.C (a j))) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro j hj
      rw [eval_add, eval_X, eval_C]
      intro h0
      have : a j = a k := by linear_combination h0
      exact (Finset.ne_of_mem_erase hj) (ha this)
    exact (mul_eq_zero.1 hev).resolve_right hprod
  · intro i _ hik
    rw [eval_mul, eval_prod]
    apply mul_eq_zero_of_right
    apply Finset.prod_eq_zero (Finset.mem_erase.2 ⟨Ne.symm hik, Finset.mem_univ k⟩)
    simp
  · intro hk; exact absurd (Finset.mem_univ k) hk

end Receipts

/-- **The near-`p` multiplicity is harmless** (receipt): a provider weight `≡ −1` can only match a
consumer count `≡ −1 (mod p)`, impossible while the count is `< p − 1`. -/
theorem nearP_count_ne (p cnt : ℕ) [Fact p.Prime] (h : cnt + 1 < p) :
    ((cnt : ZMod p) : ZMod p) ≠ -1 := by
  intro hc
  have h0 : ((cnt + 1 : ℕ) : ZMod p) = 0 := by push_cast; rw [hc]; ring
  have hv := congrArg ZMod.val h0
  rw [ZMod.val_natCast, ZMod.val_zero, Nat.mod_eq_of_lt h] at hv
  omega

theorem ioFUB_mul (m k₁ k₂ c : ℕ) :
    ioFailureUnionBound m k₁ k₂ c = c * ioFailureUnionBound m k₁ k₂ 1 := by
  unfold ioFailureUnionBound; ring

theorem ioFUB_sq (m t c : ℕ) :
    ioFailureUnionBound m 0 t (c ^ 2) = c ^ 2 * ioFailureUnionBound m 0 t 1 :=
  ioFUB_mul m 0 t (c ^ 2)

end Nock.NockVMROM.Thm54.FiniteIO
