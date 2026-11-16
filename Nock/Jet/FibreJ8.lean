/-
  Nock/Jet/FibreJ8.lean

  **The weighted LogUp, provider direction.**

  `FiniteIO.finiteIO_lookup_sound_weighted` is the CONSUMER direction of the weighted LogUp (every
  consumed key is provided).  This module proves the PROVIDER direction, at the granularity the
  identity actually controls: the key fibre.

  * `fibreW provs k`: the total weight of the providers of key `k`; `effP provs`: the providers whose
    key fibre weight is nonzero (the EFFECTIVE providers).
  * **`consumed_of_fibre`** ("a weighted provider is consumed"): outside the RLC-collision and the
    weighted log-derivative events, with nonzero denominators and the sampled-pole identity, every
    provider whose key fibre weight is nonzero has its key consumed.  No count bound is needed.
    A single provider of weight `m ≠ 0` is NOT enough: two providers of one key with weights
    `m, −m` cancel and need no consumer (`fibre_cancel`, the negative control).
  * **`sum_effP`**: dropping the non-effective providers leaves every weighted provider sum
    unchanged (their contributions cancel key by key), so a balance identity over `provs` is the
    same identity over `effP provs`; `fibreW_effP` (an effective key keeps its fibre), `effP_map` /
    `fibreW_map` (lifting along injective maps).
-/
import Nock.NockVMROM.Thm54.P8Core.SVFrame.WeightedIO

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.Jet.FibreJ8

open Nock Nock.NockVMROM.Thm54.FiniteIO
open Polynomial
open scoped BigOperators

noncomputable section

/-! ## 1. Fibres -/

section Fibre
variable {K : Type*} [Field K] [DecidableEq K] {m : ℕ}

/-- **The fibre weight** of key `k`: the sum of the weights of the providers of `k`. -/
def fibreW (provs : List ((Fin m → K) × K)) (k : Fin m → K) : K :=
  ((provs.filter fun q => decide (q.1 = k)).map Prod.snd).sum

/-- **The effective providers**: those whose key fibre weight is nonzero. -/
def effP (provs : List ((Fin m → K) × K)) : List ((Fin m → K) × K) :=
  provs.filter fun q => decide (fibreW provs q.1 ≠ 0)

theorem fibreW_nil (k : Fin m → K) : fibreW ([] : List ((Fin m → K) × K)) k = 0 := rfl

theorem fibreW_cons (a : (Fin m → K) × K) (l : List ((Fin m → K) × K)) (k : Fin m → K) :
    fibreW (a :: l) k = (if a.1 = k then a.2 else 0) + fibreW l k := by
  unfold fibreW
  by_cases h : a.1 = k <;> simp [List.filter_cons, h]

/-- **An effective key keeps its whole fibre** in `effP`. -/
theorem fibreW_effP (l : List ((Fin m → K) × K)) {k : Fin m → K} (hk : fibreW l k ≠ 0) :
    fibreW (effP l) k = fibreW l k := by
  unfold fibreW effP
  rw [List.filter_filter]
  congr 2
  apply List.filter_congr
  intro q _
  by_cases h : q.1 = k
  · simp [h, hk]
  · simp [h]

/-- The membership form of `effP`. -/
theorem mem_effP {l : List ((Fin m → K) × K)} {q : (Fin m → K) × K} :
    q ∈ effP l ↔ q ∈ l ∧ fibreW l q.1 ≠ 0 := by
  unfold effP; simp

/-- **Lifting a fibre** along an injective key map and a ring embedding of the weights. -/
theorem fibreW_map {L : Type*} [Field L] [DecidableEq L] {m' : ℕ} (g : (Fin m → K) → (Fin m' → L))
    (hg : Function.Injective g) (φ : K →+* L) (l : List ((Fin m → K) × K)) (k : Fin m → K) :
    fibreW (l.map fun q => (g q.1, φ q.2)) (g k) = φ (fibreW l k) := by
  induction l with
  | nil => simp [fibreW]
  | cons a l ih =>
    rw [List.map_cons, fibreW_cons, fibreW_cons, ih, map_add]
    by_cases h : a.1 = k
    · simp [h]
    · have : g a.1 ≠ g k := fun e => h (hg e)
      simp [h, this]

/-- `effP` commutes with the lift. -/
theorem effP_map {L : Type*} [Field L] [DecidableEq L] {m' : ℕ} (g : (Fin m → K) → (Fin m' → L))
    (φ : K →+* L) (l : List ((Fin m → K) × K)) :
    effP (l.map fun q => (g q.1, φ q.2)) =
      (l.filter fun q => decide (fibreW (l.map fun q => (g q.1, φ q.2)) (g q.1) ≠ 0)).map
        fun q => (g q.1, φ q.2) := by
  unfold effP
  rw [List.filter_map]
  rfl

end Fibre

/-! ## 2. Lists as `Fin` sums -/

section Sums
variable {α M : Type*} [AddCommMonoid M]

theorem sum_map_eq_fin (l : List α) (g : α → M) :
    (l.map g).sum = ∑ i : Fin l.length, g (l.get i) := by
  rw [← List.ofFn_getElem_eq_map, List.sum_ofFn]
  rfl

theorem filter_map_sum_ite (l : List α) (p : α → Bool) (g : α → M) :
    ((l.filter p).map g).sum = (l.map fun x => if p x = true then g x else 0).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h : p a = true
    · simp [List.filter_cons, h, ih]
    · simp [List.filter_cons, h, ih]

/-- **A filtered list sum as a `Fin`-indexed filtered sum.** -/
theorem list_filter_sum (l : List α) (p : α → Bool) (g : α → M) :
    ((l.filter p).map g).sum =
      ∑ j ∈ Finset.univ.filter (fun j : Fin l.length => p (l.get j) = true), g (l.get j) := by
  rw [filter_map_sum_ite, sum_map_eq_fin, Finset.sum_filter]

end Sums

/-! ## 3. Non-effective providers cancel -/

section Cancel
variable {K : Type*} [Field K] [DecidableEq K] {m : ℕ}

/-- **The non-effective providers contribute nothing** to a weighted provider sum. -/
theorem sum_noneff (f : (Fin m → K) → K) (l : List ((Fin m → K) × K)) :
    ((l.filter fun q => !decide (fibreW l q.1 ≠ 0)).map fun q => q.2 * f q.1).sum = 0 := by
  classical
  rw [list_filter_sum]
  set s := Finset.univ.filter (fun j : Fin l.length => (!decide (fibreW l (l.get j).1 ≠ 0)) = true) with hs
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun j : Fin l.length => (l.get j).1)
    (t := s.image fun j : Fin l.length => (l.get j).1) (fun j hj => Finset.mem_image_of_mem _ hj)]
  apply Finset.sum_eq_zero
  intro k hk
  obtain ⟨j0, hj0, hj0k⟩ := Finset.mem_image.mp hk
  have hk0 : fibreW l k = 0 := by
    have := (Finset.mem_filter.mp hj0).2
    simp only [ne_eq, decide_not, Bool.not_not, decide_eq_true_eq] at this
    rw [← hj0k]; exact this
  have hsub : (s.filter fun j => (l.get j).1 = k) =
      Finset.univ.filter (fun j : Fin l.length => decide ((l.get j).1 = k) = true) := by
    ext j
    simp only [hs, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq, ne_eq, decide_not,
      Bool.not_not]
    constructor
    · exact fun h => h.2
    · intro h; exact ⟨by rw [h]; exact hk0, h⟩
  rw [Finset.sum_congr rfl (g := fun j : Fin l.length => (l.get j).2 * f k) (fun j hj => by
    rw [(Finset.mem_filter.mp hj).2]), ← Finset.sum_mul, hsub]
  have hl := list_filter_sum l (fun q => decide (q.1 = k)) Prod.snd
  rw [← hl]
  change fibreW l k * f k = 0
  rw [hk0, zero_mul]

theorem sum_split (l : List ((Fin m → K) × K)) (p : (Fin m → K) × K → Bool) (g : (Fin m → K) × K → K) :
    (l.map g).sum = ((l.filter p).map g).sum + ((l.filter fun q => !p q).map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases h : p a = true
    · simp [List.filter_cons, h, ih]; ring
    · simp [List.filter_cons, h, ih]; ring

/-- **`sum_effP`: a weighted provider sum is the sum over the effective providers.** -/
theorem sum_effP (f : (Fin m → K) → K) (l : List ((Fin m → K) × K)) :
    (l.map fun q => q.2 * f q.1).sum = ((effP l).map fun q => q.2 * f q.1).sum := by
  rw [sum_split l (fun q => decide (fibreW l q.1 ≠ 0)), sum_noneff, add_zero]
  rfl

end Cancel

/-! ## 4. The provider direction of the weighted LogUp -/

section Consumed
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] {m : ℕ}

/-- **"A weighted provider is consumed"**, at the fibre: outside the RLC-collision event and the
weighted log-derivative event, with nonzero denominators and the sampled-pole identity
`Σ 1/(ρ + RLC aⱼ) = Σ wᵢ/(ρ + RLC bᵢ)`, a provider whose key has nonzero fibre weight has its key
among the consumers.  (Partial-fraction uniqueness: `#{j : aⱼ = b} = fibreW b`.) -/
theorem consumed_of_fibre (reqs : List (Fin m → K)) (provs : List ((Fin m → K) × K)) (coins : IOCoins K)
    (hdA : ∀ r ∈ reqs, compress coins r ≠ 0)
    (hdB : ∀ q ∈ provs, compress coins q.1 ≠ 0)
    (hsum : (reqs.map fun r => (compress coins r)⁻¹).sum =
      (provs.map fun q => q.2 * (compress coins q.1)⁻¹).sum)
    (hγ : coins.gamma ∉ IORLCCollisionEvent (recordsW reqs provs))
    (hpole : coins.pole ∉ IOLogDerivEventW reqs provs coins.gamma) :
    ∀ q ∈ provs, fibreW provs q.1 ≠ 0 → q.1 ∈ reqs := by
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
  have hco := (SetEq.frac_eq_iff_coeff A (fun _ => (1 : K)) B w).mp hfrac
  intro q hq hfib
  obtain ⟨j, hj⟩ := List.get_of_mem hq
  by_contra hnot
  have hmem : B j ∈ (Finset.univ.image A ∪ Finset.univ.image B) :=
    Finset.mem_union_right _ (Finset.mem_image_of_mem B (Finset.mem_univ j))
  have hc0 := hco (B j) (by convert hmem)
  have hc : (∑ i' ∈ Finset.univ.filter (fun i' => A i' = B j), (1 : K)) =
      ∑ j' ∈ Finset.univ.filter (fun j' => B j' = B j), w j' := by convert hc0
  have hempty : Finset.univ.filter (fun i' => A i' = B j) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro i _ hi
    apply hnot
    have hrec : reqs.get i = (provs.get j).1 :=
      rlc_inj_of_not_collision hγ (List.mem_append_left _ (List.get_mem _ _))
        (List.mem_append_right _ (List.mem_map_of_mem (List.get_mem _ _))) hi
    rw [← hj, ← hrec]
    exact List.get_mem _ _
  have hfil : Finset.univ.filter (fun j' => B j' = B j) =
      Finset.univ.filter (fun j' : Fin provs.length => decide ((provs.get j').1 = (provs.get j).1) = true) := by
    ext j'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
    constructor
    · intro h
      exact rlc_inj_of_not_collision hγ
        (List.mem_append_right _ (List.mem_map_of_mem (List.get_mem _ _)))
        (List.mem_append_right _ (List.mem_map_of_mem (List.get_mem _ _))) h
    · intro h
      simp only [hB, provVals, h]
  rw [hempty, Finset.sum_empty, hfil] at hc
  apply hfib
  rw [← hj, fibreW, list_filter_sum]
  exact hc.symm

/-- **The consumer direction at the effective providers**: every consumed key is the key of a
provider with nonzero fibre weight (the count of its consumers, `< p`). -/
theorem served_effective {p : ℕ} [CharP K p] (reqs : List (Fin m → K)) (provs : List ((Fin m → K) × K))
    (coins : IOCoins K)
    (hdA : ∀ r ∈ reqs, compress coins r ≠ 0)
    (hdB : ∀ q ∈ effP provs, compress coins q.1 ≠ 0)
    (hsum : (reqs.map fun r => (compress coins r)⁻¹).sum =
      (provs.map fun q => q.2 * (compress coins q.1)⁻¹).sum)
    (hcount : reqs.length < p)
    (hγ : coins.gamma ∉ IORLCCollisionEvent (recordsW reqs (effP provs)))
    (hpole : coins.pole ∉ IOLogDerivEventW reqs (effP provs) coins.gamma) :
    ∀ r ∈ reqs, r ∈ (effP provs).map Prod.fst := by
  have hsumE : (reqs.map fun r => (compress coins r)⁻¹).sum =
      ((effP provs).map fun q => q.2 * (compress coins q.1)⁻¹).sum := by
    rw [hsum]; exact sum_effP (fun k => (compress coins k)⁻¹) provs
  exact finiteIO_lookup_sound_weighted reqs (effP provs) coins hdA hdB hsumE hcount hγ hpole

end Consumed

/-! ## 5. The negative control: a single weight `≠ 0` is not enough -/

/-- **Fibre cancellation**: two providers of one key with weights `1, −1` have fibre weight `0`;
the balance `0 = 1·d⁻¹ + (−1)·d⁻¹` holds with NO consumer, so a weight-`≠ 0` provider need not be
consumed.  (Why the provider obligation ranges over EFFECTIVE providers, not `m ≠ 0`.) -/
theorem fibre_cancel {K : Type*} [Field K] [DecidableEq K] {m : ℕ} (k : Fin m → K) (d : K) :
    fibreW [(k, (1 : K)), (k, -1)] k = 0 ∧
      (([] : List (Fin m → K)).map fun _ => d⁻¹).sum =
        ([(k, (1 : K)), (k, -1)].map fun q => q.2 * d⁻¹).sum ∧
      effP [(k, (1 : K)), (k, -1)] = [] := by
  refine ⟨by simp [fibreW], by simp, by simp [effP, fibreW]⟩

end

end Nock.Jet.FibreJ8
