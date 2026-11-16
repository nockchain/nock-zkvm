/-
  Nock/NockVMROM/Thm54/VclL/Handle/BalanceQ.lean

  Additive, generic in the field.

  * `fibre_counts`: outside the weighted IO failure event (RLC collision, weighted log-derivative) at a
    coin pair with nonzero denominators and the sampled-pole identity, the weighted multiplicities
    balance RECORD BY RECORD: `#{j : a_j = r} = Σ_{b_i = r} w_i` for every record `r` (not only
    "every consumed record is provided", as `finiteIO_lookup_sound_weighted`).
  * `sum_transfer`: the per-record balance gives `Σ_j f(a_j) = Σ_i w_i · f(b_i)` for EVERY function
    `f` — in particular the LogUp identity at any other pole-free coin pair, over any field.
  * `counts_lift`: the per-record balance descends along a field embedding `K → L` (records and
    weights lifted entrywise).  So a balance proved at `𝕂′` coins holds at `𝕂` coins: the step that
    lets a `𝕂′`-accepted trace be re-filled at `𝕂` coins.
-/
import Nock.NockVMROM.Thm54.P8Core.SVFrame.WeightedIO

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ

open Nock Polynomial Nock.NockVMROM.Thm54.FiniteIO
open scoped BigOperators

noncomputable section

/-- The provider weight of record `r`: `Σ_{(b, w) ∈ provs, b = r} w`. -/
def pw {L : Type*} [Field L] {α : Type*} [DecidableEq α] (provs : List (α × L)) (r : α) : L :=
  (provs.map fun q => if q.1 = r then q.2 else 0).sum

section Fibre
variable {L : Type*} [Field L] [Fintype L] [DecidableEq L] {m : ℕ}

abbrev provWeight (provs : List ((Fin m → L) × L)) (r : Fin m → L) : L := pw provs r


theorem count_eq_ite {α : Type*} [DecidableEq α] (l : List α) (r : α) :
    (l.count r : L) = (l.map fun x => if x = r then (1 : L) else 0).sum := by
  induction l with
  | nil => simp
  | cons x t ih =>
    by_cases h : x = r
    · subst h; simp [List.count_cons, ih]; ring
    · simp [List.count_cons, h, ih]

theorem provWeight_eq_fin (provs : List ((Fin m → L) × L)) (r : Fin m → L) :
    provWeight provs r = ∑ j ∈ Finset.univ.filter (fun j : Fin provs.length => (provs.get j).1 = r),
      (provs.get j).2 := by
  unfold provWeight pw
  rw [list_sum_map_eq_fin, Finset.sum_filter]

theorem count_eq_fin (reqs : List (Fin m → L)) (r : Fin m → L) :
    (reqs.count r : L) =
      ∑ i ∈ Finset.univ.filter (fun i : Fin reqs.length => reqs.get i = r), (1 : L) := by
  rw [count_eq_ite, list_sum_map_eq_fin, Finset.sum_filter]

/-- **Per-record balance** outside the weighted failure event. -/
theorem fibre_counts (reqs : List (Fin m → L)) (provs : List ((Fin m → L) × L)) (coins : IOCoins L)
    (hdA : ∀ r ∈ reqs, compress coins r ≠ 0)
    (hdB : ∀ q ∈ provs, compress coins q.1 ≠ 0)
    (hsum : (reqs.map fun r => (compress coins r)⁻¹).sum =
      (provs.map fun q => q.2 * (compress coins q.1)⁻¹).sum)
    (hγ : coins.gamma ∉ IORLCCollisionEvent (recordsW reqs provs))
    (hpole : coins.pole ∉ IOLogDerivEventW reqs provs coins.gamma) :
    ∀ r : Fin m → L, (reqs.count r : L) = provWeight provs r := by
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
  have hmapQ : algebraMap L[X] (RatFunc L) (numerP A) * algebraMap L[X] (RatFunc L) (denomP B)
      = algebraMap L[X] (RatFunc L) (numerPW B w) * algebraMap L[X] (RatFunc L) (denomP A) := by
    rw [← map_mul, ← map_mul, hQ']
  have hdAne : algebraMap L[X] (RatFunc L) (denomP A) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (RatFunc.algebraMap_injective L)]
    exact denomP_ne_zero A
  have hdBne : algebraMap L[X] (RatFunc L) (denomP B) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (RatFunc.algebraMap_injective L)]
    exact denomP_ne_zero B
  have hfrac : (∑ i, (1 : L) • SetEq.frac (A i)) = ∑ j, w j • SetEq.frac (B j) := by
    have hA' := frac_sum_mul_denom A
    have hB' := frac_wsum_mul_denom B w
    simp only [one_smul]
    have hkey : (∑ i, SetEq.frac (A i))
          * (algebraMap L[X] (RatFunc L) (denomP A) * algebraMap L[X] (RatFunc L) (denomP B))
        = (∑ j, w j • SetEq.frac (B j))
          * (algebraMap L[X] (RatFunc L) (denomP A) * algebraMap L[X] (RatFunc L) (denomP B)) := by
      calc (∑ i, SetEq.frac (A i))
            * (algebraMap L[X] (RatFunc L) (denomP A) * algebraMap L[X] (RatFunc L) (denomP B))
          = ((∑ i, SetEq.frac (A i)) * algebraMap L[X] (RatFunc L) (denomP A))
              * algebraMap L[X] (RatFunc L) (denomP B) := by ring
        _ = algebraMap L[X] (RatFunc L) (numerP A) * algebraMap L[X] (RatFunc L) (denomP B) := by
              rw [hA']
        _ = algebraMap L[X] (RatFunc L) (numerPW B w) * algebraMap L[X] (RatFunc L) (denomP A) :=
              hmapQ
        _ = ((∑ j, w j • SetEq.frac (B j)) * algebraMap L[X] (RatFunc L) (denomP B))
              * algebraMap L[X] (RatFunc L) (denomP A) := by rw [hB']
        _ = (∑ j, w j • SetEq.frac (B j))
              * (algebraMap L[X] (RatFunc L) (denomP A)
                  * algebraMap L[X] (RatFunc L) (denomP B)) := by ring
    exact mul_right_cancel₀ (mul_ne_zero hdAne hdBne) hkey
  have hco := (SetEq.frac_eq_iff_coeff A (fun _ => (1 : L)) B w).mp hfrac
  -- records in the combined list are determined by their compression
  have hinj : ∀ u ∈ reqs ++ provs.map Prod.fst, ∀ v ∈ reqs ++ provs.map Prod.fst,
      Walk.rlc coins.gamma u = Walk.rlc coins.gamma v → u = v :=
    fun u hu v hv h => rlc_inj_of_not_collision hγ hu hv h
  intro r
  rw [provWeight_eq_fin]
  have hcount := count_eq_fin reqs r
  rw [hcount]
  by_cases hr : r ∈ reqs ∨ r ∈ provs.map Prod.fst
  · -- `r` occurs: compare the fibres of the compression at `rlc r`
    have hrm : r ∈ reqs ++ provs.map Prod.fst := List.mem_append.mpr hr
    set c := Walk.rlc coins.gamma r
    have hfA : Finset.univ.filter (fun i : Fin reqs.length => reqs.get i = r) =
        Finset.univ.filter (fun i => A i = c) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hA, consVals]
      constructor
      · intro h; rw [h]
      · intro h
        exact hinj _ (List.mem_append_left _ (List.get_mem _ _)) _ hrm h
    have hfB : Finset.univ.filter (fun j : Fin provs.length => (provs.get j).1 = r) =
        Finset.univ.filter (fun j => B j = c) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hB, provVals]
      constructor
      · intro h; rw [h]
      · intro h
        exact hinj _ (List.mem_append_right _ (List.mem_map_of_mem (List.get_mem _ _))) _ hrm h
    rw [hfA, hfB]
    by_cases hc : c ∈ (Finset.univ.image A ∪ Finset.univ.image B)
    · convert hco c (by convert hc) using 2 <;> (try ext) <;> simp [hw, provWts]
    · have h1 : Finset.univ.filter (fun i => A i = c) = ∅ := by
        rw [Finset.filter_eq_empty_iff]; intro i _ h
        exact hc (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, h⟩))
      have h2 : Finset.univ.filter (fun j => B j = c) = ∅ := by
        rw [Finset.filter_eq_empty_iff]; intro j _ h
        exact hc (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, h⟩))
      rw [h1, h2, Finset.sum_empty, Finset.sum_empty]
  · -- `r` occurs nowhere: both fibres are empty
    push_neg at hr
    have h1 : Finset.univ.filter (fun i : Fin reqs.length => reqs.get i = r) = ∅ := by
      rw [Finset.filter_eq_empty_iff]; intro i _ h; exact hr.1 (h ▸ List.get_mem _ _)
    have h2 : Finset.univ.filter (fun j : Fin provs.length => (provs.get j).1 = r) = ∅ := by
      rw [Finset.filter_eq_empty_iff]; intro j _ h
      exact hr.2 (h ▸ List.mem_map_of_mem (List.get_mem _ _))
    rw [h1, h2, Finset.sum_empty, Finset.sum_empty]

end Fibre

/-! ## 2. Transfer to any function -/

section Transfer
variable {L : Type*} [Field L] {α : Type*} [DecidableEq α]


theorem sum_map_eq_count (l : List α) (f : α → L) :
    (l.map f).sum = ∑ r ∈ l.toFinset, (l.count r : L) * f r := by
  rw [Finset.sum_list_map_count]
  simp [nsmul_eq_mul]

theorem sum_wmap_eq_pw (provs : List (α × L)) (f : α → L) (S : Finset α)
    (hS : ∀ q ∈ provs, q.1 ∈ S) :
    (provs.map fun q => q.2 * f q.1).sum = ∑ r ∈ S, pw provs r * f r := by
  induction provs with
  | nil => simp [pw]
  | cons q t ih =>
    have ht : ∀ q' ∈ t, q'.1 ∈ S := fun q' hq' => hS q' (by simp [hq'])
    rw [List.map_cons, List.sum_cons, ih ht]
    have hq : q.1 ∈ S := hS q (by simp)
    have : ∀ r ∈ S, pw (q :: t) r * f r = (if q.1 = r then q.2 * f r else 0) + pw t r * f r := by
      intro r _
      unfold pw
      by_cases h : q.1 = r
      · simp [h]; ring
      · simp [h]
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_ite_eq S q.1]
    simp [hq]

/-- **Sum transfer**: a per-record balance gives `Σ_j f(a_j) = Σ_i w_i · f(b_i)` for every `f`. -/
theorem sum_transfer (reqs : List α) (provs : List (α × L))
    (hbal : ∀ r, (reqs.count r : L) = pw provs r) (f : α → L) :
    (reqs.map f).sum = (provs.map fun q => q.2 * f q.1).sum := by
  classical
  set S := reqs.toFinset ∪ (provs.map Prod.fst).toFinset
  rw [sum_wmap_eq_pw provs f S (fun q hq => Finset.mem_union_right _
    (List.mem_toFinset.mpr (List.mem_map_of_mem hq)))]
  have hsub : ∑ r ∈ reqs.toFinset, (reqs.count r : L) * f r = ∑ r ∈ S, (reqs.count r : L) * f r :=
    Finset.sum_subset Finset.subset_union_left fun r _ hr => by
      rw [List.mem_toFinset] at hr
      rw [List.count_eq_zero_of_not_mem hr]; simp
  rw [sum_map_eq_count, hsub]
  exact Finset.sum_congr rfl fun r _ => by rw [hbal]

end Transfer

/-! ## 3. Descent along a field embedding -/

section Lift
variable {K L : Type*} [Field K] [Field L] [Algebra K L] {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- **Descent**: a per-record balance of lifted records (`φ` injective, weights `algebraMap`) holds
before the lift. -/
theorem counts_lift (φ : α → β) (hφ : Function.Injective φ) (reqs : List α) (provs : List (α × K))
    (hbal : ∀ r, (((reqs.map φ).count r : ℕ) : L) =
      pw (provs.map fun q => (φ q.1, algebraMap K L q.2)) r) :
    ∀ r, (reqs.count r : K) = pw provs r := by
  intro r
  have h := hbal (φ r)
  rw [List.count_map_of_injective _ _ hφ] at h
  have hp : pw (provs.map fun q => (φ q.1, algebraMap K L q.2)) (φ r) = algebraMap K L (pw provs r) := by
    unfold pw
    rw [List.map_map, map_list_sum, List.map_map]
    congr 1
    refine List.map_congr_left fun q _ => ?_
    by_cases hq : q.1 = r
    · simp [hq]
    · have : φ q.1 ≠ φ r := fun he => hq (hφ he)
      simp [hq, this]
  rw [hp, ← map_natCast (algebraMap K L)] at h
  exact (algebraMap K L).injective h

end Lift

/-! ## 4. The descent of the LogUp identity -/

section Descent
variable {K L : Type*} [Field K] [Field L] [Fintype L] [DecidableEq L] [Algebra K L] [DecidableEq K]
  {m : ℕ}

/-- Entrywise lift of a record. -/
def liftRec (r : Fin m → K) : Fin m → L := fun c => algebraMap K L (r c)

theorem liftRec_inj : Function.Injective (liftRec (K := K) (L := L) (m := m)) := by
  intro r s h
  funext c
  exact (algebraMap K L).injective (congrFun h c)

/-- **The descent**: if the LIFTED records balance at a coin pair of `L` outside the weighted failure
event (with nonzero denominators), then the `K` records satisfy the LogUp identity at EVERY coin pair
of `K` — no event, no field size condition: the identity holds as a multiset fact. -/
theorem logup_descends (reqs : List (Fin m → K)) (provs : List ((Fin m → K) × K)) (coins : IOCoins L)
    (hdA : ∀ r ∈ reqs.map liftRec, compress coins r ≠ 0)
    (hdB : ∀ q ∈ provs.map (fun q => (liftRec (L := L) q.1, algebraMap K L q.2)), compress coins q.1 ≠ 0)
    (hsum : ((reqs.map liftRec).map fun r => (compress coins r)⁻¹).sum =
      ((provs.map (fun q => (liftRec (L := L) q.1, algebraMap K L q.2))).map
        fun q => q.2 * (compress coins q.1)⁻¹).sum)
    (hγ : coins.gamma ∉ IORLCCollisionEvent (recordsW (reqs.map liftRec)
      (provs.map (fun q => (liftRec (L := L) q.1, algebraMap K L q.2)))))
    (hpole : coins.pole ∉ IOLogDerivEventW (reqs.map liftRec)
      (provs.map (fun q => (liftRec (L := L) q.1, algebraMap K L q.2))) coins.gamma)
    (f : (Fin m → K) → K) :
    (reqs.map f).sum = (provs.map fun q => q.2 * f q.1).sum := by
  have hL := fibre_counts _ _ coins hdA hdB hsum hγ hpole
  have hK := counts_lift (K := K) (L := L) liftRec liftRec_inj reqs provs hL
  exact sum_transfer reqs provs hK f

end Descent

end

end Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ
