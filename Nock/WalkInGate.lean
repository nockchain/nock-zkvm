/-
  Nock/WalkInGate.lean

  **`WalkSatInGate`: honest forest acc with dequeue masked on roots.**

  The paper's `WalkSat` preloads the forest seed as a
  public: `ln(1)·cur(1) + acc(1) = initial_count·cc(1) + seed` with
  `seed = Σ_{i≤k} α^i RLC(cur_i)` (`Corr:forest`, `:1006`).  On a root row the dequeue is
  masked: the first row (`kMem ≥ 1`) is always a root, so init is
  `acc(1) = initial_count·cc(1)`; the step is
  `(1 − rootMask(i+1))·ln(i+1)·cur(i+1) + acc(i+1) − acc(i) = count(i)·cc(i+1)`.

  Those agree with `WalkSat` on the same acc iff `seed = ln(1)·cur(1)`, i.e. `kMem = 1`.  General forest needs this accumulator.  The closed form is
  `acc(k) = node_list_{k⊓kMem}(α) − node_list_k(α) + initial_count·Σ_{i≤k} childSum(i)`:
  on the root prefix the two node-list terms cancel; past `kMem` it is `WalkSat`'s
  `acc_telescope` at `seed = node_list_{kMem}(α)`.  Terminal identity
  `ingate_seed_eq_forest_seed` is `:1006` by construction.
-/
import Nock.Walk

set_option autoImplicit false

namespace Nock
namespace Walk

open Polynomial BigOperators
open scoped Classical

variable {K : Type*} [Field K]

/-! ## Root mask and the in-gate accumulator -/

/-- Preprocessing root indicator: `1` on walk rows `1..kMem`, else `0`. -/
def rootMask (kMem : ℕ) (i : ℕ) : K := if i ≤ kMem then 1 else 0

/-- Dequeue coefficient: `1 − rootMask`.  Zero on root rows. -/
def deqCoeff (kMem : ℕ) (i : ℕ) : K := 1 - rootMask kMem i

theorem rootMask_of_le {kMem i : ℕ} (h : i ≤ kMem) : rootMask (K := K) kMem i = 1 :=
  if_pos h

theorem rootMask_of_gt {kMem i : ℕ} (h : kMem < i) : rootMask (K := K) kMem i = 0 :=
  if_neg (Nat.not_le.mpr h)

theorem deqCoeff_of_le {kMem i : ℕ} (h : i ≤ kMem) : deqCoeff (K := K) kMem i = 0 := by
  simp [deqCoeff, rootMask_of_le (K := K) h]

theorem deqCoeff_of_gt {kMem i : ℕ} (h : kMem < i) : deqCoeff (K := K) kMem i = 1 := by
  simp [deqCoeff, rootMask_of_gt (K := K) h]

/-- Honest in-gate acc (`:1006` identity after `k ≥ kMem`). -/
noncomputable def accInGate (cur : ℕ → K) (chld' : ℕ → ℕ → K) (fo : ℕ → ℕ)
    (α initial_count : K) (kMem k : ℕ) : K :=
  (nodeListP cur (k ⊓ kMem)).eval α - (nodeListP cur k).eval α
    + initial_count * ∑ i ∈ Finset.Icc 1 k, childSum chld' fo α i

/-- On the root prefix the node-list terms cancel. -/
theorem accInGate_of_le_kMem (cur : ℕ → K) (chld' : ℕ → ℕ → K) (fo : ℕ → ℕ)
    (α initial_count : K) {kMem k : ℕ} (hk : k ≤ kMem) :
    accInGate cur chld' fo α initial_count kMem k =
      initial_count * ∑ i ∈ Finset.Icc 1 k, childSum chld' fo α i := by
  have hmin : k ⊓ kMem = k := min_eq_left hk
  simp only [accInGate, hmin, sub_self, zero_add]

/-- Past the last root this is `WalkSat`'s closed form at `seed = node_list_{kMem}(α)`. -/
theorem accInGate_of_ge_kMem (cur : ℕ → K) (chld' : ℕ → ℕ → K) (fo : ℕ → ℕ)
    (α initial_count : K) {kMem k : ℕ} (hk : kMem ≤ k) :
    accInGate cur chld' fo α initial_count kMem k =
      (nodeListP cur kMem).eval α - (nodeListP cur k).eval α
        + initial_count * ∑ i ∈ Finset.Icc 1 k, childSum chld' fo α i := by
  have hmin : k ⊓ kMem = kMem := min_eq_right hk
  simp only [accInGate, hmin]

/-! ## The in-gate walk predicate -/

/-- **In-gate `RAP_walk` for a forest**.  Line/count recurrences are the paper's; only acc
    changes. -/
structure WalkSatInGate (cur : ℕ → K) (chld' : ℕ → ℕ → K) (fo : ℕ → ℕ)
    (ln count acc : ℕ → K) (α initial_count : K) (kMem h : ℕ) : Prop where
  /-- At least the first root row. -/
  hpos : 1 ≤ h
  /-- At least one root (`Corr:forest`, `:1002`). -/
  kpos : 1 ≤ kMem
  /-- Roots occupy a prefix of the table. -/
  kle : kMem ≤ h
  /-- `ln(1) = α`. -/
  ln1 : ln 1 = α
  /-- `ln(i+1) = α·ln(i)`. -/
  lnInc : ∀ i, 1 ≤ i → i < h → ln (i + 1) = α * ln i
  /-- `count(1) = initial_count·α^{fanout(1)}`. -/
  count1 : count 1 = initial_count * α ^ (fo 1)
  /-- `count(i+1) = count(i)·α^{fanout(i+1)}`. -/
  countInc : ∀ i, 1 ≤ i → i < h → count (i + 1) = count i * α ^ (fo (i + 1))
  /-- First row is a root: `acc(1) = initial_count·cc(1)`. -/
  accInit : acc 1
      = ∑ l ∈ Finset.Icc 1 (fo 1), α ^ l * initial_count * chld' 1 l
  /-- Step: dequeue only off roots. -/
  accStep : ∀ i, 1 ≤ i → i < h →
      deqCoeff (K := K) kMem (i + 1) * ln (i + 1) * cur (i + 1) + acc (i + 1) - acc i
        = ∑ l ∈ Finset.Icc 1 (fo (i + 1)), α ^ l * count i * chld' (i + 1) l

variable {cur : ℕ → K} {chld' : ℕ → ℕ → K} {fo : ℕ → ℕ} {ln count acc : ℕ → K}
variable {α initial_count : K} {kMem h : ℕ}

theorem WalkSatInGate.ln_closed (hw : WalkSatInGate cur chld' fo ln count acc α initial_count kMem h) :
    ∀ k, 1 ≤ k → k ≤ h → ln k = α ^ k := by
  intro k
  induction k with
  | zero => intro h1 _; omega
  | succ m ih =>
    intro _ hle
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; simpa using hw.ln1
    · rw [hw.lnInc m hm (by omega), ih hm (by omega)]; ring

theorem WalkSatInGate.count_closed
    (hw : WalkSatInGate cur chld' fo ln count acc α initial_count kMem h) :
    ∀ k, 1 ≤ k → k ≤ h → count k = initial_count * α ^ (Sf fo k) := by
  intro k
  induction k with
  | zero => intro h1 _; omega
  | succ m ih =>
    intro _ hle
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; rw [hw.count1, Sf_one]
    · rw [hw.countInc m hm (by omega), ih hm (by omega), Sf_succ, pow_add]; ring

theorem childSum_scale_init (chld' : ℕ → ℕ → K) (fo : ℕ → ℕ) (α initial_count : K) :
    (∑ l ∈ Finset.Icc 1 (fo 1), α ^ l * initial_count * chld' 1 l)
      = initial_count * childSum chld' fo α 1 := by
  have hcs : childSum chld' fo α 1 = ∑ l ∈ Finset.Icc 1 (fo 1), chld' 1 l * α ^ l := by
    unfold childSum; simp
  rw [hcs, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  ring

theorem childSum_scale_step (chld' : ℕ → ℕ → K) (fo : ℕ → ℕ)
    (α initial_count : K) (m : ℕ) :
    (∑ l ∈ Finset.Icc 1 (fo (m + 1)),
        α ^ l * (initial_count * α ^ Sf fo m) * chld' (m + 1) l)
      = initial_count * childSum chld' fo α (m + 1) := by
  unfold childSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  have : (m + 1) - 1 = m := by omega
  rw [this, pow_add]
  ring

/-- Telescoping closed form of the in-gate acc. -/
theorem accInGate_telescope
    (hw : WalkSatInGate cur chld' fo ln count acc α initial_count kMem h) :
    ∀ k, 1 ≤ k → k ≤ h →
      acc k = accInGate cur chld' fo α initial_count kMem k := by
  intro k
  induction k with
  | zero => intro h1 _; omega
  | succ m ih =>
    intro _ hle
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      have hinit := hw.accInit
      rw [childSum_scale_init] at hinit
      have hmin : (1 : ℕ) ⊓ kMem = 1 := min_eq_left hw.kpos
      have hnl : (nodeListP cur 1).eval α = cur 1 * α := by rw [nodeListP_eval]; simp
      have hsum : (∑ i ∈ Finset.Icc 1 1, childSum chld' fo α i) = childSum chld' fo α 1 := by
        simp
      simp only [accInGate, hmin, hnl, hsum, sub_self, zero_add]
      exact hinit
    · have hstep := hw.accStep m hm (by omega)
      rw [WalkSatInGate.ln_closed hw (m + 1) (by omega) (by omega),
          WalkSatInGate.count_closed hw m hm (by omega)] at hstep
      rw [childSum_scale_step] at hstep
      have ihm := ih hm (by omega)
      have hnl : (nodeListP cur (m + 1)).eval α
          = (nodeListP cur m).eval α + cur (m + 1) * α ^ (m + 1) := by
        rw [nodeListP_succ, eval_add, eval_mul, eval_C, eval_pow, eval_X]
      have hsum : (∑ j ∈ Finset.Icc 1 (m + 1), childSum chld' fo α j)
          = (∑ j ∈ Finset.Icc 1 m, childSum chld' fo α j) + childSum chld' fo α (m + 1) := by
        rw [Finset.sum_Icc_succ_top (by omega : (1 : ℕ) ≤ m + 1)]
      by_cases hroot : m + 1 ≤ kMem
      · have hdeq : deqCoeff (K := K) kMem (m + 1) = 0 := deqCoeff_of_le (K := K) hroot
        have hminN : (m + 1) ⊓ kMem = m + 1 := min_eq_left hroot
        have hminC : m ⊓ kMem = m := min_eq_left (le_trans (Nat.le_succ m) hroot)
        have hacc : acc (m + 1) = acc m + initial_count * childSum chld' fo α (m + 1) := by
          simp only [hdeq, zero_mul, zero_add] at hstep
          linear_combination hstep
        simp only [accInGate, hminN, hminC, hnl, hsum] at hacc ihm ⊢
        rw [hacc, ihm]
        ring
      · have hgt : kMem < m + 1 := Nat.lt_of_not_ge hroot
        have hdeq : deqCoeff (K := K) kMem (m + 1) = 1 := deqCoeff_of_gt (K := K) hgt
        have hminN : (m + 1) ⊓ kMem = kMem := min_eq_right (Nat.le_of_lt hgt)
        have hminC : m ⊓ kMem = kMem := min_eq_right (by omega)
        have hacc : acc (m + 1)
            = acc m - α ^ (m + 1) * cur (m + 1)
              + initial_count * childSum chld' fo α (m + 1) := by
          simp only [hdeq, one_mul] at hstep
          linear_combination hstep
        simp only [accInGate, hminN, hminC, hnl, hsum] at hacc ihm ⊢
        rw [hacc, ihm]
        ring

/-! ## Existence and the `:1006` identity -/

/-- The prover can build line/count/acc columns satisfying every in-gate walk constraint. -/
theorem walkSatInGate_exists (cur : ℕ → K) (chld' : ℕ → ℕ → K) (fo : ℕ → ℕ)
    (α initial_count : K) {kMem h : ℕ} (hh : 1 ≤ h) (hk : 1 ≤ kMem) (hle : kMem ≤ h) :
    ∃ ln count acc : ℕ → K,
      WalkSatInGate cur chld' fo ln count acc α initial_count kMem h := by
  refine ⟨fun k => α ^ k, fun k => initial_count * α ^ (Sf fo k),
    fun k => accInGate cur chld' fo α initial_count kMem k, ?_⟩
  refine
    { hpos := hh
      kpos := hk
      kle := hle
      ln1 := by simp
      lnInc := fun i _ _ => by rw [pow_succ]; ring
      count1 := by rw [Sf_one]
      countInc := fun i _ _ => by rw [Sf_succ, pow_add]; ring
      accInit := ?_
      accStep := ?_ }
  · have hmin : (1 : ℕ) ⊓ kMem = 1 := min_eq_left hk
    have hnl : (nodeListP cur 1).eval α = cur 1 * α := by rw [nodeListP_eval]; simp
    have hsum : (∑ i ∈ Finset.Icc 1 1, childSum chld' fo α i) = childSum chld' fo α 1 := by
      simp
    simp only [accInGate, hmin, hnl, hsum, sub_self, zero_add]
    exact (childSum_scale_init chld' fo α initial_count).symm
  · intro i hi hih
    have hnl : (nodeListP cur (i + 1)).eval α
        = (nodeListP cur i).eval α + cur (i + 1) * α ^ (i + 1) := by
      rw [nodeListP_succ, eval_add, eval_mul, eval_C, eval_pow, eval_X]
    have hsum : (∑ j ∈ Finset.Icc 1 (i + 1), childSum chld' fo α j)
        = (∑ j ∈ Finset.Icc 1 i, childSum chld' fo α j) + childSum chld' fo α (i + 1) := by
      rw [Finset.sum_Icc_succ_top (by omega : (1 : ℕ) ≤ i + 1)]
    have hkey : initial_count * childSum chld' fo α (i + 1)
        = ∑ l ∈ Finset.Icc 1 (fo (i + 1)),
            α ^ l * (initial_count * α ^ Sf fo i) * chld' (i + 1) l :=
      (childSum_scale_step chld' fo α initial_count i).symm
    by_cases hroot : i + 1 ≤ kMem
    · have hdeq : deqCoeff (K := K) kMem (i + 1) = 0 := deqCoeff_of_le (K := K) hroot
      have hminN : (i + 1) ⊓ kMem = i + 1 := min_eq_left hroot
      have hminC : i ⊓ kMem = i := min_eq_left (Nat.le_of_succ_le hroot)
      simp only [accInGate, hminN, hminC, hnl, hsum, hdeq, zero_mul, zero_add]
      linear_combination hkey
    · have hgt : kMem < i + 1 := Nat.lt_of_not_ge hroot
      have hdeq : deqCoeff (K := K) kMem (i + 1) = 1 := deqCoeff_of_gt (K := K) hgt
      have hminN : (i + 1) ⊓ kMem = kMem := min_eq_right (Nat.le_of_lt hgt)
      have hminC : i ⊓ kMem = kMem := min_eq_right (by omega)
      simp only [accInGate, hminN, hminC, hnl, hsum, hdeq, one_mul]
      linear_combination hkey

/-- The closed-form acc satisfies the masked step at every interior row. -/
theorem accInGate_accStep (cur : ℕ → K) (chld' : ℕ → ℕ → K) (fo : ℕ → ℕ)
    (α initial_count : K) (kMem i : ℕ) :
    deqCoeff (K := K) kMem (i + 1) * (α ^ (i + 1)) * cur (i + 1)
        + accInGate cur chld' fo α initial_count kMem (i + 1)
        - accInGate cur chld' fo α initial_count kMem i
      = ∑ l ∈ Finset.Icc 1 (fo (i + 1)),
          α ^ l * (initial_count * α ^ Sf fo i) * chld' (i + 1) l := by
  have hnl : (nodeListP cur (i + 1)).eval α
      = (nodeListP cur i).eval α + cur (i + 1) * α ^ (i + 1) := by
    rw [nodeListP_succ, eval_add, eval_mul, eval_C, eval_pow, eval_X]
  have hsum : (∑ j ∈ Finset.Icc 1 (i + 1), childSum chld' fo α j)
      = (∑ j ∈ Finset.Icc 1 i, childSum chld' fo α j) + childSum chld' fo α (i + 1) := by
    by_cases hi : 1 ≤ i + 1
    · rw [Finset.sum_Icc_succ_top hi]
    · omega
  have hkey : initial_count * childSum chld' fo α (i + 1)
      = ∑ l ∈ Finset.Icc 1 (fo (i + 1)),
          α ^ l * (initial_count * α ^ Sf fo i) * chld' (i + 1) l :=
    (childSum_scale_step chld' fo α initial_count i).symm
  by_cases hroot : i + 1 ≤ kMem
  · have hdeq : deqCoeff (K := K) kMem (i + 1) = 0 := deqCoeff_of_le (K := K) hroot
    have hminN : (i + 1) ⊓ kMem = i + 1 := min_eq_left hroot
    have hminC : i ⊓ kMem = i := min_eq_left (Nat.le_of_succ_le hroot)
    simp only [accInGate, hminN, hminC, hnl, hsum, hdeq, zero_mul, zero_add]
    linear_combination hkey
  · have hgt : kMem < i + 1 := Nat.lt_of_not_ge hroot
    have hdeq : deqCoeff (K := K) kMem (i + 1) = 1 := deqCoeff_of_gt (K := K) hgt
    have hminN : (i + 1) ⊓ kMem = kMem := min_eq_right (Nat.le_of_lt hgt)
    have hminC : i ⊓ kMem = kMem := min_eq_right (by omega)
    simp only [accInGate, hminN, hminC, hnl, hsum, hdeq, one_mul]
    linear_combination hkey

/-- **`:1006` identity.**  At the last row the in-gate acc is the paper's forest
    leftover `seed − node_list_h(α) + initial_count·Σ childSum` with
    `seed = node_list_{kMem}(α)`. -/
theorem ingate_seed_eq_forest_seed
    (hw : WalkSatInGate cur chld' fo ln count acc α initial_count kMem h) :
    acc h = (nodeListP cur kMem).eval α - (nodeListP cur h).eval α
      + initial_count * ∑ i ∈ Finset.Icc 1 h, childSum chld' fo α i := by
  rw [accInGate_telescope hw h hw.hpos (le_refl h), accInGate_of_ge_kMem _ _ _ _ _ hw.kle]

/-- Terminal zero iff the forest accepting identity at the paper seed. -/
theorem walkSatInGate_out_zero_iff
    (hw : WalkSatInGate cur chld' fo ln count acc α initial_count kMem h) :
    acc h = 0 ↔
      ForestAccepts cur chld' fo α ((nodeListP cur kMem).eval α) initial_count h := by
  rw [ingate_seed_eq_forest_seed hw]
  unfold ForestAccepts
  constructor
  · intro heq; linear_combination -heq
  · intro heq; rw [heq]; ring

/-- Perfect completeness: a full forest BFT closes the in-gate acc. -/
theorem walkSatInGate_completeness
    (hw : WalkSatInGate cur chld' fo ln count acc α initial_count kMem h)
    (hacc : ForestAccepts cur chld' fo α ((nodeListP cur kMem).eval α) initial_count h) :
    acc h = 0 :=
  (walkSatInGate_out_zero_iff hw).mpr hacc

/-! ## Agreement with `WalkSat` at `kMem = 1` -/

/-- At a single root the in-gate acc is `WalkSat`'s acc with `seed = ln(1)·cur(1)`. -/
theorem accInGate_eq_walkSat_of_kMem_one (cur : ℕ → K) (chld' : ℕ → ℕ → K) (fo : ℕ → ℕ)
    (α initial_count : K) {k : ℕ} (hk : 1 ≤ k) :
    accInGate cur chld' fo α initial_count 1 k
      = (nodeListP cur 1).eval α - (nodeListP cur k).eval α
        + initial_count * ∑ i ∈ Finset.Icc 1 k, childSum chld' fo α i :=
  accInGate_of_ge_kMem _ _ _ _ _ hk

theorem WalkSatInGate.toWalkSat_of_kMem_one
    (hw : WalkSatInGate cur chld' fo ln count acc α initial_count kMem h)
    (hk : kMem = 1) :
    WalkSat cur chld' fo ln count acc α (ln 1 * cur 1) initial_count h := by
  subst hk
  refine
    { hpos := hw.hpos
      ln1 := hw.ln1
      lnInc := hw.lnInc
      count1 := hw.count1
      countInc := hw.countInc
      accInit := ?_
      accStep := ?_ }
  · have hinit := hw.accInit
    rw [hinit]
    ring
  · intro i hi hih
    have hstep := hw.accStep i hi hih
    have hdeq : deqCoeff (K := K) 1 (i + 1) = 1 := deqCoeff_of_gt (K := K) (by omega)
    simpa [hdeq, one_mul] using hstep

/-- On rows `≥ kMem`, in-gate acc is `WalkSat`'s closed form at
    `seed = node_list_{kMem}(α)` (`Batch498` telescope). -/
theorem WalkSatInGate.acc_eq_walkSat_of_ge
    (hw : WalkSatInGate cur chld' fo ln count acc α initial_count kMem h)
    {k : ℕ} (hk1 : 1 ≤ k) (hkh : k ≤ h) (hk : kMem ≤ k) :
    acc k = (nodeListP cur kMem).eval α - (nodeListP cur k).eval α
      + initial_count * ∑ i ∈ Finset.Icc 1 k, childSum chld' fo α i := by
  rw [accInGate_telescope hw k hk1 hkh, accInGate_of_ge_kMem _ _ _ _ _ hk]

/-- Bridge: `WalkSat` at `seed := nodeListP kMem` exists, and its acc agrees
    with the in-gate acc on every row `≥ kMem`. -/
theorem WalkSatInGate.exists_walkSat_agree_ge
    (hw : WalkSatInGate cur chld' fo ln count acc α initial_count kMem h) :
    ∃ acc' : ℕ → K,
      WalkSat cur chld' fo ln count acc' α ((nodeListP cur kMem).eval α)
        initial_count h ∧
      ∀ k, 1 ≤ k → k ≤ h → kMem ≤ k → acc k = acc' k := by
  refine ⟨fun k => (nodeListP cur kMem).eval α - (nodeListP cur k).eval α
      + initial_count * ∑ i ∈ Finset.Icc 1 k, childSum chld' fo α i, ?_, ?_⟩
  · have hln : ∀ k, 1 ≤ k → k ≤ h → ln k = α ^ k := WalkSatInGate.ln_closed hw
    have hcnt : ∀ k, 1 ≤ k → k ≤ h → count k = initial_count * α ^ Sf fo k :=
      WalkSatInGate.count_closed hw
    refine
      { hpos := hw.hpos
        ln1 := hw.ln1
        lnInc := hw.lnInc
        count1 := hw.count1
        countInc := hw.countInc
        accInit := ?_
        accStep := ?_ }
    · have hnl : (nodeListP cur 1).eval α = cur 1 * α := by rw [nodeListP_eval]; simp
      have hkey : initial_count * (∑ j ∈ Finset.Icc 1 1, childSum chld' fo α j)
          = ∑ l ∈ Finset.Icc 1 (fo 1), α ^ l * initial_count * chld' 1 l := by
        rw [Finset.Icc_self, Finset.sum_singleton]
        unfold childSum
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l _
        rw [show (1 : ℕ) - 1 = 0 from rfl, Sf_zero, Nat.add_zero]
        ring
      rw [hw.ln1, hnl]
      linear_combination hkey
    · intro i hi hih
      have hnl : (nodeListP cur (i + 1)).eval α
          = (nodeListP cur i).eval α + cur (i + 1) * α ^ (i + 1) := by
        rw [nodeListP_succ, eval_add, eval_mul, eval_C, eval_pow, eval_X]
      have hsum : (∑ j ∈ Finset.Icc 1 (i + 1), childSum chld' fo α j)
          = (∑ j ∈ Finset.Icc 1 i, childSum chld' fo α j) + childSum chld' fo α (i + 1) := by
        rw [Finset.sum_Icc_succ_top (by omega : (1 : ℕ) ≤ i + 1)]
      have hcnti := hcnt i hi (by omega)
      have hlnip := hln (i + 1) (by omega) (by omega)
      have hkey : initial_count * childSum chld' fo α (i + 1)
          = ∑ l ∈ Finset.Icc 1 (fo (i + 1)),
              α ^ l * count i * chld' (i + 1) l := by
        rw [hcnti]
        exact (childSum_scale_step chld' fo α initial_count i).symm
      simp only [hlnip, hnl, hsum]
      linear_combination hkey
  · intro k hk1 hkh hk
    exact WalkSatInGate.acc_eq_walkSat_of_ge hw hk1 hkh hk

/-- `WalkSat` with `seed = ln(1)·cur(1)` is an in-gate walk at `kMem = 1`. -/
theorem WalkSat.toWalkSatInGate_of_seed {seed : K}
    (hw : WalkSat cur chld' fo ln count acc α seed initial_count h)
    (hseed : seed = ln 1 * cur 1) :
    WalkSatInGate cur chld' fo ln count acc α initial_count 1 h := by
  refine
    { hpos := hw.hpos
      kpos := le_rfl
      kle := hw.hpos
      ln1 := hw.ln1
      lnInc := hw.lnInc
      count1 := hw.count1
      countInc := hw.countInc
      accInit := ?_
      accStep := ?_ }
  · have hinit := hw.accInit
    rw [hseed, add_comm (∑ l ∈ Finset.Icc 1 (fo 1), α ^ l * initial_count * chld' 1 l)] at hinit
    exact add_left_cancel hinit
  · intro i hi hih
    have hstep := hw.accStep i hi hih
    have hdeq : deqCoeff (K := K) 1 (i + 1) = 1 :=
      deqCoeff_of_gt (K := K) (by omega)
    simpa [hdeq, one_mul] using hstep

end Walk
end Nock
