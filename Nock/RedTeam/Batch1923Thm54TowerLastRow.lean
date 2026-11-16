/-
  Nock/RedTeam/Batch1923Thm54TowerLastRow.lean

  **The last row's next environment is the interpolant extrapolation,
  not a wrap to row 0.**

  * NC `wrap_false` (finding of REPORT-C2d, scratch proof compiled here): on an injective orbit with the package's
    `AdjacentC` shape, `orderOf ω = 3·2^h` and `2 ≤ n ≤ 2^h`, the cyclic wrap `ω·x_{n−1} = x_0` is FALSE.  So
    C1g's `hadj` at the last row (`i' = succIdx n i = 0`) was unsatisfiable at honest data.
  * `lastPt_off_rows`: stronger — `ω·x_{n−1}` is no row node at all, so no wrap to ANY row is available.
  * `lag_at_node`: the Lagrange combination at a row node is that row (`pullNext_honestQT_lag` agrees with
    `honestQT_hFn` on the interior rows).
  * `TowerAssembled.lean` (changed): `residAt` reads row `j+1` for `j+1 < n` and the extrapolation `extRow`
    (`lagRow (lagW nodes (ω·x_{n−1}))` of the rows with `58/59` zeroed) at the last row; `nextFinal`,
    `residAt_eq`, `nextFinal_isK`, `honestQT_hFn_final`, `walkRowEnv_final` and `assembled_row` take the
    `AdjacentC`-shape adjacency `hadjC` (`i+1 < n` only); `succIdx` deleted.
-/
import Nock.NockVMROM.Thm54.VclL.Compute.TowerAssembled
import Nock.NockVMROM.Thm54.P8Core.SVCompute.QueueTwins
import Nock.NockVMROM.Thm54.P8Core.SVWalk.ExpAlign
import Nock.NockVMROM.Thm54.TraceGen.GenFormRAxisLambda

set_option autoImplicit false

namespace Nock.RedTeam.Batch1923

open Nock.NockVMROM.Thm54.VclL.Compute.TowerD
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Compute Module Nock.NockVMROM.Thm54.T0Tower

/-- Orbit nodes are powers of `ω` times `x_0`, from the `AdjacentC` shape. -/
theorem nodes_pow {F : Type} [Field F] {n : ℕ} (hn : 0 < n) (ω : F) (nodes : Fin n → F)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨i + 1, hi⟩ = ω * nodes i) :
    ∀ k (hk : k < n), nodes ⟨k, hk⟩ = ω ^ k * nodes ⟨0, hn⟩ := by
  intro k
  induction k with
  | zero => intro hk; simp
  | succ k ih => intro hk; rw [hadj ⟨k, by omega⟩ hk, ih (by omega)]; ring

/-- **NC (REPORT-C2d finding): the cyclic wrap is false at honest data.** -/
theorem wrap_false {F : Type} [Field F] (h n : ℕ) (hn : 0 < n) (hn2 : 2 ≤ n) (hle : n ≤ 2 ^ h) (ω : F)
    (hord : orderOf ω = 3 * 2 ^ h) (nodes : Fin n → F) (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨i + 1, hi⟩ = ω * nodes i)
    (hwrap : ω * nodes ⟨n - 1, by omega⟩ = nodes ⟨0, hn⟩) : False := by
  have key := nodes_pow hn ω nodes hadj
  have h1 := key (n - 1) (by omega)
  rw [h1] at hwrap
  have h0 : nodes ⟨0, hn⟩ ≠ 0 := by
    intro hz
    have h2 := key 1 (by omega)
    rw [hz, mul_zero] at h2
    exact absurd (hinj (h2.trans hz.symm)) (by simp [Fin.ext_iff])
  have hpow : ω ^ n = 1 := by
    have : ω ^ n * nodes ⟨0, hn⟩ = 1 * nodes ⟨0, hn⟩ := by
      rw [one_mul]
      have e : ω * ω ^ (n - 1) = ω ^ n := by rw [← pow_succ']; congr 1; omega
      rw [← e, mul_assoc, hwrap]
    exact mul_right_cancel₀ h0 this
  have := orderOf_dvd_of_pow_eq_one hpow
  rw [hord] at this
  have := Nat.le_of_dvd hn this
  omega

/-- **The last row's next point is no row node** (so the next environment there is genuinely the
extrapolation, not any row). -/
theorem lastPt_off_rows {F : Type} [Field F] (h n : ℕ) (hn : 0 < n) (hle : n ≤ 2 ^ h) (ω : F)
    (hord : orderOf ω = 3 * 2 ^ h) (nodes : Fin n → F) (hx0 : nodes ⟨0, hn⟩ ≠ 0)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨i + 1, hi⟩ = ω * nodes i) (k : Fin n) :
    lastPt nodes ω ≠ nodes k := by
  intro he
  have key := nodes_pow hn ω nodes hadj
  simp only [lastPt, dif_pos hn] at he
  rw [key (n - 1) (by omega), show k = ⟨k, k.isLt⟩ from rfl, key k k.isLt, ← mul_assoc, ← pow_succ'] at he
  have he' := mul_right_cancel₀ hx0 he
  have hk := k.isLt
  have hsplit : ω ^ (n - 1 + 1) = ω ^ (n - k) * ω ^ (k : ℕ) := by rw [← pow_add]; congr 1; omega
  rw [hsplit] at he'
  have hω : ω ≠ 0 := by
    intro h0; rw [h0, orderOf_eq_zero_iff'.mpr (by intro m hm h; simp [zero_pow (by omega : m ≠ 0)] at h)] at hord
    have : 0 < 3 * 2 ^ h := by positivity
    omega
  have hone : ω ^ (n - k) = 1 := by
    have := mul_right_cancel₀ (pow_ne_zero _ hω) (he'.trans (one_mul _).symm)
    exact this
  have hd := orderOf_dvd_of_pow_eq_one hone
  rw [hord] at hd
  have := Nat.le_of_dvd (by omega) hd
  have : 0 < 2 ^ h := by positivity
  omega

/-- **Consistency**: at a row node the Lagrange combination reads that row (so the extrapolation lemma
`pullNext_honestQT_lag` agrees with `honestQT_hFn` on interior rows). -/
theorem lag_at_node {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K]
    {δ : F} [Fact (¬ IsSquare (algebraMap F K δ))] (b : Basis (Fin 3) F K) {n : ℕ} (nodes : Fin n → F)
    (hinj : Function.Injective nodes) (rows : Fin n → TowerRowVals (K := K) δ) (j : Fin n) (c : ℕ) :
    srcColT b (lagRow (lagW nodes (nodes j)) rows) c = srcColT b (rows j) c := by
  rw [srcColT_lagRow, Finset.sum_eq_single j]
  · rw [lagW, Lagrange.eval_basis_self hinj.injOn (Finset.mem_univ j), one_mul]
  · intro k _ hk
    rw [lagW, Lagrange.eval_basis_of_ne hk (Finset.mem_univ j), zero_mul]
  · intro hj; exact absurd (Finset.mem_univ j) hj

end Nock.RedTeam.Batch1923

#print axioms Nock.RedTeam.Batch1923.wrap_false
#print axioms Nock.RedTeam.Batch1923.lastPt_off_rows
#print axioms Nock.RedTeam.Batch1923.lag_at_node
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD in
#print axioms srcColT_lagRow
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD in
#print axioms pullNext_honestQT_lag
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD in
#print axioms residAt_eq
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD in
#print axioms residAt_zero_isK
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD in
#print axioms nextFinal_isK
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD in
#print axioms honestQT_hFn_final
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD in
#print axioms walkRowEnv_final
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD in
#print axioms assembled_row
