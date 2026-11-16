import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesCarrier
import Nock.NockVMROM.Thm54.P8EventEv
import Mathlib.FieldTheory.Finite.Basic

/-!
# The divisor repricing, the leaf-count tower, `hΛK`

* §1 `leafBound_ge_tower`, `hLp_hp64_exclude`: `programLeafBound` counts leaves with multiplicity,
  so a `k`-level shared tower subject has `2^k ≤ programLeafBound`; `hΛp` and `hp64` then exclude it.
* §2 `lowOrderRootSeeds_card_le_divisors`: the size-window root union is priced by the divisors
  of `|𝕂| − 1`, not by `Σ_{d ≤ Λ} d`.
* §3 `hLambdaK`: the named window Prop; `hLambdaK_of_hΛp` (the old hypothesis implies it);
  `hLambdaK_of_tau` and the Goldilocks numerals.
* §4 `p8WorkEvK`: `p8WorkEv` with the divisor sum, `≤ p8WorkEv`.
-/

open Nock Nock.Walk Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.TraceGen
  Nock.NockVMROM.Thm54.P8EventEv

namespace Nock.NockVMROM.Thm54.TightWindow

/-! ## §1 The leaf window counts with multiplicity -/

/-- All-zero shared tower: `k+1` distinct DAG nodes, `2^k` leaves. -/
def zero : ℕ → Noun
  | 0 => .atom 0
  | k + 1 => .cell (zero k) (zero k)

theorem zero_leaves (k : ℕ) : (zero k).leaves = 2 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [zero, Noun.leaves, ih, pow_succ]; ring

abbrev form0 : Noun := .cell (.atom 1) (.atom 0)

section Tower
variable {K : Type} [Field K]

abbrev Tk (k : ℕ) : NTree (GenComputeRow K) :=
  .node (skelNode (genSkelOp1 (zero k) form0 (.atom 0) (.atom 1)) [⟨form0, .atom 0, 3, 0⟩]) []

theorem genk (k : ℕ) : genComputeSkeleton (K := K) 1 (zero k) form0 = .ok (Tk k, .atom 0) := by
  simp [genComputeSkeleton]

theorem romTreek (k : ℕ) (h : evalRom 1 (zero k) form0 = some (.atom 0)) :
    romTree (K := K) h = Tk k := by
  have hs := romTree_spec (K := K) h
  rw [genk] at hs
  injection hs with hs
  exact (Prod.mk.inj hs).1.symm

theorem airk (k : ℕ) : airReorder (Tk (K := K) k) = Tk k := by
  simp [airReorder, skelNode, genSkelOp1, airNeedsSwap]

theorem bfs_leaf' {LT : Type} (g : LT) : bfsForest [NTree.node g []] = [NTree.node g []] := by
  rw [bfsForest_cons_eq _ (by simp)]; simp [NTree.children, bfsForest_nil]

theorem bfsRowsk (k : ℕ) : bfsRows (Tk (K := K) k) =
    [skelNode (genSkelOp1 (zero k) form0 (.atom 0) (.atom 1)) [⟨form0, .atom 0, 3, 0⟩]] := by
  simp [bfsRows, bfs_leaf']

/-- **The compiler window is the subject's leaf count with multiplicity.** -/
theorem leafBound_ge_tower (k : ℕ) (h : evalRom 1 (zero k) form0 = some (.atom 0)) :
    2 ^ k ≤ programLeafBound (airReorder (romTree (K := K) h)) := by
  rw [romTreek, airk, programLeafBound, bfsRowsk]
  simp [rowNounsBound, skelNode, genSkelOp1, zero_leaves]

/-- **`hΛp ∧ hp64` exclude a 64-level shared subject (65 distinct DAG nodes).** -/
theorem hLp_hp64_exclude (k p : ℕ) (hk : 64 ≤ k) (h : evalRom 1 (zero k) form0 = some (.atom 0))
    (hΛp : programLeafBound (airReorder (romTree (K := K) h)) < p) : ¬ p < 2 ^ 64 := by
  have h1 := leafBound_ge_tower (K := K) k h
  have h2 : 2 ^ 64 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  omega

/-- The run exists, so the restriction is real. -/
theorem evalRom_zero (k : ℕ) : evalRom 1 (zero k) form0 = some (.atom 0) := by simp [evalRom]

end Tower

/-! ## §2 Divisor repricing of the size-window root union -/

section Divisors
open SizeWindowCounting
variable {K : Type} [Field K]

/-- **Divisor pricing.**  `z^d = 1` with `1 ≤ d ≤ Λ` forces `orderOf z ∣ |K| − 1` and
`orderOf z ≤ Λ`, so the union is covered by the root sets of the divisors of `|K| − 1` below `Λ`.
Replaces `sizeWindowRootBound Λ = Σ_{d ≤ Λ} d`. -/
theorem lowOrderRootSeeds_card_le_divisors [Fintype K] [DecidableEq K] (Λ : ℕ) :
    (lowOrderRootSeeds (K := K) Λ).card ≤
      ∑ d ∈ (Fintype.card K - 1).divisors.filter (· ≤ Λ), d := by
  classical
  have hsub : lowOrderRootSeeds (K := K) Λ ⊆
      ((Fintype.card K - 1).divisors.filter (· ≤ Λ)).biUnion
        (fun d => Polynomial.nthRootsFinset d (1 : K)) := by
    intro z hz
    simp only [lowOrderRootSeeds, Finset.mem_biUnion, Finset.mem_Icc] at hz
    obtain ⟨d, ⟨hd1, hdΛ⟩, hzd⟩ := hz
    have hd0 : 0 < d := hd1
    have hpow : z ^ d = 1 := (Polynomial.mem_nthRootsFinset hd0 (1 : K)).mp hzd
    have hz0 : z ≠ 0 := by
      rintro rfl; rw [zero_pow (Nat.pos_iff_ne_zero.mp hd0)] at hpow; exact zero_ne_one hpow
    have hdvd : orderOf z ∣ d := orderOf_dvd_of_pow_eq_one hpow
    have hdvdq : orderOf z ∣ Fintype.card K - 1 :=
      orderOf_dvd_of_pow_eq_one (FiniteField.pow_card_sub_one_eq_one z hz0)
    have hq : Fintype.card K - 1 ≠ 0 := by
      have : 1 < Fintype.card K := Fintype.one_lt_card
      omega
    have hopos : 0 < orderOf z :=
      orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨d, hd0, hpow⟩)
    simp only [Finset.mem_biUnion, Finset.mem_filter, Nat.mem_divisors]
    exact ⟨orderOf z, ⟨⟨hdvdq, hq⟩, le_trans (Nat.le_of_dvd hd0 hdvd) hdΛ⟩,
      (Polynomial.mem_nthRootsFinset hopos (1 : K)).mpr (pow_orderOf_eq_one z)⟩
  calc (lowOrderRootSeeds (K := K) Λ).card
      ≤ (((Fintype.card K - 1).divisors.filter (· ≤ Λ)).biUnion
          (fun d => Polynomial.nthRootsFinset d (1 : K))).card := Finset.card_le_card hsub
    _ ≤ ∑ d ∈ (Fintype.card K - 1).divisors.filter (· ≤ Λ),
          (Polynomial.nthRootsFinset d (1 : K)).card := Finset.card_biUnion_le
    _ ≤ _ := Finset.sum_le_sum fun d _ => nthRootsFinset_card_le d

end Divisors

/-- Closed linear majorant: `≤ τ(q) · Λ`. -/
theorem divisorSum_le_tau_mul (q Λ : ℕ) :
    ∑ d ∈ q.divisors.filter (· ≤ Λ), d ≤ q.divisors.card * Λ := by
  calc ∑ d ∈ q.divisors.filter (· ≤ Λ), d
      ≤ ∑ _d ∈ q.divisors.filter (· ≤ Λ), Λ :=
        Finset.sum_le_sum fun d hd => (Finset.mem_filter.mp hd).2
    _ = (q.divisors.filter (· ≤ Λ)).card * Λ := by simp
    _ ≤ q.divisors.card * Λ := Nat.mul_le_mul_right _ (Finset.card_filter_le _ _)

/-- The divisor sum is below the triangular sum `Σ_{d ≤ Λ} d` (divisors are positive). -/
theorem divisorSum_le_sizeWindowRootBound (q Λ : ℕ) :
    ∑ d ∈ q.divisors.filter (· ≤ Λ), d ≤ SizeWindowCounting.sizeWindowRootBound Λ := by
  unfold SizeWindowCounting.sizeWindowRootBound
  apply Finset.sum_le_sum_of_subset
  intro d hd
  obtain ⟨hd1, hd2⟩ := Finset.mem_filter.mp hd
  exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd1, hd2⟩

/-! ## §3 The window `hΛK` -/

/-- **`hΛK`**: `1 + (3 + 13R)(2Λ − 1) + Σ_{d ∣ p^e − 1, d ≤ Λ} d < p^e`. -/
def hLambdaK (p e R Λ : ℕ) : Prop :=
  1 + (3 + 13 * R) * (2 * Λ - 1) + ∑ d ∈ (p ^ e - 1).divisors.filter (· ≤ Λ), d < p ^ e

/-- **`hΛp ⇒ hΛK`** (with the row bound and the `25 ≤ p` floor the old consumer already takes):
the new hypothesis is a strict weakening of the assumptions at `e = 3`. -/
theorem hLambdaK_of_hΛp {p R Λ : ℕ} (hrows : R < p) (hΛp : Λ < p) (hp : 25 ≤ p) :
    hLambdaK p 3 R Λ := by
  have h := seedBudgetVcomp_lt_pow_of_bounds_twenty_five hrows hΛp hp
  have hs := divisorSum_le_sizeWindowRootBound (p ^ 3 - 1) Λ
  unfold hLambdaK
  unfold GoodSeed.seedBudget at h
  have hsum : (3 + 13 * R) * (2 * Λ - 1) =
      (3 + 10 * R) * (2 * Λ - 1) + 3 * R * (2 * Λ - 1) := by ring
  omega

/-- Same, at every exponent `e ≥ 3`. -/
theorem hLambdaK_of_hΛp_pow {p e R Λ : ℕ} (he : 3 ≤ e) (hrows : R < p) (hΛp : Λ < p)
    (hp : 25 ≤ p) : hLambdaK p e R Λ := by
  have h3 := hLambdaK_of_hΛp hrows hΛp hp
  have hs := divisorSum_le_sizeWindowRootBound (p ^ e - 1) Λ
  have h3' : 1 + (3 + 13 * R) * (2 * Λ - 1) + SizeWindowCounting.sizeWindowRootBound Λ < p ^ 3 := by
    have hseed := seedBudgetVcomp_lt_pow_of_bounds_twenty_five hrows hΛp hp
    unfold GoodSeed.seedBudget at hseed
    have hsum : (3 + 13 * R) * (2 * Λ - 1) =
        (3 + 10 * R) * (2 * Λ - 1) + 3 * R * (2 * Λ - 1) := by ring
    omega
  have hp0 : 1 ≤ p := by omega
  have hle : p ^ 3 ≤ p ^ e := Nat.pow_le_pow_right hp0 he
  unfold hLambdaK
  omega

/-- `hΛK` from a bound `τ` on the number of divisors of `p^e − 1` (the divisor count is MEASURED
at Goldilocks, not proved here: see the report). -/
theorem hLambdaK_of_tau {p e R Λ τ : ℕ} (hτ : (p ^ e - 1).divisors.card ≤ τ)
    (h : 1 + (3 + 13 * R) * (2 * Λ - 1) + τ * Λ < p ^ e) : hLambdaK p e R Λ := by
  have := divisorSum_le_tau_mul (p ^ e - 1) Λ
  have h2 : (p ^ e - 1).divisors.card * Λ ≤ τ * Λ := Nat.mul_le_mul_right _ hτ
  unfold hLambdaK
  omega

/-- Goldilocks prime. -/
def pG : ℕ := 2 ^ 64 - 2 ^ 32 + 1

/-- Numeral at the tower field: any `τ ≤ 2^200` suffices (measured `τ(p⁶−1) = 835584`). -/
theorem hLambdaK6_goldilocks (τ R : ℕ) (hτ : τ ≤ 2 ^ 200) (hR : R ≤ 2 ^ 32) :
    1 + (3 + 13 * R) * (2 * 2 ^ 110 - 1) + τ * 2 ^ 110 < pG ^ 6 := by
  have h1 : (3 + 13 * R) * (2 * 2 ^ 110 - 1) ≤ (3 + 13 * 2 ^ 32) * (2 * 2 ^ 110 - 1) :=
    Nat.mul_le_mul_right _ (Nat.add_le_add_left (Nat.mul_le_mul_left _ hR) _)
  have h2 : τ * 2 ^ 110 ≤ 2 ^ 200 * 2 ^ 110 := Nat.mul_le_mul_right _ hτ
  calc 1 + (3 + 13 * R) * (2 * 2 ^ 110 - 1) + τ * 2 ^ 110
      ≤ 1 + (3 + 13 * 2 ^ 32) * (2 * 2 ^ 110 - 1) + 2 ^ 200 * 2 ^ 110 :=
        Nat.add_le_add (Nat.add_le_add_left h1 _) h2
    _ < pG ^ 6 := by norm_num [pG]

/-- Numeral at `p³`, at the measured `τ(p³−1) = 12672`. -/
theorem hLambdaK3_goldilocks (R : ℕ) (hR : R ≤ 2 ^ 32) :
    1 + (3 + 13 * R) * (2 * 2 ^ 110 - 1) + 12672 * 2 ^ 110 < pG ^ 3 := by
  have h1 : (3 + 13 * R) * (2 * 2 ^ 110 - 1) ≤ (3 + 13 * 2 ^ 32) * (2 * 2 ^ 110 - 1) :=
    Nat.mul_le_mul_right _ (Nat.add_le_add_left (Nat.mul_le_mul_left _ hR) _)
  calc 1 + (3 + 13 * R) * (2 * 2 ^ 110 - 1) + 12672 * 2 ^ 110
      ≤ 1 + (3 + 13 * 2 ^ 32) * (2 * 2 ^ 110 - 1) + 12672 * 2 ^ 110 :=
        Nat.add_le_add_right (Nat.add_le_add_left h1 _) _
    _ < pG ^ 3 := by norm_num [pG]

/-- `hΛK` at `p³`, `Λ = 2^110`, given `τ(p³−1) ≤ 12672` (measured). -/
theorem hLambdaK3_goldilocks_hΛK (R : ℕ) (hR : R ≤ 2 ^ 32)
    (hτ : (pG ^ 3 - 1).divisors.card ≤ 12672) : hLambdaK pG 3 R (2 ^ 110) :=
  hLambdaK_of_tau (p := pG) (e := 3) (R := R) (Λ := 2 ^ 110) (τ := 12672) hτ
    (hLambdaK3_goldilocks R hR)

/-- `hΛK` at `p⁶`, `Λ = 2^110`, given any `τ(p⁶−1) ≤ 2^200` (measured `835584`). -/
theorem hLambdaK6_goldilocks_hΛK (R : ℕ) (hR : R ≤ 2 ^ 32)
    (hτ : (pG ^ 6 - 1).divisors.card ≤ 2 ^ 200) : hLambdaK pG 6 R (2 ^ 110) :=
  hLambdaK_of_tau (p := pG) (e := 6) (R := R) (Λ := 2 ^ 110) (τ := 2 ^ 200) hτ
    (hLambdaK6_goldilocks (2 ^ 200) R le_rfl hR)


/-- `p8WorkEv` with the size-window slot priced by the divisors of `q = |𝕂| − 1`. -/
def p8WorkEvK (q N M Λ : ℕ) : ℕ :=
  1 + (3 + 19 * N) * (2 * Λ - 1) + (24 * N + 8 * M) + axisUniformWorkload N M +
    ∑ d ∈ q.divisors.filter (· ≤ Λ), d

/-- **The repriced numerator is below the old one, for every `q`.** -/
theorem p8WorkEvK_le (q N M Λ : ℕ) : p8WorkEvK q N M Λ ≤ p8WorkEv N M Λ := by
  have := divisorSum_le_sizeWindowRootBound q Λ
  unfold p8WorkEvK p8WorkEv
  omega

/-- At `|𝕂| = p^e`. -/
theorem p8WorkEvK_pow_le (p e N M Λ : ℕ) : p8WorkEvK (p ^ e - 1) N M Λ ≤ p8WorkEv N M Λ :=
  p8WorkEvK_le _ _ _ _

/-- Linear closed form: `≤ p8WorkEv` with the window `τ·Λ`. -/
theorem p8WorkEvK_le_tau (q N M Λ : ℕ) :
    p8WorkEvK q N M Λ ≤
      1 + (3 + 19 * N) * (2 * Λ - 1) + (24 * N + 8 * M) + axisUniformWorkload N M +
        q.divisors.card * Λ := by
  have := divisorSum_le_tau_mul q Λ
  unfold p8WorkEvK
  omega

end Nock.NockVMROM.Thm54.TightWindow
