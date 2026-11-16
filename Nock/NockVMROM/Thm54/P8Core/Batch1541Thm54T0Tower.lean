/-
  Nock/NockVMROM/Thm54/P8Core/Batch1541Thm54T0Tower.lean

  **The quadratic tower `𝕂′ = 𝕂(√δ)` as a field.**

  * `nonsquare_lift` — a base non-square stays a non-square in a cubic (odd-degree) extension;
  * `quad_irreducible`, `Quad` (`= 𝕂[X]/(X² − δ)`) with its `Field` instance under
    `Fact (¬ IsSquare δ)`, `quad_finrank`, `quad_card : |𝕂′| = |𝕂|²`;
  * coordinates `Quad.mk δ a b = a + b·√δ`, `mk_mul`, `mk_injective`, `Quad.equiv : 𝕂 × 𝕂 ≃ 𝕂′`,
    `Quad.re` / `Quad.im`, `mk_inv`;
  * `tower_pair_collision_prob` — `NPR.collision_card_le_tight` is field-generic, so one seed in 𝕂′
    gives `(2Λ−1)/|𝕂|²` per pair; `tower_beats_two_seeds`;
  * `tower_window_card_le` — the low-order-root window at 𝕂′ is priced by the divisors of
    `|𝕂|² − 1` (`lowOrderRootSeeds_card_le_divisors` is field-generic).
-/
import Nock.NPR
import Nock.NockVMROM.Thm54.SizeWindowCounting
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.RingTheory.AdjoinRoot

namespace Nock.NockVMROM.Thm54.T0Tower

open Polynomial

/-! ## A base non-square stays a non-square in a cubic extension -/

section Lift
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype F] [Fintype K]

theorem odd_card_cube_div_two {q : ℕ} (hq : q % 2 = 1) :
    q ^ 3 / 2 = (q / 2) * (q ^ 2 + q + 1) := by
  obtain ⟨k, hk⟩ : ∃ k, q = 2 * k + 1 := ⟨q / 2, by omega⟩
  subst hk
  have h1 : (2 * k + 1) ^ 3 = 2 * (k * ((2 * k + 1) ^ 2 + (2 * k + 1) + 1)) + 1 := by ring
  have h2 : (2 * k + 1) / 2 = k := by omega
  rw [h1, h2, Nat.mul_add_div (by norm_num)]
  simp

theorem odd_sq_add_self_add_one {q : ℕ} (hq : q % 2 = 1) : Odd (q ^ 2 + q + 1) := by
  obtain ⟨k, hk⟩ : ∃ k, q = 2 * k + 1 := ⟨q / 2, by omega⟩
  subst hk
  exact ⟨2 * k ^ 2 + 3 * k + 1, by ring⟩

/-- **A base non-square stays a non-square in the cubic extension** (Euler's criterion,
`[𝕂 : 𝔽] = 3` odd). -/
theorem nonsquare_lift (hF2 : ringChar F ≠ 2) (hK2 : ringChar K ≠ 2)
    (hK : Module.finrank F K = 3) (δ : F) (hδ0 : δ ≠ 0) (hδ : ¬ IsSquare δ) :
    ¬ IsSquare (algebraMap F K δ) := by
  have hqF : Fintype.card F % 2 = 1 := FiniteField.odd_card_of_char_ne_two hF2
  have hneg : δ ^ (Fintype.card F / 2) = -1 := by
    rcases FiniteField.pow_dichotomy hF2 hδ0 with h | h
    · exact absurd ((FiniteField.isSquare_iff hF2 hδ0).mpr h) hδ
    · exact h
  have hcard : Fintype.card K = Fintype.card F ^ 3 := by
    rw [Module.card_eq_pow_finrank (K := F) (V := K), hK]
  have hδK0 : algebraMap F K δ ≠ 0 := by
    intro h; exact hδ0 ((map_eq_zero _).mp h)
  rw [FiniteField.isSquare_iff hK2 hδK0, hcard, odd_card_cube_div_two hqF, pow_mul, ← map_pow,
    hneg, map_neg, map_one, Odd.neg_one_pow (odd_sq_add_self_add_one hqF)]
  exact Ring.neg_one_ne_one_of_char_ne_two hK2

end Lift

/-! ## The tower `𝕂′ = 𝕂[X]/(X² − δ)` -/

section Tower
variable {K : Type} [Field K]

/-- The tower polynomial `X² − δ` is irreducible over `𝕂` when `δ` is not a square there. -/
theorem tower_irreducible (δ : K) (hδ : ¬ IsSquare δ) : Irreducible (X ^ 2 - C δ) :=
  X_pow_sub_C_irreducible_of_prime Nat.prime_two (fun b hb => hδ ⟨b, by rw [← hb]; ring⟩)

/-- `𝕂′ = 𝕂(√δ) := 𝕂[X]/(X² − δ)`. -/
abbrev Quad (δ : K) : Type := AdjoinRoot (X ^ 2 - C δ : K[X])

instance quadFactIrreducible (δ : K) [h : Fact (¬ IsSquare δ)] :
    Fact (Irreducible (X ^ 2 - C δ : K[X])) := ⟨tower_irreducible δ h.out⟩

theorem quad_poly_ne_zero (δ : K) : (X ^ 2 - C δ : K[X]) ≠ 0 := by
  intro h
  have := congrArg natDegree h
  rw [natDegree_X_pow_sub_C, natDegree_zero] at this
  exact absurd this (by norm_num)

/-- `[𝕂′ : 𝕂] = 2`. -/
theorem quad_finrank (δ : K) : Module.finrank K (Quad δ) = 2 := by
  rw [(AdjoinRoot.powerBasis (quad_poly_ne_zero δ)).finrank, AdjoinRoot.powerBasis_dim,
    natDegree_X_pow_sub_C]

noncomputable instance quadFintype [Fintype K] (δ : K) : Fintype (Quad δ) :=
  Module.fintypeOfFintype (AdjoinRoot.powerBasis (quad_poly_ne_zero δ)).basis

/-- `|𝕂′| = |𝕂|²`. -/
theorem quad_card [Fintype K] (δ : K) : Fintype.card (Quad δ) = Fintype.card K ^ 2 := by
  rw [Module.card_eq_pow_finrank (K := K) (V := Quad δ), quad_finrank]

end Tower

/-! ## Coordinates `a + b·√δ` -/

namespace Quad

variable {K : Type} [Field K] (δ : K)

/-- The adjoined root `√δ`. -/
noncomputable def r : Quad δ := AdjoinRoot.root _

theorem r_sq : r δ ^ 2 = algebraMap K (Quad δ) δ := by
  have h := AdjoinRoot.eval₂_root (X ^ 2 - C δ : K[X])
  simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C] at h
  exact sub_eq_zero.mp h

/-- The element `a + b·√δ` of `𝕂′`. -/
noncomputable def mk (a b : K) : Quad δ := algebraMap K (Quad δ) a + algebraMap K (Quad δ) b * r δ

theorem mk_add (a b c d : K) : mk δ a b + mk δ c d = mk δ (a + c) (b + d) := by
  simp only [mk, map_add]; ring

theorem mk_sub (a b c d : K) : mk δ a b - mk δ c d = mk δ (a - c) (b - d) := by
  simp only [mk, map_sub]; ring

/-- **`(a + b√δ)(c + d√δ) = (ac + δ·bd) + (ad + bc)√δ`** — the formula `qmul` encodes. -/
theorem mk_mul (a b c d : K) :
    mk δ a b * mk δ c d = mk δ (a * c + δ * (b * d)) (a * d + b * c) := by
  simp only [mk, map_add, map_mul]
  linear_combination (algebraMap K (Quad δ) b * algebraMap K (Quad δ) d) * r_sq δ

theorem mk_smul (c a b : K) : algebraMap K (Quad δ) c * mk δ a b = mk δ (c * a) (c * b) := by
  simp only [mk, map_mul]; ring

theorem mk_zero' : mk δ 0 0 = 0 := by simp [mk]
theorem mk_one' : mk δ 1 0 = 1 := by simp [mk]
theorem mk_base (a : K) : mk δ a 0 = algebraMap K (Quad δ) a := by simp [mk]

variable [Fact (¬ IsSquare δ)]

theorem mk_injective : Function.Injective (fun p : K × K => mk δ p.1 p.2) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [mk] at h
  have h1 : algebraMap K (Quad δ) (a - c) = algebraMap K (Quad δ) (d - b) * r δ := by
    rw [map_sub, map_sub]; linear_combination h
  by_cases hbd : d - b = 0
  · rw [hbd, map_zero, zero_mul] at h1
    have hac : a - c = 0 := (map_eq_zero _).mp h1
    have hb : b = d := (sub_eq_zero.mp hbd).symm
    have ha : a = c := sub_eq_zero.mp hac
    rw [ha, hb]
  · exfalso
    apply (Fact.out : ¬ IsSquare δ)
    refine ⟨(a - c) / (d - b), ?_⟩
    apply (algebraMap K (Quad δ)).injective
    have hd0 : algebraMap K (Quad δ) (d - b) ≠ 0 := fun h0 => hbd ((map_eq_zero _).mp h0)
    have hr : r δ = algebraMap K (Quad δ) ((a - c) / (d - b)) := by
      rw [map_div₀, eq_div_iff hd0, h1]; ring
    rw [map_mul, ← hr, ← pow_two, r_sq]

theorem mk_eq_mk_iff (a b c d : K) : mk δ a b = mk δ c d ↔ a = c ∧ b = d := by
  constructor
  · intro h
    have := mk_injective δ (a₁ := (a, b)) (a₂ := (c, d)) h
    simpa [Prod.ext_iff] using this
  · rintro ⟨rfl, rfl⟩; rfl

theorem mk_eq_zero_iff (a b : K) : mk δ a b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    have := mk_injective δ (a₁ := (a, b)) (a₂ := (0, 0)) (by simpa [mk_zero'] using h)
    simpa [Prod.ext_iff] using this
  · rintro ⟨rfl, rfl⟩; exact mk_zero' δ

theorem mk_bijective [Fintype K] : Function.Bijective (fun p : K × K => mk δ p.1 p.2) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨mk_injective δ, ?_⟩
  rw [quad_card, Fintype.card_prod, sq]

/-- `𝕂′ ≃ 𝕂 × 𝕂`, the coordinate equivalence in the basis `{1, √δ}`. -/
noncomputable def equiv [Fintype K] : K × K ≃ Quad δ := Equiv.ofBijective _ (mk_bijective δ)

/-- Real coordinate. -/
noncomputable def re [Fintype K] (x : Quad δ) : K := ((equiv δ).symm x).1
/-- Imaginary coordinate. -/
noncomputable def im [Fintype K] (x : Quad δ) : K := ((equiv δ).symm x).2

theorem mk_re_im [Fintype K] (x : Quad δ) : mk δ (re δ x) (im δ x) = x :=
  (equiv δ).apply_symm_apply x

theorem re_mk [Fintype K] (a b : K) : re δ (mk δ a b) = a := by
  have := (equiv δ).symm_apply_apply (a, b)
  simpa [equiv, re] using congrArg Prod.fst this

theorem im_mk [Fintype K] (a b : K) : im δ (mk δ a b) = b := by
  have := (equiv δ).symm_apply_apply (a, b)
  simpa [equiv, im] using congrArg Prod.snd this

/-- The explicit inverse `(a + b√δ)⁻¹ = (a − b√δ)/(a² − δb²)`. -/
theorem mk_inv (a b : K) (hab : ¬ (a = 0 ∧ b = 0)) :
    (mk δ a b)⁻¹ = mk δ (a / (a * a - δ * (b * b))) (-b / (a * a - δ * (b * b))) := by
  have hN : a * a - δ * (b * b) ≠ 0 := by
    intro h
    apply hab
    by_cases hb : b = 0
    · subst hb
      have : a * a = 0 := by linear_combination h
      exact ⟨mul_self_eq_zero.mp this, rfl⟩
    · exfalso
      apply (Fact.out : ¬ IsSquare δ)
      refine ⟨a / b, ?_⟩
      field_simp
      linear_combination -h
  have hne : mk δ a b ≠ 0 := fun h0 => hab ((mk_eq_zero_iff δ a b).mp h0)
  rw [inv_eq_of_mul_eq_one_right]
  rw [mk_mul]
  have e1 : a * (a / (a * a - δ * (b * b))) + δ * (b * (-b / (a * a - δ * (b * b)))) = 1 := by
    have : a * (a / (a * a - δ * (b * b))) + δ * (b * (-b / (a * a - δ * (b * b))))
        = (a * a - δ * (b * b)) / (a * a - δ * (b * b)) := by ring
    rw [this, div_self hN]
  have e2 : a * (-b / (a * a - δ * (b * b))) + b * (a / (a * a - δ * (b * b))) = 0 := by
    field_simp; ring
  rw [e1, e2, mk_one']

end Quad

/-! ## Per-pair collision in the tower -/

section Collision
variable {K : Type} [Field K] [Fintype K]

open Nock in
/-- **Per-pair collision in the tower**: the same `2Λ − 1` roots (`NPR.collision_card_le_tight`
is field-generic), now over `|𝕂|²` seeds: probability `≤ (2Λ−1)/|𝕂|²`. -/
theorem tower_pair_collision_prob (δ : K) [Fact (¬ IsSquare δ)]
    [DecidableEq (Quad δ)] (Λ : ℕ) (n₁ n₂ : Noun)
    (h₁ : n₁.leaves ≤ Λ) (h₂ : n₂.leaves ≤ Λ)
    (hne : (NPR.leafF (K := Quad δ) n₁, NPR.dyckBits (K := Quad δ) n₁) ≠
      (NPR.leafF (K := Quad δ) n₂, NPR.dyckBits (K := Quad δ) n₂)) :
    ((Finset.univ.filter (fun r : Quad δ => NPR.fn n₁ r = NPR.fn n₂ r)).card : ℚ) /
        (Fintype.card (Quad δ) : ℚ) ≤ ((2 * Λ - 1 : ℕ) : ℚ) / ((Fintype.card K : ℚ) ^ 2) := by
  have hc := NPR.collision_card_le_tight (K := Quad δ) Λ n₁ n₂ h₁ h₂ hne
  have h := quad_card δ
  simp only [Fintype.card_eq_nat_card] at h ⊢
  rw [h]
  have hK0 : 0 < Nat.card K := Nat.card_pos
  have hpos : (0 : ℚ) < (Nat.card K : ℚ) ^ 2 := pow_pos (Nat.cast_pos.mpr hK0) 2
  rw [Nat.cast_pow, div_le_div_iff_of_pos_right hpos]
  exact_mod_cast hc

/-- Two independent seeds in `𝕂` give `((2Λ−1)/|𝕂|)²` per pair; the tower gives `(2Λ−1)/|𝕂|²`:
strictly better by the factor `2Λ − 1` as soon as `Λ ≥ 2`. -/
theorem tower_beats_two_seeds (Λ cardK : ℕ) (hΛ : 2 ≤ Λ) (hK : 0 < cardK) :
    ((2 * Λ - 1 : ℕ) : ℚ) / ((cardK : ℚ) ^ 2) < (((2 * Λ - 1 : ℕ) : ℚ) / cardK) ^ 2 := by
  rw [div_pow]
  have hpos : (0 : ℚ) < (cardK : ℚ) ^ 2 := by positivity
  rw [div_lt_div_iff_of_pos_right hpos]
  have h3 : (3 : ℚ) ≤ ((2 * Λ - 1 : ℕ) : ℚ) := by
    have : 3 ≤ 2 * Λ - 1 := by omega
    exact_mod_cast this
  nlinarith

end Collision

/-! ## The size window at the tower -/

section Window
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
open Nock.NockVMROM.Thm54.SizeWindowCounting

theorem lowOrderRootSeeds_card_le_divisors (Λ : ℕ) :
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

omit [DecidableEq K] in
/-- At the tower: the window union is priced by the divisors of `|𝕂|² − 1`, over `|𝕂|²` seeds. -/
theorem tower_window_card_le (δ : K) [Fact (¬ IsSquare δ)]
    [DecidableEq (Quad δ)] (Λ : ℕ) :
    (lowOrderRootSeeds (K := Quad δ) Λ).card ≤
      ∑ d ∈ (Fintype.card K ^ 2 - 1).divisors.filter (· ≤ Λ), d := by
  have := lowOrderRootSeeds_card_le_divisors (K := Quad δ) Λ
  rwa [quad_card] at this

end Window

end Nock.NockVMROM.Thm54.T0Tower
