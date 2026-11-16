/-
  Nock/NockVMROM/Thm54/FormRCore/PwEvent.lean

  Same fully qualified
  names (`Nock.RedTeam.Batch556.*`): the bivariate event `F`, `bivariate_bad_card_le`, the per-root
  and cylinder bounds.
-/
import Nock.NockVMROM.Thm54.FormRCore.PwFunctional

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch556

open Nock
open Polynomial

/-! ## A. The bivariate event, re-derived -/

section Event

variable {K : Type*} [Field K] {ι : Type*} [DecidableEq ι]

/-- `F(α, λ) = Σ_{k ∈ s} α^{e k}·Q_k(λ)`. -/
noncomputable def F (s : Finset ι) (e : ι → ℕ) (Q : ι → K[X]) (α l : K) : K :=
  ∑ k ∈ s, α ^ e k * (Q k).eval l

/-- `F(·, λ)` as a polynomial in `α`. -/
noncomputable def Fα (s : Finset ι) (e : ι → ℕ) (Q : ι → K[X]) (l : K) : K[X] :=
  ∑ k ∈ s, C ((Q k).eval l) * X ^ e k

theorem Fα_eval (s : Finset ι) (e : ι → ℕ) (Q : ι → K[X]) (l α : K) :
    (Fα s e Q l).eval α = F s e Q α l := by
  unfold Fα F
  rw [eval_finset_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [eval_mul, eval_C, eval_pow, eval_X, mul_comm]

/-- With distinct exponents, the `α^{e k₀}` coefficient of `F(·, λ)` is `Q_{k₀}(λ)`. -/
theorem Fα_coeff (s : Finset ι) (e : ι → ℕ) (Q : ι → K[X]) (l : K) (hinj : Set.InjOn e s)
    (k₀ : ι) (hk₀ : k₀ ∈ s) : (Fα s e Q l).coeff (e k₀) = (Q k₀).eval l := by
  unfold Fα
  rw [finsetSum_coeff, Finset.sum_eq_single k₀]
  · simp
  · intro k hk hne
    rw [coeff_C_mul, coeff_X_pow, if_neg (fun h => hne (hinj hk hk₀ h.symm)), mul_zero]
  · intro h; exact absurd hk₀ h

theorem Fα_natDegree_le (s : Finset ι) (e : ι → ℕ) (Q : ι → K[X]) (l : K) (E : ℕ)
    (hE : ∀ k ∈ s, e k ≤ E) : (Fα s e Q l).natDegree ≤ E :=
  natDegree_sum_le_of_forall_le _ _ fun k hk =>
    (natDegree_C_mul_X_pow_le _ _).trans (hE k hk)

/-- `F` as a bivariate polynomial: outer variable `α`, inner variable `λ`. -/
noncomputable def Fpoly (s : Finset ι) (e : ι → ℕ) (Q : ι → K[X]) : (K[X])[X] :=
  ∑ k ∈ s, C (Q k) * X ^ e k

theorem Fpoly_eval (s : Finset ι) (e : ι → ℕ) (Q : ι → K[X]) (α l : K) :
    ((Fpoly s e Q).eval (C α)).eval l = F s e Q α l := by
  unfold Fpoly F
  rw [eval_finset_sum, eval_finset_sum]
  exact Finset.sum_congr rfl fun k _ => by
    rw [eval_mul, eval_C, eval_pow, eval_X, eval_mul, eval_pow, eval_C, mul_comm]

theorem Fpoly_coeff (s : Finset ι) (e : ι → ℕ) (Q : ι → K[X]) (hinj : Set.InjOn e s)
    (k₀ : ι) (hk₀ : k₀ ∈ s) : (Fpoly s e Q).coeff (e k₀) = Q k₀ := by
  unfold Fpoly
  rw [finsetSum_coeff, Finset.sum_eq_single k₀]
  · simp
  · intro k hk hne
    rw [coeff_C_mul, coeff_X_pow, if_neg (fun h => hne (hinj hk hk₀ h.symm)), mul_zero]
  · intro h; exact absurd hk₀ h

/-- **`F ≡ 0` as a bivariate polynomial iff every record's `Q_k ≡ 0`**: distinct exponents do
not interfere.  (Over a finite field "vanishes at every point" is weaker than "is the zero
polynomial"; the event bound below is about the polynomial.) -/
theorem forest_zero_iff (s : Finset ι) (e : ι → ℕ) (Q : ι → K[X]) (hinj : Set.InjOn e s) :
    Fpoly s e Q = 0 ↔ ∀ k ∈ s, Q k = 0 := by
  constructor
  · intro h k hk
    rw [← Fpoly_coeff s e Q hinj k hk, h, coeff_zero]
  · intro h
    unfold Fpoly
    exact Finset.sum_eq_zero fun k hk => by rw [h k hk, C_0, zero_mul]

variable [Fintype K] [DecidableEq K]

/-- **The bad set**: if `Q_{k₀} ≠ 0` then at most `|𝕂|·(deg Q_{k₀} + E)` pairs `(α, λ)` satisfy
`F(α, λ) = 0`. -/
theorem bivariate_bad_card_le (s : Finset ι) (e : ι → ℕ) (Q : ι → K[X]) (E : ℕ)
    (hinj : Set.InjOn e s) (hE : ∀ k ∈ s, e k ≤ E) (k₀ : ι) (hk₀ : k₀ ∈ s) (hQ : Q k₀ ≠ 0) :
    (Finset.univ.filter fun p : K × K => F s e Q p.1 p.2 = 0).card
      ≤ Fintype.card K * ((Q k₀).natDegree + E) := by
  -- the λ's that kill `Q_{k₀}`, and for every other λ the α's that kill `F(·, λ)`
  set badL : Finset K := (Q k₀).roots.toFinset with hbadL
  set bad : Finset (K × K) := Finset.univ.filter fun p : K × K => F s e Q p.1 p.2 = 0 with hbad
  have hsub : bad ⊆ (Finset.univ ×ˢ badL) ∪
      Finset.univ.biUnion (fun l : K => ((Fα s e Q l).roots.toFinset).image fun α => (α, l)) := by
    intro p hp
    have hF : F s e Q p.1 p.2 = 0 := (Finset.mem_filter.mp hp).2
    rw [Finset.mem_union]
    by_cases hl : (Q k₀).eval p.2 = 0
    · left
      exact Finset.mem_product.mpr ⟨Finset.mem_univ _, by
        simpa [hbadL, Multiset.mem_toFinset, mem_roots hQ] using hl⟩
    · right
      rw [Finset.mem_biUnion]
      refine ⟨p.2, Finset.mem_univ _, Finset.mem_image.mpr ⟨p.1, ?_, rfl⟩⟩
      have hne : Fα s e Q p.2 ≠ 0 := fun h0 =>
        hl (by rw [← Fα_coeff s e Q p.2 hinj k₀ hk₀, h0, coeff_zero])
      rw [Multiset.mem_toFinset, mem_roots hne, IsRoot.def, Fα_eval]
      exact hF
  calc bad.card
      ≤ ((Finset.univ ×ˢ badL) ∪ Finset.univ.biUnion (fun l : K =>
          ((Fα s e Q l).roots.toFinset).image fun α => (α, l))).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.univ ×ˢ badL).card
          + (Finset.univ.biUnion (fun l : K =>
              ((Fα s e Q l).roots.toFinset).image fun α => (α, l))).card :=
        Finset.card_union_le _ _
    _ ≤ Fintype.card K * (Q k₀).natDegree + Fintype.card K * E := by
        apply Nat.add_le_add
        · rw [Finset.card_product, Finset.card_univ]
          exact Nat.mul_le_mul_left _ ((Multiset.toFinset_card_le _).trans (card_roots' _))
        · calc _ ≤ ∑ l ∈ (Finset.univ : Finset K),
                (((Fα s e Q l).roots.toFinset).image fun α => (α, l)).card :=
                Finset.card_biUnion_le
            _ ≤ ∑ _l ∈ (Finset.univ : Finset K), E :=
                Finset.sum_le_sum fun l _ =>
                  Finset.card_image_le.trans ((Multiset.toFinset_card_le _).trans
                    ((card_roots' _).trans (Fα_natDegree_le s e Q l E hE)))
            _ = Fintype.card K * E := by simp
    _ = Fintype.card K * ((Q k₀).natDegree + E) := by ring

end Event

/-! ## B. Per root -/

section PerRoot

variable {T : Type*} [Fintype T] [DecidableEq T] {ρ : Type*} [Fintype ρ]

/-- Acceptance requires every root's polynomial to vanish, so the accepting tuples are inside
the zero set of ANY single root: one nonzero root polynomial bounds the whole event. -/
theorem accept_subset_root (G : ρ → T → Prop) [∀ r t, Decidable (G r t)] (r₀ : ρ) :
    (Finset.univ.filter fun t : T => ∀ r, G r t) ⊆ Finset.univ.filter fun t => G r₀ t := by
  intro t ht
  rw [Finset.mem_filter] at ht ⊢
  exact ⟨ht.1, ht.2 r₀⟩

theorem accept_card_le_root (G : ρ → T → Prop) [∀ r t, Decidable (G r t)] (r₀ : ρ) :
    (Finset.univ.filter fun t : T => ∀ r, G r t).card
      ≤ (Finset.univ.filter fun t => G r₀ t).card :=
  Finset.card_le_card (accept_subset_root G r₀)

/-- The brief's item 3 question: "a forest with two roots where the SUM of two nonzero root
polynomials is zero AND each root is separately zero" is contradictory — a root that is
separately zero is not nonzero. -/
theorem no_cancelling_roots {K : Type*} [Field K] (P₁ P₂ : K[X]) (h₁ : P₁ ≠ 0) :
    ¬ (P₁ + P₂ = 0 ∧ P₁ = 0 ∧ P₂ = 0) := fun h => h₁ h.2.1

end PerRoot

/-! ## C. The tuple: a cylinder over `(α, λ)` -/

section Tuple

variable {K : Type*} [Fintype K] [DecidableEq K] {R : Type*} [Fintype R] [DecidableEq R]

/-- An event that reads only `(α, λ)` is a cylinder on `(α, λ) × R`. -/
theorem cylinder_card (P : K × K → Prop) [DecidablePred P] :
    (Finset.univ.filter fun t : (K × K) × R => P t.1).card
      = (Finset.univ.filter P).card * Fintype.card R := by
  rw [← Finset.card_univ, ← Finset.card_product]
  congr 1
  ext t
  simp [Finset.mem_filter, Finset.mem_product]

theorem event_probability_le [Nonempty K] [Nonempty R] (P : K × K → Prop) [DecidablePred P]
    (D : ℕ) (hcard : (Finset.univ.filter P).card ≤ Fintype.card K * D) :
    ((Finset.univ.filter fun t : (K × K) × R => P t.1).card : ℚ)
        / Fintype.card ((K × K) × R) ≤ (D : ℚ) / Fintype.card K := by
  rw [cylinder_card, Fintype.card_prod, Fintype.card_prod]
  have hK : (0 : ℚ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
  have hR : (0 : ℚ) < Fintype.card R := by exact_mod_cast Fintype.card_pos
  have h : ((Finset.univ.filter P).card : ℚ) ≤ Fintype.card K * D := by exact_mod_cast hcard
  push_cast
  rw [div_le_div_iff₀ (by positivity) hK]
  nlinarith [mul_pos hK hR, mul_nonneg hK.le hR.le,
    mul_le_mul_of_nonneg_right h (mul_nonneg hR.le hK.le)]

end Tuple

end Nock.RedTeam.Batch556
