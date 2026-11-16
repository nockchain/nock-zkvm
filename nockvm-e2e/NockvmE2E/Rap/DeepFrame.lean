/-
the DEEP-RAP extension of the Rap frame twin. Appended rounds: R' (sample α, commit quotient chunks `Q_j`, column round
`R+1`), R'' (sample ζ). Generic in the RAP; no Nock types. Nothing in `Frame/Protocol/Bridge` is edited.

Modelling choices : the two new coins `a` (α, `sampledAfter = R`) and
`z` (ζ, `sampledAfter = R+1`) are reserved coins of the frame `Φ` itself (the old summands never price them),
so the coin type is unchanged and only the trace type grows, `ι ⊕ Fin nq`.
-/
import NockvmE2E.Rap.Frame
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.BigOperators

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.deprecated false

open Polynomial

namespace NockvmE2E.Rap

/-- DEEP data: reserved coins `a` (α) and `z` (ζ), the trace domain `H`, the LDE domain `D`, the reading of a
trace value as a polynomial, and the constraint polynomials `C_i ∘ P` of the (old) trace. -/
structure DeepParams (Φ : CoinFrame) (K : Type) [Field K] (ι β : Type) (colRound : ι → ℕ) where
  R : ℕ
  nq : ℕ
  ns : ℕ
  a : Fin Φ.n
  z : Fin Φ.n
  ha : Φ.sampledAfter a = R
  hz : Φ.sampledAfter z = R + 1
  hcol : ∀ j, colRound j ≤ R
  H : Finset K
  D : Finset K
  toPoly : β → K[X]
  hβ : ∀ b, (toPoly b).natDegree ≤ H.card
  /-- Constraint polynomials; they may read the coins of rounds `< R` (the coins sampled before α). -/
  Cp : Coins Φ K → (ι → β) → Fin ns → K[X]
  hC : ∀ χ tr i, (Cp χ tr i).natDegree ≤ (nq + 1) * H.card
  hCcoin : ∀ χ χ' : Coins Φ K, (∀ i, Φ.sampledAfter i < R → χ i = χ' i) → Cp χ = Cp χ'
  /-- Base-field chunks: each `K`-chunk is `e` base columns; column `j` is the `j % e`-th coordinate of
  chunk `j / e`, weighted by `cw j` (the basis element). Default `e = 1`, `cw = 1`: one column per chunk. -/
  e : ℕ := 1
  cw : Fin nq → K := fun _ => 1

section
variable {Φ : CoinFrame} {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι β : Type}
  {colRound : ι → ℕ} (P : DeepParams Φ K ι β colRound)

/-- Extended column rounds: old columns keep theirs, the quotient chunks are in round `R+1`. -/
def DeepParams.colRoundX : ι ⊕ Fin P.nq → ℕ := Sum.elim colRound (fun _ => P.R + 1)

/-- Extended traces. -/
abbrev DeepTr := Tr (ι ⊕ Fin P.nq) β

/-- Extended staged-ness. -/
abbrev DeepStaged (Q : Coins Φ K → DeepTr P) : Prop := TracesStaged Φ P.colRoundX Q

/-- Restriction to the old columns. -/
def DeepParams.restr (tr : DeepTr P) : Tr ι β := fun j => tr (Sum.inl j)

/-- `Z_H`. -/
noncomputable def DeepParams.Zpoly : K[X] := ∏ h ∈ P.H, (X - C h)

/-- `Σ_j X^{j|H|} Q_j`. -/
noncomputable def DeepParams.Qsum (tr : DeepTr P) : K[X] :=
  ∑ j : Fin P.nq, C (P.cw j) * X ^ (j.1 / P.e * P.H.card) * P.toPoly (tr (Sum.inr j))

/-- `Σ_i αⁱ (C_i ∘ P)`. -/
noncomputable def DeepParams.Apoly (χ : Coins Φ K) (tr : Tr ι β) (α : K) : K[X] :=
  ∑ i : Fin P.ns, C (α ^ i.1) * P.Cp χ tr i

/-- `G_α = Σ_i αⁱ (C_i∘P) − Z_H · Σ_j X^{j|H|} Q_j`. -/
noncomputable def DeepParams.Gpoly (χ : Coins Φ K) (tr : DeepTr P) (α : K) : K[X] :=
  P.Apoly χ (P.restr tr) α - P.Zpoly * P.Qsum tr

/-- Some constraint is nonzero somewhere on `H`. -/
def DeepParams.HasBad (χ : Coins Φ K) (tr : Tr ι β) : Prop := ∃ x ∈ P.H, ∃ i, eval x (P.Cp χ tr i) ≠ 0

open Classical in
/-- The first such `x₀` (any, by choice). -/
noncomputable def DeepParams.x0 (χ : Coins Φ K) (tr : Tr ι β) : K :=
  if h : P.HasBad χ tr then h.choose else 0

/-- The univariate in α: `Σ_i C_i(x₀) αⁱ`. -/
noncomputable def DeepParams.Palpha (χ : Coins Φ K) (tr : Tr ι β) : K[X] :=
  ∑ i : Fin P.ns, C (eval (P.x0 χ tr) (P.Cp χ tr i)) * X ^ i.1

/-- Counting helper: a predicate on the value of a one-coin cylinder, contained in `T`, has at most
`|T|` members. -/
theorem card_single_le {n : ℕ} (c : Fin n) (p : K → Prop) [DecidablePred p] (T : Finset K)
    (hT : ∀ x, p x → x ∈ T) :
    (Finset.univ.filter fun f : ({c} : Finset (Fin n)) → K => p (f ⟨c, Finset.mem_singleton_self c⟩)).card
      ≤ T.card := by
  refine Finset.card_le_card_of_injOn (fun f => f ⟨c, Finset.mem_singleton_self c⟩) ?_ ?_
  · intro f hf
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hf
    exact hT _ hf
  · intro f _ g _ h
    funext i
    have : i = ⟨c, Finset.mem_singleton_self c⟩ := Subtype.ext (Finset.mem_singleton.mp i.2)
    subst this; exact h

/-! ### The two appended summands -/

open Classical in
/-- Bad α's: `Σ_i C_i(x₀) αⁱ = 0` although some constraint is nonzero on `H`. -/
noncomputable def DeepParams.badAlpha (χ : Coins Φ K) (tr : Tr ι β) :
    Finset (({P.a} : Finset (Fin Φ.n)) → K) :=
  Finset.univ.filter fun f => P.HasBad χ tr ∧ eval (f ⟨P.a, Finset.mem_singleton_self _⟩) (P.Palpha χ tr) = 0

theorem DeepParams.Palpha_natDegree (χ : Coins Φ K) (tr : Tr ι β) : (P.Palpha χ tr).natDegree ≤ P.ns - 1 := by
  refine natDegree_sum_le_of_forall_le _ _ (fun i _ => ?_)
  refine (natDegree_C_mul_le _ _).trans ?_
  refine (natDegree_X_pow_le _).trans ?_
  have := i.2; omega

theorem DeepParams.Palpha_ne (χ : Coins Φ K) (tr : Tr ι β) (h : P.HasBad χ tr) : P.Palpha χ tr ≠ 0 := by
  have hx := h.choose_spec
  obtain ⟨i, hi⟩ := hx.2
  intro h0
  have hc : (P.Palpha χ tr).coeff i.1 = eval (P.x0 χ tr) (P.Cp χ tr i) := by
    simp only [DeepParams.Palpha, finset_sum_coeff, coeff_C_mul, coeff_X_pow]
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      have : i.1 ≠ b.1 := fun e => hb (Fin.ext e.symm)
      simp [this]
    · simp
  have hx0 : P.x0 χ tr = h.choose := by simp [DeepParams.x0, h]
  rw [h0, coeff_zero, hx0] at hc
  exact hi hc.symm

open Classical in
theorem DeepParams.badAlpha_card (χ : Coins Φ K) (tr : Tr ι β) : (P.badAlpha χ tr).card ≤ P.ns - 1 := by
  by_cases h : P.HasBad χ tr
  · have hh := card_single_le P.a (fun x => eval x (P.Palpha χ tr) = 0)
      (P.Palpha χ tr).roots.toFinset (fun x hx => by simp [mem_roots (P.Palpha_ne χ tr h), hx])
    have h2 : (P.badAlpha χ tr).card ≤ (P.Palpha χ tr).roots.toFinset.card := by
      simpa [DeepParams.badAlpha, h] using hh
    exact h2.trans ((Multiset.toFinset_card_le _).trans
        ((card_roots' _).trans (P.Palpha_natDegree χ tr)))
  · simp [DeepParams.badAlpha, h]

open Classical in
/-- Bad ζ's for a given α and traces: `ζ ∈ D`, or a root of a nonzero `G_α`. -/
noncomputable def DeepParams.badZeta (χ : Coins Φ K) (tr : DeepTr P) (α : K) :
    Finset (({P.z} : Finset (Fin Φ.n)) → K) :=
  Finset.univ.filter fun f =>
    f ⟨P.z, Finset.mem_singleton_self _⟩ ∈ P.D ∨
      (P.Gpoly χ tr α ≠ 0 ∧ eval (f ⟨P.z, Finset.mem_singleton_self _⟩) (P.Gpoly χ tr α) = 0)

theorem DeepParams.Zpoly_natDegree : P.Zpoly.natDegree = P.H.card := by
  simp [DeepParams.Zpoly]

theorem DeepParams.Gpoly_natDegree (χ : Coins Φ K) (tr : DeepTr P) (α : K) :
    (P.Gpoly χ tr α).natDegree ≤ (P.nq + 1) * P.H.card := by
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · refine natDegree_sum_le_of_forall_le _ _ (fun i _ => ?_)
    exact (natDegree_C_mul_le _ _).trans (P.hC χ _ i)
  · have hQ : (P.Qsum tr).natDegree ≤ P.nq * P.H.card := by
      unfold DeepParams.Qsum
      refine natDegree_sum_le_of_forall_le _ _ (fun j _ => ?_)
      refine natDegree_mul_le.trans ?_
      have h0 := (natDegree_C_mul_le (P.cw j) (X ^ (j.1 / P.e * P.H.card) : K[X]))
      have h1 := natDegree_X_pow_le (R := K) (j.1 / P.e * P.H.card)
      have h2 := P.hβ (tr (Sum.inr j))
      have h4 : j.1 / P.e ≤ j.1 := Nat.div_le_self _ _
      have h3 : (j.1 / P.e + 1) * P.H.card ≤ P.nq * P.H.card :=
        Nat.mul_le_mul_right _ (by have := j.2; omega)
      nlinarith
    refine natDegree_mul_le.trans ?_
    rw [P.Zpoly_natDegree]
    nlinarith

open Classical in
theorem DeepParams.badZeta_card (χ : Coins Φ K) (tr : DeepTr P) (α : K) :
    (P.badZeta χ tr α).card ≤ P.D.card + (P.nq + 1) * P.H.card := by
  refine le_trans (card_single_le P.z
    (fun x => x ∈ P.D ∨ (P.Gpoly χ tr α ≠ 0 ∧ eval x (P.Gpoly χ tr α) = 0))
    (P.D ∪ (P.Gpoly χ tr α).roots.toFinset) ?_) ?_
  · intro x hx
    rcases hx with h | ⟨h0, h1⟩
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ (by simp [mem_roots h0, h1])
  · refine (Finset.card_union_le _ _).trans (Nat.add_le_add_left ?_ _)
    exact (Multiset.toFinset_card_le _).trans
      ((card_roots' _).trans (P.Gpoly_natDegree χ tr α))

end

/-! ### Coin-free AIRs are a special case -/

/-- A coin-free `DeepParams`: the old data, `Cp` constant in the coins. -/
def DeepParams.ofCoinFree (Φ : CoinFrame) (K : Type) [Field K] {ι β : Type} (colRound : ι → ℕ)
    (R nq ns : ℕ) (a z : Fin Φ.n) (ha : Φ.sampledAfter a = R) (hz : Φ.sampledAfter z = R + 1)
    (hcol : ∀ j, colRound j ≤ R) (H D : Finset K) (toPoly : β → K[X])
    (hβ : ∀ b, (toPoly b).natDegree ≤ H.card) (Cp0 : (ι → β) → Fin ns → K[X])
    (hC0 : ∀ tr i, (Cp0 tr i).natDegree ≤ (nq + 1) * H.card) : DeepParams Φ K ι β colRound where
  R := R
  nq := nq
  ns := ns
  a := a
  z := z
  ha := ha
  hz := hz
  hcol := hcol
  H := H
  D := D
  toPoly := toPoly
  hβ := hβ
  Cp := fun _ => Cp0
  hC := fun _ => hC0
  hCcoin := fun _ _ _ => rfl

/-- The coin-free constraint is the old one. -/
example (Φ : CoinFrame) (K : Type) [Field K] {ι β : Type} (colRound : ι → ℕ) (R nq ns : ℕ) (a z : Fin Φ.n)
    ha hz hcol (H D : Finset K) (toPoly : β → K[X]) hβ (Cp0 : (ι → β) → Fin ns → K[X]) hC0
    [Fintype K] [DecidableEq K] (χ : Coins Φ K) :
    (DeepParams.ofCoinFree Φ K colRound R nq ns a z ha hz hcol H D toPoly hβ Cp0 hC0).Cp χ = Cp0 := rfl

section
variable {Φ : CoinFrame} {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι β : Type}
  {colRound : ι → ℕ} (P : DeepParams Φ K ι β colRound)

/-- If `Cp` is constant in the coins, the old coin-free `hlink` implies the new one. -/
theorem hlink_of_coinFree {M0 Mfin : Type} (Acc : M0 → Tr ι β → Mfin → Coins Φ K → Prop)
    (RestX : M0 → DeepTr P → Mfin → Coins Φ K → Prop) (Cp0 : (ι → β) → Fin P.ns → K[X])
    (hconst : ∀ χ, P.Cp χ = Cp0)
    (hlink0 : ∀ m0 (tr : DeepTr P) fin χ, RestX m0 tr fin χ →
      (∀ i, ∀ x ∈ P.H, eval x (Cp0 (P.restr tr) i) = 0) → Acc m0 (P.restr tr) fin χ) :
    ∀ m0 (tr : DeepTr P) fin χ, RestX m0 tr fin χ →
      (∀ i, ∀ x ∈ P.H, eval x (P.Cp χ (P.restr tr) i) = 0) → Acc m0 (P.restr tr) fin χ := by
  intro m0 tr fin χ hr hC
  exact hlink0 m0 tr fin χ hr (by simpa [hconst χ] using hC)

end

end NockvmE2E.Rap
