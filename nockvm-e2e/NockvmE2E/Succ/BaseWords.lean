/-
base-field committed words.

The committed words are `B`-valued (`β = Fin (2^n) → B`, structural base-ness: the Merkle leaves and the
`DeepParams.toPoly` domain are `B`-words), the coins and the FRI field are `F ⊇ B`, and FRI runs on the lifted
word `liftW w = algebraMap ∘ w` (`Succ/FriDeep`). The quotient chunks are base columns too: a `K`-chunk is
`e = [F : B]` base columns weighted by a basis (`DeepParams.e`, `DeepParams.cw`).

* `fixed_iff_range`: inside a finite field extension `F ⊇ B`, `x ^ |B| = x ↔ x ∈ range (algebraMap B F)`.
* `udDecode_base`: **Frobenius + unique decoding.** For a `B`-word `w` on a domain inside `B`, inside the
  unique-decoding radius, `udDecode ω δ N (liftW w)` is the image of a polynomial over `B`.
* `B = F` recovers the old statements (the examples at the end).
-/
import NockvmE2E.Succ.FriDeep

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial NockvmE2E.Deep NockvmE2E.Rap NockvmE2E.Succ.FriDeep Fri.Spec Domain
open scoped NNReal

namespace NockvmE2E.Succ.BaseWords

variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra B F]
variable {n : ℕ} {ω : SmoothCosetFftDomain n F}

/-- In `F ⊇ B` (finite), the `|B|`-th-power fixed points of `F` are exactly the image of `B`. -/
theorem fixed_iff_range (x : F) : x ^ Fintype.card B = x ↔ x ∈ Set.range (algebraMap B F) := by
  classical
  have hq : 1 < Fintype.card B := Fintype.one_lt_card
  have hinj := (algebraMap B F).injective
  constructor
  · intro hx
    have hne : (Polynomial.X ^ Fintype.card B - Polynomial.X : F[X]) ≠ 0 := by
      intro h0
      have := congrArg (natDegree (R := F)) h0
      rw [natDegree_sub_eq_left_of_natDegree_lt (by simpa using hq)] at this
      simp at this
    have hdeg : (Polynomial.X ^ Fintype.card B - Polynomial.X : F[X]).natDegree = Fintype.card B := by
      rw [natDegree_sub_eq_left_of_natDegree_lt (by simpa using hq)]; simp
    have hsub : (Finset.univ.image (algebraMap B F)) ⊆ (Polynomial.X ^ Fintype.card B - Polynomial.X : F[X]).roots.toFinset := by
      intro y hy
      obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hy
      simp [mem_roots hne, ← map_pow, FiniteField.pow_card]
    have hcard : (Polynomial.X ^ Fintype.card B - Polynomial.X : F[X]).roots.toFinset.card ≤
        (Finset.univ.image (algebraMap B F)).card := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
      exact (Multiset.toFinset_card_le _).trans ((card_roots' _).trans hdeg.le)
    have heq := Finset.eq_of_subset_of_card_le hsub hcard
    have hmem : x ∈ (Polynomial.X ^ Fintype.card B - Polynomial.X : F[X]).roots.toFinset := by
      simp [mem_roots hne, hx]
    rw [← heq] at hmem
    obtain ⟨b, -, hb⟩ := Finset.mem_image.mp hmem
    exact ⟨b, hb⟩
  · rintro ⟨b, rfl⟩
    rw [← map_pow, FiniteField.pow_card]

/-- **`udDecode_base` (Frobenius + unique decoding).** If the evaluation domain lies in `B`, `w` is a `B`-word
and `δ` is inside the unique-decoding radius at degree bound `N + 1 ≤ 2^n`, then FRI's `F`-decoding of the
lifted word is the image of a `B`-polynomial. -/
theorem udDecode_base (hω : ∀ i, domEmb ω i ∈ Set.range (algebraMap B F)) {δ : ℝ≥0} {N : ℕ}
    (hN : N + 1 ≤ 2 ^ n)
    (hδ : δ ≤ Code.relativeUniqueDecodingRadius
      (ReedSolomon.code (domEmb ω) (N + 1) : Set (Fin (2 ^ n) → F)))
    (w : Fin (2 ^ n) → B) :
    ∃ q : B[X], udDecode ω δ N (liftW w) = q.map (algebraMap B F) := by
  classical
  by_cases hex : ∃ p : F[X], p.natDegree < N + 1 ∧
      ∃ S : Finset (Fin (2 ^ n)), Dense δ S ∧ Agree (domEmb ω) (liftW w) p S
  swap
  · refine ⟨0, ?_⟩
    rw [udDecode, dif_neg hex]
    simp
  obtain ⟨p, hp, S, hS, hA⟩ := hex
  rw [udDecode_eq hN hδ hp hS hA]
  -- the Frobenius `x ↦ x ^ |B|` as a ring hom
  obtain ⟨c, hc⟩ := CharP.exists B
  have : CharP F c := charP_of_injective_algebraMap (algebraMap B F).injective c
  have : Fact c.Prime := ⟨CharP.char_is_prime F c⟩
  obtain ⟨m, hcm, hm⟩ := FiniteField.card B c
  let σ : F →+* F := iterateFrobenius F c m
  have hσ : ∀ x, σ x = x ^ Fintype.card B := fun x => by
    simp only [σ, iterateFrobenius_def, hm]
  have hM : N + 1 ≤ Fintype.card (Fin (2 ^ n)) := by rwa [Fintype.card_fin]
  have hcard := card_inter_ge (S := S) (S' := S)
    (by have := card_add_of_le_relUDR (domEmb ω) hM hδ hS hS; omega)
  have hdeg : (p.map σ).natDegree < N + 1 := lt_of_le_of_lt (natDegree_map_le) hp
  have hA' : Agree (domEmb ω) (liftW w) (p.map σ) S := by
    intro i hi
    have h1 : σ (domEmb ω i) = domEmb ω i := by
      rw [hσ]; exact (fixed_iff_range _).mpr (hω i)
    have h2 : σ (liftW w i) = liftW w i := by
      rw [hσ]; exact (fixed_iff_range _).mpr ⟨w i, rfl⟩
    rw [eval_map]
    nth_rewrite 1 [← h1]
    rw [eval₂_at_apply, ← hA i hi, h2]
  have hfix : p.map σ = p := eq_of_agree (domEmb ω) (domEmb ω).injective hdeg hp hA' hA hcard
  have hlift : p ∈ Polynomial.lifts (algebraMap B F) := by
    rw [lifts_iff_coeff_lifts]
    intro i
    rw [← fixed_iff_range, ← hσ]
    have := congrArg (fun q => q.coeff i) hfix
    simpa [coeff_map] using this
  exact (mem_lifts p).mp hlift |>.imp fun q hq => hq.symm

/-! ## `B = F` recovers the old statements -/

/-- With `B = F` the lift is the identity. -/
example (w : Fin (2 ^ n) → F) : liftW (B := F) w = w := rfl

/-- With `B = F` the base-word decoding is the old `udDecode`. -/
example (δ : ℝ≥0) (N : ℕ) (w : Fin (2 ^ n) → F) : udDecodeB (B := F) ω δ N w = udDecode ω δ N w := rfl

/-- With `B = F` the DEEP batched-FRI statement is the old one (the quotient words of the committed words). -/
example {Φ : CoinFrame} {ι : Type} [Fintype ι] {colRound : ι → ℕ}
    (P : DeepParams Φ F ι (Fin (2 ^ n) → F) colRound) {r : ℕ} (A : AirShape P r)
    (R0 : RapStatement Φ F ι (Fin (2 ^ n) → F) colRound) {m : ℕ}
    (e : Fin (m + 1) ≃ (ι × Fin r) ⊕ Fin P.nq) (tr : DeepTr P) (fin : DeepFin P (r := r) R0) (χ : Coins Φ F) :
    deepStmt (B := F) (ω := ω) P A R0 e tr fin χ =
      ((), fun j x => deepWord (⇑ω) (tr (colOf P e j)) (ptOf P A e χ j) (valOf P R0 e fin j)
        (ω.equivToFinset.symm x)) := rfl

/-- With one column per chunk (`e = 1`, `cw = 1`, the default) `Qsum` is the old `Σ_j X^{j|H|} Q_j`. -/
example {Φ : CoinFrame} {ι β : Type} (P : DeepParams Φ F ι β (fun _ => 0)) (h1 : P.e = 1)
    (hc : ∀ j, P.cw j = 1) (tr : DeepTr P) :
    P.Qsum tr = ∑ j : Fin P.nq, Polynomial.X ^ (j.1 * P.H.card) * P.toPoly (tr (Sum.inr j)) := by
  simp [DeepParams.Qsum, h1, hc]

end NockvmE2E.Succ.BaseWords
