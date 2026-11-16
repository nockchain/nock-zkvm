/-
packaging: a tuple of committed words `f_c` (`c: γ`), openings `j: J` at points
`pt j` (= `ζ ω^k`) of column `col j` with values `val j`, and DEEP quotient words that agree on ONE common set
`S` with polynomials `q_j` of `natDegree < M` (the conclusion of batched FRI, `inputRelation`). Conclusion:
∃ polynomials `P_c` (`natDegree < M + 1`) with
  (i)  `P_c` agrees with `f_c` on the common `S`,
  (ii) `P_{col j}(pt j) = val j` for every opening,
and, under unique decoding `δ ≤ relUDR (RS[ι, M+1])` (ArkLib `Code.relativeUniqueDecodingRadius`),
  (iii) `P_c` is the unique polynomial of `natDegree < M + 1` that is `δ`-close to `f_c`: it depends on the
        committed word `f_c` only (not on `ζ`, `v` or the FRI transcript).
Error-free.
-/
import NockvmE2E.Deep.UDCore
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.Basic.DecodingRadius

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial NNReal

namespace NockvmE2E.Deep

/-- `S` has relative size at least `1 − δ` (ArkLib's `inputRelation` form). -/
def Dense {ι : Type} [Fintype ι] (δ : ℝ≥0) (S : Finset ι) : Prop :=
  (1 - δ) * (Fintype.card ι : ℝ≥0) ≤ (S.card : ℝ≥0)

/-- **Unique decoding as a count.** For the RS code of dimension `M + 1` on `n ≥ M + 1` points,
`δ ≤ relUDR` makes any two `(1−δ)`-dense sets satisfy `|S| + |S'| ≥ n + M + 1`. -/
theorem card_add_of_le_relUDR {ι : Type} [Fintype ι] {F : Type} [Field F] [DecidableEq F] (α : ι ↪ F)
    {M : ℕ} (hM : M + 1 ≤ Fintype.card ι) {δ : ℝ≥0}
    (hδ : δ ≤ Code.relativeUniqueDecodingRadius (ReedSolomon.code α (M + 1) : Set (ι → F)))
    {S S' : Finset ι} (hS : Dense δ S) (hS' : Dense δ S') :
    Fintype.card ι + (M + 1) ≤ S.card + S'.card := by
  set n := Fintype.card ι with hn
  unfold Code.relativeUniqueDecodingRadius at hδ
  rw [ReedSolomon.dist_eq_of_le hM] at hδ
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hcast : (((n - (M + 1) + 1 : ℕ) : ℝ≥0) - 1 : ℝ≥0) = ((n - (M + 1) : ℕ) : ℝ≥0) := by
    rw [Nat.cast_add, Nat.cast_one, add_tsub_cancel_right]
  rw [hcast] at hδ
  -- move to ℝ
  have hδR : (δ : ℝ) ≤ ((n - (M + 1) : ℕ) : ℝ) / 2 / n := by
    have := NNReal.coe_le_coe.mpr hδ
    rwa [NNReal.coe_div, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_natCast, NNReal.coe_ofNat] at this
  have hsub : ((n - (M + 1) : ℕ) : ℝ) = (n : ℝ) - (M + 1) := by
    rw [Nat.cast_sub hM]; push_cast; ring
  rw [hsub, div_div, le_div_iff₀ (by positivity)] at hδR
  have hδ1 : (δ : ℝ) ≤ 1 := by nlinarith
  have hδ1' : δ ≤ 1 := by exact_mod_cast hδ1
  have h1 : (1 - (δ : ℝ)) * n ≤ S.card := by
    have := NNReal.coe_le_coe.mpr hS
    simpa [Dense, NNReal.coe_sub hδ1'] using this
  have h2 : (1 - (δ : ℝ)) * n ≤ S'.card := by
    have := NNReal.coe_le_coe.mpr hS'
    simpa [Dense, NNReal.coe_sub hδ1'] using this
  have : ((n + (M + 1) : ℕ) : ℝ) ≤ ((S.card + S'.card : ℕ) : ℝ) := by
    push_cast; nlinarith
  exact_mod_cast this

section
variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (x : ι → K)
  {γ J : Type} (col : J → γ) (pt val : J → K)

/-- **Tuple DEEP binding (common set, error-free).** Every column is opened at least once (`col` surjective),
every opening point is off the domain, the DEEP quotient words agree on one common `S` (`|S| ≥ M + 1`) with
polynomials of `natDegree < M`. Then one polynomial per column agrees with `f_c` on `S` and satisfies every
opening equation. -/
theorem deep_tuple (hx : Function.Injective x) (f : γ → ι → K) (hcov : Function.Surjective col)
    (hz : ∀ j i, x i ≠ pt j) {M : ℕ} (q : J → K[X]) (hq : ∀ j, (q j).natDegree < M)
    (S : Finset ι) (hS : M + 1 ≤ S.card)
    (hagree : ∀ j, Agree x (deepWord x (f (col j)) (pt j) (val j)) (q j) S) :
    ∃ P : γ → K[X], (∀ c, (P c).natDegree < M + 1) ∧ (∀ c, Agree x (f c) (P c) S) ∧
      ∀ j, (P (col j)).eval (pt j) = val j := by
  choose pick hpick using hcov
  refine ⟨fun c => unquot (q (pick c)) (pt (pick c)) (val (pick c)),
    fun c => unquot_natDegree_lt (hq _) _ _, fun c => ?_, fun j => ?_⟩
  · have := agree_unquot x (hz (pick c)) (hagree (pick c))
    rwa [hpick c] at this
  · have hA : Agree x (f (col j)) (unquot (q (pick (col j))) (pt (pick (col j))) (val (pick (col j)))) S := by
      have := agree_unquot x (hz (pick (col j))) (hagree (pick (col j)))
      rwa [hpick (col j)] at this
    have hE := eq_of_agree x hx (unquot_natDegree_lt (hq _) _ _) (unquot_natDegree_lt (hq j) _ _) hA
      (agree_unquot x (hz j) (hagree j)) (by rwa [Finset.inter_self])
    show eval (pt j) (unquot (q (pick (col j))) (pt (pick (col j))) (val (pick (col j)))) = val j
    rw [hE, eval_unquot]

/-- **the unique-decoding form.** Evaluation domain `α: ι ↪ K`; `δ ≤ relUDR(RS[α, M+1])`,
`M + 1 ≤ |ι|`; the DEEP quotient words agree with polynomials `q_j` (`natDegree < M`) on one common
`(1−δ)`-dense set `S`. Then there are `P_c` (`natDegree < M + 1`) with (i) agreement with `f_c` on `S`,
(ii) the opening equations `P_{col j}(pt j) = val j`, and (iii) uniqueness: every polynomial of
`natDegree < M + 1` that agrees with `f_c` on some `(1−δ)`-dense set equals `P_c`. -/
theorem deep_ud [DecidableEq K] (α : ι ↪ K) (f : γ → ι → K) (hcov : Function.Surjective col)
    (hz : ∀ j i, α i ≠ pt j) {M : ℕ} (hM : M + 1 ≤ Fintype.card ι) {δ : ℝ≥0}
    (hδ : δ ≤ Code.relativeUniqueDecodingRadius (ReedSolomon.code α (M + 1) : Set (ι → K)))
    (q : J → K[X]) (hq : ∀ j, (q j).natDegree < M) (S : Finset ι) (hS : Dense δ S)
    (hagree : ∀ j, Agree α (deepWord α (f (col j)) (pt j) (val j)) (q j) S) :
    ∃ P : γ → K[X], (∀ c, (P c).natDegree < M + 1) ∧ (∀ c, Agree α (f c) (P c) S) ∧
      (∀ j, (P (col j)).eval (pt j) = val j) ∧
      ∀ c (P' : K[X]) (S' : Finset ι), P'.natDegree < M + 1 → Dense δ S' → Agree α (f c) P' S' →
        P' = P c := by
  have hSS := card_add_of_le_relUDR α hM hδ hS hS
  have hS1 : M + 1 ≤ S.card := by
    have := Finset.card_le_univ S; omega
  obtain ⟨P, hdeg, hag, hop⟩ := deep_tuple α col pt val α.injective f hcov hz q hq S hS1 hagree
  refine ⟨P, hdeg, hag, hop, fun c P' S' hP' hS' hA' => ?_⟩
  exact eq_of_agree α α.injective hP' (hdeg c) hA' (hag c)
    (card_inter_ge (by have := card_add_of_le_relUDR α hM hδ hS' hS; omega))

end

end NockvmE2E.Deep
