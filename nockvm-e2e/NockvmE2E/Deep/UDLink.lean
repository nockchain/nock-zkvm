/-
link to `Rap/DeepSound` (read-only): what the verifier actually checks is the DEEP identity on
OPENED VALUES, `Σ αⁱ C_i(v) = Z_H(ζ)·Σ_j ζ^{j|H|} v_{Q_j}`, not `G_α(ζ) = 0` on polynomials. Given an AIR shape
(each `C_i ∘ P` evaluated at `y` is a fixed function of the columns at `y·ω^k`) and the opening equations
(ii) of `deep_ud`, the opened-value check is the first conjunct of `(P.statement R0 Rest).Accepts`.
`accepts_of_deep` packages: DEEP quotient words on one common dense set + the opened-value check
⇒ a trace (the decoded `P_c`, read back into `β`) on which the extended statement accepts, each column
`δ`-close to (and the unique decoding of) its committed word.
-/
import NockvmE2E.Rap.DeepSound
import NockvmE2E.Deep.UDBatch

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial NNReal NockvmE2E.Rap

namespace NockvmE2E.Deep

section
variable {Φ : CoinFrame} {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι β : Type}
  {colRound : ι → ℕ} (P : DeepParams Φ K ι β colRound)

/-- AIR shape: `(C_i ∘ P)(y)` is a fixed function `Cv i` of the column values at the shifted points
`y · off k` (`off k = ω^k`; `r` offsets), and of the coins `χ` (rounds `< R`, see `DeepParams.hCcoin`) and the
point `y` itself (fixed preprocessing). Instance-level (per AIR). -/
structure AirShape (r : ℕ) where
  off : Fin r → K
  Cv : Coins Φ K → K → Fin P.ns → (ι × Fin r → K) → K
  /-- The opening point of column `c`, offset `k`, at challenge `y`. Default `y · off k`; a column may
  instead be opened at a fixed off-domain point (route vi: public message columns). -/
  pt : ι → Fin r → K → K := fun _ k y => y * off k
  hCv : ∀ (χ : Coins Φ K) (tr : Tr ι β) (i : Fin P.ns) (y : K),
    eval y (P.Cp χ tr i) = Cv χ y i (fun ck => eval (pt ck.1 ck.2 y) (P.toPoly (tr ck.1)))

/-- Coin-free AIR shapes are a special case: the old `Cv` (reading neither `χ` nor `y`) gives an `AirShape`
as soon as `Cp` is constant in the coins. -/
def AirShape.ofCoinFree {r : ℕ} (off : Fin r → K) (Cp0 : (ι → β) → Fin P.ns → K[X])
    (hconst : ∀ χ, P.Cp χ = Cp0) (Cv0 : Fin P.ns → (ι × Fin r → K) → K)
    (hCv0 : ∀ (tr : Tr ι β) (i : Fin P.ns) (y : K),
      eval y (Cp0 tr i) = Cv0 i (fun ck => eval (y * off ck.2) (P.toPoly (tr ck.1)))) : AirShape P r where
  off := off
  Cv := fun _ _ => Cv0
  hCv χ tr i y := by rw [hconst χ]; exact hCv0 tr i y

example {r : ℕ} (off : Fin r → K) (Cp0 : (ι → β) → Fin P.ns → K[X]) (hconst : ∀ χ, P.Cp χ = Cp0) Cv0 hCv0
    (χ : Coins Φ K) (y : K) (i) (vT : ι × Fin r → K) :
    (AirShape.ofCoinFree P off Cp0 hconst Cv0 hCv0).Cv χ y i vT = Cv0 i vT := rfl

/-- Existing instances are definitionally unchanged: the default point is `y * off k`. -/
example {r : ℕ} (off : Fin r → K) (Cp0 : (ι → β) → Fin P.ns → K[X]) (hconst : ∀ χ, P.Cp χ = Cp0) Cv0 hCv0
    (c : ι) (k : Fin r) (y : K) :
    (AirShape.ofCoinFree P off Cp0 hconst Cv0 hCv0).pt c k y = y * off k := rfl

/-- The verifier's DEEP check on opened values `vT` (trace columns at `ζ·ω^k`), `vQ` (chunks at `ζ`). -/
def DeepCheck {r : ℕ} (A : AirShape P r) (χ : Coins Φ K) (α ζ : K) (vT : ι × Fin r → K) (vQ : Fin P.nq → K) : Prop :=
  ∑ i : Fin P.ns, α ^ i.1 * A.Cv χ ζ i vT = eval ζ P.Zpoly * ∑ j : Fin P.nq, P.cw j * ζ ^ (j.1 / P.e * P.H.card) * vQ j

/-- **Opened-value check + opening equations ⇒ `G_α(ζ) = 0`.** -/
theorem gpoly_eval_zero_of_check {r : ℕ} (A : AirShape P r) (χ : Coins Φ K) (tr : DeepTr P) (α ζ : K)
    (vT : ι × Fin r → K) (vQ : Fin P.nq → K)
    (hT : ∀ ck : ι × Fin r, eval (A.pt ck.1 ck.2 ζ) (P.toPoly (tr (Sum.inl ck.1))) = vT ck)
    (hQ : ∀ j, eval ζ (P.toPoly (tr (Sum.inr j))) = vQ j) (h : DeepCheck P A χ α ζ vT vQ) :
    eval ζ (P.Gpoly χ tr α) = 0 := by
  have hv : (fun ck : ι × Fin r => eval (A.pt ck.1 ck.2 ζ) (P.toPoly (P.restr tr ck.1))) = vT :=
    funext hT
  simp only [DeepParams.Gpoly, DeepParams.Apoly, DeepParams.Qsum, eval_sub, eval_mul, eval_finsetSum,
    eval_C, eval_pow, eval_X, A.hCv, hv, hQ]
  rw [DeepCheck] at h
  rw [h, sub_self]

/-- **⇒ the extended statement's acceptance.** Openings `J = (ι × Fin r) ⊕ Fin nq` at points
`ζ·off k` (trace) and `ζ` (chunks), all off the domain `α' : D ↪ K`; `r ≥ 1`; unique decoding
`δ ≤ relUDR(RS[α', M+1])`, `M + 1 ≤ |D|`; the DEEP quotient words agree with `natDegree < M` polynomials on one
common `δ`-dense set; `mk` reads a polynomial of `natDegree < M + 1` back as a trace value (`toPoly ∘ mk = id`).
If the verifier's opened-value check holds, there is a trace `tr` whose columns are `δ`-close to the
committed words (and are their unique decodings) on which `(P.statement R0 Rest).Accepts` holds as soon as
`Rest` holds (the quotient conjunct `G_α(ζ) = 0` is discharged). -/
theorem accepts_of_deep {r : ℕ} [NeZero r] (A : AirShape P r) {D : Type} [Fintype D] [DecidableEq D]
    (α' : D ↪ K) {M : ℕ} (hM : M + 1 ≤ Fintype.card D) {δ : ℝ≥0}
    (hδ : δ ≤ Code.relativeUniqueDecodingRadius (ReedSolomon.code α' (M + 1) : Set (D → K)))
    (mk : ∀ p : K[X], p.natDegree < M + 1 → β) (hmk : ∀ p h, P.toPoly (mk p h) = p)
    (f : ι ⊕ Fin P.nq → D → K) (χ : Coins Φ K)
    (vT : ι × Fin r → K) (vQ : Fin P.nq → K)
    (hz : ∀ i, (∀ ck : ι × Fin r, α' i ≠ A.pt ck.1 ck.2 (χ P.z)) ∧ α' i ≠ χ P.z)
    (q : (ι × Fin r) ⊕ Fin P.nq → K[X]) (hq : ∀ j, (q j).natDegree < M) (S : Finset D) (hS : Dense δ S)
    (hagree : ∀ j, Agree α'
      (deepWord α' (f (Sum.elim (fun ck => Sum.inl ck.1) Sum.inr j))
        (Sum.elim (fun ck : ι × Fin r => A.pt ck.1 ck.2 (χ P.z)) (fun _ => χ P.z) j) (Sum.elim vT vQ j))
      (q j) S)
    (hcheck : DeepCheck P A χ (χ P.a) (χ P.z) vT vQ) :
    ∃ tr : DeepTr P,
      (∀ (R0 : RapStatement Φ K ι β colRound) (Rest) m0 fin,
        Rest m0 tr fin χ → (P.statement R0 Rest).Accepts m0 tr fin χ) ∧
      (∀ c, Agree α' (f c) (P.toPoly (tr c)) S) ∧
      ∀ c (P' : K[X]) (S' : Finset D), P'.natDegree < M + 1 → Dense δ S' → Agree α' (f c) P' S' →
        P' = P.toPoly (tr c) := by
  have hcov : Function.Surjective
      (Sum.elim (fun ck : ι × Fin r => (Sum.inl ck.1 : ι ⊕ Fin P.nq)) Sum.inr) := by
    rintro (c | j)
    · exact ⟨Sum.inl (c, 0), rfl⟩
    · exact ⟨Sum.inr j, rfl⟩
  obtain ⟨Pc, hdeg, hA, hop, huniq⟩ := deep_ud _ _ _ α' f hcov
    (by rintro (ck | j) i; exacts [(hz i).1 ck, (hz i).2]) hM hδ q hq S hS hagree
  refine ⟨fun c => mk (Pc c) (hdeg c), fun R0 Rest m0 fin hr => ⟨?_, hr⟩, fun c => by rw [hmk]; exact hA c,
    fun c P' S' h1 h2 h3 => by rw [hmk]; exact huniq c P' S' h1 h2 h3⟩
  refine gpoly_eval_zero_of_check P A χ _ _ _ vT vQ (fun ck => ?_) (fun j => ?_) hcheck
  · rw [hmk]; exact hop (Sum.inl ck)
  · rw [hmk]; exact hop (Sum.inr j)

end

end NockvmE2E.Deep
