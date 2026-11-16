/-
ArkLib bridge: membership in batched FRI's `BatchingRound.inputRelation` (words agree with their
degree-bounded witnesses on ONE common set of relative size `≥ 1 − δ`; ArkLib
`BatchedFri/Spec/SingleRound.lean:96-100`), when the batched words are the DEEP quotient words of committed
words `f_c`, gives the polynomials `P_c` of `deep_ud`: (i) common-set closeness, (ii) the opening equations,
(iii) uniqueness within `δ`. FRI degree bound `N = 2^{Σ s}·d`; the `P_c` have `natDegree < N + 1`.
-/
import NockvmE2E.Deep.UDBatch
import ArkLib.ProofSystem.BatchedFri.Spec.SingleRound

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial NNReal

namespace NockvmE2E.Deep

section
variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F] {n k : ℕ}
  {s : Fin (k + 1) → ℕ+} {d : ℕ+} {m : ℕ} {ω : Domain.SmoothCosetFftDomain n F}

/-- The smooth coset domain as an embedding (its points are distinct). -/
def domEmb (ω : Domain.SmoothCosetFftDomain n F) : Fin (2 ^ n) ↪ F :=
  ⟨ω, Domain.CosetFftDomain.injective⟩

/-- The FRI degree bound `2^{Σ s}·d`. -/
abbrev friBound (s : Fin (k + 1) → ℕ+) (d : ℕ+) : ℕ := 2 ^ (∑ i, (s i).1) * d

theorem natDegree_witness_lt (p : CompPoly.CPolynomial.degreeLT (R := F) (friBound s d)) :
    (p.1.toPoly).natDegree < friBound s d := by
  have hpos : 0 < friBound s d := Nat.mul_pos (Nat.pow_pos (by norm_num)) d.pos
  have h := CompPoly.CPolynomial.mem_degreeLT.mp p.2
  rw [CompPoly.CPolynomial.degree_toPoly] at h
  by_cases h0 : p.1.toPoly = 0
  · rw [h0, natDegree_zero]; exact hpos
  · exact (natDegree_lt_iff_degree_lt h0).mpr h

/-- **FRI form.** `sw ∈ inputRelation s d m δ`; its oracle words are the DEEP quotient words
`(f_{col j} − val j)/(X − pt j)` (`hwords`); every column is opened (`col` surjective); opening points are off
the domain; `δ ≤ relUDR(RS[ω, N+1])` with `N + 1 ≤ 2^n`, `N = 2^{Σ s}·d`. Then there are `P_c`
(`natDegree < N + 1`), agreeing with `f_c` on one common `(1−δ)`-dense set, with `P_{col j}(pt j) = val j`, and
each `P_c` is the unique polynomial of `natDegree < N + 1` that is `δ`-close to `f_c`. -/
theorem deep_of_inputRelation {γ : Type} (col : Fin (m + 1) → γ) (pt val : Fin (m + 1) → F)
    (f : γ → Fin (2 ^ n) → F) (hcov : Function.Surjective col) (hz : ∀ j i, ω i ≠ pt j)
    (hN : friBound s d + 1 ≤ 2 ^ n) {δ : ℝ≥0}
    (hδ : δ ≤ Code.relativeUniqueDecodingRadius
      (ReedSolomon.code (domEmb ω) (friBound s d + 1) : Set (Fin (2 ^ n) → F)))
    (sw : (Unit × (∀ j, BatchedFri.Spec.OracleStatement m ω j)) × BatchedFri.Spec.Witness F s d m)
    (hsw : sw ∈ BatchedFri.Spec.BatchingRound.inputRelation s d m δ)
    (hwords : ∀ j i, sw.1.2 j (ω.equivToFinset i) = deepWord ω (f (col j)) (pt j) (val j) i) :
    ∃ P : γ → F[X], (∃ S : Finset (Fin (2 ^ n)), Dense δ S ∧ ∀ c, Agree ω (f c) (P c) S) ∧
      (∀ c, (P c).natDegree < friBound s d + 1) ∧
      (∀ j, (P (col j)).eval (pt j) = val j) ∧
      ∀ c (P' : F[X]) (S' : Finset (Fin (2 ^ n))), P'.natDegree < friBound s d + 1 → Dense δ S' →
        Agree ω (f c) P' S' → P' = P c := by
  obtain ⟨S, hS, hag⟩ := hsw
  have hagree : ∀ j, Agree (domEmb ω) (deepWord (domEmb ω) (f (col j)) (pt j) (val j))
      ((sw.2 j).1.toPoly) S := by
    intro j i hi
    have := hag j i hi
    rw [hwords, CompPoly.CPolynomial.eval_toPoly] at this
    exact this
  obtain ⟨P, hdeg, hA, hop, huniq⟩ := deep_ud col pt val (domEmb ω) f hcov hz
    (M := friBound s d) (by rwa [Fintype.card_fin]) hδ
    (fun j => (sw.2 j).1.toPoly) (fun j => natDegree_witness_lt _) S hS hagree
  exact ⟨P, ⟨S, hS, hA⟩, hdeg, hop, huniq⟩

end

end NockvmE2E.Deep
