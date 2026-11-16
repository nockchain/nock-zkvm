/-
FRI's `List Round` for Quang Dao's
fixed-round format, as an instance of the generic embedding `Lift.Alternating`.

The legacy `Fri.Spec.pSpec k s l = pSpecFold ++ₚ FinalFoldPhase.pSpec ++ₚ QueryRound.pSpec`
(`Fri/Spec/General.lean:55-61`) is used **unchanged**: its length `Fin.vsum (fun _ => 2) + 2 + 1`
is shown equal to `2(k+1)+1` (a `Prop`), its directions are read off the existing position lemmas
(`foldChallenge_val`, `queryChallenge_val`, `nonfinalMessage_val`, `finalMessage_val`), and the
native rounds are
`(Unit, α₀), (f₁, α₁), …, (f_k, α_k), (p_final, xs)`.
The one refinement is the final polynomial: `CompPoly.CPolynomial F` is not `Finite`, so the
native message at legacy position `2k+1` is the subtype of polynomials with `natDegree < d`
(the legacy final-fold degree check made a type, as Sumcheck does with `degreeLE`); every other
native message is the legacy word itself (the subtype predicate is vacuous there).
-/
import NockvmE2E.Lift.OfRbr
import ArkLib.ProofSystem.Fri.Spec.Soundness

open OracleComp OracleSpec ProtocolSpec
open Interaction.Oracle Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open Fri.Spec Domain

set_option linter.unusedSectionVars false

namespace NockvmE2E.FriPort

variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable (s : Fin (k + 1) → ℕ+) (d : ℕ+) (l : ℕ)

/-- FRI's legacy length is `2(k+1)+1`. -/
theorem friLength : (Fin.vsum fun (_ : Fin k) ↦ 2) + 2 + 1 = 2 * (k + 1) + 1 := by
  rw [Fin.vsum_eq_univ_sum]; simp; ring

/-- Challenges sit at the even positions `2i`, `i ≤ k+1`. -/
theorem fri_dirV (i : ℕ) (h : 2 * i < (Fin.vsum fun (_ : Fin k) ↦ 2) + 2 + 1) :
    (pSpec k (ω := ω) s l).dir ⟨2 * i, h⟩ = .V_to_P := by
  have hk := friLength (k := k)
  by_cases hi : i ≤ k
  · have e : (foldChallenge (ω := ω) s l ⟨i, by omega⟩).1 = ⟨2 * i, h⟩ := Fin.ext (by simp)
    rw [← e]; exact (foldChallenge s l _).2
  · have e : (queryChallenge (ω := ω) s l).1 = ⟨2 * i, h⟩ := Fin.ext (by simp; omega)
    rw [← e]; exact (queryChallenge s l).2

/-- Prover messages sit at the odd positions `2i+1`, `i ≤ k`. -/
theorem fri_dirP (i : ℕ) (h : 2 * i + 1 < (Fin.vsum fun (_ : Fin k) ↦ 2) + 2 + 1) :
    (pSpec k (ω := ω) s l).dir ⟨2 * i + 1, h⟩ = .P_to_V := by
  have hk := friLength (k := k)
  by_cases hi : i < k
  · have e : (nonfinalMessage (ω := ω) s l ⟨i, hi⟩).1 = ⟨2 * i + 1, h⟩ := Fin.ext (by simp)
    rw [← e]; exact (nonfinalMessage s l _).2
  · have e : (finalMessage (ω := ω) s l).1 = ⟨2 * i + 1, h⟩ := Fin.ext (by simp; omega)
    rw [← e]; exact (finalMessage s l).2

/-- At `i = k` the legacy message type is the final polynomial. -/
theorem fri_msgType_final (i : ℕ) (h : 2 * i + 1 < (Fin.vsum fun (_ : Fin k) ↦ 2) + 2 + 1)
    (hik : i = k) : (pSpec k (ω := ω) s l).«Type» ⟨2 * i + 1, h⟩ = CompPoly.CPolynomial F := by
  have e : (finalMessage (ω := ω) s l).1 = ⟨2 * i + 1, h⟩ := Fin.ext (by simp; omega)
  rw [← e]; exact finalMessage_type s l

/-- Below `k` the legacy message type is a folded word on a finite domain. -/
theorem fri_msgType_finite (i : ℕ) (h : 2 * i + 1 < (Fin.vsum fun (_ : Fin k) ↦ 2) + 2 + 1)
    (hik : i < k) : Finite ((pSpec k (ω := ω) s l).«Type» ⟨2 * i + 1, h⟩) := by
  have e : (nonfinalMessage (ω := ω) s l ⟨i, hik⟩).1 = ⟨2 * i + 1, h⟩ := Fin.ext (by simp)
  have t := nonfinalMessage_type (ω := ω) s l ⟨i, hik⟩
  rw [← e]; change Finite ((pSpec k (ω := ω) s l).Message _); rw [t]; infer_instance

/-- The native type of the `i`-th FRI prover message: the legacy message, with the final
polynomial (`i = k`) restricted to `natDegree < d`. -/
def FriMsg (i : ℕ) (h : 2 * i + 1 < (Fin.vsum fun (_ : Fin k) ↦ 2) + 2 + 1) : Type :=
  {x : (pSpec k (ω := ω) s l).«Type» ⟨2 * i + 1, h⟩ //
    ∀ hik : i = k, (cast (fri_msgType_final s l i h hik) x).natDegree < d.val}

theorem friMsg_finite (i : ℕ) (h : 2 * i + 1 < (Fin.vsum fun (_ : Fin k) ↦ 2) + 2 + 1) :
    Finite (FriMsg (ω := ω) s d l i h) := by
  have hk := friLength (k := k)
  by_cases hik : i < k
  · have := fri_msgType_finite (ω := ω) s l i h hik
    exact Subtype.finite
  · have hik' : i = k := by omega
    let coeffs : FriMsg (ω := ω) s d l i h → (Fin d.val → F) :=
      fun x j => (cast (fri_msgType_final s l i h hik') x.1).coeff j.val
    refine Finite.of_injective coeffs (fun x y hxy => ?_)
    apply Subtype.ext
    have hc : cast (fri_msgType_final s l i h hik') x.1 = cast (fri_msgType_final s l i h hik') y.1 := by
      apply CompPoly.CPolynomial.eq_iff_coeff.mpr
      intro j
      by_cases hj : j < d.val
      · exact congrFun hxy ⟨j, hj⟩
      · rw [CompPoly.CPolynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (x.2 hik') (by omega)),
          CompPoly.CPolynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (y.2 hik') (by omega))]
    exact (cast_inj _).mp hc

theorem friChal_finite (j : (pSpec k (ω := ω) s l).ChallengeIdx) :
    Finite ((pSpec k (ω := ω) s l).Challenge j) := by
  rcases challenge_cases s l j with ⟨i, rfl⟩ | rfl
  · rw [foldChallenge_type]; infer_instance
  · rw [queryChallenge_type]; infer_instance

theorem friChal_nonempty (j : (pSpec k (ω := ω) s l).ChallengeIdx) :
    Nonempty ((pSpec k (ω := ω) s l).Challenge j) := by
  rcases challenge_cases s l j with ⟨i, rfl⟩ | rfl
  · rw [foldChallenge_type]; exact ⟨0⟩
  · rw [queryChallenge_type]
    exact ⟨fun _ => initialQuery (ω := ω) ⟨0, Nat.two_pow_pos n⟩⟩

/-- **F1. FRI as an alternating verifier-first spec** (`r = k+1` prover messages). -/
noncomputable def friAlt : Lift.Alternating (pSpec k (ω := ω) s l) where
  r := k + 1
  hn := friLength
  dirV := fri_dirV s l
  dirP := fri_dirP s l
  Msg := FriMsg (ω := ω) s d l
  emb := fun _ _ x => x.1
  decEqMsg := fun _ _ => Classical.decEq _
  finiteMsg := friMsg_finite s d l
  finiteChal := friChal_finite s l
  nonemptyChal := friChal_nonempty s l

variable [∀ j, SampleableType ((pSpec k (ω := ω) s l).Challenge j)]

/-- **F1. FRI's native round list** `(Unit, α₀), (f₁, α₁), …, (f_k, α_k), (p_final, xs)`. -/
noncomputable abbrev friRounds : List Round := (friAlt (ω := ω) s d l).rounds

theorem friRounds_length : (friRounds (ω := ω) s d l).length = k + 2 :=
  (friAlt (ω := ω) s d l).rounds_length

end NockvmE2E.FriPort
