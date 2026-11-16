/-
SUCC-0, part 2b: the parameterised theorem exercised once end to end, in the IOP form.
* `deepCS P` = `iopCS` at the evaluation oracle `evalOI P.toPoly` (honest oracle access, `ε_CS = 0`).
* `deepPlan`: the DEEP opening plan — opened trace values at `ζ·ω^k`, opened quotient chunks at `ζ`, the
  verifier's opened-value check `DeepCheck` (`Deep/UDLink`) and a residual `RestV`. Its `Link` is
  `gpoly_eval_zero_of_check` plus the per-instance residual link `hRest`.
* `roundBound_deep`: the per-round errors of `P.statement R0 Rest` are the old ones plus `ε_α` at round
  `R` and `ε_ζ` at round `R+1` (`ε_DEEP`, cf. `epsilon_deep`).
* `rap_succinct_sound_deep`: from the RAP inputs of the OLD RAP (`RapInput R0`) and the DEEP
  link `hlink`, composing `certificate_deep` with `rap_succinct_sound_perfect` (hence with
  `rap_singleSalt_knowledge_soundness`):
  `Pr[accepted ∧ ¬Holds] ≤ Q · max_j errs j + Σ_j errs j`, `errs` = old per-round error + `ε_DEEP` split.
-/
import NockvmE2E.Succ.Statement
import NockvmE2E.Succ.ArkLib
import NockvmE2E.Deep.UDLink

set_option autoImplicit false
set_option linter.unusedSectionVars false

open OracleComp OracleSpec Polynomial
open Interaction.Oracle Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir
open scoped ENNReal

namespace NockvmE2E.Succ

open NockvmE2E.Rap NockvmE2E.Deep

variable {Φ : CoinFrame} {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι β : Type}
  {colRound : ι → ℕ} (P : DeepParams Φ K ι β colRound)

/-- The evaluation oracle on DEEP's column polynomials. -/
abbrev deepOI : OracleInterface β := evalOI P.toPoly

/-- The IOP commitment at DEEP's column polynomials (oracle = evaluation). -/
abbrev deepCS : CommitScheme β (deepOI P) := iopCS (deepOI P)

theorem blkOf_eq_of {ι' : Type} {colRound' : ι' → ℕ}
    {s : BadSummand Φ K (Tr ι' β) (TracesStaged Φ colRound')} {b : ℕ}
    (hne : s.coins.Nonempty) (h : ∀ i ∈ s.coins, Φ.sampledAfter i = b) : blkOf s = b := by
  unfold blkOf
  simp only [hne, dite_true]
  exact h _ hne.choose_spec

theorem blkOf_sAlpha : blkOf P.sAlpha = P.R :=
  blkOf_eq_of ⟨P.a, Finset.mem_singleton_self _⟩ (fun i hi => by
    have : i = P.a := Finset.mem_singleton.mp hi
    subst this; exact P.ha)

theorem blkOf_sZeta : blkOf P.sZeta = P.R + 1 :=
  blkOf_eq_of ⟨P.z, Finset.mem_singleton_self _⟩ (fun i hi => by
    have : i = P.z := Finset.mem_singleton.mp hi
    subst this; exact P.hz)

/-- `ε_α = (ns − 1)/|K|`. -/
noncomputable abbrev epsAlpha : ℝ≥0∞ := ((P.ns - 1 : ℕ) : ℝ≥0∞) / (Fintype.card K : ℝ≥0∞)

/-- `ε_ζ = (|D| + (nq+1)|H|)/|K|`. -/
noncomputable abbrev epsZeta : ℝ≥0∞ :=
  ((P.D.card + (P.nq + 1) * P.H.card : ℕ) : ℝ≥0∞) / (Fintype.card K : ℝ≥0∞)

/-- **`ε_DEEP` per round**: the DEEP statement's round error is the old one, plus `ε_α` at round `R` and
`ε_ζ` at round `R+1`. -/
theorem roundBound_deep (R0 : RapStatement Φ K ι β colRound) (Rest) (m0 : R0.M0) (r : ℕ) :
    roundBound (P.statement R0 Rest) blkOf m0 r =
      roundBound R0 blkOf m0 r + (if P.R = r then epsAlpha P else 0) +
        (if P.R + 1 = r then epsZeta P else 0) := by
  have hmap : (((R0.summands m0).map P.liftS).map fun s =>
      if blkOf s = r then (s.weight : ℝ≥0∞) / (Fintype.card K : ℝ≥0∞) ^ s.coins.card else 0).sum =
      roundBound R0 blkOf m0 r := by
    rw [List.map_map]; rfl
  show ((((R0.summands m0).map P.liftS ++ [P.sAlpha, P.sZeta]).map fun s =>
      if blkOf s = r then (s.weight : ℝ≥0∞) / (Fintype.card K : ℝ≥0∞) ^ s.coins.card else 0).sum) = _
  rw [List.map_append, List.sum_append, hmap]
  have hA : (P.sAlpha.weight : ℝ≥0∞) / (Fintype.card K : ℝ≥0∞) ^ P.sAlpha.coins.card = epsAlpha P := by
    show ((P.ns - 1 : ℕ) : ℝ≥0∞) / (Fintype.card K : ℝ≥0∞) ^ ({P.a} : Finset (Fin Φ.n)).card = _
    rw [Finset.card_singleton, pow_one]
  have hZ : (P.sZeta.weight : ℝ≥0∞) / (Fintype.card K : ℝ≥0∞) ^ P.sZeta.coins.card = epsZeta P := by
    show ((P.D.card + (P.nq + 1) * P.H.card : ℕ) : ℝ≥0∞) / (Fintype.card K : ℝ≥0∞) ^
      ({P.z} : Finset (Fin Φ.n)).card = _
    rw [Finset.card_singleton, pow_one]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, blkOf_sAlpha P,
    blkOf_sZeta P, hA, hZ, add_assoc]

/-- The DEEP-extended per-round error schedule. -/
noncomputable def errDeep (errOld : ℕ → ℝ≥0∞) (r : ℕ) : ℝ≥0∞ :=
  errOld r + (if P.R = r then epsAlpha P else 0) + (if P.R + 1 = r then epsZeta P else 0)

/-! ### The DEEP opening plan and its link -/

section Plan

variable [Fintype ι] {r : ℕ} (A : AirShape P r) (R0 : RapStatement Φ K ι β colRound)
  (Rest : R0.M0 → DeepTr P → R0.Mfin → Coins Φ K → Prop)

/-- The DEEP succinct final message: the full verifier's final message, the opened trace values
`vT (c, k)` at `ζ·off k`, the opened chunks `vQ j` at `ζ`. -/
abbrev DeepFin := R0.Mfin × (ι × Fin r → K) × (Fin P.nq → K)

/-- The DEEP claims. -/
noncomputable def deepClaims (χ : Coins Φ K) (fin : DeepFin P (r := r) R0) : Claims (deepOI P) (ι ⊕ Fin P.nq) :=
  (Finset.univ.toList.map fun ck : ι × Fin r =>
      ((Sum.inl ck.1 : ι ⊕ Fin P.nq), (⟨A.pt ck.1 ck.2 (χ P.z), fin.2.1 ck⟩ : (_ : K) × K))) ++
    (Finset.univ.toList.map fun j : Fin P.nq =>
      ((Sum.inr j : ι ⊕ Fin P.nq), (⟨χ P.z, fin.2.2 j⟩ : (_ : K) × K)))

/-- **The DEEP opening plan** with a residual check `RestV` on the opened values. -/
noncomputable def deepPlan (RestV : R0.M0 → DeepFin P (r := r) R0 → Coins Φ K → Prop) :
    OpenPlan (P.statement R0 Rest) (deepCS P) where
  Mfin := DeepFin P (r := r) R0
  claims _ fin χ := deepClaims P A R0 χ fin
  pf _ := ()
  check m0 fin χ := DeepCheck P A χ (χ P.a) (χ P.z) fin.2.1 fin.2.2 ∧ RestV m0 fin χ
  finOf fin := fin.1

/-- **The DEEP link**: the opened-value check (`gpoly_eval_zero_of_check`) and the residual link `hRest`
give the full (DEEP-extended) verifier on any trace satisfying the openings. -/
theorem link_deepPlan (RestV : R0.M0 → DeepFin P (r := r) R0 → Coins Φ K → Prop)
    (hRest : ∀ m0 (tr : DeepTr P) fin χ, RestV m0 fin χ →
      SatClaims (deepOI P) tr (deepClaims P A R0 χ fin) → Rest m0 tr fin.1 χ) :
    Link (P.statement R0 Rest) (deepCS P) (deepPlan P A R0 Rest RestV) := by
  intro m0 tr fin χ hc hs
  refine ⟨?_, hRest m0 tr fin χ hc.2 hs⟩
  refine gpoly_eval_zero_of_check P A χ tr (χ P.a) (χ P.z) fin.2.1 fin.2.2 (fun ck => ?_) (fun j => ?_) hc.1
  · exact hs _ (List.mem_append_left _ (List.mem_map.mpr ⟨ck, Finset.mem_toList.mpr (Finset.mem_univ _), rfl⟩))
  · exact hs _ (List.mem_append_right _ (List.mem_map.mpr ⟨j, Finset.mem_toList.mpr (Finset.mem_univ _), rfl⟩))

end Plan

/-! ### The IOP form, end to end -/

section Sound

variable [SampleableType K] [Inhabited K] [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
  [Inhabited β]

/-- **`rap_succinct_sound` in the IOP form for the DEEP-extended RAP** (`ε_CS = 0`). Inputs: the old RAP's
`RapInput` (pointwise soundness, one-round summands, `|K| ≥ 2`; locality derived), the DEEP link `hlink`
(old acceptance from constraint vanishing), `R+1 < nb`, an opening plan with its `Link`, and old per-round
bounds `errOld`. The errors are `errDeep errOld` (`ε_α` at `R`, `ε_ζ` at `R+1`). -/
theorem rap_succinct_sound_deep (R0 : RapStatement Φ K ι β colRound)
    (Rest : R0.M0 → DeepTr P → R0.Mfin → Coins Φ K → Prop) {nb : ℕ} (hR0 : RapInput R0 nb)
    (hlink : ∀ m0 (tr : DeepTr P) fin χ, Rest m0 tr fin χ →
      (∀ i, ∀ x ∈ P.H, eval x (P.Cp χ (P.restr tr) i) = 0) → R0.Accepts m0 (P.restr tr) fin χ)
    (hnb : P.R + 1 < nb)
    (plan : OpenPlan (P.statement R0 Rest) (deepCS P)) (hl : Link (P.statement R0 Rest) (deepCS P) plan)
    [DecidableEq (P.statement R0 Rest).M0] [Finite (P.statement R0 Rest).M0]
    [DecidableEq plan.Mfin] [Finite plan.Mfin]
    (I0 : OracleInterface (P.statement R0 Rest).M0)
    (I : (r : ℕ) → OracleInterface (Cols P.colRoundX β r)) (Ifin : OracleInterface plan.Mfin)
    (errOld : ℕ → ℝ≥0∞) (herr0 : ∀ m0 r, roundBound R0 blkOf m0 r ≤ errOld r)
    {Statement GlobalSalt Witness : Type} [DecidableEq Statement] [DecidableEq GlobalSalt]
    (guards : GuardSchedule (Statement × GlobalSalt) PUnit
      (sRounds (P.statement R0 Rest) (deepCS P) plan I0 I Ifin nb))
    (adversary : SingleSaltAdversary Statement GlobalSalt Witness
      (sRounds (P.statement R0 Rest) (deepCS P) plan I0 I Ifin nb))
    (Q : ℕ) (queryBound : ∀ phase ∈ support (randomOracleLoggedRun adversary.withQueryLog ∅),
      (freshKeysOfLog phase.1.2).card ≤ Q) :
    Pr{let joint ← (randomOracleLoggedRun (singleSaltAcceptedExecution
        (sRounds (P.statement R0 Rest) (deepCS P) plan I0 I Ifin nb) guards
        (sAccept (P.statement R0 Rest) (deepCS P) plan I0 I Ifin nb) adversary) ∅)}[
        (∃ x, joint.1.1.1 = some x) ∧ ¬ R0.Holds] ≤
      Q * Finset.univ.sup (sErrors (P.statement R0 Rest) (deepCS P) plan I0 I Ifin nb (errDeep P errOld)) +
        ∑ j, sErrors (P.statement R0 Rest) (deepCS P) plan I0 I Ifin nb (errDeep P errOld) j := by
  have hC : Certificate (P.statement R0 Rest) blkOf nb :=
    certificate_deep P R0 Rest hlink blkOf nb (certificate_of_input hR0) hnb blkOf
      (fun _ _ _ => rfl) (blkOf_sAlpha P) (blkOf_sZeta P)
  exact rap_succinct_sound_perfect (iopCS_perfect _) hC hl (errDeep P errOld)
    (fun m0 r => by
      refine (roundBound_deep P R0 Rest m0 r).le.trans ?_
      unfold errDeep
      gcongr
      exact herr0 m0 r)
    guards adversary Q queryBound

end Sound

end NockvmE2E.Succ
