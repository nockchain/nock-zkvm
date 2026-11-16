/-
FRI under Quang Dao's native
single-salt Fiat–Shamir, route (c) with `Witness := Unit`.

The certificate is FRI's own round-by-round certificate, used verbatim: the bad-event state
function `Verifier.badEventState` (`OracleReduction/Security/BadEvents.lean:85`) of the bad events
`Fri.Spec.badEvent` with the per-challenge bound `Fri.Spec.badEvent_prob_le`
(`Fri/Spec/BadEvents.lean:175`) — exactly the inputs from which `Fri.Spec.rbr_soundness`
(`Soundness.lean:100`) is assembled by `rbrSoundness_of_badEvents`. (`rbr_soundness` itself exposes
the state function only under `∃`; using its two ingredients directly lets the terminal law be
FRI's acceptance predicate rather than the legacy output language.) It is transported by the
generic (`Lift/`), and the error sum is `Fri.Spec.sum_challengeError`.
-/
import NockvmE2E.FriPort.Accepts

open OracleComp OracleSpec ProtocolSpec
open Interaction.Oracle Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir
open Fri.Spec Domain
open scoped NNReal ENNReal

set_option linter.unusedSectionVars false

namespace NockvmE2E.FriPort

variable {F : Type} [NonBinaryField F] [Fintype F] [SampleableType F] [DecidableEq F]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable (s : Fin (k + 1) → ℕ+) (d : ℕ+) (l : ℕ)
variable [∀ j, SampleableType ((pSpec k (ω := ω) s l).Challenge j)]

/-- FRI's legacy state at a statement: the initial word is `δ`-close, or a bad challenge already
occurred (`Verifier.badEventState` of `Fri.Spec.badEvent`). -/
def friState (hs : (∑ j, (s j).val) ≤ n) (θ δ : ℝ) (stmt : FriStmt (ω := ω) s)
    (m : Fin ((Fin.vsum fun (_ : Fin k) ↦ 2) + 2 + 1 + 1))
    (tr : Transcript m (pSpec k (ω := ω) s l)) : Prop :=
  Verifier.badEventState (proximityLanguage s d δ) (badEvent s d l hs θ) m (initialOracle s stmt) tr

/-- The legacy per-challenge law of `friState`, from `Fri.Spec.badEvent_prob_le`. -/
theorem friState_challengeLaw (hs : (∑ j, (s j).val) ≤ n) (θ δ : ℝ) (stmt : FriStmt (ω := ω) s)
    (hstmt : initialOracle s stmt ∉ proximityLanguage s d δ) :
    Lift.Alternating.ChallengeLaw (friState s d l hs θ δ stmt)
      (fun j => (challengeError (ω := ω) s d l θ δ j : ℝ≥0∞)) := by
  intro j tr
  by_cases hb : friState s d l hs θ δ stmt j.1.castSucc tr
  · simp [hb]
  · refine le_trans (prEvent_mono _ _ _ ?_)
      (badEvent_prob_le s d l hs θ δ (initialOracle s stmt) hstmt j tr hb)
    intro c hc
    obtain ⟨_, hbad⟩ := Verifier.badEventState_new _ _ _ tr c hc.1 hc.2
    exact hbad

/-- **FRI, native single-salt Fiat–Shamir soundness**.
For FRI's native round list `(Unit, α₀), (f₁, α₁), …, (f_k, α_k), (p_final, xs)`, its
terminal check `friAccepts` (F2: the legacy FRI verifier's acceptance on the decoded transcript)
and *any* guard schedule: every single-salt adversary with at most `Q` distinct fresh
random-oracle keys outputs an accepted proof whose initial word is `δ`-far from the initial
Reed–Solomon code with probability at most
`Q · max_j challengeError_j + (Σ_i foldingError_i + (1 − min θ δ)^l)`,
where `challengeError` is `foldingError i` at the `i`-th folding challenge and `(1 − min θ δ)^l`
at the query challenge (`Fri.Spec.challengeError`). -/
theorem fri_singleSalt_soundness (hdom : 2 ^ (∑ j, (s j).val) * d.val ≤ 2 ^ n) (θ δ : ℝ)
    {Salt W : Type} [DecidableEq (FriStmt (ω := ω) s)] [DecidableEq Salt]
    (guards : GuardSchedule (FriStmt (ω := ω) s × Salt) PUnit (friRounds (ω := ω) s d l))
    (adversary : SingleSaltAdversary (FriStmt (ω := ω) s) Salt W (friRounds (ω := ω) s d l))
    (Q : ℕ)
    (queryBound : ∀ phase ∈ support (randomOracleLoggedRun adversary.withQueryLog ∅),
      (freshKeysOfLog phase.1.2).card ≤ Q) :
    Pr{let joint ← (randomOracleLoggedRun
      (singleSaltAcceptedExecution (friRounds (ω := ω) s d l) guards (friAccepts s d l hdom)
        adversary) ∅)}[
      match joint.1.1.1 with
      | none => False
      | some (z, _, _) => initialOracle s z.1 ∉ proximityLanguage s d δ] ≤
    Q * Finset.univ.sup (fun j => (challengeError (ω := ω) s d l θ δ j : ℝ≥0∞)) +
      (((∑ i, foldingError (ω := ω) s d θ i) + Real.toNNReal (1 - min θ δ) ^ l : ℝ≥0) : ℝ≥0∞) := by
  have hs := round_bound hdom
  have h := (friAlt (ω := ω) s d l).singleSalt_soundness_of_stateFamily'
    {stmt | initialOracle s stmt ∈ proximityLanguage s d δ}
    (friState s d l hs θ δ)
    (fun stmt h0 => by
      rcases h0 with h0 | ⟨_, hi, _⟩
      · exact h0
      · exact absurd hi (Nat.not_lt_zero _))
    (fun stmt m hm tr msg hafter => by
      by_contra hb
      exact Verifier.badEventState_prover_next _ _ m hm _ tr hb msg hafter)
    (fun j => (challengeError (ω := ω) s d l θ δ j : ℝ≥0∞))
    (fun stmt hstmt => friState_challengeLaw s d l hs θ δ stmt hstmt)
    guards (friAccepts s d l hdom) adversary (fun _ _ _ => True)
    (fun z path _ hacc _ => Or.inr ⟨queryChallenge s l, (queryChallenge s l).1.isLt,
      (badEvent_query s d l hs θ _ _).mpr ((friAccepts_iff s d l hdom z path).mp hacc)⟩)
    Q queryBound
  rw [← ENNReal.ofNNReal_finsetSum, sum_challengeError] at h
  refine le_trans (prEvent_mono _ _ _ ?_) h
  rintro ⟨⟨⟨_ | ⟨z, path, w⟩, _⟩, _⟩, _⟩ hbad
  · exact hbad.elim
  · exact ⟨hbad, trivial⟩

/-- The same with the canonical guard schedule (no early stop). -/
theorem fri_singleSalt_soundness_trueGuards (hdom : 2 ^ (∑ j, (s j).val) * d.val ≤ 2 ^ n)
    (θ δ : ℝ) {Salt W : Type} [DecidableEq (FriStmt (ω := ω) s)] [DecidableEq Salt]
    (adversary : SingleSaltAdversary (FriStmt (ω := ω) s) Salt W (friRounds (ω := ω) s d l))
    (Q : ℕ)
    (queryBound : ∀ phase ∈ support (randomOracleLoggedRun adversary.withQueryLog ∅),
      (freshKeysOfLog phase.1.2).card ≤ Q) :
    Pr{let joint ← (randomOracleLoggedRun
      (singleSaltAcceptedExecution (friRounds (ω := ω) s d l) (trueGuards _)
        (friAccepts s d l hdom) adversary) ∅)}[
      match joint.1.1.1 with
      | none => False
      | some (z, _, _) => initialOracle s z.1 ∉ proximityLanguage s d δ] ≤
    Q * Finset.univ.sup (fun j => (challengeError (ω := ω) s d l θ δ j : ℝ≥0∞)) +
      (((∑ i, foldingError (ω := ω) s d θ i) + Real.toNNReal (1 - min θ δ) ^ l : ℝ≥0) : ℝ≥0∞) :=
  fri_singleSalt_soundness s d l hdom θ δ _ adversary Q queryBound

end NockvmE2E.FriPort
