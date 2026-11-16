/-
batched FRI (`ArkLib.ProofSystem.BatchedFri`) in Quang Dao's
native single-salt Fiat–Shamir, `Witness := Unit`, stated against the SAME input relation
`BatchedFri.Spec.BatchingRound.inputRelation s d m δ` that `Deep/UDFri.lean deep_of_inputRelation`
consumes (the bad event is `stmt ∉ (inputRelation s d m δ).language`).

Native rounds: `(Unit, cs) :: friRounds` (the batching round: no prover message, seed `cs : S`,
then FRI's own native rounds, F1). The legacy per-round certificates are used verbatim:
the batching error `BatchingRound.batching_error` (the head law) and FRI's `badEventState`
(tail), glued by the generic `Batched.singleSalt_soundness_cons`.
-/
import NockvmE2E.FriPort.BatchedCons
import NockvmE2E.FriPort.Soundness
import ArkLib.ProofSystem.BatchedFri.Security

open OracleComp OracleSpec ProtocolSpec
open Interaction.Oracle Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir
open Fri.Spec Domain
open BatchedFri.Spec BatchedFri.Spec.BatchingRound
open scoped NNReal ENNReal

set_option linter.unusedSectionVars false

namespace NockvmE2E.FriPort.Batched

/-- The batching round as a native round: no prover message (`Unit`), challenge the seed `cs : S`. -/
def batchRound (S : Type) [Fintype S] [Nonempty S] [SampleableType S] : Round where
  Message := Unit
  Challenge := S
  interface := OracleInterface.instDefault
  decEqMessage := inferInstance
  finiteMessage := inferInstance
  finiteChallenge := inferInstance
  nonemptyChallenge := inferInstance
  sampleChallenge := inferInstance

variable {F : Type} [NonBinaryField F] [Fintype F] [SampleableType F] [DecidableEq F]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable (s : Fin (k + 1) → ℕ+) (d : ℕ+) (l m : ℕ)
variable [∀ j, SampleableType ((pSpec k (ω := ω) s l).Challenge j)]
variable {S : Type} [Fintype S] [Nonempty S] [SampleableType S]
variable (G : CoreDefinitions.Generator S (Fin (m + 1)) F)

/-- Batched FRI's native round list: the batching round, then FRI's rounds. -/
noncomputable abbrev batchedRounds : List Round := batchRound S :: friRounds (ω := ω) s d l

/-- The batched statement type: exactly the `Unit × oracle words` of `BatchingRound.inputRelation`. -/
abbrev BStmt (ω : SmoothCosetFftDomain n F) (m : ℕ) :=
  Unit × (∀ j, BatchedFri.Spec.OracleStatement m ω j)

/-- The FRI statement produced by the batching round on seed `cs`. -/
def combinedStmt (cs : S) (stmt : BStmt ω m) : FriStmt (ω := ω) s :=
  (Fin.elim0, combinedOracle s m G cs stmt.2)

/-- The native terminal check: FRI's `friAccepts` on the combined statement. -/
noncomputable def batchedAccepts {Salt : Type} (hdom : 2 ^ (∑ j, (s j).val) * d.val ≤ 2 ^ n)
    (z : BStmt ω m × Salt)
    (path : (protocol (batchedRounds (ω := ω) (S := S) s d l)).tree.ExecutionPath) : Bool :=
  friAccepts s d l hdom (combinedStmt s m G path.2.1 z.1, z.2) path.2.2

/-- FRI's `badEventState`, for all statements (trivially true if the word is already close). -/
theorem friState_challengeLaw_all (hs : (∑ j, (s j).val) ≤ n) (θ δ : ℝ) (stmt : FriStmt (ω := ω) s) :
    Lift.Alternating.ChallengeLaw (friState s d l hs θ δ stmt)
      (fun j => (challengeError (ω := ω) s d l θ δ j : ℝ≥0∞)) := by
  by_cases hstmt : initialOracle s stmt ∈ proximityLanguage s d δ
  · intro j tr
    have hb : friState s d l hs θ δ stmt j.1.castSucc tr := Or.inl hstmt
    simp [hb]
  · exact friState_challengeLaw s d l hs θ δ stmt hstmt

/-- **F4. Batched FRI, native single-salt Fiat–Shamir soundness.**
For the native rounds `(Unit, cs), (Unit, α₀), (f₁, α₁), …, (f_k, α_k), (p_final, xs)`, the terminal
check `batchedAccepts` (FRI's acceptance on the combined word) and *any* guard schedule: every
single-salt adversary with at most `Q` distinct fresh keys outputs an accepted proof whose input
words are NOT in `(BatchingRound.inputRelation s d m δ).language` (no common `(1-δ)`-dense set with
degree-bounded witnesses) with probability at most
`Q · max(ε, max_j challengeError_j) + (ε + (Σ_i foldingError_i + (1 − min θ δ)^l))`,
where `ε` bounds the generator's correlated-agreement error `caError G RS δ δ`. -/
theorem batchedFri_singleSalt_soundness (hdom : 2 ^ (∑ j, (s j).val) * d.val ≤ 2 ^ n)
    (θ : ℝ) (δ ε : ℝ≥0)
    (hε : ProximityGap.caError G
      (ReedSolomon.code (ω : Fin (2 ^ n) ↪ F) (2 ^ (∑ i, (s i).1) * d)).carrier δ δ ≤ ε)
    {Salt W : Type} [DecidableEq (BStmt ω m)] [DecidableEq Salt]
    (guards : GuardSchedule (BStmt ω m × Salt) PUnit (batchedRounds (ω := ω) (S := S) s d l))
    (adversary : SingleSaltAdversary (BStmt ω m) Salt W (batchedRounds (ω := ω) (S := S) s d l))
    (Q : ℕ)
    (queryBound : ∀ phase ∈ support (randomOracleLoggedRun adversary.withQueryLog ∅),
      (freshKeysOfLog phase.1.2).card ≤ Q) :
    Pr{let joint ← (randomOracleLoggedRun
      (singleSaltAcceptedExecution (batchedRounds (ω := ω) (S := S) s d l) guards
        (batchedAccepts s d l m G hdom) adversary) ∅)}[
      match joint.1.1.1 with
      | none => False
      | some (z, _, _) => z.1 ∉ (inputRelation (ω := ω) s d m δ).language] ≤
    Q * ((ε : ℝ≥0∞) ⊔ Finset.univ.sup (fun j => (challengeError (ω := ω) s d l θ δ j : ℝ≥0∞))) +
      ((ε : ℝ≥0∞) +
        (((∑ i, foldingError (ω := ω) s d θ i) + Real.toNNReal (1 - min θ δ) ^ l : ℝ≥0) : ℝ≥0∞)) := by
  classical
  have hs := round_bound hdom
  have h := singleSalt_soundness_cons (friAlt (ω := ω) s d l) (batchRound S)
    (inputRelation (ω := ω) s d m δ).language
    (fun stmt cs => friState s d l hs θ δ (combinedStmt s m G cs stmt))
    (fun stmt cs m' hm tr msg hafter => by
      by_contra hb
      exact Verifier.badEventState_prover_next _ _ m' hm _ tr hb msg hafter)
    (ε : ℝ≥0∞) (fun j => (challengeError (ω := ω) s d l θ δ j : ℝ≥0∞))
    (fun stmt hnot => by
      refine le_trans (prEvent_mono _ _ _ ?_) (batching_error s d m G hdom δ ε hε stmt hnot)
      intro c hc
      rcases hc with hc | ⟨_, hi, _⟩
      · exact mem_inputLanguage_of_proximity s d hdom δ _ hc
      · exact absurd hi (Nat.not_lt_zero _))
    (fun stmt _ cs => friState_challengeLaw_all s d l hs θ δ _)
    guards (batchedAccepts s d l m G hdom) adversary (fun _ _ _ => True)
    (fun z path _ hacc _ => Or.inr ⟨queryChallenge s l, (queryChallenge s l).1.isLt,
      (badEvent_query s d l hs θ _ _).mpr
        ((friAccepts_iff s d l hdom (combinedStmt s m G path.2.1 z.1, z.2) path.2.2).mp hacc)⟩)
    Q queryBound
  rw [← ENNReal.ofNNReal_finsetSum, sum_challengeError] at h
  refine le_trans (prEvent_mono _ _ _ ?_) h
  rintro ⟨⟨⟨_ | ⟨z, path, w⟩, _⟩, _⟩, _⟩ hbad
  · exact hbad.elim
  · exact ⟨hbad, trivial⟩

end NockvmE2E.FriPort.Batched
