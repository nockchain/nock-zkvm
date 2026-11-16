/-
part 1: batched FRI soundness over an ARBITRARY statement type `Stmt`
with a statement map `stm : Stmt → BStmt ω m` composed in (the side statement of the verification-key
proof is `SideStmt`, `Exec/SideStmt.lean`).

This is `batchedFri_singleSalt_soundness` (FriPort/BatchedSoundness.lean:80) re-run through
`singleSalt_soundness_cons` with `stm` composed into the state family, the head law and the acceptance:
the adversary's statement is a `Stmt`, the words FRI runs on are those of `stm z.1`, the bad event is
`stm z.1 ∉ (inputRelation s d m δ).language`.  The right-hand side is the same (`bfriErr`).
-/
import NockvmE2E.FriPort.BatchedSoundness

open OracleComp OracleSpec ProtocolSpec
open Interaction.Oracle Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir
open Fri.Spec Domain
open BatchedFri.Spec BatchedFri.Spec.BatchingRound
open scoped NNReal ENNReal

set_option linter.unusedSectionVars false

namespace NockvmE2E.FriPort.Batched

variable {F : Type} [NonBinaryField F] [Fintype F] [SampleableType F] [DecidableEq F]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable (s : Fin (k + 1) → ℕ+) (d : ℕ+) (l m : ℕ)
variable [∀ j, SampleableType ((pSpec k (ω := ω) s l).Challenge j)]
variable {S : Type} [Fintype S] [Nonempty S] [SampleableType S]
variable (G : CoreDefinitions.Generator S (Fin (m + 1)) F)

/-- The native terminal check over `Stmt`: FRI's `friAccepts` on the combined word of `stm z.1`. -/
noncomputable def stmAccepts {Stmt Salt : Type} (stm : Stmt → BStmt ω m)
    (hdom : 2 ^ (∑ j, (s j).val) * d.val ≤ 2 ^ n)
    (z : Stmt × Salt)
    (path : (protocol (batchedRounds (ω := ω) (S := S) s d l)).tree.ExecutionPath) : Bool :=
  friAccepts s d l hdom (combinedStmt s m G path.2.1 (stm z.1), z.2) path.2.2

/-- the bad outcome of a game: an accepted output whose derived input words are not in the language `L` -/
def badOpt {Stmt Salt P W B : Type} (stm : Stmt → B) (L : Set B) : Option ((Stmt × Salt) × P × W) → Prop
  | none => False
  | some (z, _, _) => stm z.1 ∉ L

/-- **Batched FRI, native single-salt Fiat-Shamir soundness over a statement type `Stmt`.**
For the rounds `batchedRounds` and any single-salt adversary outputting `Stmt`s with at most `Q` fresh keys: the
probability that it outputs an accepted proof whose derived input words `stm z.1` are NOT in the input language is at most
the same bound as `batchedFri_singleSalt_soundness`. -/
theorem batchedFri_stmtOf_soundness {Stmt Salt W : Type} [DecidableEq Stmt] [DecidableEq Salt]
    (stm : Stmt → BStmt ω m)
    (hdom : 2 ^ (∑ j, (s j).val) * d.val ≤ 2 ^ n)
    (θ : ℝ) (δ ε : ℝ≥0)
    (hε : ProximityGap.caError G
      (ReedSolomon.code (ω : Fin (2 ^ n) ↪ F) (2 ^ (∑ i, (s i).1) * d)).carrier δ δ ≤ ε)
    (guards : GuardSchedule (Stmt × Salt) PUnit (batchedRounds (ω := ω) (S := S) s d l))
    (adversary : SingleSaltAdversary Stmt Salt W (batchedRounds (ω := ω) (S := S) s d l))
    (Q : ℕ)
    (queryBound : ∀ phase ∈ support (randomOracleLoggedRun adversary.withQueryLog ∅),
      (freshKeysOfLog phase.1.2).card ≤ Q) :
    Pr{let joint ← (randomOracleLoggedRun
      (singleSaltAcceptedExecution (batchedRounds (ω := ω) (S := S) s d l) guards
        (stmAccepts s d l m G stm hdom) adversary) ∅)}[
      badOpt stm (inputRelation (ω := ω) s d m δ).language joint.1.1.1] ≤
    Q * ((ε : ℝ≥0∞) ⊔ Finset.univ.sup (fun j => (challengeError (ω := ω) s d l θ δ j : ℝ≥0∞))) +
      ((ε : ℝ≥0∞) +
        (((∑ i, foldingError (ω := ω) s d θ i) + Real.toNNReal (1 - min θ δ) ^ l : ℝ≥0) : ℝ≥0∞)) := by
  classical
  have hs := round_bound hdom
  have h := singleSalt_soundness_cons (friAlt (ω := ω) s d l) (batchRound S)
    {st : Stmt | stm st ∈ (inputRelation (ω := ω) s d m δ).language}
    (fun st cs => friState s d l hs θ δ (combinedStmt s m G cs (stm st)))
    (fun st cs m' hm tr msg hafter => by
      by_contra hb
      exact Verifier.badEventState_prover_next _ _ m' hm _ tr hb msg hafter)
    (ε : ℝ≥0∞) (fun j => (challengeError (ω := ω) s d l θ δ j : ℝ≥0∞))
    (fun st hnot => by
      refine le_trans (prEvent_mono _ _ _ ?_) (batching_error s d m G hdom δ ε hε (stm st) hnot)
      intro c hc
      rcases hc with hc | ⟨_, hi, _⟩
      · exact mem_inputLanguage_of_proximity s d hdom δ _ hc
      · exact absurd hi (Nat.not_lt_zero _))
    (fun st _ cs => friState_challengeLaw_all s d l hs θ δ _)
    guards (stmAccepts s d l m G stm hdom) adversary (fun _ _ _ => True)
    (fun z path _ hacc _ => Or.inr ⟨queryChallenge s l, (queryChallenge s l).1.isLt,
      (badEvent_query s d l hs θ _ _).mpr
        ((friAccepts_iff s d l hdom (combinedStmt s m G path.2.1 (stm z.1), z.2) path.2.2).mp hacc)⟩)
    Q queryBound
  rw [← ENNReal.ofNNReal_finsetSum, sum_challengeError] at h
  refine le_trans (prEvent_mono _ _ _ ?_) h
  rintro ⟨⟨⟨_ | ⟨z, path, w⟩, _⟩, _⟩, _⟩ hbad
  · exact (hbad : False).elim
  · exact ⟨hbad, trivial⟩

end NockvmE2E.FriPort.Batched

#print axioms NockvmE2E.FriPort.Batched.batchedFri_stmtOf_soundness
