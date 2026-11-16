/-
generic "prepend one `(Unit, c₀)` round" transport.

The legacy batched spec `batchSpec S ++ₚ pSpec` is `V,V,P,V,…`, so it is not itself `Alternating`.
Native rounds, however, are `(Unit, cs) :: A.rounds`, and the native round extractor for such a
list is the one of `A.rounds` run under the state "after seed `cs`" (`consExt`). This file proves the
single-salt FS bound for `r₀ :: A.rounds` with a legacy-style head law for the first challenge and
`Alternating`'s per-challenge law for the tail (a state family `S cs` for each head challenge `cs`).
-/
import NockvmE2E.Lift.OfRbr

open OracleComp OracleSpec ProtocolSpec
open Interaction.Oracle Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir
open scoped NNReal ENNReal

set_option linter.unusedSectionVars false

namespace NockvmE2E.FriPort.Batched

open NockvmE2E.Lift NockvmE2E.Lift.Alternating

variable {n : ℕ} {pSpec : ProtocolSpec n} (A : Alternating pSpec)
  [hsamp : ∀ j, SampleableType (pSpec.Challenge j)]

/-- The native round extractor of `r₀ :: A.rounds`: input state `P0`; after head challenge `cs` the
state is `S cs` at the empty legacy prefix, and the tail is `A`'s `Unit`-witness extractor of `S cs`. -/
def consExt (r0 : Round) (P0 : Prop)
    (S : r0.Challenge → (m : Fin (n + 1)) → Transcript m pSpec → Prop) :
    RoundExtractor (protocol (r0 :: A.rounds)).tree (kst P0) :=
  fun _ => ⟨kst P0, id, fun cs => ⟨kst (S cs _ (tr0 pSpec)), fun _ => (), A.headExt (S cs)⟩⟩

theorem consExt_terminalState (r0 : Round) (P0 : Prop)
    (S : r0.Challenge → (m : Fin (n + 1)) → Transcript m pSpec → Prop)
    (path : (protocol (r0 :: A.rounds)).tree.ExecutionPath) :
    (consExt A r0 P0 S).terminalState path =
      kst (S path.2.1 (Fin.last n) (A.pathTranscript path.2.2)) :=
  A.headExt_terminalState (S path.2.1) path.2.2

theorem consExt_preserving (r0 : Round) (P0 : Prop)
    (S : r0.Challenge → (m : Fin (n + 1)) → Transcript m pSpec → Prop)
    (hnext : ∀ cs, NextLaw (S cs)) :
    (consExt A r0 P0 S).IsProverPreserving (protocol (r0 :: A.rounds)).roles :=
  ⟨fun _ _ h => h, fun _ => ⟨fun _ hrole => (nomatch hrole), fun cs =>
    A.headExt_preserving (S cs) (hnext cs)⟩⟩

/-- Local bounds: head challenge with error `ε0`, tail from the legacy per-challenge law. -/
theorem consExt_bounded (r0 : Round) (P0 : Prop)
    (S : r0.Challenge → (m : Fin (n + 1)) → Transcript m pSpec → Prop)
    (ε0 : ℝ≥0∞) (err : pSpec.ChallengeIdx → ℝ≥0∞)
    (hhead : Pr{let c ← $ᵗ r0.Challenge}[¬ P0 ∧ S c _ (tr0 pSpec)] ≤ ε0)
    (hlaw : ∀ cs, ChallengeLaw (S cs) err)
    (errors : RoundErrors (r0 :: A.rounds))
    (h0 : errors 0 = ε0) (hs : ∀ t, errors t.succ = A.roundErrors err t) :
    RoundExtractor.IsLocallyBounded (consExt A r0 P0 S) (protocol (r0 :: A.rounds)).roles
      (roundErrorSchedule (r0 :: A.rounds) errors) := fun _ => by
  have hfun : (fun j => errors j.succ) = A.roundErrors err := funext hs
  refine ⟨?_, fun cs => ?_⟩
  · rw [_root_.RoundByRound.GameFamily.isBounded_iff]
    intro _ _
    refine le_trans (prEvent_mono _ _ _ ?_) (h0 ▸ hhead)
    rintro c ⟨_, hbefore, hafter⟩
    exact ⟨hbefore, hafter⟩
  · show RoundExtractor.IsLocallyBounded (A.headExt (S cs)) (protocol A.rounds).roles
      (roundErrorSchedule A.rounds (fun j => errors j.succ))
    rw [hfun]
    exact A.headExt_bounded (S cs) err (hlaw cs)

variable {StmtIn Salt W : Type} [DecidableEq StmtIn] [DecidableEq Salt]

/-- **Prepend-a-round transport.** Single-salt FS soundness of `r₀ :: A.rounds`. -/
theorem singleSalt_soundness_cons (r0 : Round)
    (L : Set StmtIn) (S : StmtIn → r0.Challenge → (m : Fin (n + 1)) → Transcript m pSpec → Prop)
    (hnext : ∀ stmt cs, NextLaw (S stmt cs))
    (ε0 : ℝ≥0∞) (err : pSpec.ChallengeIdx → ℝ≥0∞)
    (hhead : ∀ stmt ∉ L, Pr{let c ← $ᵗ r0.Challenge}[S stmt c _ (tr0 pSpec)] ≤ ε0)
    (hlaw : ∀ stmt ∉ L, ∀ cs, ChallengeLaw (S stmt cs) err)
    (guards : GuardSchedule (StmtIn × Salt) PUnit (r0 :: A.rounds))
    (accepts : (StmtIn × Salt) → (protocol (r0 :: A.rounds)).tree.ExecutionPath → Bool)
    (adversary : SingleSaltAdversary StmtIn Salt W (r0 :: A.rounds))
    (Rout : (StmtIn × Salt) → (protocol (r0 :: A.rounds)).tree.ExecutionPath → W → Prop)
    (outputLaw : ∀ z path w, accepts z path = true → Rout z path w →
      S z.1 path.2.1 (Fin.last n) (A.pathTranscript path.2.2))
    (Q : ℕ)
    (queryBound : ∀ phase ∈ support (randomOracleLoggedRun adversary.withQueryLog ∅),
      (freshKeysOfLog phase.1.2).card ≤ Q) :
    Pr{let joint ← (randomOracleLoggedRun
      (singleSaltAcceptedExecution (r0 :: A.rounds) guards accepts adversary) ∅)}[
      match joint.1.1.1 with
      | none => False
      | some (z, path, w) => z.1 ∉ L ∧ Rout z path w] ≤
    Q * (ε0 ⊔ Finset.univ.sup err) + (ε0 + ∑ j, err j) := by
  let errors : RoundErrors (r0 :: A.rounds) := fun j => Fin.cases ε0 (A.roundErrors err) j
  have h0 : errors 0 = ε0 := rfl
  have hs : ∀ t, errors t.succ = A.roundErrors err t := fun t => rfl
  have h := singleSalt_knowledge_soundness_queryBound guards accepts errors adversary
    (fun z => kst (z.1 ∈ L)) (fun z => consExt A r0 (z.1 ∈ L) (S z.1)) {z | z.1 ∉ L}
    (fun z _ => consExt_preserving A r0 _ (S z.1) (hnext z.1))
    (fun z hz => consExt_bounded A r0 _ (S z.1) ε0 err
      (le_trans (prEvent_mono _ _ _ (fun c hc => hc.2)) (hhead z.1 hz))
      (hlaw z.1 hz) errors h0 hs)
    (fun z _ => z.1 ∈ L) Rout
    (fun z path _ => (consExt_terminalState A r0 _ (S z.1) path).symm ▸ ())
    (fun _ _ => Iff.rfl)
    (fun z path w hacc hR => (KnowledgeState.holds_cast
      (consExt_terminalState A r0 _ (S z.1) path) ()).mpr (outputLaw z path w hacc hR))
    Q queryBound
  have hsum : ∑ j, errors j = ε0 + ∑ j, err j := by
    show ∑ j : Fin (A.rounds.length + 1), errors j = _
    rw [Fin.sum_univ_succ]
    simp only [h0, hs]
    rw [A.sum_roundErrors]
  have hsup : Finset.univ.sup errors ≤ ε0 ⊔ Finset.univ.sup err := by
    refine Finset.sup_le (fun i _ => ?_)
    refine Fin.cases ?_ (fun t => ?_) i
    · exact le_sup_left
    · rw [hs]
      exact le_sup_of_le_right (by
        rw [← A.sup_roundErrors]; exact Finset.le_sup (f := A.roundErrors err) (Finset.mem_univ t))
  rw [hsum] at h
  refine le_trans (prEvent_mono _ _ _ ?_) (le_trans h (add_le_add_left (by gcongr) _))
  rintro ⟨⟨⟨_ | ⟨z, path, w⟩, _⟩, _⟩, _⟩ hbad
  · exact hbad.elim
  · exact ⟨hbad.1, hbad.2, fun h0 => hbad.1 h0⟩

end NockvmE2E.FriPort.Batched
