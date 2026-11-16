/-
legacy round-by-round soundness
of an alternating verifier-first spec ⇒ native single-salt Fiat–Shamir soundness through
`Interaction.Oracle.FiatShamir.singleSalt_knowledge_soundness_queryBound`, `ArkLib/Interaction/Oracle/FiatShamir/SingleSaltSecurity.lean:319`), with
`Witness := Unit` (ordinary soundness, exactly Sumcheck's `claimState` use of the theorem; not a
claim of substantive witness extraction).

* `singleSalt_soundness_of_stateFamily`: from any legacy state predicate family with the
  three legacy laws (empty prefix ⇒ input language, `toFun_next`, per-challenge bound) and an
  output law for the native terminal check, the bound `Q · max ε + Σ ε` on
  `Pr[accepted ∧ statement ∉ language ∧ Rout]`.
* `singleSalt_soundness_of_rbrSoundness`: the same from the legacy `Verifier.rbrSoundness`
  itself, with `Rout` the legacy terminal acceptance (`toFun_full`).
* `sum_roundErrors`, `sup_roundErrors`: the native error vector is the legacy
  per-challenge error re-indexed by a bijection `Fin rounds.length ≃ ChallengeIdx`.
-/
import NockvmE2E.Lift.Alternating
import ArkLibFs.Interaction.Oracle.FiatShamir.SingleSaltSecurity

open OracleComp OracleSpec ProtocolSpec
open Interaction.Oracle Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir
open scoped NNReal ENNReal

set_option linter.unusedSectionVars false

namespace NockvmE2E.Lift.Alternating

variable {n : ℕ} {pSpec : ProtocolSpec n} (A : Alternating pSpec)
  [hsamp : ∀ j, SampleableType (pSpec.Challenge j)]

/-! ## error re-indexing -/

/-- Native rounds ↔ legacy challenges: round `t` is the challenge at position `2t`. -/
noncomputable def roundChallengeEquiv : Fin A.rounds.length ≃ pSpec.ChallengeIdx :=
  Equiv.ofBijective (fun t => A.chIdx t.val (A.lt_of_le_r (by have := A.rounds_length; omega)))
    ⟨fun t t' h => by
      have := congrArg (fun j : pSpec.ChallengeIdx => j.1.val) h
      simp only [chIdx_val] at this
      exact Fin.ext (by omega),
     fun j => by
      obtain ⟨t, ht, rfl⟩ := A.challenge_even j
      exact ⟨⟨t, by rw [A.rounds_length]; omega⟩, rfl⟩⟩

theorem roundErrors_eq (err : pSpec.ChallengeIdx → ℝ≥0∞) (t : Fin A.rounds.length) :
    A.roundErrors err t = err (A.roundChallengeEquiv t) := rfl

/-- `Σ_t ε_t` over native rounds is `Σ_j err j` over legacy challenges. -/
theorem sum_roundErrors (err : pSpec.ChallengeIdx → ℝ≥0∞) :
    ∑ t, A.roundErrors err t = ∑ j, err j :=
  Fintype.sum_equiv A.roundChallengeEquiv _ _ (fun _ => rfl)

/-- `max_t ε_t` over native rounds is `max_j err j` over legacy challenges. -/
theorem sup_roundErrors (err : pSpec.ChallengeIdx → ℝ≥0∞) :
    Finset.univ.sup (A.roundErrors err) = Finset.univ.sup err := by
  classical
  rw [← Finset.map_univ_equiv A.roundChallengeEquiv, Finset.sup_map]
  rfl

/-! ## the transport -/

variable {StmtIn Salt W : Type} [DecidableEq StmtIn] [DecidableEq Salt]

/-- **state-family form.** Native single-salt FS soundness of the embedded legacy protocol from
a legacy state predicate family `S stmt` with: (i) at the empty prefix it implies the input
language, (ii) the prover-message law, (iii) the per-challenge law outside the language; plus an
output law tying the native terminal check `accepts` (and `Rout`) to `S` at the decoded legacy
full transcript. Every adversary with at most `Q` distinct fresh keys outputs an accepted proof of
a statement outside `L` (with `Rout`) w.p. at most `Q · max ε + Σ ε`. -/
theorem singleSalt_soundness_of_stateFamily
    (L : Set StmtIn) (S : StmtIn → (m : Fin (n + 1)) → Transcript m pSpec → Prop)
    (hzero : ∀ stmt, S stmt _ (tr0 pSpec) → stmt ∈ L)
    (hnext : ∀ stmt, NextLaw (S stmt))
    (err : pSpec.ChallengeIdx → ℝ≥0∞)
    (hlaw : ∀ stmt ∉ L, ChallengeLaw (S stmt) err)
    (guards : GuardSchedule (StmtIn × Salt) PUnit A.rounds)
    (accepts : (StmtIn × Salt) → (protocol A.rounds).tree.ExecutionPath → Bool)
    (adversary : SingleSaltAdversary StmtIn Salt W A.rounds)
    (Rout : (StmtIn × Salt) → (protocol A.rounds).tree.ExecutionPath → W → Prop)
    (outputLaw : ∀ z path w, accepts z path = true → Rout z path w →
      S z.1 (Fin.last n) (A.pathTranscript path))
    (Q : ℕ)
    (queryBound : ∀ phase ∈ support (randomOracleLoggedRun adversary.withQueryLog ∅),
      (freshKeysOfLog phase.1.2).card ≤ Q) :
    Pr{let joint ← (randomOracleLoggedRun
      (singleSaltAcceptedExecution A.rounds guards accepts adversary) ∅)}[
      match joint.1.1.1 with
      | none => False
      | some (z, path, w) => z.1 ∉ L ∧ Rout z path w] ≤
    Q * Finset.univ.sup (A.roundErrors err) + ∑ t, A.roundErrors err t := by
  have h := singleSalt_knowledge_soundness_queryBound guards accepts (A.roundErrors err) adversary
    (fun z => kst (S z.1 _ (tr0 pSpec))) (fun z => A.headExt (S z.1)) {z | z.1 ∉ L}
    (fun z _ => A.headExt_preserving _ (hnext z.1))
    (fun z hz => A.headExt_bounded _ err (hlaw z.1 hz))
    (fun z _ => S z.1 _ (tr0 pSpec)) Rout
    (fun z path _ => (A.headExt_terminalState (S z.1) path).symm ▸ ())
    (fun _ _ => Iff.rfl)
    (fun z path w hacc hR => (KnowledgeState.holds_cast
      (A.headExt_terminalState (S z.1) path) ()).mpr (outputLaw z path w hacc hR))
    Q queryBound
  refine le_trans (prEvent_mono _ _ _ ?_) h
  rintro ⟨⟨⟨_ | ⟨z, path, w⟩, _⟩, _⟩, _⟩ hbad
  · exact hbad.elim
  · exact ⟨hbad.1, hbad.2, fun h0 => hbad.1 (hzero z.1 h0)⟩

/-- Same bound with the error sums re-indexed by legacy challenges. -/
theorem singleSalt_soundness_of_stateFamily'
    (L : Set StmtIn) (S : StmtIn → (m : Fin (n + 1)) → Transcript m pSpec → Prop)
    (hzero : ∀ stmt, S stmt _ (tr0 pSpec) → stmt ∈ L)
    (hnext : ∀ stmt, NextLaw (S stmt))
    (err : pSpec.ChallengeIdx → ℝ≥0∞)
    (hlaw : ∀ stmt ∉ L, ChallengeLaw (S stmt) err)
    (guards : GuardSchedule (StmtIn × Salt) PUnit A.rounds)
    (accepts : (StmtIn × Salt) → (protocol A.rounds).tree.ExecutionPath → Bool)
    (adversary : SingleSaltAdversary StmtIn Salt W A.rounds)
    (Rout : (StmtIn × Salt) → (protocol A.rounds).tree.ExecutionPath → W → Prop)
    (outputLaw : ∀ z path w, accepts z path = true → Rout z path w →
      S z.1 (Fin.last n) (A.pathTranscript path))
    (Q : ℕ)
    (queryBound : ∀ phase ∈ support (randomOracleLoggedRun adversary.withQueryLog ∅),
      (freshKeysOfLog phase.1.2).card ≤ Q) :
    Pr{let joint ← (randomOracleLoggedRun
      (singleSaltAcceptedExecution A.rounds guards accepts adversary) ∅)}[
      match joint.1.1.1 with
      | none => False
      | some (z, path, w) => z.1 ∉ L ∧ Rout z path w] ≤
    Q * Finset.univ.sup err + ∑ j, err j := by
  rw [← A.sup_roundErrors, ← A.sum_roundErrors]
  exact A.singleSalt_soundness_of_stateFamily L S hzero hnext err hlaw guards accepts adversary
    Rout outputLaw Q queryBound

section Rbr

variable {ι : Type} {oSpec : OracleSpec ι} {StmtOut : Type}
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- Legacy terminal acceptance on a native path: positive probability, in the legacy fresh-`init`
experiment, that the legacy verifier run on the decoded full transcript outputs a statement in
`langOut` (the premise of `StateFunction.toFun_full`). -/
def legacyAccepts (verifier : Verifier oSpec StmtIn StmtOut pSpec) (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (langOut : Set StmtOut)
    (stmt : StmtIn) (path : (protocol A.rounds).tree.ExecutionPath) : Prop :=
  Pr{let stmtOut ← (OptionT.mk do
    (simulateQ impl (verifier.run stmt (A.pathTranscript path))).run' (← init))}[
      stmtOut ∈ langOut] > 0

/-- **from `rbrSoundness`.** Legacy round-by-round soundness of any verifier on an alternating
verifier-first spec gives native single-salt FS soundness of its embedding: for every guard
schedule and terminal check, every adversary with at most `Q` distinct fresh keys outputs an
accepted proof of a statement outside `langIn` on which the legacy verifier accepts (output in
`langOut` with positive probability) w.p. at most `Q · max_j ε_j + Σ_j ε_j`. -/
theorem singleSalt_soundness_of_rbrSoundness
    {langIn : Set StmtIn} {langOut : Set StmtOut} {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {err : pSpec.ChallengeIdx → ℝ≥0}
    (hrbr : verifier.rbrSoundness init impl langIn langOut err)
    (guards : GuardSchedule (StmtIn × Salt) PUnit A.rounds)
    (accepts : (StmtIn × Salt) → (protocol A.rounds).tree.ExecutionPath → Bool)
    (adversary : SingleSaltAdversary StmtIn Salt W A.rounds)
    (Q : ℕ)
    (queryBound : ∀ phase ∈ support (randomOracleLoggedRun adversary.withQueryLog ∅),
      (freshKeysOfLog phase.1.2).card ≤ Q) :
    Pr{let joint ← (randomOracleLoggedRun
      (singleSaltAcceptedExecution A.rounds guards accepts adversary) ∅)}[
      match joint.1.1.1 with
      | none => False
      | some (z, path, _) => z.1 ∉ langIn ∧ A.legacyAccepts verifier init impl langOut z.1 path] ≤
    Q * Finset.univ.sup (fun j => (err j : ℝ≥0∞)) + ∑ j, (err j : ℝ≥0∞) := by
  obtain ⟨sf, hsf⟩ := hrbr
  refine A.singleSalt_soundness_of_stateFamily' langIn (fun stmt m tr => sf.toFun m stmt tr)
    ?_ ?_ _ ?_ guards accepts adversary _ ?_ Q queryBound
  · intro stmt h0
    apply sf.toFun_empty stmt
    have hidx : (⟨0, Nat.succ_pos n⟩ : Fin (n + 1)) = 0 := Fin.ext (by simp)
    have key : ∀ (m : Fin (n + 1)) (hm : m = 0) (tr : Transcript m pSpec),
        sf.toFun m stmt tr → sf.toFun 0 stmt default := by
      rintro m rfl tr h
      rwa [Subsingleton.elim tr default] at h
    exact key _ hidx _ h0
  · intro stmt m hm tr msg hafter
    by_contra hbefore
    exact sf.toFun_next m hm stmt tr hbefore msg hafter
  · intro stmt hstmt j tr
    exact hsf stmt hstmt j tr
  · intro z path _ _ hacc
    by_contra hS
    have h0 := sf.toFun_full z.1 (A.pathTranscript path) hS
    exact (ne_of_gt hacc) h0

end Rbr

end NockvmE2E.Lift.Alternating
