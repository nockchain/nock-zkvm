/-
SPIKE-LIFT, MAIN GOAL: knowledge-certificate transport legacy → native, bolted into Quang Dao's
single-salt Fiat–Shamir theorem `Interaction.Oracle.FiatShamir.singleSalt_knowledge_soundness`, `ArkLib/Interaction/Oracle/FiatShamir/SingleSaltSecurity.lean:218`).

From a legacy `KnowledgeStateFunction` + `Extractor.RoundByRound` + `rbrKnowledgeSoundnessWith`
bound on the one-challenge spec `oneChallenge C`, we build exactly the inputs of that theorem over
`(protocol (rounds C)).tree`: per-input `KnowledgeState`, `RoundExtractor`, `IsProverPreserving`,
`IsLocallyBounded` against `roundErrorSchedule`, input and output laws. No ambient-oracle
restriction is needed here: the legacy terminal law is consumed only as an implication.
-/
import NockvmE2E.Spike.Embed
import ArkLibFs.Interaction.Oracle.FiatShamir.SingleSaltSecurity
import ArkLib.ProofSystem.Component.RandomEvaluation

open OracleComp OracleSpec ProtocolSpec
open Interaction.Oracle Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir
open scoped NNReal ENNReal

namespace NockvmE2E.Spike

section Transport

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type}
  {C : Type} [Fintype C] [Nonempty C] [SampleableType C]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
  {verifier : Verifier oSpec StmtIn StmtOut (oneChallenge C)}
  {WitMid : Fin 2 → Type}
  {E : Extractor.RoundByRound oSpec StmtIn WitIn WitOut (oneChallenge C) WitMid}

/-- Native knowledge state before the challenge: the legacy state at the empty transcript. -/
def inputState (K : verifier.KnowledgeStateFunction init impl relIn relOut E) (stmt : StmtIn) :
    KnowledgeState where
  Witness := WitMid (i0 C).1.castSucc
  holds := K.toFun _ stmt (emptyTr C)

/-- Native knowledge state after the challenge `c`: the legacy state at `[c]`. -/
def challengeState (K : verifier.KnowledgeStateFunction init impl relIn relOut E)
    (stmt : StmtIn) (c : C) : KnowledgeState where
  Witness := WitMid (i0 C).1.succ
  holds := K.toFun _ stmt (challengeTr c)

/-- The transported round extractor. The (`Unit`) prover message keeps the state and maps
witnesses by `id`; the challenge uses the legacy `extractMid`. -/
def extractorOf (K : verifier.KnowledgeStateFunction init impl relIn relOut E) (stmt : StmtIn) :
    RoundExtractor (protocol (rounds C)).tree (inputState K stmt) :=
  fun _ => ⟨inputState K stmt, id, fun c =>
    ⟨challengeState K stmt c, E.extractMid (i0 C).1 stmt (challengeTr c), PUnit.unit⟩⟩

theorem terminalState_extractorOf
    (K : verifier.KnowledgeStateFunction init impl relIn relOut E) (stmt : StmtIn)
    (path : (protocol (rounds C)).tree.ExecutionPath) :
    (extractorOf K stmt).terminalState path = challengeState K stmt (pathChallenge path) := rfl

/-- Prover preservation is trivial: the only prover move is the inserted `Unit` message. -/
theorem extractorOf_preserving
    (K : verifier.KnowledgeStateFunction init impl relIn relOut E) (stmt : StmtIn) :
    (extractorOf K stmt).IsProverPreserving (protocol (rounds C)).roles :=
  ⟨fun _ _ h => h, fun _ => ⟨fun _ hrole => (nomatch hrole), fun _ => trivial⟩⟩

/-- The legacy per-challenge bound is literally the native local bound at the unique verifier
node, with `$ᵗ C` as the schedule's sampler. -/
theorem extractorOf_bounded
    (K : verifier.KnowledgeStateFunction init impl relIn relOut E)
    (err : (oneChallenge C).ChallengeIdx → ℝ≥0)
    (hK : verifier.rbrKnowledgeSoundnessWith init impl relIn relOut WitMid E K err)
    (stmt : StmtIn) :
    RoundExtractor.IsLocallyBounded (extractorOf K stmt) (protocol (rounds C)).roles
      (roundErrorSchedule (rounds C) (fun _ => (err (i0 C) : ℝ≥0∞))) := by
  intro _
  refine ⟨?_, fun _ => trivial⟩
  rw [_root_.RoundByRound.GameFamily.isBounded_iff]
  intro _ _
  exact hK stmt (i0 C) (emptyTr C)

/-- The terminal seed: the legacy `extractOut` on the path's transcript. -/
def seedOf (K : verifier.KnowledgeStateFunction init impl relIn relOut E) {Salt : Type}
    (z : StmtIn × Salt) (path : (protocol (rounds C)).tree.ExecutionPath) (w : WitOut) :
    ((extractorOf K z.1).terminalState path).Witness :=
  E.extractOut z.1 (pathTranscript path) w

/-- Legacy terminal acceptance on a native path: positive probability, in the legacy fresh-`init`
experiment, that the verifier outputs a statement related to `w` (the premise of
`KnowledgeStateFunction.toFun_full`). -/
def legacyAccepts (verifier : Verifier oSpec StmtIn StmtOut (oneChallenge C))
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (relOut : Set (StmtOut × WitOut)) {Salt : Type}
    (z : StmtIn × Salt) (path : (protocol (rounds C)).tree.ExecutionPath) (w : WitOut) : Prop :=
  Pr{let stmtOut ← (OptionT.mk do
    (simulateQ impl (verifier.run z.1 (pathTranscript path))).run' (← init))}[
      (stmtOut, w) ∈ relOut] > 0

/-- **Transport, general output relation.** Native single-salt FS knowledge soundness of the
embedded legacy one-challenge verifier, for any terminal relation `Rout` that implies the legacy
terminal knowledge state at the extracted output witness. -/
theorem legacy_singleSalt_knowledge_soundness_of_outputLaw
    [DecidableEq StmtIn] {Salt : Type} [DecidableEq Salt]
    (K : verifier.KnowledgeStateFunction init impl relIn relOut E)
    (err : (oneChallenge C).ChallengeIdx → ℝ≥0)
    (hK : verifier.rbrKnowledgeSoundnessWith init impl relIn relOut WitMid E K err)
    (guards : GuardSchedule (StmtIn × Salt) PUnit (rounds C))
    (accepts : (StmtIn × Salt) → (protocol (rounds C)).tree.ExecutionPath → Bool)
    (adversary : SingleSaltAdversary StmtIn Salt WitOut (rounds C))
    (Z : Set (StmtIn × Salt))
    (Rout : (StmtIn × Salt) → (protocol (rounds C)).tree.ExecutionPath → WitOut → Prop)
    (outputLaw : ∀ z path w, accepts z path = true → Rout z path w →
      K.toFun (Fin.last 1) z.1 (pathTranscript path) (E.extractOut z.1 (pathTranscript path) w)) :
    Pr{let joint ← (randomOracleLoggedRun
      (singleSaltAcceptedExecution (rounds C) guards accepts adversary) ∅)}[
      badStoppedRelation (fun z => inputState K z.1) (fun z => extractorOf K z.1)
        (fun z w => K.toFun _ z.1 (emptyTr C) w) Rout (seedOf K) Z joint.1.1.1] ≤
    expectedFreshQueryCharge (singleSaltAcceptedExecution (rounds C) guards accepts adversary)
      (keyError (rounds := rounds C) (fun _ => (err (i0 C) : ℝ≥0∞))) :=
  singleSalt_knowledge_soundness guards accepts (fun _ => (err (i0 C) : ℝ≥0∞)) adversary
    (fun z => inputState K z.1) (fun z => extractorOf K z.1) Z
    (fun z _ => extractorOf_preserving K z.1)
    (fun z _ => extractorOf_bounded K err hK z.1)
    (fun z w => K.toFun _ z.1 (emptyTr C) w) Rout (seedOf K)
    (fun _ _ => Iff.rfl) outputLaw

/-- **Transport, legacy output relation.** The terminal relation is the legacy acceptance
`legacyAccepts` (positive-probability related output); the output law is `toFun_full`. -/
theorem legacy_singleSalt_knowledge_soundness
    [DecidableEq StmtIn] {Salt : Type} [DecidableEq Salt]
    (K : verifier.KnowledgeStateFunction init impl relIn relOut E)
    (err : (oneChallenge C).ChallengeIdx → ℝ≥0)
    (hK : verifier.rbrKnowledgeSoundnessWith init impl relIn relOut WitMid E K err)
    (guards : GuardSchedule (StmtIn × Salt) PUnit (rounds C))
    (accepts : (StmtIn × Salt) → (protocol (rounds C)).tree.ExecutionPath → Bool)
    (adversary : SingleSaltAdversary StmtIn Salt WitOut (rounds C))
    (Z : Set (StmtIn × Salt)) :
    Pr{let joint ← (randomOracleLoggedRun
      (singleSaltAcceptedExecution (rounds C) guards accepts adversary) ∅)}[
      badStoppedRelation (fun z => inputState K z.1) (fun z => extractorOf K z.1)
        (fun z w => K.toFun _ z.1 (emptyTr C) w) (legacyAccepts verifier init impl relOut)
        (seedOf K) Z joint.1.1.1] ≤
    expectedFreshQueryCharge (singleSaltAcceptedExecution (rounds C) guards accepts adversary)
      (keyError (rounds := rounds C) (fun _ => (err (i0 C) : ℝ≥0∞))) :=
  legacy_singleSalt_knowledge_soundness_of_outputLaw K err hK guards accepts adversary Z _
    (fun z path w _ h => K.toFun_full z.1 (pathTranscript path) w h)

/-- **Transport with an adversary query cap** (`singleSalt_knowledge_soundness_queryBound`):
error `Q · ε + ε` for a one-round protocol with legacy per-challenge error `ε`. -/
theorem legacy_singleSalt_knowledge_soundness_queryBound_of_outputLaw
    [DecidableEq StmtIn] {Salt : Type} [DecidableEq Salt]
    (K : verifier.KnowledgeStateFunction init impl relIn relOut E)
    (err : (oneChallenge C).ChallengeIdx → ℝ≥0)
    (hK : verifier.rbrKnowledgeSoundnessWith init impl relIn relOut WitMid E K err)
    (guards : GuardSchedule (StmtIn × Salt) PUnit (rounds C))
    (accepts : (StmtIn × Salt) → (protocol (rounds C)).tree.ExecutionPath → Bool)
    (adversary : SingleSaltAdversary StmtIn Salt WitOut (rounds C))
    (Z : Set (StmtIn × Salt))
    (Rout : (StmtIn × Salt) → (protocol (rounds C)).tree.ExecutionPath → WitOut → Prop)
    (outputLaw : ∀ z path w, accepts z path = true → Rout z path w →
      K.toFun (Fin.last 1) z.1 (pathTranscript path) (E.extractOut z.1 (pathTranscript path) w))
    (Q : ℕ)
    (queryBound : ∀ phase ∈ support (randomOracleLoggedRun adversary.withQueryLog ∅),
      (freshKeysOfLog phase.1.2).card ≤ Q) :
    Pr{let joint ← (randomOracleLoggedRun
      (singleSaltAcceptedExecution (rounds C) guards accepts adversary) ∅)}[
      badStoppedRelation (fun z => inputState K z.1) (fun z => extractorOf K z.1)
        (fun z w => K.toFun _ z.1 (emptyTr C) w) Rout (seedOf K) Z joint.1.1.1] ≤
    Q * (err (i0 C) : ℝ≥0∞) + (err (i0 C) : ℝ≥0∞) := by
  have h := singleSalt_knowledge_soundness_queryBound guards accepts
    (fun _ => (err (i0 C) : ℝ≥0∞)) adversary
    (fun z => inputState K z.1) (fun z => extractorOf K z.1) Z
    (fun z _ => extractorOf_preserving K z.1)
    (fun z _ => extractorOf_bounded K err hK z.1)
    (fun z w => K.toFun _ z.1 (emptyTr C) w) Rout (seedOf K)
    (fun _ _ => Iff.rfl) outputLaw Q queryBound
  have hsup : (Finset.univ.sup fun _ : Fin (rounds C).length => (err (i0 C) : ℝ≥0∞)) =
      (err (i0 C) : ℝ≥0∞) := Finset.sup_const Finset.univ_nonempty _
  simpa [hsup] using h

end Transport

/-! ## Instance: `RandomEvaluation` (Schwartz–Zippel) under single-salt Fiat–Shamir -/

section RandomEvaluation

variable (F : Type) [Field F] [Fintype F] [SampleableType F] (m : ℕ) (Statement : Type) {κ : Type} (OStatement : κ → Type)
  [∀ i, OracleInterface (OStatement i)]
  (P : Statement → (∀ i, OStatement i) → MvPolynomial (Fin m) F)

/-- **Fiat–Shamir knowledge soundness of the embedded legacy `RandomEvaluation`.**
For every single-salt FS adversary with at most `Q` distinct challenge-oracle keys, every guard
schedule and terminal check: the probability that it outputs an accepted proof whose sampled point
`τ` is a zero of `P stmt oracles` (the legacy output relation) while `P stmt oracles ≠ 0` (the
legacy input relation fails for the extracted witness) is at most `Q · d/|F| + d/|F|`.
The certificate is the legacy `RandomEvaluation.oracleVerifier_rbrKnowledgeSoundnessWith`,
transported; nothing about the protocol is re-proved natively. -/
theorem randomEvaluation_singleSalt_knowledge_soundness
    [DecidableEq (Statement × ∀ i, OStatement i)] {Salt : Type} [DecidableEq Salt]
    (d : ℕ) (hP : ∀ stmt oracles, (P stmt oracles).totalDegree ≤ d)
    (guards : GuardSchedule ((Statement × ∀ i, OStatement i) × Salt) PUnit (rounds (Fin m → F)))
    (accepts : ((Statement × ∀ i, OStatement i) × Salt) →
      (protocol (rounds (Fin m → F))).tree.ExecutionPath → Bool)
    (adversary : SingleSaltAdversary (Statement × ∀ i, OStatement i) Salt Unit
      (rounds (Fin m → F)))
    (Q : ℕ)
    (queryBound : ∀ phase ∈ support (randomOracleLoggedRun adversary.withQueryLog ∅),
      (freshKeysOfLog phase.1.2).card ≤ Q) :
    Pr{let joint ← (randomOracleLoggedRun
      (singleSaltAcceptedExecution (rounds (Fin m → F)) guards accepts adversary) ∅)}[
      match joint.1.1.1 with
      | none => False
      | some (z, path, _) =>
          MvPolynomial.eval (pathChallenge path) (P z.1.1 z.1.2) = 0 ∧ P z.1.1 z.1.2 ≠ 0] ≤
    Q * (((d : ℝ≥0) / Fintype.card F : ℝ≥0) : ℝ≥0∞) + (((d : ℝ≥0) / Fintype.card F : ℝ≥0) : ℝ≥0∞) := by
  -- The FS statement does not mention the legacy ambient oracle; instantiate it as `[]ₒ`.
  let K := RandomEvaluation.knowledgeStateFunction []ₒ F m Statement OStatement P
    (init := (pure () : ProbComp Unit)) (impl := fun x => PEmpty.elim x)
  have hK := RandomEvaluation.oracleVerifier_rbrKnowledgeSoundnessWith []ₒ F m Statement
    OStatement P (init := (pure () : ProbComp Unit)) (impl := fun x => PEmpty.elim x) d hP
  have h := legacy_singleSalt_knowledge_soundness_queryBound_of_outputLaw K _ hK guards accepts
    adversary Set.univ
    (fun z path _ => MvPolynomial.eval (pathChallenge path) (P z.1.1 z.1.2) = 0)
    (fun z path _ _ hz => by
      change MvPolynomial.eval (pathChallenge path) (P z.1.1 z.1.2) =
        MvPolynomial.eval (pathChallenge path) (0 : MvPolynomial (Fin m) F)
      rw [map_zero]
      exact hz)
    Q queryBound
  refine le_trans (prEvent_mono _ _ _ ?_) h
  rintro ⟨⟨⟨_ | ⟨z, path, w⟩, _⟩, _⟩, _⟩ hbad
  · exact hbad.elim
  · exact ⟨Set.mem_univ _, hbad.1, hbad.2⟩

end RandomEvaluation

end NockvmE2E.Spike
