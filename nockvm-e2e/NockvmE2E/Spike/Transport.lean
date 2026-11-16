/-
SPIKE-LIFT, part 2: ordinary (plain) soundness transport legacy → native.

From the legacy knowledge certificate of a one-challenge verifier (`KnowledgeStateFunction` +
`rbrKnowledgeSoundnessWith`; an ordinary legacy `StateFunction` enters through
`StateFunction.toKnowledgeStateFunction` with `Unit` witnesses) we build the native
`OrdinaryState`, `ChallengeModel`, `ChallengeSchedule`, `LocalSoundness`, the embedded verifier
strategy and its `FreshVerifier` proof, and conclude native ordinary soundness of the embedded
verifier against every native prover by `executeStrategies_soundness`.
-/
import NockvmE2E.Spike.KnowledgeTransport
import ArkLib.Interaction.Oracle.Security.Soundness

open OracleComp OracleSpec ProtocolSpec
open Interaction.Oracle Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.TypeTree
open scoped NNReal ENNReal

namespace NockvmE2E.Spike

/-! ## Generic prefix data -/

/-- Number of public moves crossed by a cursor spine (the challenge rank, in a tree whose public
nodes are all verifier nodes). Structural recursion on the spine: no casts. -/
def publicDepth : {tree residual : Interaction.Oracle.TypeTree} → PFunctor.FreeM.Cursor.Spine tree residual → ℕ
  | _, _, .root _ => 0
  | _, _, .down (a := Position.public _) _ tail => publicDepth tail + 1
  | _, _, .down (a := Position.oracle _) _ tail => publicDepth tail

section Ordinary

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type}
  {C : Type} [Fintype C] [Nonempty C] [SampleableType C]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
  {verifier : Verifier oSpec StmtIn StmtOut (oneChallenge C)}
  {WitMid : Fin 2 → Type}
  {E : Extractor.RoundByRound oSpec StmtIn WitIn WitOut (oneChallenge C) WitMid}

/-- The native ordinary state: some witness satisfies the transported knowledge state at the
prefix. -/
def ordState (K : verifier.KnowledgeStateFunction init impl relIn relOut E) (stmt : StmtIn)
    (pfx : ExecutionPrefix (protocol (rounds C)).tree) : Prop :=
  ∃ w, (RoundExtractor.knowledgeState (extractorOf K stmt) pfx).holds w

/-- Legacy acceptance of a native path for one statement (some output witness is related with
positive probability in the legacy experiment). -/
def legacyOutput (verifier : Verifier oSpec StmtIn StmtOut (oneChallenge C))
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (relOut : Set (StmtOut × WitOut)) (stmt : StmtIn)
    (path : (protocol (rounds C)).tree.ExecutionPath) : Prop :=
  ∃ w : WitOut, legacyAccepts verifier init impl relOut (stmt, ()) path w

/-- The transported ordinary certificate. Input: `stmt` in the legacy input language. -/
def ordinaryState (K : verifier.KnowledgeStateFunction init impl relIn relOut E) (stmt : StmtIn) :
    OrdinaryState (protocol (rounds C)) (stmt ∈ relIn.language)
      (legacyOutput verifier init impl relOut stmt) where
  state := ordState K stmt
  initial := fun hnot ⟨w, hw⟩ =>
    hnot ((Set.mem_language_iff relIn stmt).2 ⟨_, K.toFun_empty stmt w hw⟩)
  prover := ⟨fun _ h => h, fun _ => ⟨fun h => (nomatch h), fun _ => trivial⟩⟩
  terminal := fun path ⟨w, hw⟩ =>
    ⟨seedOf K (stmt, ()) path w, K.toFun_full stmt (pathTranscript path) w hw⟩

variable (C) in
/-- The fresh-challenge model: every authored prefix samples `$ᵗ C`; the extension is the unique
post-challenge prefix (the prover message is `Unit`, so it is determined by the challenge). -/
def challengeModel : ChallengeModel (protocol (rounds C)) where
  Result := fun _ => C
  sample := fun _ => $ᵗ C
  extend := fun _ c => ExecutionPrefix.prependOracle (Messages := Unit) ()
    (ExecutionPrefix.prependPublic c (.root _))

/-- Challenge rank of a prefix. -/
def rankOf (pfx : ExecutionPrefix (protocol (rounds C)).tree) : ℕ := publicDepth pfx.cursor.spine

theorem challengeSchedule :
    Security.ChallengeSchedule (protocol (rounds C)).tree (protocol (rounds C)).roles rankOf 1 :=
  ⟨fun _ => rfl, fun _ => ⟨⟨Nat.zero_lt_one, fun _ => rfl⟩, fun _ => Nat.le_refl 1⟩⟩

/-- The only verifier prefix is "after the `Unit` message"; there the ordinary state is the
transported input state. This is the one dependent case analysis on cursor spines. -/
theorem ordState_of_isVerifierPrefix
    (K : verifier.KnowledgeStateFunction init impl relIn relOut E) (stmt : StmtIn)
    (pfx : ExecutionPrefix (protocol (rounds C)).tree)
    (hpfx : IsVerifierPrefix (protocol (rounds C)).roles pfx) :
    ordState K stmt pfx ↔ ∃ w, (inputState K stmt).holds w := by
  rcases pfx with ⟨⟨residual, spine⟩, messages⟩
  cases spine with
  | root => exact hpfx.elim
  | down answer tail =>
    cases tail with
    | root => rfl
    | down c tail' =>
      cases tail' with
      | root => exact hpfx.elim

/-- Legacy per-challenge knowledge bound ⇒ native ordinary local soundness. -/
theorem localSoundness
    (K : verifier.KnowledgeStateFunction init impl relIn relOut E)
    (err : (oneChallenge C).ChallengeIdx → ℝ≥0)
    (hK : verifier.rbrKnowledgeSoundnessWith init impl relIn relOut WitMid E K err)
    (stmt : StmtIn) :
    LocalSoundness (challengeModel C) (ordState K stmt) rankOf
      (fun _ => (err (i0 C) : ℝ≥0∞)) := by
  rw [LocalSoundness, _root_.RoundByRound.GameFamily.isBounded_iff]
  rintro ⟨pfx, hpfx⟩ _
  refine le_trans (prEvent_mono _ _ _ ?_) (hK stmt (i0 C) (emptyTr C))
  rintro c ⟨hnot, w, hw⟩
  refine ⟨w, fun h => hnot ((ordState_of_isVerifierPrefix K stmt pfx hpfx).2 ⟨_, h⟩), hw⟩

end Ordinary

/-! ## Freshness of the embedded verifier strategy (`Embed.embeddedVerifier`) -/

section Strategy

variable {C : Type} [Fintype C] [Nonempty C] [SampleableType C]
  {ιa : Type} (ambient : OracleSpec ιa)

set_option backward.isDefEq.respectTransparency false in
/-- The embedded verifier draws fresh challenges with the model's marginals. -/
theorem embeddedVerifier_fresh {m : Type → Type} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
    [LawfulEvalDistSemantics m] [MonadAttach m] [ExactMonadAttach m]
    (handler : QueryImpl ambient m) {Out : Type} (challenge : OracleComp ambient C)
    (hchallenge : ∀ event : C → Prop,
      Pr{let r ← simulateQ handler challenge}[event r] = Pr{let r ← ($ᵗ C)}[event r])
    (leaf : C → OracleComp ambient Out) (initial : PFunctor)
    (implA : QueryImpl (OracleSpec.ofPFunctor initial) Id) :
    FreshVerifier (challengeModel C) ambient handler (protocol (rounds C)).tree
      (protocol (rounds C)).roles (protocol (rounds C)).oracles initial implA (fun _ => Out)
      (embeddedVerifier ambient challenge leaf initial) id := by
  intro message next hnext
  simp only [embeddedVerifier, simulateQ_pure, mem_support_pure_iff] at hnext
  subst next
  refine ⟨rfl, ⟨id, ?_, fun _ => rfl⟩, fun _ _ => trivial⟩
  intro event
  dsimp only [protocol, Protocol.oracleWith_oracles]
  simp only [simulateQ_bind, simulateQ_pure]
  rw [QueryImpl.simulateQ_liftComp_left_eq_of_apply _ (QueryImpl.id' ambient)
    (fun _ => rfl), simulateQ_id']
  simp only [prEvent_norm]
  exact hchallenge event

end Strategy

/-! ## Native ordinary soundness of the embedded legacy verifier -/

section Soundness

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type}
  {C : Type} [Fintype C] [Nonempty C] [SampleableType C]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
  {verifier : Verifier oSpec StmtIn StmtOut (oneChallenge C)}
  {WitMid : Fin 2 → Type}
  {E : Extractor.RoundByRound oSpec StmtIn WitIn WitOut (oneChallenge C) WitMid}

/-- **Plain transport.** For a statement outside the legacy input language, against EVERY native
prover strategy and any lawful handler whose interpreted challenge is uniform, the probability that
the native execution with the embedded verifier ends on a path the legacy verifier accepts is at
most the legacy per-challenge error. -/
theorem legacy_executeStrategies_soundness
    (K : verifier.KnowledgeStateFunction init impl relIn relOut E)
    (err : (oneChallenge C).ChallengeIdx → ℝ≥0)
    (hK : verifier.rbrKnowledgeSoundnessWith init impl relIn relOut WitMid E K err)
    {ιa : Type} (ambient : OracleSpec ιa) {m : Type → Type} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] [MonadAttach m] [ExactMonadAttach m]
    (handler : QueryImpl ambient m) (challenge : OracleComp ambient C)
    (hchallenge : ∀ event : C → Prop,
      Pr{let r ← simulateQ handler challenge}[event r] = Pr{let r ← ($ᵗ C)}[event r])
    {Out : Type} (leaf : C → OracleComp ambient Out)
    (initial : PFunctor) (implA : QueryImpl (OracleSpec.ofPFunctor initial) Id)
    {OutP : (protocol (rounds C)).tree.ExecutionPath → Type}
    (prover : Interaction.Oracle.Prover.Strategy ambient (protocol (rounds C)).tree
      (protocol (rounds C)).roles OutP)
    (stmt : StmtIn) (hstmt : stmt ∉ relIn.language) :
    Pr{let result ← (simulateQ handler (executeStrategies ambient (protocol (rounds C)).tree
      (protocol (rounds C)).roles (protocol (rounds C)).oracles initial implA prover
      (embeddedVerifier ambient challenge leaf initial)))}[
        legacyOutput verifier init impl relOut stmt result.1] ≤ (err (i0 C) : ℝ≥0∞) := by
  have bound := executeStrategies_soundness ambient handler (ordinaryState K stmt)
    (challengeModel C) rankOf (fun _ => (err (i0 C) : ℝ≥0∞)) 1 rfl challengeSchedule
    (fun _ => localSoundness K err hK stmt) initial implA prover
    (embeddedVerifier ambient challenge leaf initial)
    (embeddedVerifier_fresh ambient handler challenge hchallenge leaf initial implA) hstmt
  simpa using bound

end Soundness

end NockvmE2E.Spike
