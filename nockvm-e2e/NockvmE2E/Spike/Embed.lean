/-
SPIKE-LIFT, part 1: embedding data.

A legacy one-challenge protocol `⟨!v[.V_to_P], !v[C]⟩` (the shape of `RandomQuery`,
`RandomEvaluation`, `SendChallenge`) is presented in Quang Dao's fixed-round format
`StateRestoration.protocol rounds` as ONE round whose prover message is `Unit`
(the "shift": legacy `V,P,V,…` becomes `(unit, α₀), (f₁, α₁), …`).

Everything below is general in the legacy statement/witness types, the verifier, the extractor and
the knowledge state function; it is specialised only in the protocol shape (one challenge, `n = 1`).
-/
import ArkLib.OracleReduction.Security.RoundByRound
import ArkLib.Interaction.Oracle.Security.StateRestorationBudget
import ArkLib.Interaction.Oracle.Execution

open OracleComp OracleSpec ProtocolSpec
open Interaction.Oracle Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration

namespace NockvmE2E.Spike

/-! ## Legacy side: the one-challenge protocol spec and its transcripts -/

/-- The legacy protocol spec with a single verifier challenge of type `C`.
`RandomQuery.pSpec C` is this, by `rfl`. -/
abbrev oneChallenge (C : Type) : ProtocolSpec 1 := ⟨!v[.V_to_P], !v[C]⟩

/-- Its unique challenge index. -/
abbrev i0 (C : Type) : (oneChallenge C).ChallengeIdx := ⟨0, rfl⟩

/-- The empty legacy transcript, at the index the legacy RBR definitions use before the challenge. -/
abbrev emptyTr (C : Type) : Transcript (i0 C).1.castSucc (oneChallenge C) := fun j => Fin.elim0 j

/-- The legacy transcript after the challenge, exactly as `rbrKnowledgeSoundness` builds it. -/
abbrev challengeTr {C : Type} (c : C) : Transcript (i0 C).1.succ (oneChallenge C) :=
  (emptyTr C).concat c

/-- The same transcript, read as a full transcript (`Fin.last 1` and `(0 : Fin 1).succ` agree
definitionally, so no cast is needed). -/
abbrev challengeFull {C : Type} (c : C) : FullTranscript (oneChallenge C) := challengeTr c

/-! ## Native side: Quang Dao's fixed-round presentation -/

variable (C : Type) [Fintype C] [Nonempty C] [SampleableType C]

/-- The one native round: a trivial (`Unit`) prover oracle message, then the legacy challenge. -/
def round : Round where
  Message := Unit
  Challenge := C
  interface := OracleInterface.instDefault
  decEqMessage := inferInstance
  finiteMessage := inferInstance
  finiteChallenge := inferInstance
  nonemptyChallenge := inferInstance
  sampleChallenge := inferInstance

/-- The fixed-round list consumed by `singleSalt_knowledge_soundness`. -/
abbrev rounds : List Round := [round C]

/-- The native tree is literally: oracle message `Unit`, then a verifier-owned public `C` move. -/
example : (protocol (rounds C)).tree =
    .oracle Unit (fun _ => .public C (fun _ => .done)) := rfl

example : (protocol (rounds C)).roles.2 PUnit.unit = ⟨.receiver, fun _ => ⟨⟩⟩ := rfl

variable {C}

/-- The verifier challenge recorded on a native execution path. -/
def pathChallenge (path : (protocol (rounds C)).tree.ExecutionPath) : C := path.2.1

/-- Native execution path ↦ legacy full transcript. -/
abbrev pathTranscript (path : (protocol (rounds C)).tree.ExecutionPath) :
    FullTranscript (oneChallenge C) :=
  challengeFull (pathChallenge path)

/-- Legacy full transcript ↦ native execution path. -/
def transcriptPath (tr : FullTranscript (oneChallenge C)) :
    (protocol (rounds C)).tree.ExecutionPath :=
  ⟨(), tr 0, PUnit.unit⟩

/-- The path ↔ transcript correspondence is a bijection (one round: the `Unit` message and the
terminal `PUnit` carry no information). -/
def pathEquiv : (protocol (rounds C)).tree.ExecutionPath ≃ FullTranscript (oneChallenge C) where
  toFun := pathTranscript
  invFun := transcriptPath
  left_inv path := by
    rcases path with ⟨⟨⟩, c, ⟨⟩⟩
    rfl
  right_inv tr := by
    funext j
    fin_cases j
    exact Transcript.concat_zero (pSpec := oneChallenge C) (tr 0) _

/-! ## Embedded strategies -/

section Strategies

variable {C : Type} [Fintype C] [Nonempty C] [SampleableType C]
  {ιa : Type} (ambient : OracleSpec ιa)

/-- The embedded verifier: passive at the (`Unit`) prover message, samples its challenge with
`challenge` at the receiver node (the legacy `$ᵗ`, interpreted by the handler), and runs `leaf`
(the legacy `verify` on the reconstructed transcript) at the leaf. -/
def embeddedVerifier {Out : Type} (challenge : OracleComp ambient C)
    (leaf : C → OracleComp ambient Out) (initial : PFunctor) :
    Interaction.Oracle.Verifier.Strategy ambient (protocol (rounds C)).tree
      (protocol (rounds C)).roles (protocol (rounds C)).oracles initial (fun _ => Out) :=
  pure (do
    let c ← OracleComp.liftComp challenge
      (ambient + OracleSpec.ofPFunctor (Access.extend initial (round C).interface))
    return ⟨c, OracleComp.liftComp (leaf c) _⟩)


/-- The embedded legacy prover (one challenge): send the `Unit` message, then on challenge `c`
run the legacy `receiveChallenge` from `input (stmt, wit)` and the legacy `output`. Its ambient
oracle is the legacy `oSpec`. -/
def embeddedProver {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type}
    (P : Prover oSpec StmtIn WitIn StmtOut WitOut (oneChallenge C)) (stmt : StmtIn) (wit : WitIn) :
    Interaction.Oracle.Prover.Strategy oSpec (protocol (rounds C)).tree
      (protocol (rounds C)).roles (fun _ => StmtOut × WitOut) :=
  pure ⟨(), fun c => do
    let f ← P.receiveChallenge (i0 C) (P.input (stmt, wit))
    P.output (f c)⟩

end Strategies

end NockvmE2E.Spike
