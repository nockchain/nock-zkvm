/-
general-`n` embedding of an
alternating, verifier-first legacy protocol spec into Quang Dao's fixed-round format
`StateRestoration.protocol rounds`.

A legacy spec `pSpec : ProtocolSpec n` with `n = 2r+1` and directions `V,P,V,P,…,V` (challenge at
every even position, prover message at every odd position) becomes the `r+1` native rounds
`(Unit, c₀), (m₀, c₁), …, (m_{r-1}, c_r)` (the "shift": a `Unit` first message). A native message
type may refine the legacy one through an embedding `emb` (FRI needs this for the final
polynomial, which is not `Finite`).

The legacy transcript is carried as an accumulator through the recursion on the round list, so
every `Transcript.concat` happens at a literal index `⟨2i+1⟩`/`⟨2i+2⟩`: no `Fin.append`,
`Fin.vsum` or `dcast` is ever unfolded. The only index cast is at the terminal node
(`⟨2r+1⟩ = Fin.last n`), handled once by `subst` in `stateAt_last_iff`.

Everything is generic in a state predicate `S : (m : Fin (n+1)) → Transcript m pSpec → Prop`
(a legacy state function at a fixed statement). With `Witness := Unit` the native round extractor
is "state `S` at the decoded legacy prefix" (`headExt`); `Lift/OfRbr.lean` proves its laws.
-/
import ArkLib.OracleReduction.Security.RoundByRound
import ArkLib.Interaction.Oracle.Security.StateRestorationBudget

open OracleComp OracleSpec ProtocolSpec
open Interaction.Oracle Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open scoped ENNReal

namespace NockvmE2E.Lift

/-- Shape data of an alternating verifier-first legacy spec: `n = 2r+1`, challenges at even and
prover messages at odd positions, and a (possibly refined) native type for each prover message. -/
structure Alternating {n : ℕ} (pSpec : ProtocolSpec n) where
  /-- Number of prover messages; the native protocol has `r + 1` rounds. -/
  r : ℕ
  hn : n = 2 * r + 1
  dirV : ∀ i (h : 2 * i < n), pSpec.dir ⟨2 * i, h⟩ = .V_to_P
  dirP : ∀ i (h : 2 * i + 1 < n), pSpec.dir ⟨2 * i + 1, h⟩ = .P_to_V
  /-- The native type of the `i`-th prover message (legacy position `2i+1`). -/
  Msg : (i : ℕ) → 2 * i + 1 < n → Type
  /-- How a native message is read as the legacy message. -/
  emb : ∀ i h, Msg i h → pSpec.«Type» ⟨2 * i + 1, h⟩
  decEqMsg : ∀ i h, DecidableEq (Msg i h)
  finiteMsg : ∀ i h, Finite (Msg i h)
  finiteChal : ∀ j : pSpec.ChallengeIdx, Finite (pSpec.Challenge j)
  nonemptyChal : ∀ j : pSpec.ChallengeIdx, Nonempty (pSpec.Challenge j)

/-- The empty legacy transcript. -/
abbrev tr0 {n : ℕ} (pSpec : ProtocolSpec n) : Transcript ⟨0, Nat.succ_pos n⟩ pSpec :=
  fun j => Fin.elim0 j

set_option linter.unusedSectionVars false

namespace Alternating

variable {n : ℕ} {pSpec : ProtocolSpec n} (A : Alternating pSpec)

/-- The legacy challenge index at position `2i`. -/
def chIdx (i : ℕ) (h : 2 * i < n) : pSpec.ChallengeIdx := ⟨⟨2 * i, h⟩, A.dirV i h⟩

theorem lt_of_le_r {i : ℕ} (h : i ≤ A.r) : 2 * i < n := by have := A.hn; omega
theorem lt_of_lt_r {i : ℕ} (h : i < A.r) : 2 * i + 1 < n := by have := A.hn; omega
theorem pos_lt {i : ℕ} (h : i ≤ A.r) : 2 * i + 1 < n + 1 := by have := A.hn; omega

/-- The legacy challenge index of native round `t`, as a `Fin`-valued position. -/
theorem chIdx_val (i : ℕ) (h : 2 * i < n) : (A.chIdx i h).1.val = 2 * i := rfl

/-- Every legacy challenge sits at an even position `2t` with `t ≤ r`. -/
theorem challenge_even (j : pSpec.ChallengeIdx) : ∃ t, ∃ ht : t ≤ A.r, j = A.chIdx t (A.lt_of_le_r ht) := by
  rcases j with ⟨⟨v, hv⟩, hdir⟩
  rcases Nat.even_or_odd v with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · refine ⟨t, by have := A.hn; omega, ?_⟩
    apply Subtype.ext; apply Fin.ext; simp [chIdx]; omega
  · exfalso
    have h := A.dirP t (by omega)
    rw [show (⟨2 * t + 1, hv⟩ : Fin n) = ⟨2 * t + 1, by omega⟩ from rfl] at hdir
    rw [hdir] at h
    exact Direction.noConfusion h

variable [hsamp : ∀ j, SampleableType (pSpec.Challenge j)]

/-- Native round 0: the inserted `Unit` message, then the legacy challenge at position 0. -/
def headRound : Round where
  Message := Unit
  Challenge := pSpec.Challenge (A.chIdx 0 (A.lt_of_le_r (Nat.zero_le _)))
  interface := OracleInterface.instDefault
  decEqMessage := inferInstance
  finiteMessage := inferInstance
  finiteChallenge := A.finiteChal _
  nonemptyChallenge := A.nonemptyChal _
  sampleChallenge := hsamp _

/-- Native round `i+1` (`i < r`): legacy message `2i+1` (refined), then legacy challenge `2i+2`. -/
def midRound (i : ℕ) (h : i < A.r) : Round where
  Message := A.Msg i (A.lt_of_lt_r h)
  Challenge := pSpec.Challenge (A.chIdx (i + 1) (A.lt_of_le_r h))
  interface := OracleInterface.instDefault
  decEqMessage := A.decEqMsg _ _
  finiteMessage := A.finiteMsg _ _
  finiteChallenge := A.finiteChal _
  nonemptyChallenge := A.nonemptyChal _
  sampleChallenge := hsamp _

/-- The native rounds `i+1, …, r` (fuel `c = r - i`). -/
def tailRounds : (i c : ℕ) → i + c = A.r → List Round
  | _, 0, _ => []
  | i, c + 1, h => A.midRound i (by omega) :: tailRounds i.succ c (by omega)

/-- The native round list consumed by `singleSalt_knowledge_soundness`. -/
def rounds : List Round := A.headRound :: A.tailRounds 0 A.r (Nat.zero_add _)

theorem tailRounds_length : (i c : ℕ) → (h : i + c = A.r) → (A.tailRounds i c h).length = c
  | _, 0, _ => rfl
  | i, c + 1, h => by
      simp only [tailRounds, List.length_cons]
      rw [tailRounds_length i.succ c]

theorem rounds_length : A.rounds.length = A.r + 1 := by
  simp only [rounds, List.length_cons, tailRounds_length]

/-! ## The legacy transcript along a native path -/

/-- The legacy transcript before native round `i+1`'s message: positions `0 … 2i`. -/
abbrev PosTr (i : ℕ) (h : i ≤ A.r) := Transcript ⟨2 * i + 1, A.pos_lt h⟩ pSpec


/-- Append native message `msg` (round `i+1`) and challenge `ch` to a legacy prefix. -/
abbrev step (i : ℕ) (h : i < A.r) (tr : A.PosTr i h.le) (msg : A.Msg i (A.lt_of_lt_r h))
    (ch : pSpec.Challenge (A.chIdx (i + 1) (A.lt_of_le_r h))) : A.PosTr (i + 1) h :=
  Transcript.concat (m := ⟨2 * i + 2, by have := A.hn; omega⟩) ch
    (Transcript.concat (m := ⟨2 * i + 1, A.lt_of_lt_r h⟩) (A.emb i _ msg) tr)

/-- Read a legacy transcript at position `2r+1 = n` as a full transcript (no cast: the entries are
re-indexed by value). -/
def toFull {m : Fin (n + 1)} (hm : m.val = n) (tr : Transcript m pSpec) : FullTranscript pSpec :=
  fun j => tr ⟨j.val, by omega⟩

/-- The legacy full transcript of a native path through the rounds `i+1, …, r`. -/
def tailPath : (i c : ℕ) → (h : i + c = A.r) → A.PosTr i (by omega) →
    (protocol (A.tailRounds i c h)).tree.ExecutionPath → FullTranscript pSpec
  | i, 0, h, tr, _ => toFull (m := ⟨2 * i + 1, A.pos_lt (by omega)⟩) (by have := A.hn; simp; omega) tr
  | i, c + 1, h, tr, path =>
      tailPath i.succ c (by omega) (A.step i (by omega) tr path.1 path.2.1) path.2.2

/-- **The path ↦ transcript decoder.** The legacy full transcript of a native execution path. -/
def pathTranscript (path : (protocol A.rounds).tree.ExecutionPath) : FullTranscript pSpec :=
  A.tailPath 0 A.r (Nat.zero_add _)
    (Transcript.concat (m := ⟨0, A.lt_of_le_r (Nat.zero_le _)⟩) path.2.1 (tr0 pSpec)) path.2.2

/-! ## The `Unit`-witness round extractor of a state predicate -/

/-- The knowledge state "`P` holds", with `Unit` witnesses. -/
abbrev kst (P : Prop) : KnowledgeState.{0} := ⟨Unit, fun _ => P⟩

variable (S : (m : Fin (n + 1)) → Transcript m pSpec → Prop)

/-- Round extractor of the rounds `i+1, …, r` from the legacy prefix `tr`: the state at every
native prefix is `S` at the decoded legacy prefix; witness maps are trivial. -/
def tailExt : (i c : ℕ) → (h : i + c = A.r) → (tr : A.PosTr i (by omega)) →
    RoundExtractor (protocol (A.tailRounds i c h)).tree (kst (S _ tr))
  | _, 0, _, _ => PUnit.unit
  | i, c + 1, h, tr => fun msg =>
      ⟨kst (S _ (Transcript.concat (m := ⟨2 * i + 1, A.lt_of_lt_r (by omega)⟩) (A.emb i _ msg) tr)),
        fun _ => (), fun ch =>
          ⟨kst (S _ (A.step i (by omega) tr msg ch)), fun _ => (),
            tailExt i.succ c (by omega) (A.step i (by omega) tr msg ch)⟩⟩

/-- **The native round extractor** of the whole protocol, from the empty legacy prefix. -/
def headExt : RoundExtractor (protocol A.rounds).tree (kst (S _ (tr0 pSpec))) :=
  fun _ => ⟨kst (S _ (tr0 pSpec)), id, fun ch =>
    ⟨kst (S _ (Transcript.concat (m := ⟨0, A.lt_of_le_r (Nat.zero_le _)⟩) ch (tr0 pSpec))), fun _ => (),
      A.tailExt S 0 A.r (Nat.zero_add _)
        (Transcript.concat (m := ⟨0, A.lt_of_le_r (Nat.zero_le _)⟩) ch (tr0 pSpec))⟩⟩

/-- `S` at position `⟨n⟩` is `S` at `Fin.last n` of the re-indexed transcript. -/
theorem stateAt_last_iff {m : Fin (n + 1)} (hm : m.val = n) (tr : Transcript m pSpec) :
    S m tr ↔ S (Fin.last n) (toFull hm tr) := by
  obtain rfl : m = Fin.last n := Fin.ext hm
  rfl

theorem tailExt_terminalState : (i c : ℕ) → (h : i + c = A.r) → (tr : A.PosTr i (by omega)) →
    (path : (protocol (A.tailRounds i c h)).tree.ExecutionPath) →
    (A.tailExt S i c h tr).terminalState path = kst (S (Fin.last n) (A.tailPath i c h tr path))
  | i, 0, h, tr, _ => congrArg kst (propext (stateAt_last_iff S _ tr))
  | i, c + 1, h, tr, path =>
      tailExt_terminalState i.succ c (by omega) (A.step i (by omega) tr path.1 path.2.1) path.2.2

/-- The terminal knowledge state of a native path is `S` at its decoded legacy full transcript. -/
theorem headExt_terminalState (path : (protocol A.rounds).tree.ExecutionPath) :
    (A.headExt S).terminalState path = kst (S (Fin.last n) (A.pathTranscript path)) :=
  A.tailExt_terminalState S 0 A.r _ _ path.2.2

/-! ## Prover preservation -/

/-- The legacy prover-message law (contrapositive of `StateFunction.toFun_next`). -/
def NextLaw : Prop :=
  ∀ (m : Fin n), pSpec.dir m = .P_to_V → ∀ (tr : Transcript m.castSucc pSpec) (msg : pSpec.«Type» m),
    S m.succ (tr.concat msg) → S m.castSucc tr

theorem tailExt_preserving (hnext : NextLaw S) : (i c : ℕ) → (h : i + c = A.r) →
    (tr : A.PosTr i (by omega)) →
    (A.tailExt S i c h tr).IsProverPreserving (protocol (A.tailRounds i c h)).roles
  | _, 0, _, _ => trivial
  | i, c + 1, h, tr => by
      refine ⟨fun msg _ hafter => hnext _ (A.dirP i _) tr (A.emb i _ msg) hafter, fun msg => ?_⟩
      exact ⟨fun _ hrole => (nomatch hrole), fun ch =>
        tailExt_preserving hnext i.succ c (by omega) (A.step i (by omega) tr msg ch)⟩

/-- `IsProverPreserving` of the native extractor, from the legacy prover-message law. -/
theorem headExt_preserving (hnext : NextLaw S) :
    (A.headExt S).IsProverPreserving (protocol A.rounds).roles :=
  ⟨fun _ _ h => h, fun _ => ⟨fun _ hrole => (nomatch hrole), fun ch =>
    A.tailExt_preserving S hnext 0 A.r _ _⟩⟩

/-! ## Local bounds against `roundErrorSchedule` -/

/-- The legacy per-challenge law: at every challenge and every prefix, a fresh challenge turns
`S` from false to true with probability at most `err`. (The body of `rbrSoundness`.) -/
def ChallengeLaw (err : pSpec.ChallengeIdx → ℝ≥0∞) : Prop :=
  ∀ (j : pSpec.ChallengeIdx) (tr : Transcript j.1.castSucc pSpec),
    Pr{let c ← $ᵗ (pSpec.Challenge j)}[¬ S j.1.castSucc tr ∧ S j.1.succ (tr.concat c)] ≤ err j

theorem tailExt_bounded (err : pSpec.ChallengeIdx → ℝ≥0∞) (hlaw : ChallengeLaw S err) :
    (i c : ℕ) → (h : i + c = A.r) → (tr : A.PosTr i (by omega)) →
    (errs : RoundErrors (A.tailRounds i c h)) →
    (∀ (t : Fin (A.tailRounds i c h).length) (j : pSpec.ChallengeIdx),
      j.1.val = 2 * (i + 1 + t.val) → err j ≤ errs t) →
    RoundExtractor.IsLocallyBounded (A.tailExt S i c h tr) (protocol (A.tailRounds i c h)).roles
      (roundErrorSchedule (A.tailRounds i c h) errs)
  | _, 0, _, _, _, _ => trivial
  | i, c + 1, h, tr, errs, herrs => fun msg => by
      refine ⟨?_, fun ch => ?_⟩
      · rw [_root_.RoundByRound.GameFamily.isBounded_iff]
        intro _ _
        refine le_trans ?_ (herrs ⟨0, Nat.succ_pos _⟩ (A.chIdx (i + 1) (A.lt_of_le_r (by omega))) rfl)
        refine le_trans (prEvent_mono _ _ _ ?_)
          (hlaw (A.chIdx (i + 1) (A.lt_of_le_r (by omega)))
            (Transcript.concat (m := ⟨2 * i + 1, A.lt_of_lt_r (by omega)⟩) (A.emb i _ msg) tr))
        rintro c ⟨_, hbefore, hafter⟩
        exact ⟨hbefore, hafter⟩
      · exact tailExt_bounded err hlaw i.succ c (by omega) _ _ (fun t j hj =>
          herrs t.succ j (by rw [hj, Fin.val_succ]; simp only [Nat.succ_eq_add_one]; omega))

/-- The native error vector: round `t` carries the legacy error of challenge `2t`. -/
noncomputable def roundErrors (err : pSpec.ChallengeIdx → ℝ≥0∞) : RoundErrors A.rounds :=
  fun t => err (A.chIdx t.val (A.lt_of_le_r (by have := A.rounds_length; omega)))

/-- `IsLocallyBounded` of the native extractor against `roundErrorSchedule`, from the legacy
per-challenge law. -/
theorem headExt_bounded (err : pSpec.ChallengeIdx → ℝ≥0∞) (hlaw : ChallengeLaw S err) :
    RoundExtractor.IsLocallyBounded (A.headExt S) (protocol A.rounds).roles
      (roundErrorSchedule A.rounds (A.roundErrors err)) := fun _ => by
  refine ⟨?_, fun ch => ?_⟩
  · rw [_root_.RoundByRound.GameFamily.isBounded_iff]
    intro _ _
    refine le_trans (prEvent_mono _ _ _ ?_)
      (hlaw (A.chIdx 0 (A.lt_of_le_r (Nat.zero_le _))) (tr0 pSpec))
    rintro c ⟨_, hbefore, hafter⟩
    exact ⟨hbefore, hafter⟩
  · refine A.tailExt_bounded S err hlaw 0 A.r _ _ _ (fun t j hj => ?_)
    have hj' : j = A.chIdx (t.val + 1) (A.lt_of_le_r (by
        have := A.tailRounds_length 0 A.r (Nat.zero_add _); omega)) := by
      apply Subtype.ext; apply Fin.ext; simp only [chIdx_val]; omega
    rw [hj']
    exact le_rfl

end Alternating

end NockvmE2E.Lift
