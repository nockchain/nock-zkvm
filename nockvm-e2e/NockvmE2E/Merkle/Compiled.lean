/-
the Merkle-compiled (BCS) presentation of a
Quang Dao `List Round` protocol. Definitions only; the soundness game hop is proved in
`NockvmE2E.Merkle.Soundness` (`merkle_singleSalt_soundness`).

* `rootRound`     : a word-message round with its message replaced by a digest `Y` (the root).
* `openingRound`  : the final round, message = openings `Op`, challenge `Unit`.
* `compiledRounds`: `[(Y, C₁), …, (Y, C_k), (Op, Unit)]`.
* `pairedRound` / `pairedRounds`: the in-the-clear protocol the reduction targets, message
  `word × root`, so the FS-key translation root-prefix ↦ (word, root)-prefix is injective
  (`translate_injective`).
* `pathRoots`     : the roots and the opening read off a compiled execution path.
* `SuccinctSpec`, `succinctVerify`, `succinctAcceptedExecution`: the succinct verifier
  (QD's public stopped FS verification on the compiled rounds, then a hash-oracle Merkle check,
  then a pure local check) and the joint experiment syntax. The hash oracle is a separate summand
  of the adversary's oracle (domain separation by construction).
-/
import ArkLibFs.Interaction.Oracle.FiatShamir.SingleSaltSecurity
import ToMathlib.Data.IndexedBinaryTree.Basic

open OracleComp OracleSpec
open Interaction.Oracle Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir

namespace NockvmE2E.Merkle

/-! ## Compiled round list -/

section Rounds

variable (Y : Type) [Finite Y] [DecidableEq Y]

/-- A round whose prover message is a digest (Merkle root) instead of the word. -/
def rootRound (r : Round) : Round where
  Message := Y
  Challenge := r.Challenge
  interface := OracleInterface.instDefault
  decEqMessage := inferInstance
  finiteMessage := inferInstance
  finiteChallenge := r.finiteChallenge
  nonemptyChallenge := r.nonemptyChallenge
  sampleChallenge := r.sampleChallenge

/-- The terminal openings round: the prover sends all openings; the challenge is trivial. -/
def openingRound (Op : Type) [Finite Op] [DecidableEq Op] : Round where
  Message := Op
  Challenge := Unit
  interface := OracleInterface.instDefault
  decEqMessage := inferInstance
  finiteMessage := inferInstance
  finiteChallenge := inferInstance
  nonemptyChallenge := inferInstance
  sampleChallenge := inferInstanceAs (SampleableType Unit)

/-- `[(Y, C₁), …, (Y, C_k), (Op, Unit)]`. -/
def compiledRounds (Op : Type) [Finite Op] [DecidableEq Op] : List Round → List Round
  | [] => [openingRound Op]
  | r :: rs => rootRound Y r :: compiledRounds Op rs

theorem compiledRounds_length (Op : Type) [Finite Op] [DecidableEq Op] (rounds : List Round) :
    (compiledRounds Y Op rounds).length = rounds.length + 1 := by
  induction rounds with
  | nil => rfl
  | cons r rs ih => simp [compiledRounds, ih]

/-- The reduction's in-the-clear round: the word together with the root it was extracted from. -/
def pairedRound (r : Round) : Round where
  Message := r.Message × Y
  Challenge := r.Challenge
  interface := OracleInterface.instDefault
  decEqMessage := inferInstance
  finiteMessage := inferInstance
  finiteChallenge := r.finiteChallenge
  nonemptyChallenge := r.nonemptyChallenge
  sampleChallenge := r.sampleChallenge

def pairedRounds (rounds : List Round) : List Round := rounds.map (pairedRound Y)

/-- Root-prefix FS keys ↦ (word, root)-prefix keys, given the word chosen for each root prefix.
`words` is the reduction's memo: for the key's own round it receives the input and the roots so
far (as the compiled key prefix) and returns the extracted word. -/
def translate {Input : Type} (Op : Type) [Finite Op] [DecidableEq Op] :
    (rounds : List Round) →
    (words : (r : Round) → Input → List Y → Y → r.Message) → List Y →
    Key Input PUnit (compiledRounds Y Op rounds) →
    Option (Key Input PUnit (pairedRounds Y rounds))
  | [], _, _, _ => none
  | r :: _, words, pre, .inl (z, root, _) =>
      some (.inl (z, ((words r z pre root, root) : r.Message × Y), PUnit.unit))
  | r :: rs, words, pre, .inr (root, _, key) =>
      (translate Op rs words (pre ++ [show Y from root]) key).map fun k =>
        .inr (((words r key.input pre root, root) : r.Message × Y), PUnit.unit, k)

/-- Forget the words: a paired key back to the compiled (roots-only) key. -/
def untranslate {Input : Type} (Op : Type) [Finite Op] [DecidableEq Op] :
    (rounds : List Round) → Key Input PUnit (pairedRounds Y rounds) →
    Key Input PUnit (compiledRounds Y Op rounds)
  | [], k => nomatch k
  | _ :: _, .inl (z, message, u) => .inl (z, (message.2 : Y), u)
  | _ :: rs, .inr (message, u, k) => .inr ((message.2 : Y), u, untranslate Op rs k)

/-- `untranslate` is a left inverse of `translate` for every memo and prefix. -/
theorem untranslate_translate {Input : Type} (Op : Type) [Finite Op] [DecidableEq Op] :
    (rounds : List Round) → (words : (r : Round) → Input → List Y → Y → r.Message) →
    (pre : List Y) → (k : Key Input PUnit (compiledRounds Y Op rounds)) →
    (x : Key Input PUnit (pairedRounds Y rounds)) →
    translate Y Op rounds words pre k = some x → untranslate Y Op rounds x = k
  | [], _, _, k, _, _ => nomatch k
  | _ :: _, _, _, .inl (_, _, ⟨⟩), _, h => by
      cases h
      rfl
  | _ :: rs, words, pre, .inr (root, ⟨⟩, key), _, h => by
      obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp h
      change Sum.inr _ = Sum.inr _
      rw [untranslate_translate Op rs words _ key t ht]

/-- The translation is injective (on the keys it is defined on) for every memo and prefix: the
root is retained in the paired message. This is the property that lets the reduction answer the
succinct adversary's FS queries with its own FS oracle without correlating fresh answers. -/
theorem translate_injective {Input : Type} (Op : Type) [Finite Op] [DecidableEq Op]
    (rounds : List Round) (words : (r : Round) → Input → List Y → Y → r.Message)
    (pre : List Y) (k k' : Key Input PUnit (compiledRounds Y Op rounds))
    (x : Key Input PUnit (pairedRounds Y rounds))
    (h : translate Y Op rounds words pre k = some x)
    (h' : translate Y Op rounds words pre k' = some x) : k = k' :=
  (untranslate_translate Y Op rounds words pre k x h).symm.trans
    (untranslate_translate Y Op rounds words pre k' x h')

end Rounds

/-! ## Masked rounds: per-round `clear | merkle skel codec`

The all-merkle definitions above are kept unchanged. FRI needs a mask: the folding rounds `f_i`
are merkle rounds, while `(Unit, α₀)` and `(p_final, xs)` are in the clear. The masked family
(suffix `K`) is defined beside them; `RoundKind.clear` rounds are kept as they are by compilation
and pairing. -/

section Masked

/-- How a round is compiled. `merkle skel F enc`: the message is a word over the leaf alphabet `F`
on the skeleton `skel`, committed by a digest of type `Y`; `enc` is the codec `F ↪ Y` (the raw
leaves are `Y`-valued in VCVio's model). `words` identifies the round's message type with
`LeafData F skel`. -/
inductive RoundKind (Y : Type) (r : Round) : Type 1
  | clear : RoundKind Y r
  | merkle (skel : BinaryTree.Skeleton) (F : Type) (ne : Nonempty F) (enc : F ↪ Y)
      (words : r.Message ≃ BinaryTree.LeafData F skel) : RoundKind Y r

/-- Constant leaf data. -/
def constLeafData {F : Type} (a : F) : (s : BinaryTree.Skeleton) → BinaryTree.LeafData F s
  | .leaf => .leaf a
  | .internal l r => .internal (constLeafData a l) (constLeafData a r)

/-- A merkle round's message type is inhabited: it is a word over a nonempty leaf alphabet. -/
theorem merkle_nonempty {r : Round} {skel : BinaryTree.Skeleton} {F : Type} (ne : Nonempty F)
    (words : r.Message ≃ BinaryTree.LeafData F skel) : Nonempty r.Message :=
  ⟨words.symm (constLeafData (Classical.choice ne) skel)⟩

/-- A masked round list: each in-the-clear round with its compilation kind. -/
abbrev MRounds (Y : Type) : Type 1 := List ((r : Round) × RoundKind Y r)

variable (Y : Type) [Finite Y] [DecidableEq Y]

/-- The underlying in-the-clear round list. -/
def baseRounds : MRounds Y → List Round
  | [] => []
  | ⟨r, _⟩ :: ms => r :: baseRounds ms

/-- `compiledRounds` with a mask: merkle rounds send a root, clear rounds are unchanged. -/
def compiledRoundsK (Op : Type) [Finite Op] [DecidableEq Op] : MRounds Y → List Round
  | [] => [openingRound Op]
  | ⟨r, .clear⟩ :: ms => r :: compiledRoundsK Op ms
  | ⟨r, .merkle _ _ _ _ _⟩ :: ms => rootRound Y r :: compiledRoundsK Op ms

/-- `pairedRounds` with a mask: only merkle rounds carry the root next to the word. -/
def pairedRoundsK : MRounds Y → List Round
  | [] => []
  | ⟨r, .clear⟩ :: ms => r :: pairedRoundsK ms
  | ⟨r, .merkle _ _ _ _ _⟩ :: ms => pairedRound Y r :: pairedRoundsK ms

theorem compiledRoundsK_length (Op : Type) [Finite Op] [DecidableEq Op] (ms : MRounds Y) :
    (compiledRoundsK Y Op ms).length = ms.length + 1 := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
      obtain ⟨r, k⟩ := m
      cases k <;> simp [compiledRoundsK, ih]

/-- Masked `translate`. Clear rounds pass through; merkle rounds are translated as before and
extend the root prefix. -/
def translateK {Input : Type} (Op : Type) [Finite Op] [DecidableEq Op] :
    (ms : MRounds Y) →
    (words : (r : Round) → Nonempty r.Message → Input → List Y → Y → r.Message) → List Y →
    Key Input PUnit (compiledRoundsK Y Op ms) →
    Option (Key Input PUnit (pairedRoundsK Y ms))
  | [], _, _, _ => none
  | ⟨_, .clear⟩ :: _, _, _, .inl (z, m, u) => some (.inl (z, m, u))
  | ⟨_, .clear⟩ :: ms, words, pre, .inr (m, u, key) =>
      (translateK Op ms words pre key).map fun k => .inr (m, u, k)
  | ⟨r, .merkle _ _ ne _ we⟩ :: _, words, pre, .inl (z, root, _) =>
      some (.inl (z, ((words r (merkle_nonempty ne we) z pre root, root) : r.Message × Y), PUnit.unit))
  | ⟨r, .merkle _ _ ne _ we⟩ :: ms, words, pre, .inr (root, _, key) =>
      (translateK Op ms words (pre ++ [show Y from root]) key).map fun k =>
        .inr (((words r (merkle_nonempty ne we) key.input pre root, root) : r.Message × Y), PUnit.unit, k)

/-- Masked `untranslate`: forget the words of merkle rounds. -/
def untranslateK {Input : Type} (Op : Type) [Finite Op] [DecidableEq Op] :
    (ms : MRounds Y) → Key Input PUnit (pairedRoundsK Y ms) →
    Key Input PUnit (compiledRoundsK Y Op ms)
  | [], k => nomatch k
  | ⟨_, .clear⟩ :: _, .inl (z, m, u) => .inl (z, m, u)
  | ⟨_, .clear⟩ :: ms, .inr (m, u, k) => .inr (m, u, untranslateK Op ms k)
  | ⟨_, .merkle _ _ _ _ _⟩ :: _, .inl (z, m, u) => .inl (z, (m.2 : Y), u)
  | ⟨_, .merkle _ _ _ _ _⟩ :: ms, .inr (m, u, k) => .inr ((m.2 : Y), u, untranslateK Op ms k)

/-- `untranslateK` is a left inverse of `translateK` for every memo and prefix. -/
theorem untranslate_translateK {Input : Type} (Op : Type) [Finite Op] [DecidableEq Op] :
    (ms : MRounds Y) → (words : (r : Round) → Nonempty r.Message → Input → List Y → Y → r.Message) →
    (pre : List Y) → (k : Key Input PUnit (compiledRoundsK Y Op ms)) →
    (x : Key Input PUnit (pairedRoundsK Y ms)) →
    translateK Y Op ms words pre k = some x → untranslateK Y Op ms x = k
  | [], _, _, _, _, h => by simp [translateK] at h
  | ⟨_, .clear⟩ :: _, _, _, .inl (_, _, ⟨⟩), _, h => by
      cases h
      rfl
  | ⟨_, .clear⟩ :: ms, words, pre, .inr (m, ⟨⟩, key), _, h => by
      obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp h
      change Sum.inr _ = Sum.inr _
      rw [untranslate_translateK Op ms words _ key t ht]
  | ⟨_, .merkle _ _ _ _ _⟩ :: _, _, _, .inl (_, _, ⟨⟩), _, h => by
      cases h
      rfl
  | ⟨_, .merkle _ _ _ _ _⟩ :: ms, words, pre, .inr (root, ⟨⟩, key), _, h => by
      obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp h
      change Sum.inr _ = Sum.inr _
      rw [untranslate_translateK Op ms words _ key t ht]

theorem translate_injectiveK {Input : Type} (Op : Type) [Finite Op] [DecidableEq Op]
    (ms : MRounds Y) (words : (r : Round) → Nonempty r.Message → Input → List Y → Y → r.Message)
    (pre : List Y) (k k' : Key Input PUnit (compiledRoundsK Y Op ms))
    (x : Key Input PUnit (pairedRoundsK Y ms))
    (h : translateK Y Op ms words pre k = some x)
    (h' : translateK Y Op ms words pre k' = some x) : k = k' :=
  (untranslate_translateK Y Op ms words pre k x h).symm.trans
    (untranslate_translateK Y Op ms words pre k' x h')

/-- The renaming keeps the challenge type: `untranslateK` preserves `Key.Challenge`. -/
theorem untranslate_challengeK {Input : Type} (Op : Type) [Finite Op] [DecidableEq Op] :
    (ms : MRounds Y) → (k : Key Input PUnit (pairedRoundsK Y ms)) →
    (untranslateK Y Op ms k).Challenge = k.Challenge
  | [], k => nomatch k
  | ⟨_, .clear⟩ :: _, .inl _ => rfl
  | ⟨_, .clear⟩ :: ms, .inr (_, _, k) => untranslate_challengeK Op ms k
  | ⟨_, .merkle _ _ _ _ _⟩ :: _, .inl _ => rfl
  | ⟨_, .merkle _ _ _ _ _⟩ :: ms, .inr (_, _, k) => untranslate_challengeK Op ms k

/-- Guards of the compiled protocol read as guards of the paired protocol: a merkle round's guard
sees the root only (`pairGuards` never reads a word). -/
def pairGuards {Input : Type} (Op : Type) [Finite Op] [DecidableEq Op] :
    (ms : MRounds Y) → GuardSchedule Input PUnit (compiledRoundsK Y Op ms) →
    GuardSchedule Input PUnit (pairedRoundsK Y ms)
  | [], _ => PUnit.unit
  | ⟨_, .clear⟩ :: ms, (g, next) => (g, fun m u c => pairGuards Op ms (next m u c))
  | ⟨_, .merkle _ _ _ _ _⟩ :: ms, (g, next) =>
      (fun z m u => g z m.2 u, fun m u c => pairGuards Op ms (next m.2 u c))

/-- Forget the roots of a paired execution path. -/
def forgetPath : (ms : MRounds Y) → (protocol (pairedRoundsK Y ms)).tree.ExecutionPath →
    (protocol (baseRounds Y ms)).tree.ExecutionPath
  | [], p => p
  | ⟨_, .clear⟩ :: ms, p => ⟨p.1, p.2.1, forgetPath ms p.2.2⟩
  | ⟨_, .merkle _ _ _ _ _⟩ :: ms, p => ⟨p.1.1, p.2.1, forgetPath ms p.2.2⟩

/-- The in-the-clear acceptance predicate, read on paired paths (roots forgotten). -/
def pairAccepts {Input : Type} (ms : MRounds Y)
    (accepts : Input → (protocol (baseRounds Y ms)).tree.ExecutionPath → Bool)
    (z : Input) (p : (protocol (pairedRoundsK Y ms)).tree.ExecutionPath) : Bool :=
  accepts z (forgetPath Y ms p)

/-- The roots (merkle rounds only, in order) and the terminal opening of a masked compiled path. -/
def pathRootsK (Op : Type) [Finite Op] [DecidableEq Op] :
    (ms : MRounds Y) → (protocol (compiledRoundsK Y Op ms)).tree.ExecutionPath → List Y × Op
  | [], path => ([], path.1)
  | ⟨_, .clear⟩ :: ms, path => pathRootsK Op ms path.2.2
  | ⟨_, .merkle _ _ _ _ _⟩ :: ms, path =>
      let rest := pathRootsK Op ms path.2.2
      (path.1 :: rest.1, rest.2)

/-- Number of merkle rounds of a mask. -/
def merkleCount : MRounds Y → ℕ
  | [] => 0
  | ⟨_, .clear⟩ :: ms => merkleCount ms
  | ⟨_, .merkle _ _ _ _ _⟩ :: ms => merkleCount ms + 1

theorem pathRootsK_length (Op : Type) [Finite Op] [DecidableEq Op] (ms : MRounds Y)
    (path : (protocol (compiledRoundsK Y Op ms)).tree.ExecutionPath) :
    (pathRootsK Y Op ms path).1.length = merkleCount Y ms := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
      obtain ⟨r, k⟩ := m
      cases k
      · exact ih _
      · exact congrArg (· + 1) (ih _)

end Masked

/-! ## Reading roots and openings off a compiled path -/

section Path

variable {Y : Type} [Finite Y] [DecidableEq Y] {Op : Type} [Finite Op] [DecidableEq Op]

/-- The roots in order, and the terminal opening, of a compiled execution path. -/
def pathRoots : (rounds : List Round) →
    (protocol (compiledRounds Y Op rounds)).tree.ExecutionPath → List Y × Op
  | [], path => ([], path.1)
  | _ :: rs, path =>
      let rest := pathRoots rs path.2.2
      (path.1 :: rest.1, rest.2)

theorem pathRoots_length (rounds : List Round)
    (path : (protocol (compiledRounds Y Op rounds)).tree.ExecutionPath) :
    (pathRoots rounds path).1.length = rounds.length := by
  induction rounds with
  | nil => rfl
  | cons r rs ih => exact congrArg (· + 1) (ih _)

end Path

/-! ## Succinct verifier and experiment (syntax) -/

section Experiment

variable {Y : Type} [Finite Y] [DecidableEq Y] {Op : Type} [Finite Op] [DecidableEq Op]
variable {Query : Type} {Statement Salt W : Type} {rounds : List Round}

/-- Adversary oracles: private coins, the Merkle hash oracle `Query →ₒ Y`, and the FS oracle of
the compiled rounds. The two random oracles are separate summands (domain separation). -/
abbrev SuccinctSpec (Y Op Query Statement Salt : Type) [Finite Y] [DecidableEq Y] [Finite Op]
    [DecidableEq Op] (rounds : List Round) :=
  unifSpec + (Query →ₒ Y) + oracleSpec (Statement × Salt) PUnit (compiledRounds Y Op rounds)

/-- A malicious succinct prover: statement, one salt, roots and openings, terminal seed. -/
abbrev SuccinctAdversary (Y Op Query Statement Salt W : Type) [Finite Y] [DecidableEq Y]
    [Finite Op] [DecidableEq Op] (rounds : List Round) :=
  OracleComp (SuccinctSpec Y Op Query Statement Salt rounds)
    (Option (Statement × SaltedProof Salt (compiledRounds Y Op rounds) × W))

/-- Route FS queries into the third summand. -/
def fsQueries : QueryImpl (oracleSpec (Statement × Salt) PUnit (compiledRounds Y Op rounds))
    (OracleComp (SuccinctSpec Y Op Query Statement Salt rounds)) :=
  fun key => liftM ((SuccinctSpec Y Op Query Statement Salt rounds).query (.inr key))

/-- Route hash queries into the second summand. -/
def hashQueries : QueryImpl (Query →ₒ Y)
    (OracleComp (SuccinctSpec Y Op Query Statement Salt rounds)) :=
  fun q => liftM ((SuccinctSpec Y Op Query Statement Salt rounds).query (.inl (.inr q)))

/-- Succinct verification: QD's public stopped FS verification of the compiled transcript, then
the Merkle check (hash oracle) of the openings against the roots, then the pure local check of
the query-only verifier on the challenges and opened values. -/
def succinctVerify
    (guards : GuardSchedule (Statement × Salt) PUnit (compiledRounds Y Op rounds))
    (merkleCheck : List Y → Op → OracleComp (Query →ₒ Y) Bool)
    (localAccepts : (Statement × Salt) →
      (protocol (compiledRounds Y Op rounds)).tree.ExecutionPath → Bool)
    (z : Statement × Salt) (messages : PublicMessages (compiledRounds Y Op rounds)) :
    OracleComp (SuccinctSpec Y Op Query Statement Salt rounds)
      (Option (protocol (compiledRounds Y Op rounds)).tree.ExecutionPath) := do
  let path? ← simulateQ fsQueries (publicStoppedVerify _ guards z messages)
  match path? with
  | none => pure none
  | some path =>
      let ok ← simulateQ hashQueries
        (merkleCheck (pathRoots rounds path).1 (pathRoots rounds path).2)
      pure (if ok && localAccepts z path then some path else none)

/-- The succinct joint experiment (syntax; semantics: lazy random oracles on both summands,
shared between the adversary and verification). -/
def succinctAcceptedExecution
    (guards : GuardSchedule (Statement × Salt) PUnit (compiledRounds Y Op rounds))
    (merkleCheck : List Y → Op → OracleComp (Query →ₒ Y) Bool)
    (localAccepts : (Statement × Salt) →
      (protocol (compiledRounds Y Op rounds)).tree.ExecutionPath → Bool)
    (adversary : SuccinctAdversary Y Op Query Statement Salt W rounds) :
    OracleComp (SuccinctSpec Y Op Query Statement Salt rounds)
      (Option ((Statement × Salt) × (protocol (compiledRounds Y Op rounds)).tree.ExecutionPath ×
        W)) := do
  match ← adversary with
  | none => pure none
  | some (statement, (salt, messages), witness) =>
      let path ← succinctVerify guards merkleCheck localAccepts (statement, salt) messages
      pure (path.map fun p => ((statement, salt), p, witness))

end Experiment

/-! ## Masked succinct experiment in QD's random-oracle shape 

`randomOracleLoggedRun` runs `OracleComp (unifSpec + ofFn R)` with a single lazy random oracle on
the key domain of `R`. The hash `Query →ₒ Y` and the FS keys are the two halves of one domain
`Query ⊕ Key`, so the reduction can address both through one oracle. -/

section MaskedExperiment

variable {Y : Type} [Finite Y] [DecidableEq Y] [SampleableType Y]
  {Op : Type} [Finite Op] [DecidableEq Op]
variable {Query : Type} {Statement Salt W : Type} {ms : MRounds Y}

/-- Answer family on `Query ⊕ Key`: digests for hash queries, challenges for FS keys. -/
abbrev succinctRange (Y Op Query Statement Salt : Type) [Finite Y] [DecidableEq Y] [Finite Op]
    [DecidableEq Op] (ms : MRounds Y) : Query ⊕ Key (Statement × Salt) PUnit
      (compiledRoundsK Y Op ms) → Type :=
  Sum.elim (fun _ => Y) Key.Challenge

instance succinctRange_sampleable (Y Op Query Statement Salt : Type) [Finite Y] [DecidableEq Y]
    [SampleableType Y] [Finite Op] [DecidableEq Op] (ms : MRounds Y)
    (d : Query ⊕ Key (Statement × Salt) PUnit (compiledRoundsK Y Op ms)) :
    SampleableType (succinctRange Y Op Query Statement Salt ms d) := by
  cases d with
  | inl _ => exact (inferInstance : SampleableType Y)
  | inr k => exact (inferInstance : SampleableType k.Challenge)

/-- Adversary oracles in QD's shape: private coins and one random oracle on `Query ⊕ Key`. -/
abbrev SuccinctSpecK (Y Op Query Statement Salt : Type) [Finite Y] [DecidableEq Y] [Finite Op]
    [DecidableEq Op] (ms : MRounds Y) :=
  unifSpec + OracleSpec.ofFn (succinctRange Y Op Query Statement Salt ms)

/-- A malicious succinct prover over the masked compiled rounds. -/
abbrev SuccinctAdversaryK (Y Op Query Statement Salt W : Type) [Finite Y] [DecidableEq Y]
    [Finite Op] [DecidableEq Op] (ms : MRounds Y) :=
  OracleComp (SuccinctSpecK Y Op Query Statement Salt ms)
    (Option (Statement × SaltedProof Salt (compiledRoundsK Y Op ms) × W))

/-- Route FS queries into the key half of the oracle. -/
def fsQueriesK : QueryImpl (oracleSpec (Statement × Salt) PUnit (compiledRoundsK Y Op ms))
    (OracleComp (SuccinctSpecK Y Op Query Statement Salt ms)) :=
  fun key => liftM ((SuccinctSpecK Y Op Query Statement Salt ms).query (.inr (.inr key)))

/-- Route hash queries into the hash half of the oracle. -/
def hashQueriesK : QueryImpl (Query →ₒ Y)
    (OracleComp (SuccinctSpecK Y Op Query Statement Salt ms)) :=
  fun q => liftM ((SuccinctSpecK Y Op Query Statement Salt ms).query (.inr (.inl q)))

/-- Masked succinct verification (see `succinctVerify`). -/
def succinctVerifyK
    (guards : GuardSchedule (Statement × Salt) PUnit (compiledRoundsK Y Op ms))
    (merkleCheck : List Y → Op → OracleComp (Query →ₒ Y) Bool)
    (localAccepts : (Statement × Salt) →
      (protocol (compiledRoundsK Y Op ms)).tree.ExecutionPath → Bool)
    (z : Statement × Salt) (messages : PublicMessages (compiledRoundsK Y Op ms)) :
    OracleComp (SuccinctSpecK Y Op Query Statement Salt ms)
      (Option (protocol (compiledRoundsK Y Op ms)).tree.ExecutionPath) := do
  let path? ← simulateQ fsQueriesK (publicStoppedVerify _ guards z messages)
  match path? with
  | none => pure none
  | some path =>
      let ok ← simulateQ hashQueriesK
        (merkleCheck (pathRootsK Y Op ms path).1 (pathRootsK Y Op ms path).2)
      pure (if ok && localAccepts z path then some path else none)

/-- The masked succinct joint experiment, in the shape `randomOracleLoggedRun` consumes. -/
def succinctAcceptedExecutionK
    (guards : GuardSchedule (Statement × Salt) PUnit (compiledRoundsK Y Op ms))
    (merkleCheck : List Y → Op → OracleComp (Query →ₒ Y) Bool)
    (localAccepts : (Statement × Salt) →
      (protocol (compiledRoundsK Y Op ms)).tree.ExecutionPath → Bool)
    (adversary : SuccinctAdversaryK Y Op Query Statement Salt W ms) :
    OracleComp (SuccinctSpecK Y Op Query Statement Salt ms)
      (Option ((Statement × Salt) × (protocol (compiledRoundsK Y Op ms)).tree.ExecutionPath ×
        W)) := do
  match ← adversary with
  | none => pure none
  | some (statement, (salt, messages), witness) =>
      let path ← succinctVerifyK guards merkleCheck localAccepts (statement, salt) messages
      pure (path.map fun p => ((statement, salt), p, witness))

end MaskedExperiment

end NockvmE2E.Merkle
