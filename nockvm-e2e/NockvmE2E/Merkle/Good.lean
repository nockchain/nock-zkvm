/-
Merkle (B) file 9: off the bad event the opened values are the memo words, hence the
paired verifier accepts.
-/
import NockvmE2E.Merkle.Reduction
import NockvmE2E.Merkle.Opening
import VCVio.CryptoFoundations.MerkleTree.MultiExtractability.Game

open BinaryTree InductiveMerkleTree OracleComp OracleSpec MerkleTreeMultiExtractability
open Interaction.Oracle Interaction.Oracle.Security.StateRestoration

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NockvmE2E.Merkle.Good

open NockvmE2E.Merkle NockvmE2E.Merkle.Reduction

/-! ## Per-round codec data, indexed by the merkle tag -/

/-- Codec and word data of one merkle round on the skeleton `s`. -/
structure MInfo (Y : Type) (s : Skeleton) where
  r : Round
  F : Type
  ne : Nonempty F
  enc : F ↪ Y
  words : r.Message ≃ LeafData F s

/-- The message type of a merkle round is inhabited. -/
theorem MInfo.messageNonempty {Y : Type} {s : Skeleton} (i : MInfo Y s) : Nonempty i.r.Message :=
  merkle_nonempty i.ne i.words

/-- The data of the `j`-th merkle round of the mask. -/
def infoAt {Y : Type} : (ms : MRounds Y) → (j : Fin (merkleSkels ms).length) →
    MInfo Y ((merkleSkels ms).get j)
  | [], j => absurd j.2 (by simp [merkleSkels])
  | ⟨_, .clear⟩ :: ms, j => infoAt ms j
  | ⟨r, .merkle _ F ne enc words⟩ :: _, ⟨0, _⟩ => ⟨r, F, ne, enc, words⟩
  | ⟨_, .merkle _ _ _ _ _⟩ :: ms, ⟨j + 1, h⟩ => infoAt ms ⟨j, Nat.lt_of_succ_lt_succ h⟩

/-- The paired execution path of a compiled path: the word `W r pre root` next to each root. -/
def pairPath {Y : Type} [Finite Y] [DecidableEq Y] {Op : Type} [Finite Op] [DecidableEq Op]
    (W : (r : Round) → Nonempty r.Message → List Y → Y → r.Message) :
    (ms : MRounds Y) → List Y → (protocol (compiledRoundsK Y Op ms)).tree.ExecutionPath →
    (protocol (pairedRoundsK Y ms)).tree.ExecutionPath
  | [], _, _ => PUnit.unit
  | ⟨_, .clear⟩ :: ms, pre, p => ⟨p.1, p.2.1, pairPath W ms pre p.2.2⟩
  | ⟨r, .merkle _ _ ne _ we⟩ :: ms, pre, p =>
      ⟨((W r (merkle_nonempty ne we) pre p.1, p.1) : r.Message × Y), p.2.1, pairPath W ms (pre ++ [show Y from p.1]) p.2.2⟩


/-! ## The extractor word -/

section Words

variable {Y : Type} [Finite Y] [DecidableEq Y] {Query : Type}

/-- The observer's hash log (pairs) as VCVio's query log (sigma pairs). -/
def toLog (l : List (Query × Y)) : MerkleTreeExtractor.QueryLog Query Y :=
  l.map fun x => ⟨x.1, x.2⟩

/-- `ext` (the extractor of `Reduction.memoWords`) returns, for the `j`-th merkle round, the word
whose leaf data is the decoded leaf data of the tree `Checkpoint.extractedTree` reads from the log
(missing leaves are read as `y0`). This is how `ext` is to be defined from the extracted tree. -/
def ExtIsTree (ms : MRounds Y) (view : MerkleTreeExtractor.QueryView Query (MAddress (merkleSkels ms)) Y)
    (y0 : Y) (ext : (r : Round) → Nonempty r.Message → List Y → List (Query × Y) → Y → r.Message) : Prop :=
  ∀ (j : Fin (merkleSkels ms).length) (pre : List Y), pre.length = j.val →
    ∀ (log : List (Query × Y)) (root : Y),
    (infoAt ms j).words (ext (infoAt ms j).r (infoAt ms j).messageNonempty pre log root) =
      (Checkpoint.extractedTree view
        (config := mconfig (merkleSkels ms)) (tag := j) ⟨root, toLog log⟩).toLeafData.map
        (fun o => codecDec (infoAt ms j).ne (infoAt ms j).enc (o.getD y0))

/-- Decoded opened values are the selected values of the decoded tree. -/
theorem values_map_eq {F : Type} (dec : Y → F) (y0 : Y) {s : Skeleton}
    (o : BatchOpening Y s) (tree : FullData (Option Y) s)
    (h : selectedValues tree.toLeafData o.selector = o.values.map some) :
    o.values.map dec =
      selectedValues (tree.toLeafData.map (fun x => dec (x.getD y0))) o.selector := by
  rw [← SelectedValues.map_selectedValues, h, SelectedValues.map_comp]
  rfl

/-- One position: if the extracted opening of the checkpoint equals the opening, the decoded opened
values are the selected values of the word `ext` returns. -/
theorem posVals_of_extracted {skels : List Skeleton} (j : Fin skels.length)
    (info : MInfo Y (skels.get j)) (y0 : Y)
    (view : MerkleTreeExtractor.QueryView Query (MAddress skels) Y)
    (ext : (r : Round) → Nonempty r.Message → List Y → List (Query × Y) → Y → r.Message)
    (pre : List Y)
    (hext : ∀ (log : List (Query × Y)) (root : Y),
      info.words (ext info.r info.messageNonempty pre log root) =
        (Checkpoint.extractedTree view (config := mconfig skels) (tag := j) ⟨root, toLog log⟩).toLeafData.map
          (fun o => codecDec info.ne info.enc (o.getD y0)))
    (log : List (Query × Y)) (root : Y) (o : BatchOpening Y (skels.get j))
    (hX : Checkpoint.extractedOpening view (config := mconfig skels) (tag := j)
      ⟨root, toLog log⟩ o = o.map some) :
    o.values.map (codecDec info.ne info.enc) =
      selectedValues (info.words (ext info.r info.messageNonempty pre log root)) o.selector := by
  have h1 : selectedValues
      (Checkpoint.extractedTree view (config := mconfig skels) (tag := j)
        ⟨root, toLog log⟩).toLeafData o.selector = o.values.map some := by
    unfold Checkpoint.extractedOpening at hX
    injection hX with _ hv _
  rw [hext log root]
  exact values_map_eq (codecDec info.ne info.enc) y0 o _ h1

end Words


/-! ## Claims pointed at the memo checkpoints, and the attempts they produce -/

section Claims

variable {Y : Type} [Finite Y] [DecidableEq Y] {Query : Type} {Statement Salt : Type}
  [DecidableEq Statement] [DecidableEq Salt]

/-- The hash-log snapshot of the memo checkpoint of `(z, pre, root)` (`[]` if none): the log
`memoWords` extracts from. -/
def memoLog (s : Obs Query Statement Salt Y) (z : Statement × Salt) (pre : List Y) (root : Y) :
    List (Query × Y) :=
  match s.memo (z, pre, root) with
  | some (_, h) => h
  | none => []

theorem memoWords_eq (ext : (r : Round) → Nonempty r.Message → List Y → List (Query × Y) → Y → r.Message)
    (s : Obs Query Statement Salt Y) (r : Round) (hr : Nonempty r.Message) (z : Statement × Salt)
    (pre : List Y) (root : Y) :
    memoWords ext s r hr z pre root = ext r hr pre (memoLog s z pre root) root := rfl

/-- The opening claims of the opening phase: the `j`-th claim opens the `j`-th root against the
memo checkpoint of its root prefix `roots.take j`. The claims read the observer state `s` only
through the memo snapshots; this is how Phases' `mkTerminal` is to be filled, with `α` the pair
(A's output, final observer state), `roots`/`ops` read off A's messages. -/
def memoClaims (skels : List Skeleton) (s : Obs Query Statement Salt Y) (z : Statement × Salt)
    (roots : List Y) (h : roots.length = skels.length) (ops : OpenAll Y skels) :
    List (OpeningClaim Query Y (mconfig skels)) :=
  mkClaims skels roots h ops fun j =>
    toLog (memoLog s z (roots.take j) (roots.get (j.cast h.symm)))

/-- The attempt a verifier decision `b` gives on a claim. -/
def attemptOf {Cfg Address : Type} {config : Configuration Cfg Address}
    (c : OpeningClaim Query Y config) (b : Bool) : AnyEvaluatedOpeningClaim Cfg Query Address Y config :=
  ⟨c.tag, { checkpoint := c.checkpoint, opening := c.opening, accepted := b }⟩

/-- If every attempt of `verifyOpeningClaims` is accepted, the attempts are the claims, accepted. -/
theorem attempts_eq_of_accepted {Cfg Address : Type} {config : Configuration Cfg Address}
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y) :
    ∀ (claims : List (OpeningClaim Query Y config))
      (attempts : List (AnyEvaluatedOpeningClaim Cfg Query Address Y config)),
      attempts ∈ support (verifyOpeningClaims model claims) →
      (∀ a ∈ attempts, a.2.accepted = true) →
      attempts = claims.map fun c => attemptOf c true
  | [], attempts, h, _ => by
      simp [verifyOpeningClaims] at h
      simp [h]
  | c :: cs, attempts, h, hacc => by
      simp only [verifyOpeningClaims, support_bind, Set.mem_iUnion, support_pure,
        Set.mem_singleton_iff] at h
      obtain ⟨b, _, as, has, rfl⟩ := h
      have hb : b = true :=
        hacc ⟨c.tag, { checkpoint := c.checkpoint, opening := c.opening, accepted := b }⟩
          (List.mem_cons_self ..)
      subst hb
      have := attempts_eq_of_accepted model cs as has (fun a ha => hacc a (by simp [ha]))
      simp [attemptOf, this]

end Claims


/-! ## Agreement of a compiled path with its paired path -/

section Recursion

variable {Y : Type} [Finite Y] [DecidableEq Y] {Op : Type} [Finite Op] [DecidableEq Op]

/-- Position `j`: the decoded opened values are the values of the word `W` returns for the
root prefix `pj` and root `root`, at the selected leaves. -/
def PosVals (ms : MRounds Y) (os : OpenAll Y (merkleSkels ms))
    (W : (r : Round) → Nonempty r.Message → List Y → Y → r.Message) (pj : List Y) (root : Y)
    (j : Fin (merkleSkels ms).length) : Prop :=
  (OpenAll.get (merkleSkels ms) os j).values.map
      (codecDec (infoAt ms j).ne (infoAt ms j).enc) =
    selectedValues ((infoAt ms j).words (W (infoAt ms j).r (infoAt ms j).messageNonempty pj root))
      (OpenAll.get (merkleSkels ms) os j).selector

theorem PosVals_congr {ms : MRounds Y} {os : OpenAll Y (merkleSkels ms)}
    {W : (r : Round) → Nonempty r.Message → List Y → Y → r.Message} {pj pj' : List Y} {root root' : Y}
    {j : Fin (merkleSkels ms).length} (h : pj = pj') (h' : root = root') :
    PosVals ms os W pj root j → PosVals ms os W pj' root' j := by
  subst h h'; exact id

theorem pathRootsK_merkle_fst (r : Round) (skel : Skeleton) (F : Type) (ne : Nonempty F) (enc : F ↪ Y)
    (words : r.Message ≃ LeafData F skel) (ms : MRounds Y)
    (p : (protocol (compiledRoundsK Y Op (⟨r, RoundKind.merkle skel F ne enc words⟩ :: ms))).tree.ExecutionPath) :
    (pathRootsK Y Op (⟨r, RoundKind.merkle skel F ne enc words⟩ :: ms) p).1 =
      (show Y from p.1) :: (pathRootsK Y Op ms p.2.2).1 := rfl

/-- If every position holds, the compiled path agrees with its paired path (roots forgotten). -/
theorem agrees_pairPath (W : (r : Round) → Nonempty r.Message → List Y → Y → r.Message) (y0 : Y) :
    ∀ (ms : MRounds Y) (pre : List Y) (os : OpenAll Y (merkleSkels ms))
      (p : (protocol (compiledRoundsK Y Op ms)).tree.ExecutionPath),
      (∀ j : Fin (merkleSkels ms).length,
        PosVals ms os W (pre ++ (pathRootsK Y Op ms p).1.take j)
          ((pathRootsK Y Op ms p).1.getD j y0) j) →
      Agrees ms os p (forgetPath Y ms (pairPath W ms pre p))
  | [], _, _, _, _ => trivial
  | ⟨_, .clear⟩ :: ms, pre, os, p, h =>
      ⟨rfl, rfl, agrees_pairPath W y0 ms pre os p.2.2 h⟩
  | ⟨r, .merkle _ F ne enc words⟩ :: ms, pre, (o, os), p, h => by
      refine ⟨rfl, ?_, agrees_pairPath W y0 ms (pre ++ [show Y from p.1]) os p.2.2 ?_⟩
      · have := PosVals_congr (pj' := pre) (root' := p.1)
          (by simp only [pathRootsK_merkle_fst, List.take_zero, List.append_nil])
          (by simp only [pathRootsK_merkle_fst]; try rfl)
          (h ⟨0, by simp [merkleSkels]⟩)
        exact this
      · intro j'
        have key : ∀ (a : Y) (l : List Y) (n : ℕ), pre ++ (a :: l).take (n + 1) =
            (pre ++ [a]) ++ l.take n := by intros; simp
        have := PosVals_congr
          (pj' := (pre ++ [show Y from p.1]) ++ (pathRootsK Y Op ms p.2.2).1.take j')
          (root' := (pathRootsK Y Op ms p.2.2).1.getD j' y0)
          (by rw [pathRootsK_merkle_fst]; exact key _ _ _)
          (by simp only [pathRootsK_merkle_fst]; try rfl)
          (h j'.succ)
        exact this

end Recursion


/-! ## Off the bad event: opened values = memo words, hence the paired verifier accepts -/

section Main

variable {Y : Type} [Finite Y] [DecidableEq Y] {Op : Type} [Finite Op] [DecidableEq Op]
  {Query : Type} {Statement Salt : Type} [DecidableEq Statement] [DecidableEq Salt] {ms : MRounds Y}

theorem pathRootsK_length_skels (p : (protocol (compiledRoundsK Y Op ms)).tree.ExecutionPath) :
    (pathRootsK Y Op ms p).1.length = (merkleSkels ms).length := by
  rw [pathRootsK_length, merkleSkels_length]

/-- **Good, agreement form.** Let `claims` be the memo-pointed claims for the roots and the decoded
opening of the compiled path `p`, and `attempts` a run of `verifyOpeningClaims` on them in which every
claim was accepted (this is what `merkleCheck = true` says, `bits_mkClaims_root_only`). If no accepted
attempt disagrees with its checkpoint extraction (`¬ HasAcceptedOpeningDisagreement`; the bad event of
VCVio's `HasAnyCheckpointExtractionDisagreement` contains it) and each claim's checkpoint is a
checkpoint of the extractor state `E` (`hmem`), then the decoded opened values are the memo words at
the selected positions, i.e. `p` agrees with the paired path carrying the memo words. -/
theorem good_agrees
    (model : MerkleTreeExtractability.NodeQueryModel Query (MAddress (merkleSkels ms)) Y)
    (decode : Op → OpenAll Y (merkleSkels ms)) (y0 : Y)
    (ext : (r : Round) → Nonempty r.Message → List Y → List (Query × Y) → Y → r.Message)
    (hext : ExtIsTree ms model.view y0 ext)
    (s : Obs Query Statement Salt Y) (z : Statement × Salt)
    (p : (protocol (compiledRoundsK Y Op ms)).tree.ExecutionPath)
    (E : ExtractorState (Fin (merkleSkels ms).length) Query (MAddress (merkleSkels ms)) Y
      (mconfig (merkleSkels ms)))
    (attempts : List (AnyEvaluatedOpeningClaim (Fin (merkleSkels ms).length) Query
      (MAddress (merkleSkels ms)) Y (mconfig (merkleSkels ms))))
    (hatt : attempts ∈ support (verifyOpeningClaims model
      (memoClaims (merkleSkels ms) s z (pathRootsK Y Op ms p).1 (pathRootsK_length_skels p)
        (decode (pathRootsK Y Op ms p).2))))
    (hacc : ∀ a ∈ attempts, a.2.accepted = true)
    (hno : ¬ HasAcceptedOpeningDisagreement model.view E attempts)
    (hmem : ∀ c ∈ memoClaims (merkleSkels ms) s z (pathRootsK Y Op ms p).1
      (pathRootsK_length_skels p) (decode (pathRootsK Y Op ms p).2),
        (⟨c.tag, c.checkpoint⟩ : AnyCheckpoint _ Query _ Y _) ∈ E.checkpoints) :
    Agrees ms (decode (pathRootsK Y Op ms p).2) p
      (forgetPath Y ms (pairPath (fun r hr => memoWords ext s r hr z) ms [] p)) := by
  set roots := (pathRootsK Y Op ms p).1 with hroots
  have hlen := pathRootsK_length_skels p
  have heq := attempts_eq_of_accepted model _ attempts hatt hacc
  refine agrees_pairPath (fun r hr => memoWords ext s r hr z) y0 ms [] _ p ?_
  intro j
  set c : OpeningClaim Query Y (mconfig (merkleSkels ms)) :=
    { tag := j
      checkpoint := { root := roots.get (j.cast hlen.symm)
                      cumulativeLog := toLog (memoLog s z (roots.take j) (roots.get (j.cast hlen.symm))) }
      opening := OpenAll.get (merkleSkels ms) (decode (pathRootsK Y Op ms p).2) j } with hc
  have hcmem : c ∈ memoClaims (merkleSkels ms) s z roots hlen (decode (pathRootsK Y Op ms p).2) := by
    unfold memoClaims mkClaims
    exact List.mem_ofFn.mpr ⟨j, rfl⟩
  have ha : attemptOf c true ∈ attempts := by
    rw [heq]; exact List.mem_map.mpr ⟨c, hcmem, rfl⟩
  have hX : Checkpoint.extractedOpening model.view c.checkpoint c.opening = c.opening.map some := by
    by_contra hne
    exact hno ⟨j, _, ha, hmem c hcmem, rfl, hne⟩
  have hj : (j : ℕ) < roots.length := by rw [hroots, hlen]; exact j.2
  have key := posVals_of_extracted j (infoAt ms j) y0 model.view ext (roots.take j) (hext j (roots.take j) (by rw [List.length_take]; omega))
    (memoLog s z (roots.take j) (roots.get (j.cast hlen.symm))) (roots.get (j.cast hlen.symm))
    c.opening hX
  refine PosVals_congr (pj := roots.take j) (root := roots.get (j.cast hlen.symm)) rfl ?_ key
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  rfl



/-- `merkleCheck = true` is a run of `verifyOpeningClaims` on the memo-pointed claims in which every
claim is accepted (the check reads roots and openings only: `bits_mkClaims_root_only`). -/
theorem accepted_of_merkleCheck
    (model : MerkleTreeExtractability.NodeQueryModel Query (MAddress (merkleSkels ms)) Y)
    (decode : Op → OpenAll Y (merkleSkels ms)) (s : Obs Query Statement Salt Y)
    (z : Statement × Salt) (roots : List Y) (h : roots.length = (merkleSkels ms).length) (op : Op)
    (hok : true ∈ support (merkleCheck (Query := Query) (merkleSkels ms) model decode roots op)) :
    ∃ attempts ∈ support (verifyOpeningClaims model (memoClaims (merkleSkels ms) s z roots h (decode op))),
      ∀ a ∈ attempts, a.2.accepted = true := by
  rw [merkleCheck_of_length _ model decode roots op h] at hok
  have hroot := bits_mkClaims_root_only (Query := Query) (merkleSkels ms) model roots h (decode op)
    (fun j => toLog (memoLog s z (roots.take j) (roots.get (j.cast h.symm))))
  simp only [support_map, Set.mem_image] at hok
  obtain ⟨bits, ⟨bits', hb', rfl⟩, hall⟩ := hok
  have hmem : acceptBits bits' ∈ support (acceptBits <$> verifyOpeningClaims model
      (mkClaims (Query := Query) (merkleSkels ms) roots h (decode op) fun _ => [])) := by
    simp only [support_map, Set.mem_image]; exact ⟨bits', hb', rfl⟩
  rw [← hroot] at hmem
  simp only [support_map, Set.mem_image] at hmem
  obtain ⟨att, hatt, hbits⟩ := hmem
  refine ⟨att, hatt, fun a ha => ?_⟩
  have hall' : (acceptBits att).all id = true := by rw [hbits]; exact hall
  have := List.all_eq_true.mp hall' (a.2.accepted) (by
    simp only [acceptBits, List.mem_map]; exact ⟨a, ha, rfl⟩)
  simpa using this



/-- **Good.** Off the bad event the paired verifier accepts: if the compiled verifier's local check
accepts `p`, the local check is query-only, every claim was accepted by the hash check, and no
accepted attempt disagrees with its checkpoint extraction, then the in-the-clear acceptance
predicate holds on the paired path that carries the memo words (`pairAccepts`). The guards read
roots only (`pairGuards`), and the paired path has the same challenges as `p`. -/
theorem good_accepts
    (model : MerkleTreeExtractability.NodeQueryModel Query (MAddress (merkleSkels ms)) Y)
    (decode : Op → OpenAll Y (merkleSkels ms)) (y0 : Y)
    (ext : (r : Round) → Nonempty r.Message → List Y → List (Query × Y) → Y → r.Message)
    (hext : ExtIsTree ms model.view y0 ext)
    (s : Obs Query Statement Salt Y) (z : Statement × Salt)
    (p : (protocol (compiledRoundsK Y Op ms)).tree.ExecutionPath)
    (E : ExtractorState (Fin (merkleSkels ms).length) Query (MAddress (merkleSkels ms)) Y
      (mconfig (merkleSkels ms)))
    (attempts : List (AnyEvaluatedOpeningClaim (Fin (merkleSkels ms).length) Query
      (MAddress (merkleSkels ms)) Y (mconfig (merkleSkels ms))))
    (hatt : attempts ∈ support (verifyOpeningClaims model
      (memoClaims (merkleSkels ms) s z (pathRootsK Y Op ms p).1 (pathRootsK_length_skels p)
        (decode (pathRootsK Y Op ms p).2))))
    (hacc : ∀ a ∈ attempts, a.2.accepted = true)
    (hno : ¬ HasAcceptedOpeningDisagreement model.view E attempts)
    (hmem : ∀ c ∈ memoClaims (merkleSkels ms) s z (pathRootsK Y Op ms p).1
      (pathRootsK_length_skels p) (decode (pathRootsK Y Op ms p).2),
        (⟨c.tag, c.checkpoint⟩ : AnyCheckpoint _ Query _ Y _) ∈ E.checkpoints)
    (accepts : Statement × Salt → (protocol (baseRounds Y ms)).tree.ExecutionPath → Bool)
    (localAccepts : Statement × Salt → (protocol (compiledRoundsK Y Op ms)).tree.ExecutionPath → Bool)
    (hq : QueryOnly ms decode accepts localAccepts) (hl : localAccepts z p = true) :
    pairAccepts Y ms accepts z (pairPath (fun r hr => memoWords ext s r hr z) ms [] p) = true :=
  hq.accepts_of_agrees z p _ (good_agrees model decode y0 ext hext s z p E attempts hatt hacc hno hmem) hl

/-- The same, off VCVio's strong bad event (`AnyCheckpointExtractionDisagreement` contains
`HasAcceptedOpeningDisagreement`). -/
theorem good_accepts_of_not_any
    (model : MerkleTreeExtractability.NodeQueryModel Query (MAddress (merkleSkels ms)) Y)
    (decode : Op → OpenAll Y (merkleSkels ms)) (y0 : Y)
    (ext : (r : Round) → Nonempty r.Message → List Y → List (Query × Y) → Y → r.Message)
    (hext : ExtIsTree ms model.view y0 ext)
    (s : Obs Query Statement Salt Y) (z : Statement × Salt)
    (p : (protocol (compiledRoundsK Y Op ms)).tree.ExecutionPath)
    (E : ExtractorState (Fin (merkleSkels ms).length) Query (MAddress (merkleSkels ms)) Y
      (mconfig (merkleSkels ms)))
    (attempts : List (AnyEvaluatedOpeningClaim (Fin (merkleSkels ms).length) Query
      (MAddress (merkleSkels ms)) Y (mconfig (merkleSkels ms))))
    (suffix : MerkleTreeExtractor.QueryLog Query Y)
    (hatt : attempts ∈ support (verifyOpeningClaims model
      (memoClaims (merkleSkels ms) s z (pathRootsK Y Op ms p).1 (pathRootsK_length_skels p)
        (decode (pathRootsK Y Op ms p).2))))
    (hacc : ∀ a ∈ attempts, a.2.accepted = true)
    (hno : ¬ AnyCheckpointExtractionDisagreement model.view E attempts suffix)
    (hmem : ∀ c ∈ memoClaims (merkleSkels ms) s z (pathRootsK Y Op ms p).1
      (pathRootsK_length_skels p) (decode (pathRootsK Y Op ms p).2),
        (⟨c.tag, c.checkpoint⟩ : AnyCheckpoint _ Query _ Y _) ∈ E.checkpoints)
    (accepts : Statement × Salt → (protocol (baseRounds Y ms)).tree.ExecutionPath → Bool)
    (localAccepts : Statement × Salt → (protocol (compiledRoundsK Y Op ms)).tree.ExecutionPath → Bool)
    (hq : QueryOnly ms decode accepts localAccepts) (hl : localAccepts z p = true) :
    pairAccepts Y ms accepts z (pairPath (fun r hr => memoWords ext s r hr z) ms [] p) = true :=
  good_accepts model decode y0 ext hext s z p E attempts hatt hacc
    (fun h => hno (AnyCheckpointExtractionDisagreement.ofAcceptedOpeningDisagreement _ _ _ _ h))
    hmem accepts localAccepts hq hl

end Main

end NockvmE2E.Merkle.Good
