/-
MB-FIX1 non-vacuity witness: the extractor `ext` (and the memo `words`) that the Merkle
theorems take as arguments exist, for every masked round list, once their argument carries
`Nonempty r.Message`. `extTree` is the extractor read off the extracted tree; `ExtIsTree` holds for it
by definition. The examples instantiate `good_accepts` and `reduction_rename` with it.
-/
import NockvmE2E.Merkle.Good

open BinaryTree InductiveMerkleTree OracleComp OracleSpec MerkleTreeMultiExtractability
open Interaction.Oracle Interaction.Oracle.Security.StateRestoration

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NockvmE2E.Merkle.NonVacuous

open NockvmE2E.Merkle NockvmE2E.Merkle.Reduction NockvmE2E.Merkle.Good

variable {Y : Type} [Finite Y] [DecidableEq Y] {Query : Type}

/-- A concrete memo `words`: any word of the (inhabited) round message type. -/
noncomputable def wordsAny (Input : Type) :
    (r : Round) → Nonempty r.Message → Input → List Y → Y → r.Message :=
  fun _ hr _ _ _ => Classical.choice hr

open scoped Classical in
/-- A concrete extractor: at root prefix `pre` of length `j` (and `r` the `j`-th merkle round) it
returns the word whose leaf data is the decoded extracted tree; elsewhere an arbitrary word. -/
noncomputable def extTree (ms : MRounds Y)
    (view : MerkleTreeExtractor.QueryView Query (MAddress (merkleSkels ms)) Y) (y0 : Y) :
    (r : Round) → Nonempty r.Message → List Y → List (Query × Y) → Y → r.Message :=
  fun r hr pre log root =>
    if h : ∃ hl : pre.length < (merkleSkels ms).length,
        (infoAt ms ⟨pre.length, hl⟩).r = r then
      h.choose_spec ▸
        ((infoAt ms ⟨pre.length, h.choose⟩).words.symm
          ((Checkpoint.extractedTree view (config := mconfig (merkleSkels ms))
            (tag := (⟨pre.length, h.choose⟩ : Fin (merkleSkels ms).length))
            ⟨root, toLog log⟩).toLeafData.map
            (fun o => codecDec (infoAt ms ⟨pre.length, h.choose⟩).ne
              (infoAt ms ⟨pre.length, h.choose⟩).enc (o.getD y0))))
    else Classical.choice hr

/-- `extTree` satisfies `ExtIsTree` (by definition). -/
theorem extTree_isTree (ms : MRounds Y)
    (view : MerkleTreeExtractor.QueryView Query (MAddress (merkleSkels ms)) Y) (y0 : Y) :
    ExtIsTree ms view y0 (extTree ms view y0) := by
  intro j pre hpre log root
  obtain ⟨n, hn⟩ := j
  have hpre' : pre.length = n := hpre
  have hc : ∃ hl : pre.length < (merkleSkels ms).length,
      (infoAt ms ⟨pre.length, hl⟩).r = (infoAt ms ⟨n, hn⟩).r := by
    subst hpre'; exact ⟨hn, rfl⟩
  unfold extTree
  rw [dif_pos hc]
  subst hpre'
  simp
  exact Equiv.apply_symm_apply _ _

/-- The hypotheses of `good_accepts` (taking `ext`) are satisfiable: `extTree` is an `ext` with
`ExtIsTree`. -/
theorem good_accepts_nonvacuous {Op : Type} [Finite Op] [DecidableEq Op] {Statement Salt : Type}
    [DecidableEq Statement] [DecidableEq Salt] {ms : MRounds Y}
    (model : MerkleTreeExtractability.NodeQueryModel Query (MAddress (merkleSkels ms)) Y)
    (decode : Op → OpenAll Y (merkleSkels ms)) (y0 : Y)
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
    pairAccepts Y ms accepts z
      (pairPath (fun r hr => memoWords (extTree ms model.view y0) s r hr z) ms [] p) = true :=
  good_accepts model decode y0 (extTree ms model.view y0) (extTree_isTree ms model.view y0)
    s z p E attempts hatt hacc hno hmem accepts localAccepts hq hl

/-- `reduction_rename` (and with it `bImplK`, `reductionB`) applies to `extTree`. -/
example {Op : Type} [Finite Op] [DecidableEq Op] [DecidableEq Query] [SampleableType Y]
    {Statement Salt : Type} [DecidableEq Statement] [DecidableEq Salt] {ms : MRounds Y}
    (view : MerkleTreeExtractor.QueryView Query (MAddress (merkleSkels ms)) Y) (y0 : Y)
    {α : Type}
    (oa : OracleComp (SuccinctSpecK Y Op Query Statement Salt ms) α)
    (s₀ : Obs Query Statement Salt Y) : True := by
  have _ := reduction_rename (Op := Op) (extTree ms view y0) oa s₀
  trivial

/-- The memo `words` of `translateK` exists too. -/
noncomputable example (Input : Type) {Op : Type} [Finite Op] [DecidableEq Op] (ms : MRounds Y) :
    (pre : List Y) → Key Input PUnit (compiledRoundsK Y Op ms) →
      Option (Key Input PUnit (pairedRoundsK Y ms)) :=
  translateK Y Op ms (wordsAny Input)

end NockvmE2E.Merkle.NonVacuous

open NockvmE2E.Merkle.NonVacuous in
#print axioms extTree_isTree
open NockvmE2E.Merkle.NonVacuous in
#print axioms good_accepts_nonvacuous
open NockvmE2E.Merkle.NonVacuous in
#print axioms extTree
open NockvmE2E.Merkle.NonVacuous in
#print axioms wordsAny
