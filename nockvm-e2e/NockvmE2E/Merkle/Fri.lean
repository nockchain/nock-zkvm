/-
Merkle (B) file 11, part 1: FRI as a masked compiled protocol.
-/
import NockvmE2E.Merkle.Opening
import NockvmE2E.FriPort.Soundness
import VCVio.CryptoFoundations.MerkleTree.MultiExtractability.Game
import ToMathlib.Data.IndexedBinaryTree.Perfect
import ToMathlib.Data.IndexedBinaryTree.Equiv

open BinaryTree OracleComp OracleSpec ProtocolSpec
open Interaction.Oracle Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir
open Fri.Spec Domain NockvmE2E.FriPort
open scoped NNReal ENNReal

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NockvmE2E.Merkle.Fri

variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable (s : Fin (k + 1) → ℕ+) (d : ℕ+) (l : ℕ)

/-- The evaluation domain of the word committed by prover message `i` (`f_{i+1}`, `i < k`). -/
abbrev wordDom (i : ℕ) : Type :=
  ↥(ω.subdomain (∑ j ∈ finRangeTo (k + 1) (i + 1), (s j).val)).toFinset

/-- For `i < k` the native message type is the legacy word `domain → F` (the subtype predicate is
vacuous). -/
noncomputable def friMsgEquivFun (i : ℕ) (h : 2 * i + 1 < (Fin.vsum fun (_ : Fin k) ↦ 2) + 2 + 1)
    (hik : i < k) : FriMsg (ω := ω) s d l i h ≃ (wordDom (ω := ω) s i → F) := by
  have e : (pSpec k (ω := ω) s l).«Type» ⟨2 * i + 1, h⟩ = (wordDom (ω := ω) s i → F) := by
    have e1 : (nonfinalMessage (ω := ω) s l ⟨i, hik⟩).1 = ⟨2 * i + 1, h⟩ := Fin.ext (by simp)
    have t := nonfinalMessage_type (ω := ω) s l ⟨i, hik⟩
    rw [← e1]; exact t
  refine (Equiv.subtypeUnivEquiv (fun x => ?_)).trans (Equiv.cast e)
  intro hk; exact absurd hk (by omega)


/-- Leaf layout of the committed words: a skeleton per word `f_{i+1}` together with an indexing of its
leaves by the evaluation domain (for the perfect tree on `2^m` points, see `perfectLeaves`). -/
structure FriLeaves (s : Fin (k + 1) → ℕ+) (ω : SmoothCosetFftDomain n F) where
  skel : Fin k → Skeleton
  idx : ∀ i : Fin k, SkeletonLeafIndex (skel i) ≃ wordDom (ω := ω) s i.val

/-- The evaluation domain of word `i` has `2 ^ (n - a_i)` points. -/
theorem card_wordDom (i : ℕ) :
    Fintype.card (wordDom (ω := ω) s i) = 2 ^ (n - ∑ j ∈ finRangeTo (k + 1) (i + 1), (s j).val) := by
  rw [Fintype.card_coe]
  exact (CosetFftDomainClass.card_toFinset).trans (Fintype.card_fin _)

/-- **The perfect-tree layout**: one perfect tree per word, on `2 ^ (n - a_i)` leaves (the
evaluation domain of `f_{i+1}`), the leaves numbered by an arbitrary fixed bijection. -/
noncomputable def perfectLeaves : FriLeaves (ω := ω) s where
  skel i := Skeleton.perfect (n - ∑ j ∈ finRangeTo (k + 1) (i.val + 1), (s j).val)
  idx i := (SkeletonLeafIndex.perfectEquiv _).symm.trans
    (Fintype.equivOfCardEq (by rw [Fintype.card_fin, card_wordDom]))

variable (L : FriLeaves (ω := ω) s)

/-- The word equivalence of the `i`-th merkle round: native message `≃` leaf data. -/
noncomputable def friWords (i : Fin k) (h : 2 * i.val + 1 < (Fin.vsum fun (_ : Fin k) ↦ 2) + 2 + 1) :
    FriMsg (ω := ω) s d l i.val h ≃ LeafData F (L.skel i) :=
  (friMsgEquivFun s d l i.val h i.2).trans
    ((Equiv.arrowCongr (L.idx i).symm (Equiv.refl F)).trans (LeafData.equivIndexFun (L.skel i)).symm)


/-! ## The mask -/

section Mask

variable [∀ j, SampleableType ((pSpec k (ω := ω) s l).Challenge j)]
variable (Dg : Type) [Finite Dg] [DecidableEq Dg] (enc : F ↪ Dg)

/-- The masked rounds `i+1, …, k+1` (`c = k - i` merkle rounds `f_{i+1} … f_k`, then the clear final
round `(p_final, xs)`). -/
noncomputable def friMerkleMask : (i c : ℕ) → i + c = k → MRounds Dg
  | i, 0, _ => [⟨(friAlt (ω := ω) s d l).midRound i (show i < k + 1 by omega), .clear⟩]
  | i, c + 1, h =>
      ⟨(friAlt (ω := ω) s d l).midRound i (show i < k + 1 by omega),
        .merkle (L.skel ⟨i, by omega⟩) F ⟨0⟩ enc (friWords s d l L ⟨i, by omega⟩ _)⟩ ::
        friMerkleMask i.succ c (by omega)

/-- **The FRI round mask**: `(Unit, α₀)` and `(p_final, xs)` clear, `f_1 … f_k` merkle. -/
noncomputable def friMask : MRounds Dg :=
  ⟨(friAlt (ω := ω) s d l).headRound, .clear⟩ :: friMerkleMask s d l L Dg enc 0 k (by omega)

theorem baseRounds_friMerkleMask : (i c : ℕ) → (h : i + c = k) →
    baseRounds Dg (friMerkleMask s d l L Dg enc i c h) =
      (friAlt (ω := ω) s d l).tailRounds i (c + 1) (by have : (friAlt (ω := ω) s d l).r = k + 1 := rfl; omega)
  | _, 0, _ => rfl
  | i, c + 1, h => by
      have ih := baseRounds_friMerkleMask i.succ c (by omega)
      exact congrArg (_ :: ·) ih

/-- The mask is a mask of FRI's native rounds. -/
theorem baseRounds_friMask : baseRounds Dg (friMask s d l L Dg enc) = friRounds (ω := ω) s d l :=
  congrArg (_ :: ·) (baseRounds_friMerkleMask s d l L Dg enc 0 k _)

end Mask


/-! ## The paired alternating spec -/

section Paired

/-- The paired message type of a round: `A × Dg` if the round is committed (`c`), else `A`. -/
def PM (c : Prop) [Decidable c] (A Dg : Type) : Type := if c then A × Dg else A

theorem PM_pos {c : Prop} [Decidable c] {A Dg : Type} (h : c) : PM c A Dg = (A × Dg) := by simp [PM, h]
theorem PM_neg {c : Prop} [Decidable c] {A Dg : Type} (h : ¬ c) : PM c A Dg = A := by simp [PM, h]

instance PM.instFinite (c : Prop) [Decidable c] (A Dg : Type) [Finite A] [Finite Dg] :
    Finite (PM c A Dg) := by unfold PM; split <;> infer_instance

instance PM.instDecEq (c : Prop) [Decidable c] (A Dg : Type) [DecidableEq A] [DecidableEq Dg] :
    DecidableEq (PM c A Dg) := by unfold PM; split <;> infer_instance

/-- The underlying message of a paired message (root forgotten). -/
def PM.fst (c : Prop) [Decidable c] {A Dg : Type} (x : PM c A Dg) : A :=
  if h : c then (cast (PM_pos h) x).1 else cast (PM_neg h) x

variable {m : ℕ} {pSpec : ProtocolSpec m}

/-- `A` with the messages `i` satisfying `c` paired with a digest `Dg` (the root). The legacy view
`emb` forgets the root, so every state-function statement of `A` transfers unchanged. -/
def pairedBy (A : Lift.Alternating pSpec) (c : ℕ → Prop) [DecidablePred c]
    (Dg : Type) [Finite Dg] [DecidableEq Dg] : Lift.Alternating pSpec :=
  { A with
    Msg := fun i h => PM (c i) (A.Msg i h) Dg
    emb := fun i h x => A.emb i h (PM.fst (c i) x)
    decEqMsg := fun i h => haveI := A.decEqMsg i h; inferInstance
    finiteMsg := fun i h => haveI := A.finiteMsg i h; inferInstance }

theorem round_eq_of_msg {M M' C : Type} (e : M = M') (dec : DecidableEq M) (dec' : DecidableEq M')
    (f : Finite M) (f' : Finite M') (fc : Finite C) (nc : Nonempty C) (sc : SampleableType C) :
    (Round.mk M C OracleInterface.instDefault dec f fc nc sc) =
      (Round.mk M' C OracleInterface.instDefault dec' f' fc nc sc) := by
  subst e
  have h1 : dec = dec' := Subsingleton.elim _ _
  subst h1
  rfl

end Paired


section PairedFri

variable [∀ j, SampleableType ((pSpec k (ω := ω) s l).Challenge j)]
variable (Dg : Type) [Finite Dg] [DecidableEq Dg] (enc : F ↪ Dg)

/-- **FRI's paired alternating spec**: the folded words `f_1 … f_k` carry their root. -/
noncomputable def friAltP : Lift.Alternating (pSpec k (ω := ω) s l) :=
  pairedBy (friAlt (ω := ω) s d l) (fun i => i < k) Dg

theorem friAltP_midRound_pos (i : ℕ) (hi : i < k + 1) (hik : i < k) :
    (friAltP (ω := ω) s d l Dg).midRound i hi = pairedRound Dg ((friAlt (ω := ω) s d l).midRound i hi) :=
  round_eq_of_msg (M := PM (i < k) ((friAlt (ω := ω) s d l).midRound i hi).Message Dg)
    (M' := ((friAlt (ω := ω) s d l).midRound i hi).Message × Dg)
    (C := ((friAlt (ω := ω) s d l).midRound i hi).Challenge) (PM_pos hik) _ _ _ _ _ _ _

theorem friAltP_midRound_neg (i : ℕ) (hi : i < k + 1) (hik : ¬ i < k) :
    (friAltP (ω := ω) s d l Dg).midRound i hi = (friAlt (ω := ω) s d l).midRound i hi :=
  round_eq_of_msg (M := PM (i < k) ((friAlt (ω := ω) s d l).midRound i hi).Message Dg)
    (M' := ((friAlt (ω := ω) s d l).midRound i hi).Message)
    (C := ((friAlt (ω := ω) s d l).midRound i hi).Challenge) (PM_neg hik) _ _ _ _ _ _ _

theorem friAltP_tailRounds : (i c : ℕ) → (h : i + c = k) →
    (friAltP (ω := ω) s d l Dg).tailRounds i (c + 1)
        (by have : (friAltP (ω := ω) s d l Dg).r = k + 1 := rfl; omega) =
      pairedRoundsK Dg (friMerkleMask s d l L Dg enc i c h)
  | i, 0, h => by
      have hik : ¬ i < k := by omega
      exact congrArg (· :: []) (friAltP_midRound_neg s d l Dg i (by omega) hik)
  | i, c + 1, h => by
      have ih := friAltP_tailRounds i.succ c (by omega)
      exact (congrArg₂ List.cons (friAltP_midRound_pos s d l Dg i (by omega) (by omega)) ih)

/-- **The round equality**: the paired alternating rounds are the masked paired rounds. -/
theorem friAltP_rounds :
    (friAltP (ω := ω) s d l Dg).rounds = pairedRoundsK Dg (friMask s d l L Dg enc) := by
  simp only [Lift.Alternating.rounds, friMask, pairedRoundsK]
  rw [show (friAltP (ω := ω) s d l Dg).headRound = (friAlt (ω := ω) s d l).headRound from rfl]
  exact congrArg _ (friAltP_tailRounds s d l L Dg enc 0 k _)

variable [SampleableType F]
variable (hdom : 2 ^ (∑ j, (s j).val) * d.val ≤ 2 ^ n)

/-- FRI's terminal check on a path of the paired protocol: the legacy acceptance predicate on the
legacy transcript decoded by `friAltP` (the roots are forgotten by `emb`). -/
noncomputable def friAcceptsP {Salt : Type} (z : FriStmt (ω := ω) s × Salt)
    (path : (protocol (friAltP (ω := ω) s d l Dg).rounds).tree.ExecutionPath) : Bool :=
  open Classical in
  decide (queryBad s d l (round_bound hdom) (initialOracle s z.1)
    (Transcript.restrict (b := Fin.last _) (by simp only [Fin.val_succ, Fin.val_last]; omega)
      ((friAltP (ω := ω) s d l Dg).pathTranscript path)))

theorem friAcceptsP_iff {Salt : Type} (z : FriStmt (ω := ω) s × Salt)
    (path : (protocol (friAltP (ω := ω) s d l Dg).rounds).tree.ExecutionPath) :
    friAcceptsP s d l Dg hdom z path = true ↔
      queryBad s d l (round_bound hdom) (initialOracle s z.1)
        (Transcript.restrict (b := Fin.last _) (by simp only [Fin.val_succ, Fin.val_last]; omega)
          ((friAltP (ω := ω) s d l Dg).pathTranscript path)) := by
  classical
  unfold friAcceptsP
  exact decide_eq_true_iff

/-- **FRI, paired-protocol single-salt Fiat–Shamir soundness.** The statement of
`fri_singleSalt_soundness` for the paired protocol `friAltP` (folded words `f_1 … f_k` carry their
root), with the same bound. Since `friAltP.rounds = pairedRoundsK Dg (friMask …)`
(`friAltP_rounds`), this is the `hclear` input of the Merkle compilation. -/
theorem fri_paired_singleSalt_soundness (θ δ : ℝ)
    {Salt W : Type} [DecidableEq (FriStmt (ω := ω) s)] [DecidableEq Salt]
    (guards : GuardSchedule (FriStmt (ω := ω) s × Salt) PUnit (friAltP (ω := ω) s d l Dg).rounds)
    (adversary : SingleSaltAdversary (FriStmt (ω := ω) s) Salt W (friAltP (ω := ω) s d l Dg).rounds)
    (Q : ℕ)
    (queryBound : ∀ phase ∈ support (randomOracleLoggedRun adversary.withQueryLog ∅),
      (freshKeysOfLog phase.1.2).card ≤ Q) :
    Pr{let joint ← (randomOracleLoggedRun
      (singleSaltAcceptedExecution (friAltP (ω := ω) s d l Dg).rounds guards
        (friAcceptsP s d l Dg hdom) adversary) ∅)}[
      match joint.1.1.1 with
      | none => False
      | some (z, _, _) => initialOracle s z.1 ∉ proximityLanguage s d δ] ≤
    Q * Finset.univ.sup (fun j => (challengeError (ω := ω) s d l θ δ j : ℝ≥0∞)) +
      (((∑ i, foldingError (ω := ω) s d θ i) + Real.toNNReal (1 - min θ δ) ^ l : ℝ≥0) : ℝ≥0∞) := by
  have hs := round_bound hdom
  have h := (friAltP (ω := ω) s d l Dg).singleSalt_soundness_of_stateFamily'
    {stmt | initialOracle s stmt ∈ proximityLanguage s d δ}
    (friState s d l hs θ δ)
    (fun stmt h0 => by
      rcases h0 with h0 | ⟨_, hi, _⟩
      · exact h0
      · exact absurd hi (Nat.not_lt_zero _))
    (fun stmt m hm tr msg hafter => by
      by_contra hb
      exact Verifier.badEventState_prover_next _ _ m hm _ tr hb msg hafter)
    (fun j => (challengeError (ω := ω) s d l θ δ j : ℝ≥0∞))
    (fun stmt hstmt => friState_challengeLaw s d l hs θ δ stmt hstmt)
    guards (friAcceptsP s d l Dg hdom) adversary (fun _ _ _ => True)
    (fun z path _ hacc _ => Or.inr ⟨queryChallenge s l, (queryChallenge s l).1.isLt,
      (badEvent_query s d l hs θ _ _).mpr ((friAcceptsP_iff s d l Dg hdom z path).mp hacc)⟩)
    Q queryBound
  rw [← ENNReal.ofNNReal_finsetSum, sum_challengeError] at h
  refine le_trans (prEvent_mono _ _ _ ?_) h
  rintro ⟨⟨⟨_ | ⟨z, path, w⟩, _⟩, _⟩, _⟩ hbad
  · exact hbad.elim
  · exact ⟨hbad, trivial⟩

end PairedFri

/-! ## The FRI query-only law -/

section QueryOnlyLaw

open Fri.Spec.QueryRound

/-- The domain of the committed word `i` (`i = 0` is the input word). -/
abbrev Dw (i : Fin (k + 1)) : Type :=
  ↥(ω.subdomain (∑ j ∈ finRangeTo (k + 1) i.val, (s j).val)).toFinset

variable (hs : (∑ j, (s j).val) ≤ n)

/-- The positions of word `i` the legacy query verifier reads for the query vector `xs`: the
folding block of every query (`checkRound`) and the folded point of the previous round
(`queryNext`). -/
def readPts (xs : Fin l → (ω.subdomain 0).toFinset) (i : Fin (k + 1)) : Set (Dw (ω := ω) s i) :=
  {y | ∃ j, y ∈ queryBlock s hs i (xs j) ∨
    y.val = ((xs j).val) ^ (2 ^ foldingPrefix s i.castSucc)}

/-- The verifier's accept/reject depends on the retained history only through the final polynomial
and the words at `readPts`. -/
theorem eval_verifyQueries_congr (o o' : ∀ j, FinalOracleStatement s ω j) (α : FinalStatement F k)
    (xs : Fin l → (ω.subdomain 0).toFinset)
    (hp : finalPolynomial s o = finalPolynomial s o')
    (hw : ∀ i : Fin (k + 1), ∀ y ∈ readPts s l hs xs i, committedWord s o i y = committedWord s o' i y) :
    (simulateQ (OracleInterface.simOracle0 (FinalOracleStatement s ω) o)
      (verifyQueries s hs l α xs).run).run =
    (simulateQ (OracleInterface.simOracle0 (FinalOracleStatement s ω) o')
      (verifyQueries s hs l α xs).run).run := by
  rw [eval_verifyQueries, eval_verifyQueries]
  have key : ∀ j i, (simulateQ (OracleInterface.simOracle0 (FinalOracleStatement s ω) o)
        (checkRound s hs (finalPolynomial s o) (α i) i (xs j))).run =
      (simulateQ (OracleInterface.simOracle0 (FinalOracleStatement s ω) o')
        (checkRound s hs (finalPolynomial s o') (α i) i (xs j))).run := by
    intro j i
    rw [eval_checkRound, eval_checkRound, eval_queryNext, eval_queryNext]
    have hb : ((queryBlock s hs i (xs j)).map (fun q ↦ (q.val, committedWord s o i q))) =
        ((queryBlock s hs i (xs j)).map (fun q ↦ (q.val, committedWord s o' i q))) :=
      List.map_congr_left fun q hq => by rw [hw i q ⟨j, Or.inl hq⟩]
    have hn : committedFunction s o i.succ (((xs j).val) ^ (2 ^ foldingPrefix s i.succ)) =
        committedFunction s o' i.succ (((xs j).val) ^ (2 ^ foldingPrefix s i.succ)) := by
      unfold committedFunction
      by_cases h : i.succ.val < k + 1
      · simp only [h, ↓reduceDIte]
        split_ifs with hx
        · exact hw ⟨i.succ.val, h⟩ ⟨_, hx⟩ ⟨j, Or.inr rfl⟩
        · rfl
      · simp only [h, ↓reduceDIte, hp]
    rw [hb, hn]
  have hall : (∀ j i, (simulateQ (OracleInterface.simOracle0 (FinalOracleStatement s ω) o)
        (checkRound s hs (finalPolynomial s o) (α i) i (xs j))).run = true) ↔
      (∀ j i, (simulateQ (OracleInterface.simOracle0 (FinalOracleStatement s ω) o')
        (checkRound s hs (finalPolynomial s o') (α i) i (xs j))).run = true) :=
    forall_congr' fun j => forall_congr' fun i => by rw [key j i]
  simp only [hall]



/-- The transcript before the query vector. -/
abbrev qpre (tr : (pSpec k (ω := ω) s l).Transcript (queryChallenge (ω := ω) s l).val.succ) :
    (pSpec k (ω := ω) s l).Transcript (queryChallenge (ω := ω) s l).val.castSucc :=
  tr.restrict (by simp only [Fin.val_castSucc, Fin.val_succ]; omega)

/-- **The legacy FRI acceptance is query-only.** Two transcripts with the same fold challenges and
query vector, the same final polynomial, and the same words at `readPts`, are accepted together. -/
theorem queryBad_congr (f : (ω.subdomain 0).toFinset → F)
    (tr tr' : (pSpec k (ω := ω) s l).Transcript (queryChallenge (ω := ω) s l).val.succ)
    (hα : queryFoldChallenges s l (qpre s l tr) =
      queryFoldChallenges s l (qpre s l tr'))
    (hxs : cast (queryChallenge_type (ω := ω) s l)
        (tr.read (queryChallenge s l).val (by simp)) =
      cast (queryChallenge_type (ω := ω) s l) (tr'.read (queryChallenge s l).val (by simp)))
    (hp : readFinalPolynomial s l (qpre s l tr)
        (by simp) =
      readFinalPolynomial s l (qpre s l tr')
        (by simp))
    (hw : ∀ i : Fin (k + 1), ∀ y ∈ readPts s l hs
        (cast (queryChallenge_type (ω := ω) s l) (tr.read (queryChallenge s l).val (by simp))) i,
      readWord s l f (qpre s l tr) i
          (by simp only [Fin.val_castSucc, queryChallenge_val]; omega) y =
        readWord s l f (qpre s l tr') i
          (by simp only [Fin.val_castSucc, queryChallenge_val]; omega) y) :
    queryBad s d l hs f tr ↔ queryBad s d l hs f tr' := by
  unfold queryBad
  simp only []
  rw [← hα, ← hxs]
  refine and_congr (by rw [finalPolynomial_queryHistory, finalPolynomial_queryHistory, hp]) ?_
  rw [eval_verifyQueries_congr s l hs _ (queryHistory s l f (qpre s l tr')) _ _
    (by rw [finalPolynomial_queryHistory, finalPolynomial_queryHistory, hp])
    (fun i y hy => by rw [committedWord_queryHistory, committedWord_queryHistory]; exact hw i y hy)]

end QueryOnlyLaw


/-! ## Relating the legacy transcripts of two native paths (generic in the alternating spec) -/

section PathRel

variable {mm : ℕ} {pSpec : ProtocolSpec mm} (A : Lift.Alternating pSpec)
  [hsamp : ∀ j, SampleableType (pSpec.Challenge j)]
variable (P : ∀ j : Fin mm, pSpec.«Type» j → pSpec.«Type» j → Prop)

/-- Two partial legacy transcripts are related if `P` holds at every position read. -/
def PrefRel {c : Fin (mm + 1)} (tr tr' : Transcript c pSpec) : Prop :=
  ∀ (j : Fin mm) (h : j.val < c.val), P j (tr.read j h) (tr'.read j h)

theorem PrefRel.concat {c : Fin mm} {tr tr' : Transcript c.castSucc pSpec} (hr : PrefRel P tr tr')
    {msg msg' : pSpec.«Type» c} (hP : P c msg msg') : PrefRel P (tr.concat msg) (tr'.concat msg') := by
  intro j hj
  by_cases hlt : j.val < c.val
  · rw [Transcript.read_concat_lt tr msg j hlt, Transcript.read_concat_lt tr' msg' j hlt]
    exact hr j hlt
  · have hjc : j = c := Fin.ext (by simp only [Fin.val_succ] at hj; omega)
    subst hjc
    rw [Transcript.read_concat_last, Transcript.read_concat_last]
    exact hP

/-- Step relation along two native tail paths: the legacy message (through `emb`) and the
challenge of every native round are `P`-related at their legacy positions. -/
def StepRel : (i c : ℕ) → (h : i + c = A.r) → (protocol (A.tailRounds i c h)).tree.ExecutionPath →
    (protocol (A.tailRounds i c h)).tree.ExecutionPath → Prop
  | _, 0, _, _, _ => True
  | i, c + 1, h, path, path' =>
      P ⟨2 * i + 1, A.lt_of_lt_r (by omega)⟩ (A.emb i _ path.1) (A.emb i _ path'.1) ∧
      P ⟨2 * i + 2, by have := A.hn; omega⟩ path.2.1 path'.2.1 ∧
      StepRel i.succ c (by omega) path.2.2 path'.2.2

theorem tailPath_rel : (c i : ℕ) → (h : i + c = A.r) → (tr tr' : A.PosTr i (by omega)) →
    (path path' : (protocol (A.tailRounds i c h)).tree.ExecutionPath) →
    PrefRel P tr tr' → StepRel A P i c h path path' →
    PrefRel (c := Fin.last mm) P (A.tailPath i c h tr path) (A.tailPath i c h tr' path')
  | 0, i, h, tr, tr', _, _, hr, _ => fun j hj => hr j (by
      have := A.hn; simp only [Fin.val_last] at hj; simp only; omega)
  | c + 1, i, h, tr, tr', path, path', hr, ⟨h1, h2, h3⟩ =>
      tailPath_rel c i.succ (by omega) _ _ path.2.2 path'.2.2
        (PrefRel.concat P (PrefRel.concat P hr h1) h2) h3

theorem pathTranscript_rel (path path' : (protocol A.rounds).tree.ExecutionPath)
    (h0 : P ⟨0, A.lt_of_le_r (Nat.zero_le _)⟩ path.2.1 path'.2.1)
    (hs : StepRel A P 0 A.r (Nat.zero_add _) path.2.2 path'.2.2) :
    PrefRel (c := Fin.last mm) P (A.pathTranscript path) (A.pathTranscript path') :=
  tailPath_rel A P A.r 0 _ _ _ path.2.2 path'.2.2
    (PrefRel.concat P (fun j hj => absurd hj (by simp)) h0) hs

end PathRel

/-! ## The FRI relation between two legacy transcripts -/

section FriRel

variable (hs : (∑ j, (s j).val) ≤ n)

/-- Transport of a legacy entry along an equality of positions. -/
def xp {mm : ℕ} {pSpec : ProtocolSpec mm} {a b : Fin mm} (h : a = b) (x : pSpec.«Type» a) :
    pSpec.«Type» b := cast (congrArg pSpec.«Type» h) x

/-- The relation of two FRI legacy transcripts, position by position: fold challenges, the query
vector and the final polynomial are equal, and the word `f_{i+1}` is equal at `readPts xs`. -/
def friRel (xs : Fin l → (ω.subdomain 0).toFinset) (j : Fin ((Fin.vsum fun (_ : Fin k) ↦ 2) + 2 + 1))
    (m m' : (pSpec k (ω := ω) s l).«Type» j) : Prop :=
  (∀ i : Fin (k + 1), ∀ h : j = (foldChallenge (ω := ω) s l i).val,
    cast (foldChallenge_type s l i) (xp h m) = cast (foldChallenge_type s l i) (xp h m')) ∧
  (∀ h : j = (finalMessage (ω := ω) s l).val,
    cast (finalMessage_type s l) (xp h m) = cast (finalMessage_type s l) (xp h m')) ∧
  (∀ h : j = (queryChallenge (ω := ω) s l).val,
    cast (queryChallenge_type s l) (xp h m) = xs ∧ cast (queryChallenge_type s l) (xp h m') = xs) ∧
  (∀ i : Fin k, ∀ h : j = (nonfinalMessage (ω := ω) s l i).val,
    ∀ y : Dw (ω := ω) s ⟨i.val + 1, Nat.succ_lt_succ i.2⟩, y ∈ readPts s l hs xs ⟨i.val + 1, Nat.succ_lt_succ i.2⟩ →
      (cast (nonfinalMessage_type s l i) (xp h m) : wordDom (ω := ω) s i.val → F) y =
      (cast (nonfinalMessage_type s l i) (xp h m') : wordDom (ω := ω) s i.val → F) y)

theorem cast_fun_apply {a b : ℕ} (e : a = b) (w : (ω.subdomain a).toFinset → F)
    (y : (ω.subdomain b).toFinset) :
    (cast (congrArg (fun a ↦ (ω.subdomain a).toFinset → F) e) w) y =
      w ⟨y.val, by subst e; exact y.2⟩ := by
  subst e; rfl


/-- **Query-only on full transcripts.** If two full legacy transcripts are `friRel`-related (same
fold challenges, query vector `xs`, final polynomial, and words equal on `readPts xs`), the FRI
acceptance predicate agrees on them. -/
theorem queryBad_congr_of_rel (f : (ω.subdomain 0).toFinset → F)
    (T T' : (pSpec k (ω := ω) s l).FullTranscript)
    (xs : Fin l → (ω.subdomain 0).toFinset)
    (hrel : PrefRel (c := Fin.last _) (friRel s l hs xs) T T') :
    queryBad s d l hs f (Transcript.restrict (b := Fin.last _)
        (by simp only [Fin.val_succ, Fin.val_last]; omega) T) ↔
      queryBad s d l hs f (Transcript.restrict (b := Fin.last _)
        (by simp only [Fin.val_succ, Fin.val_last]; omega) T') := by
  have hk := friLength (k := k)
  have h3 := (hrel _ (by simp only [Fin.val_last, queryChallenge_val]; omega)).2.2.1 rfl
  have hx : cast (queryChallenge_type (ω := ω) s l)
      ((Transcript.restrict (a := (queryChallenge (ω := ω) s l).val.succ) (b := Fin.last _)
        (by simp only [Fin.val_succ, Fin.val_last]; omega) T).read
        (queryChallenge s l).val (by simp)) = xs := h3.1
  refine queryBad_congr s d l hs f _ _ ?_ ?_ ?_ ?_
  · funext i
    exact (hrel _ (by simp only [Fin.val_last, foldChallenge_val]; omega)).1 i rfl
  · exact h3.1.trans h3.2.symm
  · exact (hrel _ (by simp only [Fin.val_last, finalMessage_val]; omega)).2.1 rfl
  · intro i y hy
    rw [hx] at hy
    by_cases hi0 : i.val = 0
    · unfold readWord
      simp only [hi0, ↓reduceDIte]
    · obtain ⟨iv, hiv⟩ := i
      obtain ⟨jv, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi0
      unfold readWord
      simp only [hi0, ↓reduceDIte]
      erw [cast_fun_apply, cast_fun_apply]
      exact (hrel _ (by simp only [Fin.val_last, nonfinalMessage_val]; omega)).2.2.2
        ⟨jv, Nat.lt_of_succ_lt_succ hiv⟩ rfl _ hy
      all_goals rfl

/-- The selected value at a selected leaf is the leaf of the tree. -/
theorem selectedValueAt_selectedValues {α : Type} {sk : Skeleton} (idx : SkeletonLeafIndex sk) :
    ∀ (leaves : LeafData α sk) (sel : LeafData Bool sk) (h : sel.get idx = true),
      InductiveMerkleTree.selectedValueAt (InductiveMerkleTree.selectedValues leaves sel) idx h =
        leaves.get idx := by
  induction idx with
  | ofLeaf =>
      intro leaves sel h
      cases leaves with
      | leaf a =>
          cases sel with
          | leaf b =>
              cases b with
              | false => simp [LeafData.get] at h
              | true => rfl
  | ofLeft idx ih =>
      intro leaves sel h
      cases leaves with
      | internal la ra =>
          cases sel with
          | internal l r => exact ih la l _
  | ofRight idx ih =>
      intro leaves sel h
      cases leaves with
      | internal la ra =>
          cases sel with
          | internal l r => exact ih ra r _

/-- Two leaf data with the same selected values agree at every selected leaf. -/
theorem leaf_eq_of_selectedValues {α : Type} {sk : Skeleton} (leaves leaves' : LeafData α sk)
    (sel : LeafData Bool sk)
    (h : InductiveMerkleTree.selectedValues leaves sel = InductiveMerkleTree.selectedValues leaves' sel)
    (idx : SkeletonLeafIndex sk) (hs : sel.get idx = true) : leaves.get idx = leaves'.get idx := by
  rw [← selectedValueAt_selectedValues idx leaves sel hs,
    ← selectedValueAt_selectedValues idx leaves' sel hs]
  congr 1


theorem friWords_get (L : FriLeaves (ω := ω) s) (i : Fin k)
    (h : 2 * i.val + 1 < (Fin.vsum fun (_ : Fin k) ↦ 2) + 2 + 1)
    (m : FriMsg (ω := ω) s d l i.val h) (lf : SkeletonLeafIndex (L.skel i)) :
    (friWords s d l L i h m).get lf = friMsgEquivFun s d l i.val h i.2 m (L.idx i lf) := by
  unfold friWords
  exact congrFun (LeafData.get_ofFun _) lf

/-- **Word agreement on the selection**: two messages with the same selected leaf values are equal
at every selected evaluation point. -/
theorem words_agree (L : FriLeaves (ω := ω) s) (i : Fin k)
    (h : 2 * i.val + 1 < (Fin.vsum fun (_ : Fin k) ↦ 2) + 2 + 1)
    (m m' : FriMsg (ω := ω) s d l i.val h) (sel : LeafData Bool (L.skel i))
    (hsel : InductiveMerkleTree.selectedValues (friWords s d l L i h m) sel =
      InductiveMerkleTree.selectedValues (friWords s d l L i h m') sel)
    (y : wordDom (ω := ω) s i.val) (hy : sel.get ((L.idx i).symm y) = true) :
    friMsgEquivFun s d l i.val h i.2 m y = friMsgEquivFun s d l i.val h i.2 m' y := by
  have := leaf_eq_of_selectedValues _ _ sel hsel _ hy
  rw [friWords_get, friWords_get, Equiv.apply_symm_apply] at this
  exact this


theorem friRel_of_eq (xs : Fin l → (ω.subdomain 0).toFinset)
    (j : Fin ((Fin.vsum fun (_ : Fin k) ↦ 2) + 2 + 1)) (m : (pSpec k (ω := ω) s l).«Type» j)
    (hq : ∀ h : j = (queryChallenge (ω := ω) s l).val,
      cast (queryChallenge_type s l) (xp h m) = xs) :
    friRel s l hs xs j m m :=
  ⟨fun _ _ => rfl, fun _ => rfl, fun h => ⟨hq h, hq h⟩, fun _ _ _ _ => rfl⟩

/-- A merkle-round message position: relatedness from agreement of the words on `readPts`. -/
theorem friRel_merkle (xs : Fin l → (ω.subdomain 0).toFinset) (i : Fin k)
    (hh : 2 * i.val + 1 < (Fin.vsum fun (_ : Fin k) ↦ 2) + 2 + 1)
    (m m' : FriMsg (ω := ω) s d l i.val hh)
    (hw : ∀ y : wordDom (ω := ω) s i.val, y ∈ readPts s l hs xs ⟨i.val + 1, Nat.succ_lt_succ i.2⟩ →
      friMsgEquivFun s d l i.val hh i.2 m y = friMsgEquivFun s d l i.val hh i.2 m' y) :
    friRel s l hs xs ⟨2 * i.val + 1, hh⟩ (m.1 : (pSpec k (ω := ω) s l).«Type» ⟨2 * i.val + 1, hh⟩) m'.1 := by
  have hk := friLength (k := k)
  have hMw : ∀ (h : (⟨2 * i.val + 1, hh⟩ : Fin ((Fin.vsum fun (_ : Fin k) ↦ 2) + 2 + 1)) =
      (nonfinalMessage (ω := ω) s l i).val) (mm : FriMsg (ω := ω) s d l i.val hh),
      (cast (nonfinalMessage_type s l i) (xp h mm.1) : wordDom (ω := ω) s i.val → F) =
        friMsgEquivFun s d l i.val hh i.2 mm := by
    intro h mm
    apply eq_of_heq
    refine (cast_heq _ _).trans ((cast_heq _ _).trans ?_)
    exact (cast_heq _ _).symm
  refine ⟨fun i' h => ?_, fun h => ?_, fun h => ?_, fun i' h y hy => ?_⟩
  · exact absurd (congrArg Fin.val h) (by simp only [foldChallenge_val]; omega)
  · exact absurd (congrArg Fin.val h) (by simp only [finalMessage_val]; omega)
  · exact absurd (congrArg Fin.val h) (by simp only [queryChallenge_val]; omega)
  · have hii : i' = i := Fin.ext (by have := congrArg Fin.val h; simp only [nonfinalMessage_val] at this; omega)
    subst hii
    show (cast _ (xp h m.1) : wordDom (ω := ω) s i'.val → F) y = (cast _ (xp h m'.1) : wordDom (ω := ω) s i'.val → F) y
    rw [hMw h m, hMw h m']
    exact hw y hy


end FriRel

/-! ## Paths of the mask -/

section PathLevel

variable [∀ j, SampleableType ((pSpec k (ω := ω) s l).Challenge j)]
variable (L : FriLeaves (ω := ω) s) (Dg : Type) [Finite Dg] [DecidableEq Dg] (enc : F ↪ Dg)
  (Op : Type) [Finite Op] [DecidableEq Op]

theorem friAlt_r : (friAlt (ω := ω) s d l).r = k + 1 := rfl

/-- A base path of the merkle part of the mask, as a native FRI tail path. -/
def toTail : (i c : ℕ) → (h : i + c = k) →
    (protocol (baseRounds Dg (friMerkleMask s d l L Dg enc i c h))).tree.ExecutionPath →
    (protocol ((friAlt (ω := ω) s d l).tailRounds i (c + 1)
      (by have := friAlt_r (ω := ω) s d l; omega))).tree.ExecutionPath
  | _, 0, _, q => q
  | i, c + 1, h, q => ⟨q.1, q.2.1, toTail i.succ c (by omega) q.2.2⟩

/-- A base path of the mask as a native FRI path. -/
def toFriPath (q : (protocol (baseRounds Dg (friMask s d l L Dg enc))).tree.ExecutionPath) :
    (protocol (friRounds (ω := ω) s d l)).tree.ExecutionPath :=
  ⟨q.1, q.2.1, toTail s d l L Dg enc 0 k (by omega) q.2.2⟩

/-- The acceptance predicate on base paths of the mask (`friAccepts` of the decoded native path). -/
noncomputable def friAccepts' (hdom : 2 ^ (∑ j, (s j).val) * d.val ≤ 2 ^ n) {Salt : Type}
    (z : FriStmt (ω := ω) s × Salt)
    (q : (protocol (baseRounds Dg (friMask s d l L Dg enc))).tree.ExecutionPath) : Bool :=
  friAccepts s d l hdom z (toFriPath s d l L Dg enc q)

/-- The query vector of a compiled path (the challenge of the clear final round). -/
def XsOf : (i c : ℕ) → (h : i + c = k) →
    (protocol (compiledRoundsK Dg Op (friMerkleMask s d l L Dg enc i c h))).tree.ExecutionPath →
    (Fin l → (ω.subdomain 0).toFinset)
  | i, 0, h, p => cast (queryChallenge_type (ω := ω) s l)
      (xp (a := ⟨2 * i + 2, by have := friLength (k := k); omega⟩) (b := (queryChallenge s l).val)
        (Fin.ext (by simp only [queryChallenge_val]; omega)) p.2.1)
  | i, c + 1, h, p => XsOf i.succ c (by omega) p.2.2

variable (hs : (∑ j, (s j).val) ≤ n)

/-- The selectors of the openings cover the positions read for the query vector `xs`. -/
def Covers (xs : Fin l → (ω.subdomain 0).toFinset) : (i c : ℕ) → (h : i + c = k) →
    OpenAll Dg (merkleSkels (friMerkleMask s d l L Dg enc i c h)) → Prop
  | _, 0, _, _ => True
  | i, c + 1, h, (o, os) =>
      (∀ y : wordDom (ω := ω) s i, y ∈ readPts s l hs xs ⟨i + 1, by omega⟩ →
        o.selector.get ((L.idx ⟨i, by omega⟩).symm y) = true) ∧
      Covers xs i.succ c (by omega) os


/-- Two base paths of the merkle part of the mask that agree with the same compiled path (and whose
selectors cover `readPts`) are `friRel`-related step by step. -/
theorem stepRel_of_agrees (xs : Fin l → (ω.subdomain 0).toFinset) :
    (c i : ℕ) → (h : i + c = k) →
    (os : OpenAll Dg (merkleSkels (friMerkleMask s d l L Dg enc i c h))) →
    (p : (protocol (compiledRoundsK Dg Op (friMerkleMask s d l L Dg enc i c h))).tree.ExecutionPath) →
    (q q' : (protocol (baseRounds Dg (friMerkleMask s d l L Dg enc i c h))).tree.ExecutionPath) →
    XsOf s d l L Dg enc Op i c h p = xs →
    Agrees (friMerkleMask s d l L Dg enc i c h) os p q →
    Agrees (friMerkleMask s d l L Dg enc i c h) os p q' →
    Covers s d l L Dg enc hs xs i c h os →
    StepRel (friAlt (ω := ω) s d l) (friRel s l hs xs) i (c + 1)
      (by have := friAlt_r (ω := ω) s d l; omega)
      (toTail s d l L Dg enc i c h q) (toTail s d l L Dg enc i c h q')
  | 0, i, h, os, p, q, q', hx, hA, hA', _ => by
      obtain ⟨hm, hc, -⟩ := hA
      obtain ⟨hm', hc', -⟩ := hA'
      have hk := friLength (k := k)
      have hq : q.1 = q'.1 := hm.symm.trans hm'
      refine ⟨?_, ?_, trivial⟩
      · change friRel s l hs xs ⟨2 * i + 1, by omega⟩ ((friAlt (ω := ω) s d l).emb i _ q.1)
          ((friAlt (ω := ω) s d l).emb i _ q'.1)
        rw [← hq]
        exact friRel_of_eq s l hs xs _ _ (fun h' => absurd (congrArg Fin.val h') (by
          simp only [queryChallenge_val]; omega))
      · have hqq : q.2.1 = q'.2.1 := hc.symm.trans hc'
        change friRel s l hs xs ⟨2 * i + 2, by omega⟩ q.2.1 q'.2.1
        rw [← hqq]
        refine friRel_of_eq s l hs xs _ _ (fun h' => ?_)
        rw [← hx]
        have : q.2.1 = p.2.1 := hc.symm
        rw [this]
        rfl
  | c + 1, i, h, (o, os), p, q, q', hx, hA, hA', ⟨hcov, hC⟩ => by
      obtain ⟨hc, hw, hrest⟩ := hA
      obtain ⟨hc', hw', hrest'⟩ := hA'
      have hk := friLength (k := k)
      have hqq : q.2.1 = q'.2.1 := hc.symm.trans hc'
      refine ⟨?_, ?_, stepRel_of_agrees xs c i.succ (by omega) os p.2.2 q.2.2 q'.2.2 hx hrest hrest' hC⟩
      · exact friRel_merkle s d l hs xs ⟨i, by omega⟩ _ q.1 q'.1 (fun y hy =>
          words_agree s d l L ⟨i, by omega⟩ _ q.1 q'.1 o.selector (hw.symm.trans hw') y (hcov y hy))
      · change friRel s l hs xs ⟨2 * i + 2, by omega⟩ q.2.1 q'.2.1
        rw [← hqq]
        exact friRel_of_eq s l hs xs _ _ (fun h' => absurd (congrArg Fin.val h') (by
          simp only [queryChallenge_val]; omega))


variable (hdom : 2 ^ (∑ j, (s j).val) * d.val ≤ 2 ^ n)

/-- **The FRI local check** of the succinct verifier. It reads the compiled path (roots, challenges,
final polynomial) and the openings only: the selectors cover the query cosets
(`Covers`), and some words consistent with the opened values make the legacy verifier accept
(by `fri_queryOnly`, then all of them do). -/
noncomputable def friLocal
    (decode : Op → OpenAll Dg (merkleSkels (friMask s d l L Dg enc))) {Salt : Type}
    (z : FriStmt (ω := ω) s × Salt)
    (p : (protocol (compiledRoundsK Dg Op (friMask s d l L Dg enc))).tree.ExecutionPath) : Bool :=
  open Classical in
  decide (Covers s d l L Dg enc (round_bound hdom)
      (XsOf s d l L Dg enc Op 0 k (by omega) p.2.2) 0 k (by omega)
      (decode (pathRootsK Dg Op (friMask s d l L Dg enc) p).2) ∧
    ∃ q0 : (protocol (baseRounds Dg (friMask s d l L Dg enc))).tree.ExecutionPath,
      Agrees (friMask s d l L Dg enc) (decode (pathRootsK Dg Op (friMask s d l L Dg enc) p).2) p q0 ∧
        friAccepts' s d l L Dg enc hdom z q0 = true)

/-- **The FRI query-only law.** The legacy FRI verifier (`friAccepts` on the decoded native path)
reads each committed word `f_i` only at its query cosets: if the local check accepts a compiled path
`p`, then the in-the-clear check accepts every path `q` that agrees with `p` (same clear messages
and challenges, and the decoded opened values at the opened leaves). -/
theorem fri_queryOnly
    (decode : Op → OpenAll Dg (merkleSkels (friMask s d l L Dg enc))) {Salt : Type} :
    QueryOnly (friMask s d l L Dg enc) decode
      (friAccepts' s d l L Dg enc hdom (Salt := Salt))
      (friLocal s d l L Dg enc Op hdom decode) := by
  classical
  intro z p q hag hl
  unfold friLocal at hl
  simp only [decide_eq_true_eq] at hl
  obtain ⟨hcov, q0, hag0, hacc0⟩ := hl
  have hs := round_bound hdom
  have hk := friLength (k := k)
  set xs := XsOf s d l L Dg enc Op 0 k (by omega) p.2.2 with hxs
  have hrel : PrefRel (c := Fin.last _) (friRel s l hs xs)
      ((friAlt (ω := ω) s d l).pathTranscript (toFriPath s d l L Dg enc q0))
      ((friAlt (ω := ω) s d l).pathTranscript (toFriPath s d l L Dg enc q)) := by
    refine pathTranscript_rel _ _ _ _ ?_ ?_
    · have hh : q0.2.1 = q.2.1 := hag0.2.1.symm.trans hag.2.1
      change friRel s l hs xs ⟨0, by omega⟩ q0.2.1 q.2.1
      rw [← hh]
      exact friRel_of_eq s l hs xs _ _ (fun h' => absurd (congrArg Fin.val h') (by
        simp only [queryChallenge_val]; omega))
    · exact stepRel_of_agrees s d l L Dg enc Op hs xs k 0 (by omega) _ p.2.2 q0.2.2 q.2.2 rfl
        hag0.2.2 hag.2.2 hcov
  have := queryBad_congr_of_rel s d l hs (initialOracle s z.1) _ _ xs hrel
  unfold friAccepts' at hacc0 ⊢
  rw [friAccepts_iff] at hacc0 ⊢
  exact this.mp hacc0

end PathLevel

end NockvmE2E.Merkle.Fri
