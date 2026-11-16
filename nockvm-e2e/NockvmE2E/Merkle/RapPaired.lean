/-
Merkle (B) file 13: the RAP protocol as a masked compiled protocol.

The staged RAP `sRounds` has one round per column block. We mask it: the round-0 message and the final
message are in the clear, the column message of block `r < nb` is merkle (a perfect or arbitrary
skeleton and a codec). The paired protocol is `pairedRoundsK Dg (rapMask …)`. There is no `Alternating`
structure for RAP, so the native bridge extractor of `Rap/Bridge.lean` is rebuilt on the paired rounds
(it reads the column `c.1` and forgets the root), and the `rap_succinct_sound_deep` argument is run on it.
-/
import NockvmE2E.Succ.Deep
import NockvmE2E.Merkle.Opening
import ToMathlib.Data.IndexedBinaryTree.Perfect
import ToMathlib.Data.IndexedBinaryTree.Equiv
import Mathlib.FieldTheory.Finite.Basic

open OracleComp OracleSpec Polynomial
open Interaction.Oracle Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir
open scoped ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NockvmE2E.Merkle.RapP

open NockvmE2E.Rap NockvmE2E.Succ NockvmE2E.Merkle

/-! ## 1. The mask -/

section Mask

variable {ι β : Type} (colRound : ι → ℕ) (F Dg : Type)

/-- The leaf layout and codec of the committed column blocks: for every block `r` a skeleton and an
identification of the block's columns with leaf data over `F`, and a codec `F ↪ Dg`. -/
structure RapMaskData {ι β : Type} (colRound : ι → ℕ) (F Dg : Type) where
  skel : ℕ → BinaryTree.Skeleton
  /-- The leaf type of block `r`. For a block with a column it is `F` (see `PointMaskData.hF`); a block
  without columns (`Cols r` a singleton, e.g. the DEEP blocks `r > P.R + 1`) may use any leaf type
  ( Step 0: previously `F` for every block, which is uninhabitable for non-trivial `F`). -/
  FB : ℕ → Type
  words : ∀ r : ℕ, Cols colRound β r ≃ BinaryTree.LeafData (FB r) (skel r)
  ne : ∀ r, Nonempty (FB r)
  enc : ∀ r, FB r ↪ Dg

variable {colRound F Dg}

/-- The perfect-tree layout: block `r` is a word on `2 ^ m r` leaves (`e r`), perfect skeleton. -/
noncomputable def perfectMaskData (m : ℕ → ℕ) (e : ∀ r, Cols colRound β r ≃ (Fin (2 ^ m r) → F))
    (ne : Nonempty F) (enc : F ↪ Dg) : RapMaskData colRound (β := β) F Dg where
  skel r := BinaryTree.Skeleton.perfect (m r)
  FB _ := F
  words r := (e r).trans
    ((Equiv.arrowCongr (BinaryTree.SkeletonLeafIndex.perfectEquiv (m r)) (Equiv.refl F)).trans
      (BinaryTree.LeafData.equivIndexFun (BinaryTree.Skeleton.perfect (m r))).symm)
  ne _ := ne
  enc _ := enc

variable (Φ : CoinFrame) (K : Type) [Fintype K] [DecidableEq K] [SampleableType K]
  [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
  [Finite Dg] [DecidableEq Dg]
  (md : RapMaskData colRound (β := β) F Dg)
  (M0 Mfin : Type) [DecidableEq M0] [Finite M0] [DecidableEq Mfin] [Finite Mfin]
  (I0 : OracleInterface M0) (I : (r : ℕ) → OracleInterface (Cols colRound β r))
  (Ifin : OracleInterface Mfin)

/-- The masked column rounds `r, …, r+k-1` (merkle), then the final round (clear). -/
noncomputable def rapMerkleMask : (r k : ℕ) → MRounds Dg
  | _, 0 => [⟨unitRound Mfin Ifin, .clear⟩]
  | r, k + 1 =>
      ⟨colRoundR Φ K β colRound I r, .merkle (md.skel r) (md.FB r) (md.ne r) (md.enc r) (md.words r)⟩ ::
        rapMerkleMask r.succ k

/-- **The RAP round mask**: `M0` and the final message clear, the column blocks `0 … nb-1` merkle. -/
noncomputable def rapMask (nb : ℕ) : MRounds Dg :=
  ⟨unitRound M0 I0, .clear⟩ :: rapMerkleMask Φ K md Mfin I Ifin 0 nb

theorem baseRounds_rapMerkleMask : (r k : ℕ) →
    baseRounds Dg (rapMerkleMask Φ K md Mfin I Ifin r k) =
      colRounds Φ K β colRound I (unitRound Mfin Ifin) r k
  | _, 0 => rfl
  | r, k + 1 => congrArg (_ :: ·) (baseRounds_rapMerkleMask r.succ k)

/-- The mask is a mask of the staged-RAP rounds. -/
theorem baseRounds_rapMask (nb : ℕ) :
    baseRounds Dg (rapMask Φ K md M0 Mfin I0 I Ifin nb) = rapRounds Φ K β colRound M0 Mfin I0 I Ifin nb :=
  congrArg (_ :: ·) (baseRounds_rapMerkleMask Φ K md Mfin I Ifin 0 nb)

variable (colRound β Dg)

/-- The paired column rounds. -/
noncomputable def pairedColRounds : ℕ → ℕ → List Round
  | _, 0 => [unitRound Mfin Ifin]
  | r, k + 1 => pairedRound Dg (colRoundR Φ K β colRound I r) :: pairedColRounds r.succ k

/-- **The paired RAP rounds**: `[M0 | Unit]`, then `[(Cols r, root) | Block r]`, then `[Mfin | Unit]`. -/
noncomputable def rapPairedRounds (nb : ℕ) : List Round :=
  unitRound M0 I0 :: pairedColRounds β colRound Dg Φ K Mfin I Ifin 0 nb

theorem pairedRoundsK_rapMerkleMask : (r k : ℕ) →
    pairedRoundsK Dg (rapMerkleMask Φ K md Mfin I Ifin r k) = pairedColRounds β colRound Dg Φ K Mfin I Ifin r k
  | _, 0 => rfl
  | r, k + 1 => congrArg (_ :: ·) (pairedRoundsK_rapMerkleMask r.succ k)

/-- **The round equality**: the paired RAP rounds are the masked paired rounds. -/
theorem pairedRoundsK_rapMask (nb : ℕ) :
    pairedRoundsK Dg (rapMask Φ K md M0 Mfin I0 I Ifin nb) = rapPairedRounds β colRound Dg Φ K M0 Mfin I0 I Ifin nb :=
  congrArg (_ :: ·) (pairedRoundsK_rapMerkleMask (β := β) (colRound := colRound) (Dg := Dg) (Φ := Φ) (K := K) (md := md) (Mfin := Mfin) (I := I) (Ifin := Ifin) 0 nb)

theorem pairedColRounds_length : (r k : ℕ) →
    (pairedColRounds β colRound Dg Φ K Mfin I Ifin r k).length = k + 1
  | _, 0 => rfl
  | r, k + 1 => by simp [pairedColRounds, pairedColRounds_length r.succ k]

theorem rapPairedRounds_length (nb : ℕ) :
    (rapPairedRounds β colRound Dg Φ K M0 Mfin I0 I Ifin nb).length = nb + 2 := by
  simp [rapPairedRounds, pairedColRounds_length]

theorem rapRounds_length (nb : ℕ) :
    (rapRounds Φ K β colRound M0 Mfin I0 I Ifin nb).length = nb + 2 := by
  simp [rapRounds, colRounds_length]

end Mask

open Classical

/-! ## 2. The paired bridge -/

section Bridge

variable {Φ : CoinFrame} {K : Type} [Fintype K] [DecidableEq K] [SampleableType K]
  {ι β : Type} {colRound : ι → ℕ} {F Dg : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
  [Inhabited β] [Inhabited K] [Finite Dg] [DecidableEq Dg]
  (md : RapMaskData colRound (β := β) F Dg)
  (R : RapStatement Φ K ι β colRound)
  [DecidableEq R.M0] [Finite R.M0] [DecidableEq R.Mfin] [Finite R.Mfin]
  (blk : BadSummand Φ K (Tr ι β) (TracesStaged Φ colRound) → ℕ)
  (I0 : OracleInterface R.M0) (I : (r : ℕ) → OracleInterface (Cols colRound β r))
  (Ifin : OracleInterface R.Mfin) (nb : ℕ)

/-- The paired column rounds `r, …` of the mask. -/
noncomputable abbrev PR (r k : ℕ) : List Round :=
  pairedRoundsK Dg (rapMerkleMask Φ K md R.Mfin I Ifin r k)

theorem PR_length : (r k : ℕ) → (PR (Φ := Φ) (K := K) md (R := R) I Ifin r k).length = k + 1
  | _, 0 => rfl
  | r, k + 1 => by
      show (PR (Φ := Φ) (K := K) md (R := R) I Ifin r.succ k).length + 1 = k + 1 + 1
      rw [PR_length r.succ k]

/-- The trivial extractor on the paired column rounds (reads the column `c.1`, forgets the root). -/
noncomputable def extColsP (m0 : R.M0) : (r k : ℕ) → (tr : Tr ι β) → (χ : Coins Φ K) →
    RoundExtractor (protocol (PR (Φ := Φ) (K := K) md (R := R) I Ifin r k)).tree
      (ks (St R blk m0 tr χ r))
  | r, 0, tr, χ => fun _ =>
      ⟨ks (St R blk m0 tr χ r), id, fun _ => ⟨ks (St R blk m0 tr χ r), id, PUnit.unit⟩⟩
  | r, k + 1, tr, χ => fun c =>
      ⟨ks (St R blk m0 (setCols r c.1 tr) χ r), id, fun b =>
        ⟨ks (St R blk m0 (setCols r c.1 tr) (setBlock r b χ) (r + 1)), id,
          extColsP m0 (r + 1) k (setCols r c.1 tr) (setBlock r b χ)⟩⟩

/-- The traces, coins and final message a paired path writes. -/
def finalOfPK : (r k : ℕ) → Tr ι β → Coins Φ K →
    (protocol (PR (Φ := Φ) (K := K) md (R := R) I Ifin r k)).tree.ExecutionPath →
    Tr ι β × Coins Φ K × R.Mfin
  | _, 0, tr, χ, path => (tr, χ, path.1)
  | r, k + 1, tr, χ, path =>
      finalOfPK (r + 1) k (setCols r path.1.1 tr) (setBlock r path.2.1 χ) path.2.2

theorem extColsP_terminal (m0 : R.M0) : ∀ (r k : ℕ) (tr : Tr ι β) (χ : Coins Φ K) path,
    (extColsP md R blk I Ifin m0 r k tr χ).terminalState path =
      ks (St R blk m0 (finalOfPK md R I Ifin r k tr χ path).1 (finalOfPK md R I Ifin r k tr χ path).2.1
        (r + k))
  | _, 0, _, _, _ => rfl
  | r, k + 1, tr, χ, path => by
    have h := extColsP_terminal m0 (r + 1) k (setCols r path.1.1 tr) (setBlock r path.2.1 χ) path.2.2
    rw [show r + 1 + k = r + (k + 1) by omega] at h
    exact h

theorem extColsP_preserving (hc : ∀ m0, ∀ s ∈ R.summands m0, Local s (blk s)) (m0 : R.M0) :
    ∀ (r k : ℕ) (tr : Tr ι β) (χ : Coins Φ K),
      (extColsP md R blk I Ifin m0 r k tr χ).IsProverPreserving
        (protocol (PR (Φ := Φ) (K := K) md (R := R) I Ifin r k)).roles
  | _, 0, _, _ => ⟨fun _ _ h => h, fun _ => ⟨fun _ hrole => (nomatch hrole), fun _ => trivial⟩⟩
  | r, k + 1, tr, χ => ⟨fun c _ h => st_setCols hc m0 r c.1 tr χ h,
      fun c => ⟨fun _ hrole => (nomatch hrole),
        fun b => extColsP_preserving hc m0 (r + 1) k (setCols r c.1 tr) (setBlock r b χ)⟩⟩

theorem extColsP_bounded (hc : ∀ m0, ∀ s ∈ R.summands m0, Local s (blk s)) (m0 : R.M0) :
    ∀ (r k : ℕ) (tr : Tr ι β) (χ : Coins Φ K)
      (errs : RoundErrors (PR (Φ := Φ) (K := K) md (R := R) I Ifin r k)),
      (∀ j : Fin (PR (Φ := Φ) (K := K) md (R := R) I Ifin r k).length, (j : ℕ) < k →
        roundBound R blk m0 (r + j) ≤ errs j) →
      (extColsP md R blk I Ifin m0 r k tr χ).IsLocallyBounded
        (protocol (PR (Φ := Φ) (K := K) md (R := R) I Ifin r k)).roles
        (roundErrorSchedule (PR (Φ := Φ) (K := K) md (R := R) I Ifin r k) errs)
  | r, 0, tr, χ, errs, _ => by
    intro _
    refine ⟨?_, fun _ => trivial⟩
    rw [_root_.RoundByRound.GameFamily.isBounded_iff]
    intro _ _
    refine le_trans (le_of_eq ?_) zero_le
    exact prEvent_eq_zero_of_forall_not _ _ (fun _ ⟨_, h0, h1⟩ => h0 h1)
  | r, k + 1, tr, χ, errs, herr => by
    intro c
    refine ⟨?_, fun b => extColsP_bounded hc m0 (r + 1) k (setCols r c.1 tr) (setBlock r b χ)
      (fun j => errs j.succ) (fun j hj => ?_)⟩
    · rw [_root_.RoundByRound.GameFamily.isBounded_iff]
      intro _ _
      have h0 := herr ⟨0, by simp [PR_length]⟩ (by simp)
      simp only [Nat.add_zero] at h0
      refine le_trans ?_ h0
      refine le_trans (prEvent_mono _ _ (fun b : Block Φ K r =>
          ∃ s ∈ R.summands m0, blk s = r ∧ s.mem (setCols r c.1 tr) (setBlock r b χ)) ?_) ?_
      · rintro b ⟨_, h0', h1'⟩
        exact st_setBlock hc m0 r (setCols r c.1 tr) χ b h0' h1'
      · refine le_trans (prEvent_list_exists_le _ (fun s => blk s = r)
          (fun s b => s.mem (setCols r c.1 tr) (setBlock r b χ)) _) ?_
        unfold roundBound
        refine le_of_eq_of_le rfl (List.sum_le_sum (fun s hs => ?_))
        by_cases hb : blk s = r
        · simp only [hb, ite_true]
          exact mem_setBlock_prob s (hb ▸ hc m0 s hs) _ _
        · simp [hb]
    · have := herr j.succ (by simp; omega)
      rwa [Fin.val_succ, show r + (↑j + 1) = r + 1 + ↑j by omega] at this

/-- **The round extractor of the paired RAP protocol** (trivial witnesses). -/
noncomputable def rapExtractorP :
    RoundExtractor (protocol (pairedRoundsK Dg (rapMask Φ K md R.M0 R.Mfin I0 I Ifin nb))).tree
      (ks R.Holds) :=
  fun m0 => ⟨ks R.Holds, id, fun _ =>
    ⟨ks (St R blk m0 (fun _ => default) (fun _ => default) 0), id,
      extColsP md R blk I Ifin m0 0 nb (fun _ => default) (fun _ => default)⟩⟩

/-- The verifier's decision on a full path of the paired protocol. -/
def rapAcceptsP (path : (protocol (pairedRoundsK Dg (rapMask Φ K md R.M0 R.Mfin I0 I Ifin nb))).tree.ExecutionPath) :
    Prop :=
  let f := finalOfPK md R I Ifin 0 nb (fun _ => default) (fun _ => default) path.2.2
  R.Accepts path.1 f.1 f.2.2 f.2.1

/-- The error schedule: `err r` at the column round `r` (index `r+1`), `0` at the two `Unit` rounds. -/
def rapErrs (nb : ℕ) (err : ℕ → ℝ≥0∞) (j : ℕ) : ℝ≥0∞ :=
  if 1 ≤ j ∧ j ≤ nb then err (j - 1) else 0

variable {md R blk I0 I Ifin nb}

theorem rapExtractorP_terminal
    (path : (protocol (pairedRoundsK Dg (rapMask Φ K md R.M0 R.Mfin I0 I Ifin nb))).tree.ExecutionPath) :
    (rapExtractorP md R blk I0 I Ifin nb).terminalState path =
      ks (St R blk path.1 (finalOfPK md R I Ifin 0 nb (fun _ => default) (fun _ => default) path.2.2).1
        (finalOfPK md R I Ifin 0 nb (fun _ => default) (fun _ => default) path.2.2).2.1 (0 + nb)) :=
  extColsP_terminal md R blk I Ifin path.1 0 nb _ _ path.2.2

theorem rapExtractorP_preserving (hC : Certificate R blk nb) :
    (rapExtractorP md R blk I0 I Ifin nb).IsProverPreserving
      (protocol (pairedRoundsK Dg (rapMask Φ K md R.M0 R.Mfin I0 I Ifin nb))).roles :=
  ⟨fun _ _ h => h, fun m0 => ⟨fun _ hrole => (nomatch hrole),
    fun _ => extColsP_preserving md R blk I Ifin hC.local_ m0 0 nb _ _⟩⟩

theorem rapExtractorP_bounded (hC : Certificate R blk nb) (err : ℕ → ℝ≥0∞)
    (herr : ∀ m0 r, roundBound R blk m0 r ≤ err r) :
    (rapExtractorP md R blk I0 I Ifin nb).IsLocallyBounded
      (protocol (pairedRoundsK Dg (rapMask Φ K md R.M0 R.Mfin I0 I Ifin nb))).roles
      (roundErrorSchedule (pairedRoundsK Dg (rapMask Φ K md R.M0 R.Mfin I0 I Ifin nb))
        (fun j => rapErrs nb err j)) := by
  intro m0
  refine ⟨?_, fun _ => extColsP_bounded md R blk I Ifin hC.local_ m0 0 nb _ _ _ (fun j hj => ?_)⟩
  · rw [_root_.RoundByRound.GameFamily.isBounded_iff]
    intro _ _
    refine le_trans (le_of_eq ?_) zero_le
    refine prEvent_eq_zero_of_forall_not _ _ (fun _ ⟨_, h0, h1⟩ => h0 ?_)
    rcases h1 with h | ⟨_, _, hlt, _⟩
    · exact h
    · exact absurd hlt (Nat.not_lt_zero _)
  · refine le_trans (herr m0 _) (le_of_eq ?_)
    simp only [rapErrs, Fin.val_succ]
    rw [ite_eq_left_iff.mpr (fun h => absurd ⟨by omega, by omega⟩ h)]
    congr 1
    omega

theorem rapExtractorP_output (hC : Certificate R blk nb)
    (path : (protocol (pairedRoundsK Dg (rapMask Φ K md R.M0 R.Mfin I0 I Ifin nb))).tree.ExecutionPath)
    (hacc : rapAcceptsP md R I0 I Ifin nb path) :
    ((rapExtractorP md R blk I0 I Ifin nb).terminalState path).holds
      (rapExtractorP_terminal (md := md) (R := R) (blk := blk) path ▸ PUnit.unit) := by
  refine holds_of_eq_ks (rapExtractorP_terminal path) _ ?_
  by_cases hf : ∃ s ∈ R.summands path.1,
      s.mem (finalOfPK md R I Ifin 0 nb (fun _ => default) (fun _ => default) path.2.2).1
        (finalOfPK md R I Ifin 0 nb (fun _ => default) (fun _ => default) path.2.2).2.1
  · obtain ⟨s, hs, hm⟩ := hf
    exact Or.inr ⟨s, hs, by have := hC.blk_lt path.1 s hs; omega, hm⟩
  · push Not at hf
    exact Or.inl (hC.sound _ _ _ _ hacc hf)

/-- **The paired bridge**: `rap_singleSalt_knowledge_soundness` for the paired protocol
`pairedRoundsK Dg (rapMask …)`. -/
theorem rapP_knowledge_soundness (hC : Certificate R blk nb) (err : ℕ → ℝ≥0∞)
    (herr : ∀ m0 r, roundBound R blk m0 r ≤ err r)
    {Statement GlobalSalt Witness : Type} [DecidableEq Statement] [DecidableEq GlobalSalt]
    (guards : GuardSchedule (Statement × GlobalSalt) PUnit
      (pairedRoundsK Dg (rapMask Φ K md R.M0 R.Mfin I0 I Ifin nb)))
    (adversary : SingleSaltAdversary Statement GlobalSalt Witness
      (pairedRoundsK Dg (rapMask Φ K md R.M0 R.Mfin I0 I Ifin nb)))
    (Z : Set (Statement × GlobalSalt)) :
    Pr{let joint ← (randomOracleLoggedRun (singleSaltAcceptedExecution
      (pairedRoundsK Dg (rapMask Φ K md R.M0 R.Mfin I0 I Ifin nb)) guards
      (fun _ path => decide (rapAcceptsP md R I0 I Ifin nb path)) adversary) ∅)}[
      badStoppedRelation (fun _ => ks R.Holds) (fun _ => rapExtractorP md R blk I0 I Ifin nb)
        (fun _ _ => R.Holds) (fun _ _ _ => True)
        (fun _ path _ => rapExtractorP_terminal (md := md) (R := R) (blk := blk) path ▸ PUnit.unit) Z
        joint.1.1.1] ≤
    expectedFreshQueryCharge (singleSaltAcceptedExecution
      (pairedRoundsK Dg (rapMask Φ K md R.M0 R.Mfin I0 I Ifin nb)) guards
      (fun _ path => decide (rapAcceptsP md R I0 I Ifin nb path)) adversary)
      (keyError (fun j => rapErrs nb err j)) :=
  singleSalt_knowledge_soundness guards (fun _ path => decide (rapAcceptsP md R I0 I Ifin nb path))
    (fun j => rapErrs nb err j) adversary (fun _ => ks R.Holds)
    (fun _ => rapExtractorP md R blk I0 I Ifin nb) Z
    (fun _ _ => rapExtractorP_preserving hC) (fun _ _ => rapExtractorP_bounded hC err herr)
    (fun _ _ => R.Holds) (fun _ _ _ => True)
    (fun _ path _ => rapExtractorP_terminal (md := md) (R := R) (blk := blk) path ▸ PUnit.unit)
    (fun _ _ => Iff.rfl)
    (fun _ path _ hacc _ => rapExtractorP_output hC path (of_decide_eq_true hacc))


/-! ### The base acceptance on masked base paths, and its pairing -/

variable (md R I0 I Ifin nb)

/-- The traces, coins and final message a path of the in-the-clear masked rounds writes. -/
def finalOfBK : (r k : ℕ) → Tr ι β → Coins Φ K →
    (protocol (baseRounds Dg (rapMerkleMask Φ K md R.Mfin I Ifin r k))).tree.ExecutionPath →
    Tr ι β × Coins Φ K × R.Mfin
  | _, 0, tr, χ, path => (tr, χ, path.1)
  | r, k + 1, tr, χ, path =>
      finalOfBK (r + 1) k (setCols r path.1 tr) (setBlock r path.2.1 χ) path.2.2

/-- The in-the-clear RAP verifier on a path of the masked base rounds (`baseRounds_rapMask`). -/
def rapAcceptsB
    (path : (protocol (baseRounds Dg (rapMask Φ K md R.M0 R.Mfin I0 I Ifin nb))).tree.ExecutionPath) :
    Prop :=
  let f := finalOfBK md R I Ifin 0 nb (fun _ => default) (fun _ => default) path.2.2
  R.Accepts path.1 f.1 f.2.2 f.2.1

variable {md R I0 I Ifin nb}

theorem finalOfBK_forget : ∀ (r k : ℕ) (tr : Tr ι β) (χ : Coins Φ K)
    (p : (protocol (PR (Φ := Φ) (K := K) md (R := R) I Ifin r k)).tree.ExecutionPath),
    finalOfBK md R I Ifin r k tr χ (forgetPath Dg (rapMerkleMask Φ K md R.Mfin I Ifin r k) p) =
      finalOfPK md R I Ifin r k tr χ p
  | _, 0, _, _, _ => rfl
  | r, k + 1, tr, χ, p => finalOfBK_forget (r + 1) k _ _ p.2.2

/-- Pairing the base verifier is the paired verifier. -/
theorem rapAcceptsB_forget
    (p : (protocol (pairedRoundsK Dg (rapMask Φ K md R.M0 R.Mfin I0 I Ifin nb))).tree.ExecutionPath) :
    rapAcceptsB md R I0 I Ifin nb (forgetPath Dg (rapMask Φ K md R.M0 R.Mfin I0 I Ifin nb) p) ↔
      rapAcceptsP md R I0 I Ifin nb p := by
  unfold rapAcceptsB rapAcceptsP
  have := finalOfBK_forget (md := md) (R := R) (I := I) (Ifin := Ifin) 0 nb (fun _ => default) (fun _ => default) p.2.2
  have h2 : (forgetPath Dg (rapMask Φ K md R.M0 R.Mfin I0 I Ifin nb) p).2.2 =
      forgetPath Dg (rapMerkleMask Φ K md R.Mfin I Ifin 0 nb) p.2.2 := rfl
  show R.Accepts p.1 _ _ _ ↔ _
  simp only [h2, this]

end Bridge

/-! ## 3. Soundness -/

/-- The errors of the paired RAP, as a number: the part of `epsilonOf` priced on each coin block. -/
noncomputable def rapEps (nb : ℕ) (err : ℕ → ℝ≥0∞) (Q : ℕ) : ℝ≥0∞ :=
  Q * Finset.univ.sup (fun j : Fin (nb + 2) => rapErrs nb err j) + ∑ j : Fin (nb + 2), rapErrs nb err j

theorem sup_sum_cast {n m : ℕ} (h : n = m) (g : ℕ → ℝ≥0∞) :
    Finset.univ.sup (fun j : Fin n => g j) = Finset.univ.sup (fun j : Fin m => g j) ∧
      ∑ j : Fin n, g j = ∑ j : Fin m, g j := by
  subst h; exact ⟨rfl, rfl⟩

section Sound

variable {Φ : CoinFrame} {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι β : Type}
  {colRound : ι → ℕ} {O : OracleInterface β}
  [SampleableType K] [Inhabited K] [Fintype ι] [DecidableEq ι]
  (R : RapStatement Φ K ι β colRound) (CS : CommitScheme β O) (plan : OpenPlan R CS)
  [Fintype CS.Com] [DecidableEq CS.Com] [Inhabited CS.Com]
  [DecidableEq R.M0] [Finite R.M0] [DecidableEq plan.Mfin] [Finite plan.Mfin]
  {F Dg : Type} [Finite Dg] [DecidableEq Dg] (md : RapMaskData colRound (β := CS.Com) F Dg)
  (I0 : OracleInterface R.M0) (I : (r : ℕ) → OracleInterface (Cols colRound CS.Com r))
  (Ifin : OracleInterface plan.Mfin) (nb : ℕ)

/-- The succinct verifier's acceptance, on paths of the masked base rounds. -/
noncomputable def rapAccB
    (path : (protocol (baseRounds Dg (rapMask Φ K md R.M0 plan.Mfin I0 I Ifin nb))).tree.ExecutionPath) :
    Bool :=
  open Classical in decide (rapAcceptsB md (sStmt R CS plan) I0 I Ifin nb path)

variable {R CS plan I0 I Ifin nb}

theorem finalOfPK_succ (A B : R.M0 → Tr ι CS.Com → plan.Mfin → Coins Φ K → Prop) :
    ∀ (r k : ℕ) (tr : Tr ι CS.Com) (χ : Coins Φ K)
      (path : (protocol (PR (Φ := Φ) (K := K) md (R := succStmt R CS plan A) I Ifin r k)).tree.ExecutionPath),
      finalOfPK md (succStmt R CS plan A) I Ifin r k tr χ path =
        finalOfPK md (succStmt R CS plan B) I Ifin r k tr χ path
  | _, 0, _, _, _ => rfl
  | r, k + 1, tr, χ, path => by
    rw [finalOfPK, finalOfPK]
    exact finalOfPK_succ A B (r + 1) k _ _ path.2.2

theorem okAcc_iff (hP : CS.PerfectlyExtractable) (m0 : R.M0) (coms : Tr ι CS.Com) (fin : plan.Mfin)
    (χ : Coins Φ K) :
    succAccepts R CS plan m0 coms fin χ ↔ okAccepts R CS plan m0 coms fin χ :=
  ⟨fun h => ⟨h, hP _ _ _ h.1⟩, fun h => h.1⟩

/-- **`rap_succinct_sound_perfect` for the paired protocol** `pairedRoundsK Dg (rapMask …)`
(`ε_CS = 0`). The accepting predicate is the succinct verifier on the paths with the roots forgotten. -/
theorem rap_paired_sound_perfect (hP : CS.PerfectlyExtractable)
    (hC : Certificate R blkOf nb) (hl : Link R CS plan) (err : ℕ → ℝ≥0∞)
    (herr : ∀ m0 r, roundBound R blkOf m0 r ≤ err r)
    {Statement GlobalSalt Witness : Type} [DecidableEq Statement] [DecidableEq GlobalSalt]
    (guards : GuardSchedule (Statement × GlobalSalt) PUnit
      (pairedRoundsK Dg (rapMask Φ K md R.M0 plan.Mfin I0 I Ifin nb)))
    (adversary : SingleSaltAdversary Statement GlobalSalt Witness
      (pairedRoundsK Dg (rapMask Φ K md R.M0 plan.Mfin I0 I Ifin nb)))
    (Q : ℕ) (queryBound : ∀ phase ∈ support (randomOracleLoggedRun adversary.withQueryLog ∅),
      (freshKeysOfLog phase.1.2).card ≤ Q) :
    Pr{let joint ← (randomOracleLoggedRun (singleSaltAcceptedExecution
        (pairedRoundsK Dg (rapMask Φ K md R.M0 plan.Mfin I0 I Ifin nb)) guards
        (pairAccepts Dg (rapMask Φ K md R.M0 plan.Mfin I0 I Ifin nb)
          (fun _ q => rapAccB R CS plan md I0 I Ifin nb q)) adversary) ∅)}[
        (∃ x, joint.1.1.1 = some x) ∧ ¬ R.Holds] ≤ rapEps nb err Q := by
  classical
  let Rok := succStmt R CS plan (okAccepts R CS plan)
  have hCok : Certificate Rok blkOf nb := certificate_ok hC hl
  have herr' : ∀ m0 r, roundBound Rok blkOf m0 r ≤ err r := fun m0 r => by
    rw [roundBound_succ]; exact herr m0 r
  have hacc : (pairAccepts Dg (rapMask Φ K md R.M0 plan.Mfin I0 I Ifin nb)
        (fun (_ : Statement × GlobalSalt) q => rapAccB R CS plan md I0 I Ifin nb q)) =
      (fun _ path => decide (rapAcceptsP md Rok I0 I Ifin nb path)) := by
    funext z p
    simp only [pairAccepts, rapAccB]
    refine decide_eq_decide.mpr ?_
    rw [rapAcceptsB_forget (md := md) (R := sStmt R CS plan)]
    unfold rapAcceptsP
    dsimp only
    rw [finalOfPK_succ md (succAccepts R CS plan) (okAccepts R CS plan) 0 nb _ _ p.2.2]
    exact okAcc_iff (R := R) (plan := plan) hP _ _ _ _
  rw [hacc]
  have hrap := rapP_knowledge_soundness (md := md) (R := Rok) (blk := blkOf) (I0 := I0) (I := I)
    (Ifin := Ifin) (nb := nb) hCok err herr' guards adversary Set.univ
  have cost := singleSalt_query_cost guards (fun _ path => decide (rapAcceptsP md Rok I0 I Ifin nb path))
    (fun j => rapErrs nb err j) adversary
  have keys := expectedSingleSaltAdversaryKeys_le_queryBound adversary Q queryBound
  have hlen : (pairedRoundsK Dg (rapMask Φ K md R.M0 plan.Mfin I0 I Ifin nb)).length = nb + 2 := by
    rw [pairedRoundsK_rapMask]; exact rapPairedRounds_length ..
  obtain ⟨hs, hsum⟩ := sup_sum_cast hlen (fun j => rapErrs nb err j)
  refine le_trans (prEvent_mono _ _ _ ?_) (hrap.trans (cost.1.trans ?_))
  · rintro ⟨⟨⟨_ | ⟨z, p, w⟩, _⟩, _⟩, _⟩ ⟨⟨x, hx⟩, hH⟩
    · simp at hx
    · exact ⟨Set.mem_univ _, trivial, hH⟩
  · unfold rapEps
    rw [← hs, ← hsum, mul_comm (Q : ℝ≥0∞)]
    exact add_le_add (mul_le_mul' le_rfl keys) cost.2

/-- The same number as the bound of `rap_succinct_sound_deep`/`rap_succinct_sound`. -/
theorem rapEps_eq_sErrors (err : ℕ → ℝ≥0∞) (Q : ℕ) :
    rapEps nb err Q = Q * Finset.univ.sup (sErrors R CS plan I0 I Ifin nb err) +
      ∑ j, sErrors R CS plan I0 I Ifin nb err j := by
  obtain ⟨hs, hsum⟩ := sup_sum_cast
    (rapRounds_length (β := CS.Com) (colRound := colRound) Φ K R.M0 plan.Mfin I0 I Ifin nb).symm
    (fun j => rapErrs nb err j)
  unfold rapEps
  rw [hs, hsum]
  rfl

/-- **`rap_hclear`**: the `hclear` hypothesis of `merkle_singleSalt_soundness` for the
RAP: over `pairedRoundsK Dg (rapMask …)`, with `pairGuards` and `pairAccepts` of the succinct verifier,
the event `z.1 ∉ L` with `L = {_ | Holds}`, and `εFS Q = rapEps nb err Q`. -/
theorem rap_hclear (hP : CS.PerfectlyExtractable)
    (hC : Certificate R blkOf nb) (hl : Link R CS plan) (err : ℕ → ℝ≥0∞)
    (herr : ∀ m0 r, roundBound R blkOf m0 r ≤ err r)
    {Statement Salt W : Type} [DecidableEq Statement] [DecidableEq Salt]
    (Op : Type) [Finite Op] [DecidableEq Op]
    (guards : GuardSchedule (Statement × Salt) PUnit
      (compiledRoundsK Dg Op (rapMask Φ K md R.M0 plan.Mfin I0 I Ifin nb)))
    (B : SingleSaltAdversary Statement Salt W
      (pairedRoundsK Dg (rapMask Φ K md R.M0 plan.Mfin I0 I Ifin nb)))
    (Q : ℕ) (queryBound : ∀ phase ∈ support (randomOracleLoggedRun B.withQueryLog ∅),
      (freshKeysOfLog phase.1.2).card ≤ Q) :
    Pr{let j ← randomOracleLoggedRun (singleSaltAcceptedExecution
        (pairedRoundsK Dg (rapMask Φ K md R.M0 plan.Mfin I0 I Ifin nb))
        (pairGuards Dg Op (rapMask Φ K md R.M0 plan.Mfin I0 I Ifin nb) guards)
        (pairAccepts Dg (rapMask Φ K md R.M0 plan.Mfin I0 I Ifin nb)
          (fun _ q => rapAccB R CS plan md I0 I Ifin nb q)) B) ∅}[
      match j.1.1.1 with
      | none => False
      | some (z, _, _) => z.1 ∉ {_x : Statement | R.Holds}] ≤ rapEps nb err Q := by
  refine le_trans (prEvent_mono _ _ _ ?_)
    (rap_paired_sound_perfect md hP hC hl err herr
      (pairGuards Dg Op (rapMask Φ K md R.M0 plan.Mfin I0 I Ifin nb) guards) B Q queryBound)
  rintro ⟨⟨⟨_ | ⟨z, path, w⟩, _⟩, _⟩, _⟩ hb
  · exact hb.elim
  · exact ⟨⟨_, rfl⟩, hb⟩

end Sound

/-! ## 4. The DEEP-extended RAP -/

section Deep

open NockvmE2E.Deep

variable {Φ : CoinFrame} {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι β : Type}
  {colRound : ι → ℕ} (P : DeepParams Φ K ι β colRound)
  [SampleableType K] [Inhabited K] [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
  [Inhabited β] {F Dg : Type} [Finite Dg] [DecidableEq Dg]
  (md : RapMaskData P.colRoundX (β := β) F Dg)

/-- The inputs of `rap_succinct_sound_deep` give the certificate of the DEEP statement and its error schedule. -/
theorem deep_inputs (R0 : RapStatement Φ K ι β colRound)
    (Rest : R0.M0 → DeepTr P → R0.Mfin → Coins Φ K → Prop) {nb : ℕ} (hR0 : RapInput R0 nb)
    (hlink : ∀ m0 (tr : DeepTr P) fin χ, Rest m0 tr fin χ →
      (∀ i, ∀ x ∈ P.H, eval x (P.Cp χ (P.restr tr) i) = 0) → R0.Accepts m0 (P.restr tr) fin χ)
    (hnb : P.R + 1 < nb) (errOld : ℕ → ℝ≥0∞) (herr0 : ∀ m0 r, roundBound R0 blkOf m0 r ≤ errOld r) :
    Certificate (P.statement R0 Rest) blkOf nb ∧
      ∀ m0 r, roundBound (P.statement R0 Rest) blkOf m0 r ≤ errDeep P errOld r :=
  ⟨certificate_deep P R0 Rest hlink blkOf nb (certificate_of_input hR0) hnb blkOf
      (fun _ _ _ => rfl) (blkOf_sAlpha P) (blkOf_sZeta P),
    fun m0 r => by
      refine (roundBound_deep P R0 Rest m0 r).le.trans ?_
      unfold errDeep
      gcongr
      exact herr0 m0 r⟩

/-- **`rap_succinct_sound_deep` for the paired protocol.** `rap_succinct_sound_deep`'s per-round errors
`errDeep P errOld` (`ε_α` at `R`, `ε_ζ` at `R+1`), the same inputs, and the same bound, for every
single-salt adversary on `pairedRoundsK Dg (rapMask …)` (the folded column blocks carry their root). -/
theorem rap_paired_sound_deep (R0 : RapStatement Φ K ι β colRound)
    (Rest : R0.M0 → DeepTr P → R0.Mfin → Coins Φ K → Prop) {nb : ℕ} (hR0 : RapInput R0 nb)
    (hlink : ∀ m0 (tr : DeepTr P) fin χ, Rest m0 tr fin χ →
      (∀ i, ∀ x ∈ P.H, eval x (P.Cp χ (P.restr tr) i) = 0) → R0.Accepts m0 (P.restr tr) fin χ)
    (hnb : P.R + 1 < nb)
    (plan : OpenPlan (P.statement R0 Rest) (deepCS P)) (hl : Link (P.statement R0 Rest) (deepCS P) plan)
    [DecidableEq (P.statement R0 Rest).M0] [Finite (P.statement R0 Rest).M0]
    [DecidableEq plan.Mfin] [Finite plan.Mfin]
    (I0 : OracleInterface (P.statement R0 Rest).M0)
    (I : (r : ℕ) → OracleInterface (Cols P.colRoundX β r)) (Ifin : OracleInterface plan.Mfin)
    (errOld : ℕ → ℝ≥0∞) (herr0 : ∀ m0 r, roundBound R0 blkOf m0 r ≤ errOld r)
    {Statement GlobalSalt Witness : Type} [DecidableEq Statement] [DecidableEq GlobalSalt]
    (guards : GuardSchedule (Statement × GlobalSalt) PUnit
      (pairedRoundsK Dg (rapMask Φ K md (P.statement R0 Rest).M0 plan.Mfin I0 I Ifin nb)))
    (adversary : SingleSaltAdversary Statement GlobalSalt Witness
      (pairedRoundsK Dg (rapMask Φ K md (P.statement R0 Rest).M0 plan.Mfin I0 I Ifin nb)))
    (Q : ℕ) (queryBound : ∀ phase ∈ support (randomOracleLoggedRun adversary.withQueryLog ∅),
      (freshKeysOfLog phase.1.2).card ≤ Q) :
    Pr{let joint ← (randomOracleLoggedRun (singleSaltAcceptedExecution
        (pairedRoundsK Dg (rapMask Φ K md (P.statement R0 Rest).M0 plan.Mfin I0 I Ifin nb)) guards
        (pairAccepts Dg (rapMask Φ K md (P.statement R0 Rest).M0 plan.Mfin I0 I Ifin nb)
          (fun _ q => rapAccB (P.statement R0 Rest) (deepCS P) plan md I0 I Ifin nb q)) adversary) ∅)}[
        (∃ x, joint.1.1.1 = some x) ∧ ¬ (P.statement R0 Rest).Holds] ≤
      rapEps nb (errDeep P errOld) Q := by
  obtain ⟨hC, herr⟩ := deep_inputs P R0 Rest hR0 hlink hnb errOld herr0
  exact rap_paired_sound_perfect (R := P.statement R0 Rest) (CS := deepCS P) (plan := plan) (I0 := I0) (I := I) (Ifin := Ifin) (nb := nb) md (iopCS_perfect _) hC hl (errDeep P errOld) herr guards adversary Q
    queryBound

/-- **`rap_hclear` for the DEEP-extended RAP**: the `hclear` hypothesis of `merkle_singleSalt_soundness`,
with `εFS Q = rapEps nb (errDeep P errOld) Q` (the bound of `rap_succinct_sound_deep`, by
`rapEps_eq_sErrors`). -/
theorem rap_hclear_deep (R0 : RapStatement Φ K ι β colRound)
    (Rest : R0.M0 → DeepTr P → R0.Mfin → Coins Φ K → Prop) {nb : ℕ} (hR0 : RapInput R0 nb)
    (hlink : ∀ m0 (tr : DeepTr P) fin χ, Rest m0 tr fin χ →
      (∀ i, ∀ x ∈ P.H, eval x (P.Cp χ (P.restr tr) i) = 0) → R0.Accepts m0 (P.restr tr) fin χ)
    (hnb : P.R + 1 < nb)
    (plan : OpenPlan (P.statement R0 Rest) (deepCS P)) (hl : Link (P.statement R0 Rest) (deepCS P) plan)
    [DecidableEq (P.statement R0 Rest).M0] [Finite (P.statement R0 Rest).M0]
    [DecidableEq plan.Mfin] [Finite plan.Mfin]
    (I0 : OracleInterface (P.statement R0 Rest).M0)
    (I : (r : ℕ) → OracleInterface (Cols P.colRoundX β r)) (Ifin : OracleInterface plan.Mfin)
    (errOld : ℕ → ℝ≥0∞) (herr0 : ∀ m0 r, roundBound R0 blkOf m0 r ≤ errOld r)
    {Statement Salt W : Type} [DecidableEq Statement] [DecidableEq Salt]
    (Op : Type) [Finite Op] [DecidableEq Op]
    (guards : GuardSchedule (Statement × Salt) PUnit
      (compiledRoundsK Dg Op (rapMask Φ K md (P.statement R0 Rest).M0 plan.Mfin I0 I Ifin nb)))
    (B : SingleSaltAdversary Statement Salt W
      (pairedRoundsK Dg (rapMask Φ K md (P.statement R0 Rest).M0 plan.Mfin I0 I Ifin nb)))
    (Q : ℕ) (queryBound : ∀ phase ∈ support (randomOracleLoggedRun B.withQueryLog ∅),
      (freshKeysOfLog phase.1.2).card ≤ Q) :
    Pr{let j ← randomOracleLoggedRun (singleSaltAcceptedExecution
        (pairedRoundsK Dg (rapMask Φ K md (P.statement R0 Rest).M0 plan.Mfin I0 I Ifin nb))
        (pairGuards Dg Op (rapMask Φ K md (P.statement R0 Rest).M0 plan.Mfin I0 I Ifin nb) guards)
        (pairAccepts Dg (rapMask Φ K md (P.statement R0 Rest).M0 plan.Mfin I0 I Ifin nb)
          (fun _ q => rapAccB (P.statement R0 Rest) (deepCS P) plan md I0 I Ifin nb q)) B) ∅}[
      match j.1.1.1 with
      | none => False
      | some (z, _, _) => z.1 ∉ {_x : Statement | (P.statement R0 Rest).Holds}] ≤
      rapEps nb (errDeep P errOld) Q := by
  obtain ⟨hC, herr⟩ := deep_inputs P R0 Rest hR0 hlink hnb errOld herr0
  convert rap_hclear (R := P.statement R0 Rest) (CS := deepCS P) (plan := plan) (I0 := I0) (I := I) (Ifin := Ifin) (nb := nb) (Statement := Statement) (Salt := Salt) (W := W) md (iopCS_perfect _) hC hl (errDeep P errOld) herr Op guards B Q queryBound
  rename_i x
  rcases x with ⟨⟨⟨_ | ⟨z, p, w⟩, _⟩, _⟩, _⟩ <;> exact Iff.rfl

end Deep

/-! ## 5. Non-vacuity: a toy RAP -/

namespace NonVacuous

/-- The empty coin frame. -/
def toyΦ : CoinFrame := ⟨0, Fin.elim0⟩

/-- A toy statement: no summands, every message accepted, `Holds = True`. -/
abbrev toyR : RapStatement toyΦ (ZMod 2) Unit Unit (fun _ : Unit => 0) where
  M0 := Unit
  Mfin := Unit
  summands _ := []
  Accepts _ _ _ _ := True
  Holds := True

abbrev toyO : OracleInterface Unit := OracleInterface.instDefault

abbrev toyCS : CommitScheme Unit toyO := iopCS toyO

abbrev toyPlan : OpenPlan toyR toyCS where
  Mfin := Unit
  claims _ _ _ := []
  pf _ := ()
  check _ _ _ := True
  finOf _ := ()

instance : Fintype toyCS.Com := inferInstanceAs (Fintype Unit)
instance : DecidableEq toyCS.Com := inferInstanceAs (DecidableEq Unit)
instance : Inhabited toyCS.Com := inferInstanceAs (Inhabited Unit)

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

noncomputable local instance : SampleableType (ZMod 2) := SampleableType.ofFintype _

/-- The one-leaf layout of the unit columns. -/
def toyMd : RapMaskData (fun _ : Unit => 0) (β := toyCS.Com) Unit Unit where
  skel _ := .leaf
  FB _ := Unit
  words r :=
    { toFun := fun _ => .leaf ()
      invFun := fun _ _ => ()
      left_inv := fun _ => funext fun _ => rfl
      right_inv := fun x => by cases x with | leaf a => rfl }
  ne _ := ⟨()⟩
  enc _ := Function.Embedding.refl Unit

theorem toy_cert : Certificate toyR blkOf 1 where
  sound _ _ _ _ _ _ := trivial
  local_ _ s hs := absurd hs (by simp)
  blk_lt _ s hs := absurd hs (by simp)

set_option linter.defProp false in
/-- `rap_hclear` at the toy RAP (`K = ZMod 2`, no coins, one column, `Dg = F = Unit`, `Op = Unit`,
`Statement = Salt = W = Unit`): every hypothesis (certificate, link, perfect extractability, mask data,
instances) is built; the remaining statement is the genuine `hclear`. -/
noncomputable def nonvac_rap_hclear :=
  rap_hclear (R := toyR) (CS := toyCS) (plan := toyPlan) (I0 := toyO)
    (I := fun _ => OracleInterface.instDefault) (Ifin := toyO) (nb := 1)
    (Statement := Unit) (Salt := Unit) (W := Unit)
    toyMd (iopCS_perfect _) toy_cert (fun _ _ _ _ _ _ => trivial) (fun _ => 0)
    (fun m0 r => by simp [roundBound]) Unit

end NonVacuous

end NockvmE2E.Merkle.RapP
