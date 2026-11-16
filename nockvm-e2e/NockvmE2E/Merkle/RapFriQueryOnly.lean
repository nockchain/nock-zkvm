/-
Merkle (B) e2e row 3: the query-only law for the composed
check of RAP + DEEP + batched FRI on the combined mask `msC = rapMask ++ bmask`, and the paired `hacc`
and `hclear` that `merkle_singleSalt_soundness` consumes.

* `PointMaskData`: the RAP leaf layout together with the map (column, position) ↦ leaf.
* `cAcceptB`: the in-the-clear combined check, natively on base paths of `msC` (split by `MA.fstB/sndB`).
* `cLocal`: the succinct verifier's local check (selectors cover the read set; some agreeing path accepts).
* `rapFri_queryOnly`: `QueryOnly msC decode cAcceptB cLocal`.
* `pairAccepts_cAcceptB_imp`: the `hacc` of `rap_fri_paired_sound_deep`.
* `rapFri_hclear_deep`: `hclear` of `merkle_singleSalt_soundness` in its exact shape.
-/
import NockvmE2E.Merkle.MaskAppend
import NockvmE2E.Merkle.RapFriPaired

open BinaryTree InductiveMerkleTree OracleComp OracleSpec ProtocolSpec Polynomial
open Interaction.Oracle Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir
open Fri.Spec Domain
open BatchedFri.Spec BatchedFri.Spec.BatchingRound
open scoped NNReal ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## 0. FRI query-only with two input words (ProbeB) -/

namespace NockvmE2E.Merkle.Fri

open NockvmE2E.FriPort

variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable (s : Fin (k + 1) → ℕ+) (d : ℕ+) (l : ℕ)

section Q2
open Fri.Spec.QueryRound
variable [∀ j, SampleableType ((pSpec k (ω := ω) s l).Challenge j)]
variable (hs : (∑ j, (s j).val) ≤ n)

/-- `queryBad_congr` with two different input words `f`, `f'` (the RAP composition: word 0 is
virtual, determined by the committed columns). -/
theorem queryBad_congr₂ (f f' : (ω.subdomain 0).toFinset → F)
    (tr tr' : (pSpec k (ω := ω) s l).Transcript (queryChallenge (ω := ω) s l).val.succ)
    (hα : queryFoldChallenges s l (qpre s l tr) =
      queryFoldChallenges s l (qpre s l tr'))
    (hxs : cast (queryChallenge_type (ω := ω) s l)
        (tr.read (queryChallenge s l).val (by simp)) =
      cast (queryChallenge_type (ω := ω) s l) (tr'.read (queryChallenge s l).val (by simp)))
    (hp : readFinalPolynomial s l (qpre s l tr) (by simp) =
      readFinalPolynomial s l (qpre s l tr') (by simp))
    (hw : ∀ i : Fin (k + 1), ∀ y ∈ readPts s l hs
        (cast (queryChallenge_type (ω := ω) s l) (tr.read (queryChallenge s l).val (by simp))) i,
      readWord s l f (qpre s l tr) i
          (by simp only [Fin.val_castSucc, queryChallenge_val]; omega) y =
        readWord s l f' (qpre s l tr') i
          (by simp only [Fin.val_castSucc, queryChallenge_val]; omega) y) :
    queryBad s d l hs f tr ↔ queryBad s d l hs f' tr' := by
  unfold queryBad
  simp only []
  rw [← hα, ← hxs]
  refine and_congr (by rw [finalPolynomial_queryHistory, finalPolynomial_queryHistory, hp]) ?_
  rw [eval_verifyQueries_congr s l hs (queryHistory s l f (qpre s l tr))
    (queryHistory s l f' (qpre s l tr')) _ _
    (by rw [finalPolynomial_queryHistory, finalPolynomial_queryHistory, hp])
    (fun i y hy => by rw [committedWord_queryHistory, committedWord_queryHistory]; exact hw i y hy)]

/-- `queryBad_congr_of_rel` with two input words agreeing on `readPts xs 0`. -/
theorem queryBad_congr_of_rel₂ (f f' : (ω.subdomain 0).toFinset → F)
    (T T' : (pSpec k (ω := ω) s l).FullTranscript)
    (xs : Fin l → (ω.subdomain 0).toFinset)
    (hrel : PrefRel (c := Fin.last _) (friRel s l hs xs) T T')
    (hf : ∀ y ∈ readPts s l hs xs 0, f y = f' y) :
    queryBad s d l hs f (Transcript.restrict (b := Fin.last _)
        (by simp only [Fin.val_succ, Fin.val_last]; omega) T) ↔
      queryBad s d l hs f' (Transcript.restrict (b := Fin.last _)
        (by simp only [Fin.val_succ, Fin.val_last]; omega) T') := by
  have hk := friLength (k := k)
  have h3 := (hrel _ (by simp only [Fin.val_last, queryChallenge_val]; omega)).2.2.1 rfl
  have hx : cast (queryChallenge_type (ω := ω) s l)
      ((Transcript.restrict (a := (queryChallenge (ω := ω) s l).val.succ) (b := Fin.last _)
        (by simp only [Fin.val_succ, Fin.val_last]; omega) T).read
        (queryChallenge s l).val (by simp)) = xs := h3.1
  refine queryBad_congr₂ s d l hs f f' _ _ ?_ ?_ ?_ ?_
  · funext i
    exact (hrel _ (by simp only [Fin.val_last, foldChallenge_val]; omega)).1 i rfl
  · exact h3.1.trans h3.2.symm
  · exact (hrel _ (by simp only [Fin.val_last, finalMessage_val]; omega)).2.1 rfl
  · intro i y hy
    rw [hx] at hy
    by_cases hi0 : i.val = 0
    · have hi : i = 0 := Fin.ext hi0
      subst hi
      unfold readWord
      simp only [↓reduceDIte]
      exact hf y hy
    · obtain ⟨iv, hiv⟩ := i
      obtain ⟨jv, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi0
      unfold readWord
      simp only [hi0, ↓reduceDIte]
      erw [cast_fun_apply, cast_fun_apply]
      exact (hrel _ (by simp only [Fin.val_last, nonfinalMessage_val]; omega)).2.2.2
        ⟨jv, Nat.lt_of_succ_lt_succ hiv⟩ rfl _ hy
      all_goals rfl

end Q2

/-! ### The FRI local check with a different input word on each side -/

section PathLevel2

variable [∀ j, SampleableType ((pSpec k (ω := ω) s l).Challenge j)]
variable (L : FriLeaves (ω := ω) s) (Dg : Type) [Finite Dg] [DecidableEq Dg] (enc : F ↪ Dg)
  (Op : Type) [Finite Op] [DecidableEq Op]
variable (hdom : 2 ^ (∑ j, (s j).val) * d.val ≤ 2 ^ n)

/-- **`fri_queryOnly` with a virtual input word.** Two base paths `q0`, `q` of the FRI mask that agree
with the same compiled path `p` (selectors covering the read set), and two statements whose input words
agree on `readPts xs 0`: `q0` accepted for `z0` gives `q` accepted for `z`. -/
theorem friAccepts'_congr_stmt {Salt : Type} (z0 z : FriStmt (ω := ω) s × Salt)
    (os : OpenAll Dg (merkleSkels (friMask s d l L Dg enc)))
    (p : (protocol (compiledRoundsK Dg Op (friMask s d l L Dg enc))).tree.ExecutionPath)
    (q0 q : (protocol (baseRounds Dg (friMask s d l L Dg enc))).tree.ExecutionPath)
    (hag0 : Agrees (friMask s d l L Dg enc) os p q0) (hag : Agrees (friMask s d l L Dg enc) os p q)
    (hcov : Covers s d l L Dg enc (round_bound hdom) (XsOf s d l L Dg enc Op 0 k (by omega) p.2.2)
      0 k (by omega) os)
    (hf : ∀ y ∈ readPts s l (round_bound hdom) (XsOf s d l L Dg enc Op 0 k (by omega) p.2.2) 0,
      initialOracle s z0.1 y = initialOracle s z.1 y)
    (hacc0 : friAccepts' s d l L Dg enc hdom z0 q0 = true) :
    friAccepts' s d l L Dg enc hdom z q = true := by
  classical
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
  have := queryBad_congr_of_rel₂ s d l hs (initialOracle s z0.1) (initialOracle s z.1) _ _ xs hrel hf
  unfold friAccepts' at hacc0 ⊢
  rw [friAccepts_iff] at hacc0 ⊢
  exact this.mp hacc0

end PathLevel2

end NockvmE2E.Merkle.Fri

/-! ## 1. Point layout and the RAP agreement lemma -/

namespace NockvmE2E.Merkle.RapFriQ

open NockvmE2E.Rap NockvmE2E.Merkle

section Point

variable {ι : Type} (colRound : ι → ℕ) (Pt F Dg : Type)

/-- The RAP leaf layout (`RapMaskData`, columns of a block are words `Pt → F`) together with the map
(column, position) ↦ leaf: the query-only law needs to know which leaf carries `(column c, position x)`. -/
structure PointMaskData extends RapP.RapMaskData colRound (β := Pt → F) F Dg where
  pos : ∀ r : ℕ, {c : ι // colRound c = r} × Pt → SkeletonLeafIndex (skel r)
  /-- A block with a column has leaf type `F` (blocks without columns may use any leaf type). -/
  hF : ∀ (r : ℕ), {c : ι // colRound c = r} → FB r = F
  get_pos : ∀ (r : ℕ) (w : Cols colRound (Pt → F) r) (c : {c : ι // colRound c = r}) (x : Pt),
    cast (hF r c) ((words r w).get (pos r (c, x))) = w c x

end Point

/-! ### Perfect-tree layout: one block = `2 ^ m r` leaves, row-major in (column, position) -/

section Perfect

variable {ι Pt : Type} {colRound : ι → ℕ} {F Dg : Type}

/-- A `PointMaskData` with a perfect skeleton of `2 ^ m r` leaves for block `r`, the leaves numbered by an
equivalence `E r` with the (column, position) pairs. (With `Pt = Fin (2 ^ n)` and a block of `2 ^ a`
columns, `E r` numbering row-major gives the row-subtree skeleton: each row is a perfect subtree.) -/
noncomputable def perfectPointData (m : ℕ → ℕ)
    (E : ∀ r, {c : ι // colRound c = r} × Pt ≃ Fin (2 ^ m r)) (ne : Nonempty F) (enc : F ↪ Dg) :
    PointMaskData colRound Pt F Dg where
  skel r := Skeleton.perfect (m r)
  words r := ((Equiv.curry _ _ _).symm.trans ((Equiv.arrowCongr (E r) (Equiv.refl F)).trans
    ((Equiv.arrowCongr (SkeletonLeafIndex.perfectEquiv (m r)) (Equiv.refl F)).trans
      (LeafData.equivIndexFun (Skeleton.perfect (m r))).symm)))
  ne _ := ne
  enc _ := enc
  FB _ := F
  hF _ _ := rfl
  pos r cx := SkeletonLeafIndex.perfectEquiv (m r) (E r cx)
  get_pos r w c x := by
    show cast rfl ((LeafData.ofFun _ _).get _) = _
    rw [cast_eq, LeafData.get_ofFun]
    simp [Equiv.arrowCongr, Equiv.curry]

end Perfect

/-! ### Selected leaves determine the covered positions -/

section Agree

variable {Φ : CoinFrame} {K : Type} [Fintype K] [DecidableEq K] [SampleableType K]
  {ι Pt F Dg : Type} {colRound : ι → ℕ} [Fintype ι] [DecidableEq ι]
  [Fintype Pt] [DecidableEq Pt] [Fintype F] [DecidableEq F]
  [Finite Dg] [DecidableEq Dg]
  (md : PointMaskData colRound Pt F Dg)
  (R : RapStatement Φ K ι (Pt → F) colRound)
  [DecidableEq R.Mfin] [Finite R.Mfin]
  (I : (r : ℕ) → OracleInterface (Cols colRound (Pt → F) r))
  (Ifin : OracleInterface R.Mfin) (S : Set Pt)

/-- The selectors of the opened column blocks `r, …, r + k - 1` cover the set `S` of positions for every
column of their block. -/
def CoversR : (r k : ℕ) →
    OpenAll Dg (merkleSkels (RapP.rapMerkleMask Φ K md.toRapMaskData R.Mfin I Ifin r k)) → Prop
  | _, 0, _ => True
  | r, k + 1, (o, os) =>
      (∀ (c : {c : ι // colRound c = r}), ∀ x ∈ S, o.selector.get (md.pos r (c, x)) = true) ∧
        CoversR r.succ k os

/-- **Two base paths that agree with one compiled path, with covering selectors, write the same
traces on `S`, the same coins and the same final message.** -/
theorem finalOfBK_agree : (k r : ℕ) →
    (os : OpenAll Dg (merkleSkels (RapP.rapMerkleMask Φ K md.toRapMaskData R.Mfin I Ifin r k))) →
    (p : (protocol (MA.preRoundsK Dg
      (RapP.rapMerkleMask Φ K md.toRapMaskData R.Mfin I Ifin r k))).tree.ExecutionPath) →
    (q q' : (protocol (baseRounds Dg
      (RapP.rapMerkleMask Φ K md.toRapMaskData R.Mfin I Ifin r k))).tree.ExecutionPath) →
    (tr tr' : Tr ι (Pt → F)) → (χ χ' : Coins Φ K) →
    MA.AgreesPre (RapP.rapMerkleMask Φ K md.toRapMaskData R.Mfin I Ifin r k) os p q →
    MA.AgreesPre (RapP.rapMerkleMask Φ K md.toRapMaskData R.Mfin I Ifin r k) os p q' →
    CoversR md R I Ifin S r k os → χ = χ' → (∀ c, ∀ x ∈ S, tr c x = tr' c x) →
    (RapP.finalOfBK md.toRapMaskData R I Ifin r k tr χ q).2 =
        (RapP.finalOfBK md.toRapMaskData R I Ifin r k tr' χ' q').2 ∧
      ∀ c, ∀ x ∈ S, (RapP.finalOfBK md.toRapMaskData R I Ifin r k tr χ q).1 c x =
        (RapP.finalOfBK md.toRapMaskData R I Ifin r k tr' χ' q').1 c x
  | 0, r, _, p, q, q', tr, tr', χ, χ', hq, hq', _, hχ, htr => by
      have h1 : q.1 = q'.1 := hq.1.symm.trans hq'.1
      exact ⟨by simp only [RapP.finalOfBK, h1, hχ], by simpa only [RapP.finalOfBK] using htr⟩
  | k + 1, r, (o, os), p, q, q', tr, tr', χ, χ', hq, hq', ⟨hcov, hC⟩, hχ, htr => by
      obtain ⟨hc, hw, hrest⟩ := hq
      obtain ⟨hc', hw', hrest'⟩ := hq'
      have hqq : q.2.1 = q'.2.1 := hc.symm.trans hc'
      have hsel := hw.symm.trans hw'
      have hcol : ∀ c : {c : ι // colRound c = r}, ∀ x ∈ S, q.1 c x = q'.1 c x := fun c x hx => by
        have := Fri.leaf_eq_of_selectedValues _ _ o.selector hsel (md.pos r (c, x)) (hcov c x hx)
        exact (md.get_pos r q.1 c x).symm.trans ((congrArg (cast (md.hF r c)) this).trans (md.get_pos r q'.1 c x))
      refine finalOfBK_agree k r.succ os p.2.2 q.2.2 q'.2.2 _ _ _ _ hrest hrest' hC
        (by rw [hqq, hχ]) (fun c x hx => ?_)
      unfold setCols
      by_cases h : colRound c = r
      · simp only [h, ↓reduceDIte]
        exact hcol ⟨c, h⟩ x hx
      · simp only [h, ↓reduceDIte]
        exact htr c x hx

end Agree

/-! ## 2. The combined mask and its check -/

section Deep

open NockvmE2E.Succ NockvmE2E.Deep NockvmE2E.Succ.FriC NockvmE2E.FriPort NockvmE2E.FriPort.Batched
  NockvmE2E.Succ.FriDeep NockvmE2E.Succ.App NockvmE2E.Lift NockvmE2E.Lift.Alternating

variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra B F] [Inhabited B]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable [SampleableType F] [Inhabited F]
variable {Φ : CoinFrame} {ι : Type} [Fintype ι] [DecidableEq ι] {colRound : ι → ℕ}
  (P : DeepParams Φ F ι (Fin (2 ^ n) → B) colRound) {r : ℕ} [NeZero r] (A : AirShape P r)
  (R0 : RapStatement Φ F ι (Fin (2 ^ n) → B) colRound)
  (Rest : R0.M0 → DeepTr P → R0.Mfin → Coins Φ F → Prop)
  (RestV : R0.M0 → DeepFin P (r := r) R0 → Coins Φ F → Prop) {m : ℕ}
  (e : Fin (m + 1) ≃ (ι × Fin r) ⊕ Fin P.nq)
variable [DecidableEq (P.statement R0 Rest).M0] [Finite (P.statement R0 Rest).M0]
  [DecidableEq (friPlan (ω := ω) P A R0 Rest RestV e).Mfin] [Finite (friPlan (ω := ω) P A R0 Rest RestV e).Mfin]
  (I0 : OracleInterface (P.statement R0 Rest).M0)
  (I : (r : ℕ) → OracleInterface (Cols P.colRoundX (Fin (2 ^ n) → B) r))
  (Ifin : OracleInterface (friPlan (ω := ω) P A R0 Rest RestV e).Mfin) (nb : ℕ)
variable (s : Fin (k + 1) → ℕ+) (d : ℕ+) (l : ℕ)
variable [∀ j, SampleableType ((pSpec k (ω := ω) s l).Challenge j)]
variable {S : Type} [Fintype S] [Nonempty S] [SampleableType S]
variable (G : CoreDefinitions.Generator S (Fin (m + 1)) F)
variable (Dg : Type) [Finite Dg] [DecidableEq Dg] (enc : F ↪ Dg)
  (md : PointMaskData P.colRoundX (Fin (2 ^ n)) B Dg) (L : Fri.FriLeaves (ω := ω) s)

/-- The batched-FRI mask: the batching round clear, then FRI's mask. -/
noncomputable def bmask : MRounds Dg :=
  ⟨batchRound S, .clear⟩ :: Fri.friMask s d l L Dg enc

/-- **The combined mask**: RAP (+DEEP) column blocks merkle, then batched FRI's mask. -/
@[reducible] noncomputable def msC : MRounds Dg :=
  RapP.rapMask Φ F md.toRapMaskData (P.statement R0 Rest).M0
      (friPlan (ω := ω) P A R0 Rest RestV e).Mfin I0 I Ifin nb ++
    bmask (S := S) s d l Dg enc L

/-- The combined mask is a mask of `rap_fri_sound_deep`'s round list `cRounds`. -/
theorem baseRounds_msC :
    baseRounds Dg (msC P A R0 Rest RestV e I0 I Ifin nb s d l Dg enc md L (S := S)) =
      cRounds (P.statement R0 Rest) (friPlan (ω := ω) P A R0 Rest RestV e) I0 I Ifin nb
        (ω := ω) (S := S) s d l := by
  unfold msC bmask
  rw [MA.baseRounds_append, RapP.baseRounds_rapMask]
  exact congrArg (_ ++ ·) (congrArg (_ :: ·) (Fri.baseRounds_friMask s d l L Dg enc))

/-- The paired combined rounds, as the list on which `appExt rapExtractorP sufExtP` lives. -/
theorem pairedRoundsK_msC :
    pairedRoundsK Dg (RapP.rapMask Φ F md.toRapMaskData (P.statement R0 Rest).M0
        (friPlan (ω := ω) P A R0 Rest RestV e).Mfin I0 I Ifin nb) ++
        (batchRound S :: (Fri.friAltP (ω := ω) s d l Dg).rounds) =
      pairedRoundsK Dg (msC P A R0 Rest RestV e I0 I Ifin nb s d l Dg enc md L (S := S)) := by
  unfold msC bmask
  rw [MA.pairedRoundsK_append]
  exact congrArg (_ ++ ·) (congrArg (_ :: ·) (Fri.friAltP_rounds s d l L Dg enc))

set_option hygiene false in
local notation "PS" => P.statement R0 Rest
set_option hygiene false in
local notation "PL" => friPlan (ω := ω) P A R0 Rest RestV e
set_option hygiene false in
local notation "RM" => RapP.rapMask Φ F md.toRapMaskData (P.statement R0 Rest).M0
  (friPlan (ω := ω) P A R0 Rest RestV e).Mfin I0 I Ifin nb
set_option hygiene false in
local notation "BM" => bmask (S := S) s d l Dg enc L
set_option hygiene false in
local notation "MC" => msC P A R0 Rest RestV e I0 I Ifin nb s d l Dg enc md L (S := S)

/-- The positions of the committed columns the legacy FRI verifier reads for the query vector `xs`:
the input word at `readPts xs 0`, which reads each column at the single position of the domain point. -/
def readSet (hs : (∑ j, (s j).val) ≤ n) (xs : Fin l → (ω.subdomain 0).toFinset) : Set (Fin (2 ^ n)) :=
  {x | ∃ y ∈ Fri.readPts s l hs xs 0, x = ω.equivToFinset.symm (initialDomainPoint (s := s) 0 y)}

variable (hdom : 2 ^ (∑ j, (s j).val) * d.val ≤ 2 ^ n)

/-- **The in-the-clear combined check on base paths of the combined mask**: the plan's residual check on
the RAP prefix, and the legacy FRI acceptance on the combined DEEP statement of the traces the prefix
wrote. (`cAccept` of `rap_fri_sound_deep`, written on native split paths.) -/
noncomputable def cAcceptB {Input Salt : Type} (z : Input × Salt)
    (q : (protocol (baseRounds Dg (MC))).tree.ExecutionPath) : Bool :=
  open Classical in
  decide ((PL).check (MA.fstB Dg (RM) (BM) q).1
      (RapP.finalOfBK md.toRapMaskData (Rok (PS) (PL)) I Ifin 0 nb (fun _ => default) (fun _ => default)
        (MA.fstB Dg (RM) (BM) q).2.2).2.2
      (RapP.finalOfBK md.toRapMaskData (Rok (PS) (PL)) I Ifin 0 nb (fun _ => default) (fun _ => default)
        (MA.fstB Dg (RM) (BM) q).2.2).2.1) &&
    Fri.friAccepts' s d l L Dg enc hdom
      (combinedStmt s m G (MA.sndB Dg (RM) (BM) q).2.1
        (deepStmt (ω := ω) P A R0 e
          (RapP.finalOfBK md.toRapMaskData (Rok (PS) (PL)) I Ifin 0 nb (fun _ => default) (fun _ => default)
            (MA.fstB Dg (RM) (BM) q).2.2).1
          (RapP.finalOfBK md.toRapMaskData (Rok (PS) (PL)) I Ifin 0 nb (fun _ => default) (fun _ => default)
            (MA.fstB Dg (RM) (BM) q).2.2).2.2
          (RapP.finalOfBK md.toRapMaskData (Rok (PS) (PL)) I Ifin 0 nb (fun _ => default) (fun _ => default)
            (MA.fstB Dg (RM) (BM) q).2.2).2.1), z.2)
      (MA.sndB Dg (RM) (BM) q).2.2

/-- **Pointwise law of the virtual input word.** The batched-FRI input word at a point `v` (the
`G`-combination of the DEEP quotient words) reads every committed column at ONE position only. -/
theorem combined_deep_congr (cs : S)
    (tr tr' : DeepTr P) (fin : DeepFin P (r := r) R0) (χ : Coins Φ F) (j : Fin 1)
    (v : (ω.subdomain (∑ j' ∈ finRangeTo (k + 1) j.1, s j')).toFinset)
    (h : ∀ c, tr c (ω.equivToFinset.symm (initialDomainPoint (s := s) j v)) =
      tr' c (ω.equivToFinset.symm (initialDomainPoint (s := s) j v))) :
    combinedOracle s m G cs (deepStmt (ω := ω) P A R0 e tr fin χ).2 j v =
      combinedOracle s m G cs (deepStmt (ω := ω) P A R0 e tr' fin χ).2 j v := by
  unfold combinedOracle deepStmt
  simp only [NockvmE2E.Deep.deepWord, liftW, h]

/-- The selectors of the opened blocks cover the read set of the FRI query vector `xs`, and FRI's own
selectors cover its query cosets. -/
def CoversC (hs : (∑ j, (s j).val) ≤ n) (xs : Fin l → (ω.subdomain 0).toFinset)
    (os : OpenAll Dg (merkleSkels (MC))) : Prop :=
  CoversR md (Rok (PS) (PL)) I Ifin (readSet s l hs xs) 0 nb (MA.fstOpen (RM) (BM) os) ∧
    Fri.Covers s d l L Dg enc hs xs 0 k (by omega) (MA.sndOpen (RM) (BM) os)

variable (Op : Type) [Finite Op] [DecidableEq Op]

/-- The query vector of a compiled path of the combined mask. -/
noncomputable def xsC (p : (protocol (compiledRoundsK Dg Op (MC))).tree.ExecutionPath) : Fin l → (ω.subdomain 0).toFinset :=
  Fri.XsOf s d l L Dg enc Op 0 k (by omega) (MA.sndK Dg Op (RM) (BM) p).2.2.2.2

/-- **The local check of the succinct verifier for the composed protocol.** It reads the compiled path
(roots, challenges, clear messages) and the openings only: the selectors cover the read set, and some path
agreeing with the openings is accepted by the in-the-clear check (then all agreeing paths are:
`rapFri_queryOnly`). -/
noncomputable def cLocal (decode : Op → OpenAll Dg (merkleSkels (MC))) {Input Salt : Type}
    (z : Input × Salt) (p : (protocol (compiledRoundsK Dg Op (MC))).tree.ExecutionPath) : Bool :=
  open Classical in
  decide (CoversC P A R0 Rest RestV e I0 I Ifin nb s d l Dg enc md L (round_bound hdom)
      (xsC P A R0 Rest RestV e I0 I Ifin nb s d l Dg enc md L Op p)
      (decode (pathRootsK Dg Op (MC) p).2) ∧
    ∃ q0 : (protocol (baseRounds Dg (MC))).tree.ExecutionPath,
      Agrees (MC) (decode (pathRootsK Dg Op (MC) p).2) p q0 ∧
        cAcceptB P A R0 Rest RestV e I0 I Ifin nb s d l G Dg enc md L hdom z q0 = true)

/-- **The query-only law of the composed check.** If the local check accepts a compiled path `p`, then the
in-the-clear combined check accepts every path `q` that agrees with `p` (same clear messages and
challenges, and the decoded opened values at the opened leaves). The RAP columns enter the check only through
the virtual input word of FRI, read at the query cosets. -/
theorem rapFri_queryOnly (decode : Op → OpenAll Dg (merkleSkels (MC))) {Input Salt : Type} :
    QueryOnly (MC) decode (cAcceptB P A R0 Rest RestV e I0 I Ifin nb s d l G Dg enc md L hdom
        (Input := Input) (Salt := Salt))
      (cLocal P A R0 Rest RestV e I0 I Ifin nb s d l G Dg enc md L hdom Op decode) := by
  classical
  intro z p q hag hl
  unfold cLocal at hl
  simp only [decide_eq_true_eq] at hl
  obtain ⟨⟨hcR, hcF⟩, q0, hag0, hacc0⟩ := hl
  have hs := round_bound hdom
  have hA := (MA.Agrees_append (RM) (BM) _ p q).mp hag
  have hA0 := (MA.Agrees_append (RM) (BM) _ p q0).mp hag0
  have hRAP := finalOfBK_agree md (Rok (PS) (PL)) I Ifin (readSet s l hs
      (xsC P A R0 Rest RestV e I0 I Ifin nb s d l Dg enc md L Op p)) nb 0
    (MA.fstOpen (RM) (BM) (decode (pathRootsK Dg Op (MC) p).2)) (MA.fstK Dg Op (RM) (BM) p).2.2
    (MA.fstB Dg (RM) (BM) q).2.2 (MA.fstB Dg (RM) (BM) q0).2.2 (fun _ => default) (fun _ => default)
    (fun _ => default) (fun _ => default) hA.1.2.2 hA0.1.2.2 hcR rfl (fun _ _ _ => rfl)
  have hm : (MA.fstB Dg (RM) (BM) q).1 = (MA.fstB Dg (RM) (BM) q0).1 := hA.1.1.symm.trans hA0.1.1
  have hcs : (MA.sndB Dg (RM) (BM) q0).2.1 = (MA.sndB Dg (RM) (BM) q).2.1 :=
    hA0.2.2.1.symm.trans hA.2.2.1
  have hcoins := congrArg Prod.fst hRAP.1
  have hfin := congrArg Prod.snd hRAP.1
  unfold cAcceptB at hacc0 ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hacc0 ⊢
  obtain ⟨hchk0, hfri0⟩ := hacc0
  refine ⟨?_, ?_⟩
  · rw [hm]
    simp only [] at hcoins hfin
    rw [hfin, hcoins]
    exact hchk0
  · refine Fri.friAccepts'_congr_stmt s d l L Dg enc Op hdom _ _
      (MA.sndOpen (RM) (BM) (decode (pathRootsK Dg Op (MC) p).2)) (MA.sndK Dg Op (RM) (BM) p).2.2
      (MA.sndB Dg (RM) (BM) q0).2.2 (MA.sndB Dg (RM) (BM) q).2.2 hA0.2.2.2 hA.2.2.2 hcF ?_ hfri0
    intro y hy
    show combinedOracle s m G _ _ 0 y = combinedOracle s m G _ _ 0 y
    rw [hcs, hfin, hcoins]
    exact combined_deep_congr P A R0 e s G _ _ _ _ _ 0 y (fun c => (hRAP.2 c _ ⟨y, hy, rfl⟩).symm)

/-! ## 3. The `hacc` of `rap_fri_paired_sound_deep` -/

open NockvmE2E.Merkle.Fri in
theorem castPath_cons_congr {r' : Round} {ts ts' : List Round} (h : ts = ts')
    (x : (protocol (r' :: ts)).tree.ExecutionPath) :
    castPath (congrArg (r' :: ·) h) x = ⟨x.1, x.2.1, castPath h x.2.2⟩ := by
  subst h; rfl

open NockvmE2E.Merkle.Fri in
theorem castPath_append_right (a : List Round) {b b' : List Round} (h : b = b')
    (x : (protocol (a ++ b)).tree.ExecutionPath) :
    fstPath a (castPath (congrArg (a ++ ·) h) x) = fstPath a x ∧
      sndPath a (castPath (congrArg (a ++ ·) h) x) = castPath h (sndPath a x) := by
  subst h; exact ⟨rfl, rfl⟩

open NockvmE2E.Merkle.Fri in
/-- **`hacc` for `pairAccepts msC cAcceptB`.** If the in-the-clear combined check accepts the forgotten
path, then `CAccP` (the proposition `rap_fri_paired_sound_deep` consumes) holds on the cast path. -/
theorem pairAccepts_cAcceptB_imp {Input Salt : Type} (z : Input × Salt)
    (p : (protocol (pairedRoundsK Dg (MC))).tree.ExecutionPath)
    (h : pairAccepts Dg (MC) (cAcceptB P A R0 Rest RestV e I0 I Ifin nb s d l G Dg enc md L hdom
      (Input := Input) (Salt := Salt)) z p = true) :
    RapFri.CAccP (PS) (PL) I0 I Ifin nb s d l m G md.toRapMaskData
      (fun _ tr fin χ => deepStmt (ω := ω) P A R0 e tr fin χ) hdom
      (castPath (pairedRoundsK_msC P A R0 Rest RestV e I0 I Ifin nb s d l Dg enc md L (S := S)).symm p) := by
  classical
  have hmid : pairedRoundsK Dg (BM) = batchRound S :: (Fri.friAltP (ω := ω) s d l Dg).rounds :=
    congrArg (batchRound S :: ·) (Fri.friAltP_rounds s d l L Dg enc).symm
  have hp' : castPath (pairedRoundsK_msC P A R0 Rest RestV e I0 I Ifin nb s d l Dg enc md L (S := S)).symm p =
      castPath (congrArg (pairedRoundsK Dg (RM) ++ ·) hmid)
        (castPath (MA.pairedRoundsK_append Dg (RM) (BM)) p) := by
    unfold castPath; rw [cast_cast]
  obtain ⟨hA, hB⟩ := MA.castPath_paired_append Dg (RM) (BM) p _ rfl
  obtain ⟨hA', hB'⟩ := castPath_append_right (pairedRoundsK Dg (RM)) hmid
    (castPath (MA.pairedRoundsK_append Dg (RM) (BM)) p)
  rw [← hp'] at hA' hB'
  have hfst := hA'.trans hA
  have hsnd := hB'.trans (congrArg (castPath hmid) hB)
  have hc : castPath hmid (MA.sndP Dg (RM) (BM) p) =
      ⟨(MA.sndP Dg (RM) (BM) p).1, (MA.sndP Dg (RM) (BM) p).2.1,
        castPath (Fri.friAltP_rounds s d l L Dg enc).symm (MA.sndP Dg (RM) (BM) p).2.2⟩ :=
    castPath_cons_congr (r' := batchRound S) (Fri.friAltP_rounds s d l L Dg enc).symm _
  have hfin : RapP.finalOfBK md.toRapMaskData (Rok (PS) (PL)) I Ifin 0 nb (fun _ => default)
      (fun _ => default) (forgetPath Dg (RM) (MA.fstP Dg (RM) (BM) p)).2.2 =
      RapFri.fin1P (PS) (PL) I0 I Ifin nb md.toRapMaskData (MA.fstP Dg (RM) (BM) p) :=
    RapP.finalOfBK_forget (md := md.toRapMaskData) (R := Rok (PS) (PL)) (I := I) (Ifin := Ifin)
      0 nb _ _ (MA.fstP Dg (RM) (BM) p).2.2
  unfold pairAccepts cAcceptB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hchk, hfri⟩ := h
  rw [MA.fstB_forgetPath] at hchk hfri
  rw [MA.sndB_forgetPath] at hfri
  rw [hfin] at hchk hfri
  unfold RapFri.CAccP
  rw [hfst, hsnd, hc]
  refine ⟨hchk, ?_⟩
  have hq : castPath (Fri.friAltP_rounds s d l L Dg enc)
      (castPath (Fri.friAltP_rounds s d l L Dg enc).symm (MA.sndP Dg (RM) (BM) p).2.2) =
      (MA.sndP Dg (RM) (BM) p).2.2 := by
    unfold castPath; rw [cast_cast]; exact cast_eq _ _
  unfold RapFri.QOk
  rw [Fri.pathTranscript_paired s d l L Dg enc _ _ hq]
  unfold Fri.friAccepts' at hfri
  rw [friAccepts_iff] at hfri
  exact hfri

/-! ## 4. `hclear` -/

/-- The right-hand side of `rap_fri_sound_deep` (and of `rap_fri_paired_sound_deep`) as a function of the
number `Q` of fresh keys. -/
noncomputable def rapFriEps (errOld : ℕ → ℝ≥0∞) (θ : ℝ) (δ ε : ℝ≥0) (Q : ℕ) : ℝ≥0∞ :=
  Q * (Finset.univ.sup (rapErrors (Rok (PS) (PL)) I0 I Ifin nb (errDeep P errOld)) ⊔
        ((ε : ℝ≥0∞) ⊔ Finset.univ.sup (fun j => (challengeError (ω := ω) s d l θ δ j : ℝ≥0∞)))) +
    (∑ j, rapErrors (Rok (PS) (PL)) I0 I Ifin nb (errDeep P errOld) j +
      ((ε : ℝ≥0∞) +
        (((∑ i, foldingError (ω := ω) s d θ i) + Real.toNNReal (1 - min θ δ) ^ l : ℝ≥0) : ℝ≥0∞)))

/-- **`hclear` of `merkle_singleSalt_soundness` for RAP + DEEP + batched FRI on the combined mask `msC`**:
over `pairedRoundsK Dg msC`, with `pairGuards` and `pairAccepts` of the in-the-clear combined check
`cAcceptB`, the event `z.1 ∉ {_ | R0.Holds}` has probability at most `rapFriEps … Q` for every
single-salt adversary with at most `Q` fresh keys (the bound of `rap_fri_sound_deep`). -/
theorem rapFri_hclear_deep (hR0 : RapInput R0 nb)
    (hlink : ∀ m0 (tr : DeepTr P) fin χ, Rest m0 tr fin χ →
      (∀ i, ∀ x ∈ P.H, eval x (P.Cp χ (P.restr tr) i) = 0) → R0.Accepts m0 (P.restr tr) fin χ)
    (hnb : P.R + 1 < nb)
    (hRest : ∀ m0 (tr : DeepTr P) fin χ, RestV m0 fin χ →
      SatClaims (deepOI P) tr (deepClaims P A R0 χ fin) → Rest m0 tr fin.1 χ)
    (errOld : ℕ → ℝ≥0∞) (herr0 : ∀ m0 r, roundBound R0 blkOf m0 r ≤ errOld r)
    (θ : ℝ) (δ : ℝ≥0)
    (hN : friBound s d + 1 ≤ 2 ^ n)
    (hδ : δ ≤ Code.relativeUniqueDecodingRadius
      (ReedSolomon.code (domEmb ω) (friBound s d + 1) : Set (Fin (2 ^ n) → F)))
    (htoPoly : P.toPoly = udDecodeB ω δ (friBound s d))
    (ε : ℝ≥0)
    (hε : ProximityGap.caError G
      (ReedSolomon.code (ω : Fin (2 ^ n) ↪ F) (2 ^ (∑ i, (s i).1) * d)).carrier δ δ ≤ ε)
    {Statement Salt W : Type} [DecidableEq Statement] [DecidableEq Salt]
    (guards : GuardSchedule (Statement × Salt) PUnit (compiledRoundsK Dg Op (MC)))
    (B : SingleSaltAdversary Statement Salt W (pairedRoundsK Dg (MC)))
    (Q : ℕ) (queryBound : ∀ phase ∈ support (randomOracleLoggedRun B.withQueryLog ∅),
      (freshKeysOfLog phase.1.2).card ≤ Q) :
    Pr{let j ← randomOracleLoggedRun (singleSaltAcceptedExecution
        (pairedRoundsK Dg (MC)) (pairGuards Dg Op (MC) guards)
        (pairAccepts Dg (MC) (cAcceptB P A R0 Rest RestV e I0 I Ifin nb s d l G Dg enc md L hdom
          (Input := Statement) (Salt := Salt))) B) ∅}[
      match j.1.1.1 with
      | none => False
      | some (z, _, _) => z.1 ∉ {_x : Statement | R0.Holds}] ≤
    rapFriEps P A R0 Rest RestV e I0 I Ifin nb s d l errOld θ δ ε Q := by
  refine le_trans (prEvent_mono _ _ _ ?_)
    (RapFri.rap_fri_paired_sound_deep P A R0 Rest RestV e I0 I Ifin s d l G md.toRapMaskData hR0 hlink hnb
      hRest errOld herr0 hdom θ δ hN hδ htoPoly ε hε (pairedRoundsK Dg (MC))
      (pairedRoundsK_msC P A R0 Rest RestV e I0 I Ifin nb s d l Dg enc md L (S := S))
      (pairGuards Dg Op (MC) guards)
      (pairAccepts Dg (MC) (cAcceptB P A R0 Rest RestV e I0 I Ifin nb s d l G Dg enc md L hdom
        (Input := Statement) (Salt := Salt)))
      (fun z p hacc => pairAccepts_cAcceptB_imp P A R0 Rest RestV e I0 I Ifin nb s d l G Dg enc md L hdom z p hacc)
      B Q queryBound)
  rintro ⟨⟨⟨_ | ⟨z, path, w⟩, _⟩, _⟩, _⟩ hb
  · exact hb.elim
  · exact ⟨⟨_, rfl⟩, hb⟩

end Deep

end NockvmE2E.Merkle.RapFriQ

/-! ## 5. Non-vacuity: a `PointMaskData` with a row-subtree skeleton -/

namespace NockvmE2E.Merkle.RapFriQ.Witness

/-- Columns `(r, b)`: block `r` has the two columns `b = false, true`. -/
abbrev wColRound : ℕ × Bool → ℕ := Prod.fst

/-- The columns of block `r`, as `Bool`. -/
def wColEquiv (r : ℕ) : {c : ℕ × Bool // wColRound c = r} ≃ Bool where
  toFun c := c.1.2
  invFun b := ⟨(r, b), rfl⟩
  left_inv := fun ⟨⟨a, b⟩, h⟩ => by
    simp only [wColRound] at h
    subst h
    rfl
  right_inv _ := rfl

/-- **Row-major numbering**: leaf `2 * x + (column bit)`. Position `x`'s row is the perfect subtree of its
two columns; the block is the perfect tree of the `2` rows (height `1 + 1 = 2`, `4` leaves). -/
def wLeaf (r : ℕ) : {c : ℕ × Bool // wColRound c = r} × Fin 2 ≃ Fin (2 ^ 2) :=
  ((Equiv.prodCongr (wColEquiv r) (Equiv.refl (Fin 2))).trans
    (Equiv.prodComm Bool (Fin 2))).trans
    ((Equiv.prodCongr (Equiv.refl (Fin 2)) finTwoEquiv.symm).trans (finProdFinEquiv (m := 2) (n := 2)))

/-- A `PointMaskData` on `4`-leaf perfect skeletons: two columns of width two over `Bool` digests. -/
noncomputable def witnessMd : PointMaskData wColRound (Fin 2) Bool Bool :=
  perfectPointData (fun _ => 2) wLeaf ⟨true⟩ (Function.Embedding.refl Bool)

/-- The witness identifies leaf `2 * x + b` with column `b` at position `x`. -/
theorem witnessMd_get (r : ℕ) (w : NockvmE2E.Rap.Cols wColRound (Fin 2 → Bool) r) (c : {c : ℕ × Bool // wColRound c = r})
    (x : Fin 2) : ((witnessMd.words r) w).get (witnessMd.pos r (c, x)) = w c x :=
  witnessMd.get_pos r w c x

end NockvmE2E.Merkle.RapFriQ.Witness
