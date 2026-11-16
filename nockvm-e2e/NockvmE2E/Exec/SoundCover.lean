/-
  NockvmE2E/Exec/SoundCover.lean   (HCOV Brief C, ; proof-only)

  `hcov` of `ClosedLinks` discharged from two opening links (`hsel`, `hxs`) and the layout bijection `rk`:
  `mdX`/`LX` (the instance's `PointMaskData` / `FriLeaves`), `SelR`/`SelF`/`SelLinkC`, `coversC_of_flat`,
  `ClosedLinksL`, `verifyFlat_sound''`, and the discharge lemmas `selR_of_selOf`/`selF_of_selOf`.
-/
import NockvmE2E.Exec.LeafLayout
import NockvmE2E.Exec.DomIdx
import NockvmE2E.Exec.SoundClosed

open BinaryTree InductiveMerkleTree OracleComp OracleSpec ProtocolSpec Polynomial
open Interaction.Oracle Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir
open Fri.Spec Domain
open BatchedFri.Spec BatchedFri.Spec.BatchingRound
open scoped NNReal ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NockvmE2E.Exec.Cover

open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.VL NockvmE2E.Exec.Layout NockvmE2E.Rap NockvmE2E.Merkle NockvmE2E.Merkle.RapFriQ

/-! ### generic selector links -/

section Gen
variable {Φ : CoinFrame} {K : Type} [Fintype K] [DecidableEq K] [SampleableType K]
  {ι Pt F Dg : Type} {colRound : ι → ℕ} [Fintype ι] [DecidableEq ι]
  [Fintype Pt] [DecidableEq Pt] [Fintype F] [DecidableEq F]
  [Finite Dg] [DecidableEq Dg]
  (md : PointMaskData colRound Pt F Dg)
  (R : RapStatement Φ K ι (Pt → F) colRound)
  [DecidableEq R.Mfin] [Finite R.Mfin]
  (I : (r : ℕ) → OracleInterface (Cols colRound (Pt → F) r))
  (Ifin : OracleInterface R.Mfin)

/-- every leaf of block `r` that the predicate `Q r` marks is selected -/
def SelR (Q : ℕ → ℕ → Prop) : (r k : ℕ) →
    OpenAll Dg (merkleSkels (RapP.rapMerkleMask Φ K md.toRapMaskData R.Mfin I Ifin r k)) → Prop
  | _, 0, _ => True
  | r, k + 1, (o, os) => (∀ i, Q r (leafNum i) → o.selector.get i = true) ∧ SelR Q r.succ k os

theorem coversR_of (S : Set Pt) (Q : ℕ → ℕ → Prop)
    (hQ : ∀ r (c : {c : ι // colRound c = r}) x, x ∈ S → Q r (leafNum (md.pos r (c, x)))) :
    ∀ (k r : ℕ) (os : OpenAll Dg (merkleSkels (RapP.rapMerkleMask Φ K md.toRapMaskData R.Mfin I Ifin r k))),
      SelR md R I Ifin Q r k os → CoversR md R I Ifin S r k os
  | 0, _, _, _ => trivial
  | k + 1, r, (o, os), ⟨h1, h2⟩ =>
      ⟨fun c x hx => h1 _ (hQ r c x hx), coversR_of S Q hQ k r.succ os h2⟩

/-- the openings' selectors are the dense selectors `selOf (isSel r)` of the block skeletons (what `mkOpening` builds) -/
def CanonR (isSel : ℕ → ℕ → Bool) : (r k : ℕ) →
    OpenAll Dg (merkleSkels (RapP.rapMerkleMask Φ K md.toRapMaskData R.Mfin I Ifin r k)) → Prop
  | _, 0, _ => True
  | r, k + 1, (o, os) => o.selector = SM.selOf (isSel r) (md.skel r) 0 ∧ CanonR isSel r.succ k os

/-- the discharge of `SelR`: canonical selectors mark every leaf `isSel` marks -/
theorem selR_of_selOf (Q : ℕ → ℕ → Prop) (isSel : ℕ → ℕ → Bool) (hQ : ∀ r t, Q r t → isSel r t = true) :
    ∀ (k r : ℕ) (os : OpenAll Dg (merkleSkels (RapP.rapMerkleMask Φ K md.toRapMaskData R.Mfin I Ifin r k))),
      CanonR md R I Ifin isSel r k os → SelR md R I Ifin Q r k os
  | 0, _, _, _ => trivial
  | k + 1, r, (o, os), ⟨h1, h2⟩ =>
      ⟨fun i hi => by rw [h1, selOf_get]; simpa using hQ r _ hi, selR_of_selOf Q isSel hQ k r.succ os h2⟩

end Gen

section GenF
variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable (s : Fin (k + 1) → ℕ+) (d : ℕ+) (l : ℕ)
variable [∀ j, SampleableType ((pSpec k (ω := ω) s l).Challenge j)]
variable (L : Fri.FriLeaves (ω := ω) s) (Dg : Type) [Finite Dg] [DecidableEq Dg] (enc : F ↪ Dg)

def SelF (Q : ℕ → ℕ → Prop) : (i c : ℕ) → (h : i + c = k) →
    OpenAll Dg (merkleSkels (Fri.friMerkleMask s d l L Dg enc i c h)) → Prop
  | _, 0, _, _ => True
  | i, c + 1, h, (o, os) => (∀ t, Q i (leafNum t) → o.selector.get t = true) ∧ SelF Q i.succ c (by omega) os

theorem covers_of (hs : (∑ j, (s j).val) ≤ n) (xs : Fin l → (ω.subdomain 0).toFinset) (Q : ℕ → ℕ → Prop)
    (hQ : ∀ i (hi : i < k) (y : Fri.wordDom (ω := ω) s i), y ∈ Fri.readPts s l hs xs ⟨i + 1, by omega⟩ →
      Q i (leafNum ((L.idx ⟨i, hi⟩).symm y))) :
    ∀ (c i : ℕ) (h : i + c = k) (os : OpenAll Dg (merkleSkels (Fri.friMerkleMask s d l L Dg enc i c h))),
      SelF s d l L Dg enc Q i c h os → Fri.Covers s d l L Dg enc hs xs i c h os
  | 0, _, _, _, _ => trivial
  | c + 1, i, h, (o, os), ⟨h1, h2⟩ =>
      ⟨fun y hy => h1 _ (hQ i (by omega) y hy), covers_of hs xs Q hQ c i.succ (by omega) os h2⟩

def CanonF (isSel : ℕ → ℕ → Bool) : (i c : ℕ) → (h : i + c = k) →
    OpenAll Dg (merkleSkels (Fri.friMerkleMask s d l L Dg enc i c h)) → Prop
  | _, 0, _, _ => True
  | i, c + 1, h, (o, os) => o.selector = SM.selOf (isSel i) (L.skel ⟨i, by omega⟩) 0 ∧ CanonF isSel i.succ c (by omega) os

theorem selF_of_selOf (Q : ℕ → ℕ → Prop) (isSel : ℕ → ℕ → Bool) (hQ : ∀ i t, Q i t → isSel i t = true) :
    ∀ (c i : ℕ) (h : i + c = k) (os : OpenAll Dg (merkleSkels (Fri.friMerkleMask s d l L Dg enc i c h))),
      CanonF s d l L Dg enc isSel i c h os → SelF s d l L Dg enc Q i c h os
  | 0, _, _, _, _ => trivial
  | c + 1, i, h, (o, os), ⟨h1, h2⟩ =>
      ⟨fun t ht => by rw [h1, selOf_get]; simpa using hQ i _ ht, selF_of_selOf Q isSel hQ c i.succ (by omega) os h2⟩

end GenF


/-! ### instance layouts -/

section Inst
open NockvmE2E.Exec.SM

theorem blockLayout_size (XI : ExecInst) : (blockLayout XI).1.size = 4 := (LInv_fold XI _ le_rfl).s1

theorem lt4_of_pos (XI : ExecInst) (r : ℕ) (h : 0 < (blockLayout XI).1[r]!) : r < 4 := by
  by_contra hr
  have : ¬ r < (blockLayout XI).1.size := by rw [blockLayout_size]; exact hr
  rw [getElem!_neg _ r this] at h
  exact absurd h (by simp)

theorem getD_eq (XI : ExecInst) (r : ℕ) (hr : r < 4) : (blockLayout XI).1.getD r 0 = (blockLayout XI).1[r]! := by
  have : r < (blockLayout XI).1.size := by rw [blockLayout_size]; exact hr
  rw [getElem!_pos _ r this]; simp [Array.getD, this]

/-- width of block `r` -/
abbrev Wb (XI : ExecInst) (r : ℕ) : ℕ := (blockLayout XI).1[r]!

theorem pow_half (n : ℕ) (hn : 1 ≤ n) : 2 ^ n = 2 * 2 ^ (n - 1) := by
  rw [← pow_succ']; congr 1; omega

theorem leafCount_rag (XI : ExecInst) (hn1 : 1 ≤ XI.nD) (W : ℕ) (hW : 0 < W) :
    (skelOf (ragSpec W (2 ^ (XI.nD - 1))) (2 ^ (XI.nD - 1) * 2 * W) (2 ^ (XI.nD - 1) * 2 * W)).leafCount =
      2 ^ (XI.nD - 1) * 2 * W :=
  leafCount_skelOf _ (wf_ragSpec _ _ hW) _ _ (Nat.mul_pos (Nat.mul_pos (Nat.two_pow_pos _) two_pos) hW) le_rfl

/-- the RAP mask data of the instance: block `r` is the tree `skelOf (ragSpec W half)`, leaf of `(column c, point x)`
= `(x % half) * 2W + (x / half) * W + rk c`; width-0 blocks are empty -/
noncomputable def mdX {κ B Dg : Type} [Nonempty B] (XI : ExecInst) (hn1 : 1 ≤ XI.nD) (colR : κ → ℕ)
    (rk : ∀ r, {c : κ // colR c = r} ≃ Fin (Wb XI r)) (encB : B ↪ Dg) :
    PointMaskData colR (Fin (2 ^ XI.nD)) B Dg :=
  layoutPointMd colR (Wb XI)
    (fun r => skelOf (ragSpec (Wb XI r) (2 ^ (XI.nD - 1))) (2 ^ (XI.nD - 1) * 2 * Wb XI r) (2 ^ (XI.nD - 1) * 2 * Wb XI r))
    (fun r h => ((rk r).prodCongr (finCongr (pow_half _ hn1))).trans
      ((ragPerm _ _).trans ((finCongr (leafCount_rag XI hn1 _ h).symm).trans (leafEquiv _).symm)))
    (fun r h => haveI : IsEmpty (Fin (Wb XI r)) := ⟨fun x => by have := x.2; omega⟩; (rk r).isEmpty)
    inferInstance encB

theorem mdX_leafNum {κ B Dg : Type} [Nonempty B] (XI : ExecInst) (hn1 : 1 ≤ XI.nD) (colR : κ → ℕ)
    (rk : ∀ r, {c : κ // colR c = r} ≃ Fin (Wb XI r)) (encB : B ↪ Dg) (r : ℕ) (h : 0 < Wb XI r)
    (c : {c : κ // colR c = r}) (x : Fin (2 ^ XI.nD)) :
    leafNum ((mdX XI hn1 colR rk encB).pos r (c, x)) =
      (x.val % 2 ^ (XI.nD - 1)) * 2 * Wb XI r + (x.val / 2 ^ (XI.nD - 1)) * Wb XI r + (rk r c).val := by
  unfold mdX
  rw [layoutPointMd_pos _ _ _ _ _ _ _ r h]
  simp only [Equiv.trans_apply, Equiv.prodCongr_apply]
  refine (leafNum_symm _ _).trans ?_
  simp only [finCongr_apply, Fin.val_cast]
  rw [ragPerm_val]
  simp


/-- the FRI leaf permutation on `2^a` points (identity when `a = 0`) -/
def friPermN (a : ℕ) : Fin (2 ^ a) ≃ Fin (2 ^ a) :=
  if h : 1 ≤ a then (finCongr (pow_half a h)).trans ((friPerm (2 ^ (a - 1))).trans (finCongr (pow_half a h).symm))
  else Equiv.refl _

theorem friPermN_val (a : ℕ) (h : 1 ≤ a) (u : Fin (2 ^ a)) :
    (friPermN a u).val = 2 * (u.val % 2 ^ (a - 1)) + u.val / 2 ^ (a - 1) := by
  unfold friPermN
  rw [dif_pos h]
  simp only [Equiv.trans_apply, finCongr_apply, Fin.val_cast]
  rw [friPerm_val]; simp

theorem msum1 (k i : ℕ) (hi : i < k) :
    ∑ j ∈ finRangeTo (k + 1) (i + 1), (((fun _ : Fin (k + 1) => (1 : ℕ+)) j : ℕ+) : ℕ) = i + 1 := by
  have h : (finRangeTo (k + 1) (i + 1)).card = i + 1 := by
    unfold finRangeTo
    rw [List.toFinset_card_of_nodup ((List.nodup_finRange _).sublist (List.take_sublist _ _))]
    simp; omega
  simp only [Finset.sum_const, PNat.one_coe, smul_eq_mul, mul_one, h]

/-- the FRI leaf data of the instance: word `i` is the tree `skelOf (friSpec 2^(nD-(i+1)))`, domain point `u` at leaf
`2 (u % h) + u / h` (`h = 2^(nD-i-2)`), so the pair `{u, u + h}` is adjacent -/
noncomputable def LX (XI : ExecInst) (hn32 : XI.nD ≤ 32) :
    Fri.FriLeaves (ω := smoothDomain XI.nD hn32) (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) where
  skel i := skelOf (friSpec (2 ^ (XI.nD - (i.1 + 1)))) (2 ^ (XI.nD - (i.1 + 1))) (2 ^ (XI.nD - (i.1 + 1)))
  idx i :=
    (leafEquiv _).trans ((finCongr (leafCount_skelOf _ (wf_friSpec _) _ _ (Nat.two_pow_pos _) le_rfl)).trans
      ((friPermN (XI.nD - (i.1 + 1))).symm.trans ((finCongr (by rw [msum1 XI.k i.1 i.2])).trans
        ((smoothDomain XI.nD hn32).subdomain _).equivToFinset)))

theorem LX_leafNum (XI : ExecInst) (hn32 : XI.nD ≤ 32) (i : ℕ) (hi : i < XI.k) (hi2 : i + 2 ≤ XI.nD)
    (y : Fri.wordDom (ω := smoothDomain XI.nD hn32) (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) i) :
    leafNum (((LX XI hn32).idx ⟨i, hi⟩).symm y) =
      2 * ((((smoothDomain XI.nD hn32).subdomain (∑ j ∈ finRangeTo (XI.k + 1) (i + 1), (1 : ℕ))).equivToFinset.symm y).val
          % 2 ^ (XI.nD - i - 2)) +
        (((smoothDomain XI.nD hn32).subdomain (∑ j ∈ finRangeTo (XI.k + 1) (i + 1), ((1 : ℕ+) : ℕ))).equivToFinset.symm y).val
          / 2 ^ (XI.nD - i - 2) := by
  unfold LX
  simp only [Equiv.symm_trans_apply]
  refine (leafNum_symm _ _).trans ?_
  simp only [finCongr_symm, finCongr_apply, Fin.val_cast]
  have e : XI.nD - (i + 1) - 1 = XI.nD - i - 2 := by omega
  rw [Equiv.symm_symm, friPermN_val _ (by omega)]
  simp only [Fin.val_cast, e]
  rfl

theorem selsR (XI : ExecInst) (π : FlatProof) (r : ℕ) (hr : r < 4) :
    (selsOf XI π)[r]! = treeSel XI (Wb XI r) r π.pos := by
  unfold selsOf
  have h : r < ((Array.range (4 + XI.k)).map fun j => treeSel XI ((blockLayout XI).1.getD j 0) j π.pos).size := by
    simp; omega
  rw [getElem!_pos _ r h]
  simp only [Array.getElem_map, Array.getElem_range]
  rw [getD_eq XI r hr]

theorem treeSel_ge4 (XI : ExecInst) (W j : ℕ) (pos : Array ℕ) (h : ¬ j < 4) : treeSel XI W j pos = treeSel XI 0 j pos := by
  unfold treeSel; simp [h]

theorem selsF (XI : ExecInst) (π : FlatProof) (i : ℕ) (hi : i < XI.k) :
    (selsOf XI π)[4 + i]! = treeSel XI 0 (4 + i) π.pos := by
  unfold selsOf
  have h : 4 + i < ((Array.range (4 + XI.k)).map fun j => treeSel XI ((blockLayout XI).1.getD j 0) j π.pos).size := by
    simp; omega
  rw [getElem!_pos _ (4 + i) h]
  simp only [Array.getElem_map, Array.getElem_range]
  exact treeSel_ge4 XI _ _ _ (by omega)

/-- block `r`'s leaf `t` is in the verifier's selection (only blocks `< 4` are committed) -/
def QR (XI : ExecInst) (π : FlatProof) (r t : ℕ) : Prop := r < 4 ∧ t ∈ (selsOf XI π)[r]!.toList
/-- FRI word `i`'s leaf `t` is in the verifier's selection (tree `4 + i`) -/
def QF (XI : ExecInst) (π : FlatProof) (i t : ℕ) : Prop := t ∈ (selsOf XI π)[4 + i]!.toList

theorem flat_shape (XI : ExecInst) (H : HFn) (FS : FSFn) (z : List Nat) (π : FlatProof) (hok : FlatOk XI H FS z π) :
    XI.k + 1 ≤ XI.nD ∧ π.pos.size = XI.l := by
  refine ⟨?_, ?_⟩
  · obtain ⟨_, _, h, _⟩ := hok
    simp only [Bool.and_eq_true, decide_eq_true_eq, ge_iff_le] at h
    exact h.1.1.1.1
  · obtain ⟨_, _, _, _, _, h6, _⟩ := hok
    simp only [Bool.and_eq_true, beq_iff_eq] at h6
    exact h6.2

theorem psiV_shift (XI : ExecInst) (h : XI.dShift = 7) : psiV XI.dShift = algebraMap (ZMod NockvmE2E.Exec.p) KC 7 := by
  rw [h]; unfold psiV; exact congrArg (algebraMap (ZMod NockvmE2E.Exec.p) KC) zv_seven


/-- the verifier's own membership test of tree `j` on its sorted selection -/
def isSelB (sel : Array ℕ) (t : ℕ) : Bool := sel[lb sel t]? == some t

/-- block-`r` (`r < 4`) membership test and FRI-word-`i` membership test, on the verifier's `selsOf` -/
def isSelRP (XI : ExecInst) (π : FlatProof) (r t : ℕ) : Bool := isSelB (selsOf XI π)[r]! t
def isSelFP (XI : ExecInst) (π : FlatProof) (i t : ℕ) : Bool := isSelB (selsOf XI π)[4 + i]! t

theorem QR_isSel (XI : ExecInst) (π : FlatProof) (r t : ℕ) (h : QR XI π r t) : isSelRP XI π r t = true := by
  obtain ⟨hr, ht⟩ := h
  have hp := treeSel_pw XI (Wb XI r) r π.pos
  rw [← selsR XI π r hr] at hp
  unfold isSelRP isSelB
  simpa [mem_iff_lb _ hp] using ht

theorem QF_isSel (XI : ExecInst) (π : FlatProof) (i t : ℕ) (hi : i < XI.k) (h : QF XI π i t) : isSelFP XI π i t = true := by
  have hp := treeSel_pw XI 0 (4 + i) π.pos
  rw [← selsF XI π i hi] at hp
  unfold isSelFP isSelB
  simpa using (mem_iff_lb _ hp t).mpr h

end Inst

section Closed

open NockvmE2E.Succ NockvmE2E.Deep NockvmE2E.Succ.FriC NockvmE2E.FriPort NockvmE2E.FriPort.Batched
  NockvmE2E.Succ.FriDeep NockvmE2E.Succ.App NockvmE2E.Lift NockvmE2E.Lift.Alternating
  NockvmE2E.Exec.Inst

variable (XI : ExecInst) (H : HFn) (FS : FSFn) (zF : List Nat) (π : FlatProof) (hv : verifyFlat XI H FS zF π = true)

set_option hygiene false in
local notation "ωS" => smoothDomain XI.nD (nD_le_of_verify XI H FS zF π hv)
set_option hygiene false in
local notation "s1" => (fun _ : Fin (XI.k + 1) => (1 : ℕ+))

variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra B KC] [Inhabited B]
variable [SampleableType KC] [Inhabited KC]
variable {Φ : CoinFrame} {ι : Type} [Fintype ι] [DecidableEq ι] {colRound : ι → ℕ}
  (P : DeepParams Φ KC ι (Fin (2 ^ XI.nD) → B) colRound) {r : ℕ} [NeZero r] (A : AirShape P r)
  (R0 : RapStatement Φ KC ι (Fin (2 ^ XI.nD) → B) colRound)
  (Rest : R0.M0 → DeepTr P → R0.Mfin → Coins Φ KC → Prop)
  (RestV : R0.M0 → DeepFin P (r := r) R0 → Coins Φ KC → Prop) {m : ℕ}
  (e : Fin (m + 1) ≃ (ι × Fin r) ⊕ Fin P.nq)
variable [DecidableEq (P.statement R0 Rest).M0] [Finite (P.statement R0 Rest).M0]
  [DecidableEq (friPlan (ω := ωS) P A R0 Rest RestV e).Mfin] [Finite (friPlan (ω := ωS) P A R0 Rest RestV e).Mfin]
  (I0 : OracleInterface (P.statement R0 Rest).M0)
  (I : (r : ℕ) → OracleInterface (Cols P.colRoundX (Fin (2 ^ XI.nD) → B) r))
  (Ifin : OracleInterface (friPlan (ω := ωS) P A R0 Rest RestV e).Mfin) (nb : ℕ)
variable (d : ℕ+)
variable [∀ j, SampleableType ((pSpec XI.k (ω := ωS) s1 XI.l).Challenge j)]
variable {S : Type} [Fintype S] [Nonempty S] [SampleableType S]
variable (G : CoreDefinitions.Generator S (Fin (m + 1)) KC)
variable (Dg : Type) [Finite Dg] [DecidableEq Dg] (enc : KC ↪ Dg)
  (md : PointMaskData P.colRoundX (Fin (2 ^ XI.nD)) B Dg) (L : Fri.FriLeaves (ω := ωS) s1)
variable (hdom : 2 ^ (∑ j, ((s1) j).val) * d.val ≤ 2 ^ XI.nD)
variable (Op : Type) [Finite Op] [DecidableEq Op]

set_option hygiene false in
local notation "MC" => msC P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L (S := S)
set_option hygiene false in
local notation "PS" => P.statement R0 Rest
set_option hygiene false in
local notation "PL" => friPlan (ω := ωS) P A R0 Rest RestV e
set_option hygiene false in
local notation "RM" => RapP.rapMask Φ KC md.toRapMaskData (P.statement R0 Rest).M0
  (friPlan (ω := ωS) P A R0 Rest RestV e).Mfin I0 I Ifin nb
set_option hygiene false in
local notation "BM" => bmask (S := S) s1 d XI.l Dg enc L

/-- **the selector link**: the opened selectors mark every leaf of the verifier's selection (`selsOf`) -/
def SelLinkC (os : OpenAll Dg (merkleSkels (MC))) : Prop :=
  SelR md (Rok (PS) (PL)) I Ifin (QR XI π) 0 nb (MA.fstOpen (RM) (BM) os) ∧
    SelF s1 d XI.l L Dg enc (QF XI π) 0 XI.k (by omega) (MA.sndOpen (RM) (BM) os)

theorem coversC_of_flat (encB : B ↪ Dg) (rk : ∀ r, {c : ι ⊕ Fin P.nq // P.colRoundX c = r} ≃ Fin (Wb XI r))
    (hok : FlatOk XI H FS zF π)
    (hmd : md = mdX XI (by have := (flat_shape XI H FS zF π hok).1; omega) P.colRoundX rk encB)
    (hL : L = LX XI (nD_le_of_verify XI H FS zF π hv))
    (os : OpenAll Dg (merkleSkels (MC))) (xs : Fin XI.l → ((ωS).subdomain 0).toFinset)
    (hxs : ∀ j, (xs j).val = homV.ψ XI.dShift * homV.ψ XI.dGen ^ π.pos[j.1]!) (hsel : SelLinkC XI H FS zF π hv P A R0 Rest RestV e I0 I Ifin nb d Dg enc md L os) :
    CoversC P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L (round_bound hdom) xs os := by
  have hs := round_bound hdom
  have hn32 := nD_le_of_verify XI H FS zF π hv
  obtain ⟨hk1, hsz⟩ := flat_shape XI H FS zF π hok
  have hn1 : 1 ≤ XI.nD := by omega
  have hshift : XI.dShift = 7 := (flatOk_params XI H FS zF π hok).1
  have hgen := flatOk_dGen XI H FS zF π hok
  have hx' : ∀ j, (xs j).val = algebraMap (ZMod NockvmE2E.Exec.p) KC 7 * ((zeta XI.nD : KCˣ) : KC) ^ (fun j : Fin XI.l => π.pos[j.1]!) j := by
    intro j
    rw [hxs j]
    show psiV XI.dShift * psiV XI.dGen ^ _ = _
    rw [psiV_shift XI hshift, hgen]
  have hmem : ∀ j : Fin XI.l, π.pos[j.1]! ∈ π.pos.toList := by
    intro j
    have : j.1 < π.pos.size := by rw [hsz]; exact j.2
    rw [getElem!_pos π.pos j.1 this]; simp
  subst hmd hL
  refine ⟨coversR_of _ _ _ _ _ _ ?_ nb 0 _ hsel.1, covers_of _ _ _ _ _ _ hs xs _ ?_ XI.k 0 _ _ hsel.2⟩
  · intro r c x hx
    have hW : 0 < Wb XI r := lt_of_le_of_lt (Nat.zero_le _) (rk r c).2
    have hr := lt4_of_pos XI r hW
    obtain ⟨j, hj⟩ := DomIdx.readSet_idx (ω := smoothDomain XI.nD hn32) s1 XI.l hn32 rfl hn1 (fun _ => rfl) hs xs
      (fun j => π.pos[j.1]!) hx' x hx
    refine ⟨hr, ?_⟩
    rw [mdX_leafNum XI _ _ rk encB r hW c x, selsR XI π r hr]
    have hx2 : x.val / 2 ^ (XI.nD - 1) < 2 := by
      apply Nat.div_lt_of_lt_mul
      rw [mul_comm]; exact lt_of_lt_of_eq x.2 (pow_half _ hn1)
    have := leafPos_mem_treeSel XI (Wb XI r) r π.pos hr (π.pos[j.1]!) (rk r c).val (hmem j) (rk r c).2 _ hx2
    rw [Nat.mod_mod, ← hj] at this
    exact this
  · intro i hi y hy
    have hi2 : i + 2 ≤ XI.nD := by omega
    obtain ⟨j, hj⟩ := DomIdx.readPts_idx (ω := smoothDomain XI.nD hn32) s1 XI.l hn32 rfl (fun _ => rfl) hs xs
      (fun j => π.pos[j.1]!) hx' i hi2 hi y hy
    show _ ∈ (selsOf XI π)[4 + i]!.toList
    rw [LX_leafNum XI hn32 i hi hi2, selsF XI π i hi]
    have e1 : XI.nD - (4 + i - 3) - 1 = XI.nD - i - 2 := by omega
    have hu := ((smoothDomain XI.nD hn32).subdomain (∑ j ∈ finRangeTo (XI.k + 1) (i + 1), ((1 : ℕ+) : ℕ))).equivToFinset.symm y |>.isLt
    have hm : (∑ j ∈ finRangeTo (XI.k + 1) (i + 1), ((1 : ℕ+) : ℕ)) = i + 1 := msum1 XI.k i hi
    have hu2 : (((smoothDomain XI.nD hn32).subdomain (∑ j ∈ finRangeTo (XI.k + 1) (i + 1), ((1 : ℕ+) : ℕ))).equivToFinset.symm y).val
        < 2 ^ (XI.nD - (i + 1)) := lt_of_lt_of_eq hu (by rw [hm])
    have hx2 : (((smoothDomain XI.nD hn32).subdomain (∑ j ∈ finRangeTo (XI.k + 1) (i + 1), ((1 : ℕ+) : ℕ))).equivToFinset.symm y).val
        / 2 ^ (XI.nD - i - 2) < 2 := by
      apply Nat.div_lt_of_lt_mul
      rw [← pow_succ]
      have : XI.nD - i - 2 + 1 = XI.nD - (i + 1) := by omega
      rwa [this]
    have := mem_treeSel_fri XI (4 + i) π.pos (by omega) (π.pos[j.1]!) (hmem j) _ hx2
    rw [e1, ← hj] at this
    exact this

structure ClosedLinksL
    (decode : Op → OpenAll Dg (merkleSkels (MC))) {Input Salt : Type} (z : Input × Salt)
    (p : (protocol (compiledRoundsK Dg Op (MC))).tree.ExecutionPath)
    (PubRel : Array VF.K3 → Array VF.G → Prop) : Prop where
  hsel : SelLinkC XI H FS zF π hv P A R0 Rest RestV e I0 I Ifin nb d Dg enc md L (decode (pathRootsK Dg Op (MC) p).2)
  hxs : ∀ j, (xsC P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L Op p j).val =
      homV.ψ XI.dShift * homV.ψ XI.dGen ^ π.pos[j.1]!
  hD : DeepLinkC XI H FS zF π P A
      (chiQ P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L (q0P P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L Op decode p))
      (chiQ P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L (q0P P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L Op decode p) P.a)
      (chiQ P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L (q0P P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L Op decode p) P.z)
      (finMQ P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L (q0P P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L Op decode p)).2.1
      (finMQ P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L (q0P P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L Op decode p)).2.2
  hpts : ∀ ck : ι × Fin r, ∃ pt ∈ (openPts XI (zetaOf XI FS zF π)).toList,
      toKV pt = A.pt ck.1 ck.2 (chiQ P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L (q0P P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L Op decode p) P.z)
  hRV : PubRel (slotsOf XI FS zF π) (pubOfProof XI π) →
      RestV (MA.fstB Dg (RM) (BM) (q0P P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L Op decode p)).1
        (finMQ P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L (q0P P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L Op decode p))
        (chiQ P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L (q0P P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L Op decode p))
  hF : FriLinkAt s1 d XI.l
      ((combinedStmt s1 m G (MA.sndB Dg (RM) (BM) (q0P P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L Op decode p)).2.1
        (deepStmt (ω := ωS) P A R0 e
          (trQ P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L (q0P P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L Op decode p))
          (finMQ P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L (q0P P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L Op decode p))
          (chiQ P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L (q0P P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L Op decode p))), z.2))
      (Fri.toFriPath s1 d XI.l L Dg enc (MA.sndB Dg (RM) (BM) (q0P P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L Op decode p)).2.2)
      (homV.ψ XI.dShift) (homV.ψ XI.dGen) (fun j => π.pos[j.1]!)
      (fun w i => homV.φ (SF.Wf XI (word0Of XI FS zF π) (faV π.vals (selsOf XI π)) (fbV π.vals (selsOf XI π)) w i))
      (SF.hornerF (fun j => homV.φ π.pfinal[j]!) π.pfinal.size) (fun i => homV.φ (alphasOf XI FS zF π)[i]!)

/-- **`verifyFlat_sound''`**: `verifyFlat_sound_J8Pub` with `hcov` (`CoversC`) discharged: the audited layout objects ARE the instance's
(`md = mdX … rk`, `L = LX …`), the layout bijection `rk` (J-8 data, a cardinality fact) and the two opening links `hsel`/`hxs` replace `hcov`.
`hshift`, `hgen` (`flatOk_dGen`), `nD ≥ 1` and `pos.size = l` are read off `FlatOk`. -/
theorem verifyFlat_sound''
    (encB : B ↪ Dg) (rk : ∀ r, {c : ι ⊕ Fin P.nq // P.colRoundX c = r} ≃ Fin (Wb XI r))
    (hmd : md = mdX XI (by have := (flat_shape XI H FS zF π ((verifyFlat_iff XI H FS zF π).mp hv)).1; omega) P.colRoundX rk encB)
    (hL : L = LX XI (nD_le_of_verify XI H FS zF π hv))
    (decode : Op → OpenAll Dg (merkleSkels (MC))) {Input Salt : Type} (z : Input × Salt)
    (p : (protocol (compiledRoundsK Dg Op (MC))).tree.ExecutionPath)
    (PR : Array VF.K3 → Array VF.G → Prop) (hPS : PubSound XI PR)
    (Ls : ClosedLinksL XI H FS zF π hv P A R0 Rest RestV e I0 I Ifin nb d G Dg enc md L Op decode z p PR) :
    (∀ j, j < 4 + XI.k → ¬ (j < 4 ∧ (blockLayout XI).1[j]! = 0) → MerkleRootOk XI H π j) ∧
    cLocal P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l G Dg enc md L hdom Op decode z p = true ∧
      PR (slotsOf XI FS zF π) (pubOfProof XI π) :=
  verifyFlat_sound_Pub XI H FS zF π hv P A R0 Rest RestV e I0 I Ifin nb d G Dg enc md L hdom Op decode z p PR hPS
    ⟨coversC_of_flat XI H FS zF π hv P A R0 Rest RestV e I0 I Ifin nb d Dg enc md L hdom encB rk
      ((verifyFlat_iff XI H FS zF π).mp hv) hmd hL _ _ Ls.hxs Ls.hsel,
      Ls.hD, Ls.hpts, Ls.hRV, Ls.hF⟩

end Closed


/-! ### non-vacuity (kernel) at `toyInstB` (blocks widths `[2,0,1,3]`, `nD = 5`) -/
section NonVac
open NockvmE2E.Exec.SM

/-- columns `Fin 3 ⊕ Fin 3`: columns in blocks `0, 0, 2` (the middle one is preprocessed, kind 1), three in block `3` (as `toyInstB`) -/
def toyColR : Fin 3 ⊕ Fin 3 → ℕ := Sum.elim ![0, 0, 2] (fun _ => 3)

theorem toyCard (r : ℕ) : Fintype.card {c : Fin 3 ⊕ Fin 3 // toyColR c = r} = Wb toyInstB r := by
  by_cases hr : r < 4
  · interval_cases r <;> decide
  · have h0 : Wb toyInstB r = 0 := by
      by_contra h; exact hr (lt4_of_pos toyInstB r (Nat.pos_of_ne_zero h))
    rw [h0, Fintype.card_eq_zero_iff]
    refine ⟨fun ⟨c, hc⟩ => ?_⟩
    rcases c with c | c
    · fin_cases c <;> simp [toyColR] at hc <;> omega
    · simp [toyColR] at hc; omega

/-- the preprocessed column now occupies a slot of block `0` -/
example : Wb toyInstB 0 = 2 := by decide +kernel
/-- the batched openings: `nc * r + nq` entries (`3 * 2 + 3`), kinds 0/1 at `r` points, the public once per `r` points -/
example : (openingList toyInstB VF.K3.one (Array.replicate 3 (Array.replicate 2 VF.K3.zero)) (Array.replicate 3 VF.K3.zero)).size
    = toyInstB.nc * toyInstB.r + toyInstB.nq := by decide +kernel

noncomputable def toyRk (r : ℕ) : {c : Fin 3 ⊕ Fin 3 // toyColR c = r} ≃ Fin (Wb toyInstB r) :=
  Fintype.equivOfCardEq (by simpa using toyCard r)

noncomputable def toyMdX : PointMaskData toyColR (Fin (2 ^ toyInstB.nD)) Bool Bool :=
  mdX toyInstB (by decide) toyColR toyRk (Function.Embedding.refl Bool)

/-- block `1` is empty (leaf type `PUnit`), block `0` carries `Bool`; the block skeletons are the flat verifier's -/
example : toyMdX.FB 1 = PUnit := by
  show FBlk Bool (Wb toyInstB) 1 = PUnit
  unfold FBlk; rw [if_neg (by decide)]
example : toyMdX.FB 0 = Bool := by
  show FBlk Bool (Wb toyInstB) 0 = Bool
  unfold FBlk; rw [if_pos (by decide)]
example : (toyMdX.skel 3).leafCount = 2 ^ 4 * 2 * 3 := by decide +kernel
/-- the leaf of (column, point) is the verifier's `(x % half) * 2W + (x / half) * W + rank` (`mdX_leafNum`), at a real point -/
example (c : {c : Fin 3 ⊕ Fin 3 // toyColR c = 3}) :
    leafNum (toyMdX.pos 3 (c, (21 : Fin 32))) = (21 % 16) * 2 * 3 + (21 / 16) * 3 + (toyRk 3 c).val :=
  mdX_leafNum toyInstB _ toyColR toyRk _ 3 (by decide) c 21

/-- the FRI leaf data is a term at `toyInstB`; word `0` has `2^4` leaves, point `u` at leaf `2 (u % 8) + u / 8` -/
example : ((LX toyInstB (by decide)).skel ⟨0, by decide⟩).leafCount = 16 := by decide +kernel

/-- `hxs` is satisfiable for EVERY position vector (so it is a real link, not an inconsistency). -/
theorem xsOfPos (XI : ExecInst) (hn32 : XI.nD ≤ 32) (hshift : XI.dShift = 7)
    (hgen : psiV XI.dGen = ((zeta XI.nD : KCˣ) : KC)) (l : ℕ) (pos : Fin l → ℕ) :
    ∃ xs : Fin l → ((smoothDomain XI.nD hn32).subdomain 0).toFinset,
      ∀ j, (xs j).val = homV.ψ XI.dShift * homV.ψ XI.dGen ^ pos j := by
  refine ⟨fun j => ((smoothDomain XI.nD hn32).subdomain 0).equivToFinset ⟨pos j % 2 ^ XI.nD, Nat.mod_lt _ (by positivity)⟩, fun j => ?_⟩
  show (((smoothDomain XI.nD hn32).subdomain 0) _) = _
  rw [CosetFftDomainClass.subdomain_0_apply, Inst.smoothDomain_apply]
  show _ * _ = psiV XI.dShift * psiV XI.dGen ^ pos j
  rw [psiV_shift XI hshift, hgen]
  have h := pow_mod_orderOf (zeta XI.nD) (pos j)
  rw [orderOf_zeta hn32] at h
  show _ * ((zeta XI.nD : KCˣ) : KC) ^ (pos j % 2 ^ XI.nD) = _
  rw [← Units.val_pow_eq_pow_val, h, Units.val_pow_eq_pow_val]

/-- `hsel` is satisfiable: the verifier's own selectors (`selOf` of the real RAP skeleton, for `toyInstB`, position `3`: leaves `6, 7`)
mark exactly the leaves of the selection -/
example : (SM.selOf (isSelB (treeSel toyInstB 1 0 #[3])) (skelOf (ragSpec 1 16) 32 32) 0).get
    ((leafEquiv _).symm ⟨6, by decide +kernel⟩) = true := by
  rw [selOf_get, leafNum_symm]; decide +kernel
example : (SM.selOf (isSelB (treeSel toyInstB 1 0 #[3])) (skelOf (ragSpec 1 16) 32 32) 0).get
    ((leafEquiv _).symm ⟨8, by decide +kernel⟩) = false := by
  rw [selOf_get, leafNum_symm]; decide +kernel

end NonVac

#print axioms mdX
#print axioms LX
#print axioms coversC_of_flat
#print axioms verifyFlat_sound''
#print axioms selR_of_selOf
#print axioms selF_of_selOf
#print axioms QR_isSel
#print axioms QF_isSel
#print axioms xsOfPos

end NockvmE2E.Exec.Cover
