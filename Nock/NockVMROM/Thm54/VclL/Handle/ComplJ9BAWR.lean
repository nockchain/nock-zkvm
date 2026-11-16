/-
  Nock/NockVMROM/Thm54/VclL/Handle/ComplJ9BAWR.lean

  **The honest atom-walk rows
  with a ROOT-INDEX parameter `rI`.**

  The J-8 spec rows
  (`ComplJ8Enc.walkRow0E`) use `idxOf` (first occurrence) for both; with `comb p` duplicated in `acs` (reachable
  without `hclA`) they differ.  This module is `ComplJ8Enc`'s walk part with that parameter:

  * `idxRW`, `keyWR`, `dtWR`, `lblWR`, `walkRow0R` (`walkRow0E` with `idx := idxRW`, `ridx := rI root`); the walk
    needs NO property of `rI` beyond the bound `rI n ≤ |cells|`.
  * the base and `𝕂` facts, `walkOk_honest_listR`, `walkChip_honest_listR`, `walkChipHQK_honest_listR`,
    `wColBR_cong` (staging), and `awOK_listR` (`ComplJ8AW.awOK_list` over the variant).
  * sanity: `walkRow0R_idxOf` (at `rI = idxOf` the variant IS `walkRow0E`), `walkRow0E_enc` (`walkRow0E` at the plain
    encoder is `HonestWalkGen.walkRow0`, the J-8 atom-walk rows).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Enc
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8AW

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BAWR

open Nock Nock.Walk Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Walk
open Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8 Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8
open Nock.ComputeTable (FP)

noncomputable section

/-! ## 1. The walk labels at `E`, root serial `rI` -/

section Labels
variable {q : ℕ} {Kfp : Type} [Field Kfp] (E : Noun → FP Kfp) (cells : List Noun) (rI : Noun → ℕ)

/-- **The J-9 row serial of a walk row** (the generator's `GenAtom.wIdx`): `rI node` on a root row (no side bits),
the first occurrence `idxOf node` elsewhere. -/
def idxRW (t : NTree WN) : ℕ := if t.label.bits = [] then rI t.label.node else cells.idxOf t.label.node

theorem idxRW_le (hrI : ∀ n, rI n ≤ cells.length) (t : NTree WN) : idxRW cells rI t ≤ cells.length := by
  unfold idxRW; split_ifs
  · exact hrI _
  · exact List.idxOf_le_length

/-- The export key a walk row consumes: `(fp p, fp l, fp r, idx)`. -/
def keyWR (t : NTree WN) : XKey Kfp :=
  (E t.label.node, E (hdN t.label.node),
    E (tlN t.label.node), idxRW cells rI t)

def dtWR (t : NTree WN) : WalkVCL.DT q Kfp :=
  ⟨E t.label.node, (axisFold t.label.bits : ZMod q),
    E t.label.root, (rI t.label.root : ZMod q),
    (t.label.bits.length : ZMod q)⟩

def lblWR (t : NTree WN) : WalkVCL.LT q Kfp := ((t.label.cL, t.label.cR), dtWR (q := q) E rI t)

theorem dtWR_child (root l r : Noun) (bs : List Bool) (T : List (List Bool)) (b : Bool) :
    dtWR (q := q) E rI (trie root (if b then r else l) (bs ++ [b]) (contT b T)) =
      Chips.ChipRAP.childDT (keyWR E cells rI (trie root (.cell l r) bs T)) b
        (dtWR (q := q) E rI (trie root (.cell l r) bs T)) := by
  obtain ⟨n1, b1, r1⟩ := trie_label root (if b then r else l) (bs ++ [b]) (contT b T)
  obtain ⟨n0, b0, r0⟩ := trie_label root (.cell l r) bs T
  simp only [dtWR, keyWR, Chips.ChipRAP.childDT, WalkVCL.tgt, WalkVCL.keyEdge, childOf, n1, b1, r1, n0, b0, r0,
    hdN, tlN, axisFold_append, WalkVCL.bitZ, List.length_append, List.length_singleton]
  congr 1
  · cases b <;> simp
  · cases b <;> push_cast <;> ring
  · push_cast; ring

/-- The root rows' data: prefix `1`, `len 0`, `node = root` (the root gate's values). -/
theorem dtWR_root {t : NTree WN} (hb : t.label.bits = []) (hn : t.label.node = t.label.root) :
    (dtWR (q := q) E rI t).pre = 1 ∧ (dtWR (q := q) E rI t).len = 0 ∧
      (dtWR (q := q) E rI t).node = (dtWR (q := q) E rI t).root ∧
      (dtWR (q := q) E rI t).ridx = ((keyWR E cells rI t).2.2.2 : ZMod q) := by
  simp [dtWR, keyWR, idxRW, hb, hn, axisFold]

end Labels

/-! ## 2. The walk rows at `E` -/

section Vals
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq F] [DecidableEq K]
  [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  (E : Noun → FP (Quad (algebraMap F K δF))) (cells : List Noun) (rI : Noun → ℕ) (preads : List (Noun × ℕ))
/-- The walk's node valuation `RLC^γ(enc(lblWR t))`. -/
def wNodeValR (γ : K) (t : NTree WN) : K :=
  Nock.Walk.rlc γ (WalkVCL.enc (algebraMap F K δF) (lblWR (q := ringChar F) E rI t))

/-- **The honest values of walk row `j`** (B2 IO quantities `0`; `walkFill` sets them). -/
def walkRow0R (α γ : K) (j : ℕ) : WalkVals F K (Quad (algebraMap F K δF)) where
  idx := ((idxRW cells rI (wTrie cells preads j) : ℕ) : F)
  pre := ((axisFold (wTrie cells preads j).label.bits : ℕ) : F)
  ridx := ((rI (wTrie cells preads j).label.root : ℕ) : F)
  len := (((wTrie cells preads j).label.bits.length : ℕ) : F)
  cL := if (wTrie cells preads j).label.cL then 1 else 0
  cR := if (wTrie cells preads j).label.cR then 1 else 0
  e := (if (wTrie cells preads j).label.cL then 1 else 0) * (if (wTrie cells preads j).label.cR then 1 else 0)
  mL := (((wTrie cells preads j).label.mL : ℕ) : F)
  mR := (((wTrie cells preads j).label.mR : ℕ) : F)
  q := ((qH (krW cells preads) (foCol (walkRows cells preads)) (j + 1) : ℕ) : F)
  qinv := ((qH (krW cells preads) (foCol (walkRows cells preads)) (j + 1) : ℕ) : F)⁻¹
  u := certBit (61 - (wTrie cells preads j).label.bits.length) 1 *
    certBit (61 - (wTrie cells preads j).label.bits.length) 2
  bit := certBit (61 - (wTrie cells preads j).label.bits.length)
  p := E (wTrie cells preads j).label.node
  l := E (hdN (wTrie cells preads j).label.node)
  r := E (tlN (wTrie cells preads j).label.node)
  root := E (wTrie cells preads j).label.root
  ln := α ^ (j + 1)
  cnt := countH (foCol (walkRows cells preads)) α (krW cells preads) (j + 1)
  acc := accH (curCol (wNodeValR δF E rI γ) (walkRows cells preads))
    (chldCol (wNodeValR δF E rI γ) (walkRows cells preads)) (foCol (walkRows cells preads)) α
    (krW cells preads) (j + 1)
  xInv := 0
  pInvL := 0
  pInvR := 0
  xAcc := 0
  pAcc := 0

end Vals

section BaseR
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq F] [DecidableEq K]
  [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  (E : Noun → FP (Quad (algebraMap F K δF))) (cells : List Noun) (rI : Noun → ℕ) (preads : List (Noun × ℕ)) (α γ : K)

/-- **`WalkBaseFacts` on every honest walk row** (`kr = krW`). -/
theorem walkRow0R_base (h62 : ∀ r ∈ pathReads preads, depthOf r.2 ≤ 62)
    (hkp : krW cells preads + (walkRows cells preads).length < ringChar F)
    {n : ℕ} (hn : n = (walkRows cells preads).length) (i : Fin n) :
    WalkBaseFacts (krW cells preads)
      (fun j : Fin n => walkRow0R δF E cells rI preads α γ j) i := by
  subst hn
  have hi := i.isLt
  have hmem := wTrie_mem cells preads hi
  have hlen := walkRows_len_le h62 hmem
  have hq1 := walk_q_id cells preads
  refine
    { cL_bool := by simp only [walkRow0R]; split_ifs <;> simp
      cR_bool := by simp only [walkRow0R]; split_ifs <;> simp
      e_eq := rfl
      u_eq := rfl
      excl := certBit_excl (by omega)
      cert := ?_
      root_pre := ?_
      root_len := ?_
      root_ridx := ?_
      q_first := ?_
      q_step := ?_
      q_inv := ?_
      q_last := ?_
      bit_bool := fun k _ => certBit_bool _ k }
  · show (((wTrie cells preads i).label.bits.length : ℕ) : F) +
        ∑ k ∈ Finset.range 6, (2 : F) ^ k * certBit (61 - (wTrie cells preads i).label.bits.length) k = 61
    rw [certBit_sum (by omega), ← Nat.cast_add, Nat.add_sub_cancel' hlen]; norm_num
  · intro hk
    obtain ⟨t, ht, hb, -⟩ := walkRows_root cells preads i hk
    have : wTrie cells preads i = t := by
      unfold wTrie; rw [List.getD_eq_getElem _ _ hi]; exact Option.some_injective _ ((List.getElem?_eq_getElem hi).symm.trans ht)
    show ((axisFold (wTrie cells preads i).label.bits : ℕ) : F) = 1
    rw [this, hb]; simp [axisFold]
  · intro hk
    obtain ⟨t, ht, hb, -⟩ := walkRows_root cells preads i hk
    have : wTrie cells preads i = t := by
      unfold wTrie; rw [List.getD_eq_getElem _ _ hi]; exact Option.some_injective _ ((List.getElem?_eq_getElem hi).symm.trans ht)
    show (((wTrie cells preads i).label.bits.length : ℕ) : F) = 0
    rw [this, hb]; simp
  · intro hk
    obtain ⟨t, ht, hb, hn⟩ := walkRows_root cells preads i hk
    have : wTrie cells preads i = t := by
      unfold wTrie; rw [List.getD_eq_getElem _ _ hi]; exact Option.some_injective _ ((List.getElem?_eq_getElem hi).symm.trans ht)
    show ((rI (wTrie cells preads i).label.root : ℕ) : F) = ((idxRW cells rI (wTrie cells preads i) : ℕ) : F)
    rw [this, idxRW, if_pos hb, hn]
  · intro h0
    have h0' : (i : ℕ) = 0 := h0
    have e1 := hq1 1 le_rfl (by omega)
    rw [Sf_one] at e1
    show ((qH (krW cells preads) (foCol (walkRows cells preads)) ((i : ℕ) + 1) : ℕ) : F) + 1 =
      ((krW cells preads : ℕ) : F) + (if (wTrie cells preads i).label.cL then 1 else 0) +
        (if (wTrie cells preads i).label.cR then 1 else 0)
    have hf := foCol_walk_cast (F := F) cells preads hi
    rw [h0'] at hf ⊢
    have e := congrArg (Nat.cast : ℕ → F) (show qH (krW cells preads) (foCol (walkRows cells preads)) (0 + 1) + 1 =
      krW cells preads + foCol (walkRows cells preads) (0 + 1) by simpa using (by omega :
        qH (krW cells preads) (foCol (walkRows cells preads)) 1 + 1 = krW cells preads + foCol (walkRows cells preads) 1))
    push_cast at e
    linear_combination e + hf
  · intro hi'
    have e1 := hq1 ((i : ℕ) + 1) (by omega) (by omega)
    have e2 := hq1 ((i : ℕ) + 2) (by omega) (by omega)
    rw [show (i : ℕ) + 2 = (i : ℕ) + 1 + 1 from rfl, Sf_succ] at e2
    have hf := foCol_walk_cast (F := F) cells preads hi'
    show ((qH (krW cells preads) (foCol (walkRows cells preads)) ((i : ℕ) + 1 + 1) : ℕ) : F) + 1 =
      ((qH (krW cells preads) (foCol (walkRows cells preads)) ((i : ℕ) + 1) : ℕ) : F) +
        (if (wTrie cells preads ((i : ℕ) + 1)).label.cL then 1 else 0) +
        (if (wTrie cells preads ((i : ℕ) + 1)).label.cR then 1 else 0)
    have e := congrArg (Nat.cast : ℕ → F) (show qH (krW cells preads) (foCol (walkRows cells preads)) ((i : ℕ) + 1 + 1) + 1 =
      qH (krW cells preads) (foCol (walkRows cells preads)) ((i : ℕ) + 1) +
        foCol (walkRows cells preads) ((i : ℕ) + 1 + 1) by omega)
    push_cast at e
    linear_combination e + hf
  · intro hi'
    obtain ⟨hlt, -, -, hle⟩ := walkRows_queue cells preads
    have hpos := (hlt ((i : ℕ) + 1) (by omega) hi').1
    have hle' := hle ((i : ℕ) + 1) (by omega)
    have e1 := hq1 ((i : ℕ) + 1) (by omega) (by omega)
    have hqp : qH (krW cells preads) (foCol (walkRows cells preads)) ((i : ℕ) + 1) < ringChar F := by omega
    have hne : ((qH (krW cells preads) (foCol (walkRows cells preads)) ((i : ℕ) + 1) : ℕ) : F) ≠ 0 := by
      intro h
      have := natCast_inj_lt (F := F) hqp (show 0 < ringChar F by omega) (by rw [h]; simp)
      omega
    exact mul_inv_cancel₀ hne
  · intro hl
    obtain ⟨-, hlast, -, -⟩ := walkRows_queue cells preads
    show ((qH (krW cells preads) (foCol (walkRows cells preads)) ((i : ℕ) + 1) : ℕ) : F) = 0
    rw [hl, hlast]; simp

end BaseR

section KFactsR
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq F] [DecidableEq K]
  [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  (E : Noun → FP (Quad (algebraMap F K δF))) (cells : List Noun) (rI : Noun → ℕ) (preads : List (Noun × ℕ)) (α γ : K)
  (hF : GeneratedField.PrimeFieldElems F)
include hF

theorem zq_natCastR {k : ℕ} (hk : k < ringChar F) : zq (k : F) = (k : ZMod (ringChar F)) := by
  unfold zq; rw [natOf_natCast hF hk]

omit hF in
theorem decide_ite_oneR (b : Bool) : decide ((if b then (1 : F) else 0) = 1) = b := by
  cases b <;> simp

/-- **The honest row's label is the trie node's `lblWR`.** -/
theorem lblV_walkRow0R (hq : 2 ^ 63 < ringChar F) (hcells : cells.length < ringChar F) (hrI : ∀ n, rI n ≤ cells.length)
    (h62 : ∀ r ∈ pathReads preads, depthOf r.2 ≤ 62) {j : ℕ} (hj : j < (walkRows cells preads).length) :
    lblV δF (walkRow0R δF E cells rI preads α γ j) = lblWR (q := ringChar F) E rI (wTrie cells preads j) := by
  have hlen := walkRows_len_le h62 (wTrie_mem cells preads hj)
  have hax := axisFold_lt (wTrie cells preads j).label.bits
  have h2 : 2 ^ ((wTrie cells preads j).label.bits.length + 1) ≤ 2 ^ 62 :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : (2 : ℕ) ^ 62 < 2 ^ 63 := by norm_num
  have hri := hrI (wTrie cells preads j).label.root
  simp only [lblV, walkRow0R, lblWR, dtWR]
  rw [zq_natCastR hF (by omega), zq_natCastR hF (by omega), zq_natCastR hF (by omega)]
  congr 2
  · exact decide_ite_oneR _
  · exact decide_ite_oneR _

/-- **The honest row's consumed key is the trie node's `keyWR`.** -/
theorem keyV_walkRow0R (hcells : cells.length < ringChar F) (hrI : ∀ n, rI n ≤ cells.length) (j : ℕ) :
    keyV δF (walkRow0R δF E cells rI preads α γ j) = keyWR E cells rI (wTrie cells preads j) := by
  have hi := idxRW_le cells rI hrI (wTrie cells preads j)
  simp only [keyV, walkRow0R, keyWR]
  rw [natOf_natCast hF (by omega)]

theorem curV_walkRow0R (hq : 2 ^ 63 < ringChar F) (hcells : cells.length < ringChar F) (hrI : ∀ n, rI n ≤ cells.length)
    (h62 : ∀ r ∈ pathReads preads, depthOf r.2 ≤ 62) {j : ℕ} (hj : j < (walkRows cells preads).length) :
    curV δF γ (walkRow0R δF E cells rI preads α γ j) =
      curCol (wNodeValR δF E rI γ) (walkRows cells preads) (j + 1) := by
  rw [curCol_succ, List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map, curV,
    lblV_walkRow0R δF E cells rI preads α γ hF hq hcells hrI h62 hj]
  unfold wNodeValR wTrie
  rw [List.getD_eq_getElem _ _ hj]

theorem fanout_walkRow0R (hq : 2 ^ 63 < ringChar F) (hcells : cells.length < ringChar F) (hrI : ∀ n, rI n ≤ cells.length)
    (h62 : ∀ r ∈ pathReads preads, depthOf r.2 ≤ 62) {j : ℕ} (hj : j < (walkRows cells preads).length) :
    WalkVCL.fanout (lblV δF (walkRow0R δF E cells rI preads α γ j)).1 = foCol (walkRows cells preads) (j + 1) := by
  rw [lblV_walkRow0R δF E cells rI preads α γ hF hq hcells hrI h62 hj, foCol_walk cells preads hj,
    walkRows_fanout (wTrie_mem cells preads hj)]
  rfl

theorem ccV_walkRow0R (hq : 2 ^ 63 < ringChar F) (hcells : cells.length < ringChar F) (hrI : ∀ n, rI n ≤ cells.length)
    (h62 : ∀ r ∈ pathReads preads, depthOf r.2 ≤ 62) {j : ℕ} (hj : j < (walkRows cells preads).length) :
    ccV δF α γ (walkRow0R δF E cells rI preads α γ j) =
      ∑ l ∈ Finset.Icc 1 (foCol (walkRows cells preads) (j + 1)), α ^ l *
        chldCol (wNodeValR δF E rI γ) (walkRows cells preads) (j + 1) l := by
  unfold ccV
  rw [fanout_walkRow0R δF E cells rI preads α γ hF hq hcells hrI h62 hj]
  refine Finset.sum_congr rfl fun l hl => ?_
  obtain ⟨hl1, hl2⟩ := Finset.mem_Icc.mp hl
  congr 1
  have hlbl := lblV_walkRow0R δF E cells rI preads α γ hF hq hcells hrI h62 hj
  have hkey := keyV_walkRow0R δF E cells rI preads α γ hF hcells hrI j
  rw [hlbl, hkey]
  obtain ⟨root, n, bs, T, hT⟩ := walkRows_trie (wTrie_mem cells preads hj)
  rw [foCol_walk cells preads hj, walkRows_fanout (wTrie_mem cells preads hj)] at hl2
  rw [hT] at hl2 ⊢
  obtain ⟨a, c, rfl, hc⟩ := trie_child_get root n bs T l hl1 hl2
  have hch : chldCol (wNodeValR δF E rI γ) (walkRows cells preads) (j + 1) l =
      wNodeValR δF E rI γ (trie root
        (if sideOf ((trie root (.cell a c) bs T).label.cL, (trie root (.cell a c) bs T).label.cR) l then c else a)
        (bs ++ [sideOf ((trie root (.cell a c) bs T).label.cL, (trie root (.cell a c) bs T).label.cR) l])
        (contT (sideOf ((trie root (.cell a c) bs T).label.cL, (trie root (.cell a c) bs T).label.cR) l) T)) := by
    unfold chldCol
    have hw : (walkRows cells preads)[j]? = some (trie root (.cell a c) bs T) := by
      rw [List.getElem?_eq_getElem hj, ← hT]; unfold wTrie; rw [List.getD_eq_getElem _ _ hj]
    rw [Nat.add_sub_cancel, hw]
    simp [hc]
  rw [hch]
  unfold wNodeValR
  congr 1
  show WalkVCL.enc (algebraMap F K δF) (((false, false), _) : WalkVCL.LT (ringChar F) _) =
    WalkVCL.enc (algebraMap F K δF) ((_, dtWR (q := ringChar F) E rI _) : WalkVCL.LT (ringChar F) _)
  rw [dtWR_child]
  rfl

/-- **`WalkKFacts` on every honest walk row**, at every coin pair `(α, γ)` (no coin event). -/
theorem walkRow0R_K (hq : 2 ^ 63 < ringChar F) (hcells : cells.length < ringChar F) (hrI : ∀ n, rI n ≤ cells.length)
    (h62 : ∀ r ∈ pathReads preads, depthOf r.2 ≤ 62) {n : ℕ} (hn : n = (walkRows cells preads).length)
    (i : Fin n) :
    WalkKFacts δF (krW cells preads) (fun j : Fin n => walkRow0R δF E cells rI preads α γ j) α γ i := by
  subst hn
  have hi := i.isLt
  obtain ⟨hw, hz⟩ := honest_walk_acc_zero (wNodeValR δF E rI γ) (walkForest cells preads)
    (walkForest_ne_nil cells preads) α
  change WalkSatInGate (curCol (wNodeValR δF E rI γ) (walkRows cells preads))
    (chldCol (wNodeValR δF E rI γ) (walkRows cells preads)) (foCol (walkRows cells preads)) (lnH α)
    (countH (foCol (walkRows cells preads)) α (krW cells preads))
    (accH (curCol (wNodeValR δF E rI γ) (walkRows cells preads))
      (chldCol (wNodeValR δF E rI γ) (walkRows cells preads)) (foCol (walkRows cells preads)) α (krW cells preads))
    α (α ^ krW cells preads) (krW cells preads) (walkRows cells preads).length at hw
  change accH (curCol (wNodeValR δF E rI γ) (walkRows cells preads))
      (chldCol (wNodeValR δF E rI γ) (walkRows cells preads)) (foCol (walkRows cells preads)) α (krW cells preads)
      (walkRows cells preads).length = 0 at hz
  have fo := fun (j : ℕ) (hj : j < (walkRows cells preads).length) =>
    fanout_walkRow0R δF E cells rI preads α γ hF hq hcells hrI h62 hj
  have cc := fun (j : ℕ) (hj : j < (walkRows cells preads).length) =>
    ccV_walkRow0R δF E cells rI preads α γ hF hq hcells hrI h62 hj
  refine
    { ln_first := ?_
      ln_step := ?_
      cnt_first := ?_
      cnt_step := ?_
      acc_first := ?_
      acc_step := ?_
      acc_last := ?_ }
  · intro h0
    show α ^ ((i : ℕ) + 1) = α
    rw [h0, zero_add, pow_one]
  · intro hi'
    show α ^ ((i : ℕ) + 1 + 1) = α * α ^ ((i : ℕ) + 1)
    ring
  · intro h0
    show countH (foCol (walkRows cells preads)) α (krW cells preads) ((i : ℕ) + 1) = _
    rw [fo i hi]
    simp only [countH, h0, zero_add, Sf_one]
  · intro hi'
    show countH (foCol (walkRows cells preads)) α (krW cells preads) ((i : ℕ) + 1 + 1) =
      countH (foCol (walkRows cells preads)) α (krW cells preads) ((i : ℕ) + 1) * _
    rw [fo ((i : ℕ) + 1) hi']
    simp only [countH, Sf_succ, pow_add]
    ring
  · intro h0
    show accH _ _ _ α (krW cells preads) ((i : ℕ) + 1) = α ^ krW cells preads * _
    rw [cc i hi, h0, zero_add, hw.accInit, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  · intro hi'
    have hs := hw.accStep ((i : ℕ) + 1) (by omega) hi'
    have hcu := curV_walkRow0R δF E cells rI preads α γ hF hq hcells hrI h62 hi'
    show algebraMap F K (1 - if (i : ℕ) + 1 < krW cells preads then 1 else 0) * α ^ ((i : ℕ) + 1 + 1) *
        curV δF γ (walkRow0R δF E cells rI preads α γ ((i : ℕ) + 1)) +
        (accH _ _ _ α (krW cells preads) ((i : ℕ) + 1 + 1) - accH _ _ _ α (krW cells preads) ((i : ℕ) + 1)) =
      countH (foCol (walkRows cells preads)) α (krW cells preads) ((i : ℕ) + 1) *
        ccV δF α γ (walkRow0R δF E cells rI preads α γ ((i : ℕ) + 1))
    rw [cc ((i : ℕ) + 1) hi', hcu, Finset.mul_sum]
    have hdq : Nock.Walk.deqCoeff (K := K) (krW cells preads) ((i : ℕ) + 1 + 1) =
        algebraMap F K (1 - if (i : ℕ) + 1 < krW cells preads then 1 else 0) := by
      unfold Nock.Walk.deqCoeff Nock.Walk.rootMask
      by_cases hik : (i : ℕ) + 1 < krW cells preads
      · rw [if_pos (by omega), if_pos hik]; simp
      · rw [if_neg (by omega), if_neg hik]; simp
    rw [← hdq]
    simp only [lnH] at hs
    have hsum : (∑ l ∈ Finset.Icc 1 (foCol (walkRows cells preads) ((i : ℕ) + 1 + 1)),
        α ^ l * countH (foCol (walkRows cells preads)) α (krW cells preads) ((i : ℕ) + 1) *
          chldCol (wNodeValR δF E rI γ) (walkRows cells preads) ((i : ℕ) + 1 + 1) l) =
        ∑ l ∈ Finset.Icc 1 (foCol (walkRows cells preads) ((i : ℕ) + 1 + 1)),
          countH (foCol (walkRows cells preads)) α (krW cells preads) ((i : ℕ) + 1) *
            (α ^ l * chldCol (wNodeValR δF E rI γ) (walkRows cells preads) ((i : ℕ) + 1 + 1) l) :=
      Finset.sum_congr rfl fun l _ => by ring
    rw [hsum] at hs
    linear_combination hs
  · intro hl
    show accH _ _ _ α (krW cells preads) ((i : ℕ) + 1) = 0
    rw [hl]; exact hz

end KFactsR

section WalkR
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [FiniteDimensional F K] [DecidableEq F]
  [DecidableEq K] [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n)
  (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)

local notation "𝕂′" => Quad (algebraMap F K δF)

/-- The honest (unfilled) walk rows at the chip's walk coins `(chals 0, chals 1)`. -/
abbrev wRowsBR (E : Noun → FP (Quad (algebraMap F K δF))) (cells : List Noun) (rI : Noun → ℕ) (preads : List (Noun × ℕ)) :
    ℕ → WalkVals F K (Quad (algebraMap F K δF)) :=
  walkRow0R δF E cells rI preads (chals 0) (chals 1)

/-- The honest filled walk rows. -/
abbrev wValsBR (E : Noun → FP (Quad (algebraMap F K δF))) (γ ρ : Quad (algebraMap F K δF)) (cells : List Noun) (rI : Noun → ℕ) (preads : List (Noun × ℕ)) :
    Fin n → WalkVals F K (Quad (algebraMap F K δF)) :=
  fun i => walkFill δF γ ρ (wRowsBR δF chals E cells rI preads) i

/-- The honest 132-column walk column function. -/
abbrev wColBR (E : Noun → FP (Quad (algebraMap F K δF))) (γ ρ : Quad (algebraMap F K δF)) (cells : List Noun) (rI : Noun → ℕ) (preads : List (Noun × ℕ)) :
    ℕ → Fin n → F :=
  walkCol δF b (krW cells preads) (wValsBR δF chals E γ ρ cells rI preads)

theorem wRowsBR_root (E : Noun → FP 𝕂′) (cells : List Noun) (rI : Noun → ℕ) (preads : List (Noun × ℕ)) {j : ℕ}
    (hj : j < (walkRows cells preads).length) (hk : j < krW cells preads) :
    (wRowsBR δF chals E cells rI preads j).root = (wRowsBR δF chals E cells rI preads j).p := by
  obtain ⟨t, ht, -, hnr⟩ := walkRows_root cells preads j hk
  have : wTrie cells preads j = t := by
    unfold wTrie; rw [List.getD_eq_getElem _ _ hj]
    exact Option.some_injective _ ((List.getElem?_eq_getElem hj).symm.trans ht)
  show E (wTrie cells preads j).label.root =
    E (wTrie cells preads j).label.node
  rw [this, hnr]

/-- The `ok`-gated walk chip at the honest rows (`walkOk_sat` at `walkRow0R`). -/
theorem walkOk_honest_listR (E : Noun → FP 𝕂′) (γ ρ : 𝕂′) (cells : List Noun) (rI : Noun → ℕ) (preads : List (Noun × ℕ))
    (hF : GeneratedField.PrimeFieldElems F) (hq : 2 ^ 63 < ringChar F) (hcells : cells.length < ringChar F) (hrI : ∀ n, rI n ≤ cells.length)
    (h61 : WalkDepthOK preads) (hkp : krW cells preads + (walkRows cells preads).length < ringChar F)
    (hN : n = (walkRows cells preads).length)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hok : ChalsOK δF chals γ ρ 11)
    (hx : ∀ j < n, FiniteIO.compress (m := 11) ⟨γ, ρ⟩ (wxKeyV δF (wRowsBR δF chals E cells rI preads j)) ≠ 0)
    (hL : ∀ j < n, FiniteIO.compress (m := 8) ⟨γ, ρ⟩ (wrecLV δF (wRowsBR δF chals E cells rI preads j)) ≠ 0)
    (hR : ∀ j < n, FiniteIO.compress (m := 8) ⟨γ, ρ⟩ (wrecRV δF (wRowsBR δF chals E cells rI preads j)) ≠ 0)
    (hXt : ∑ k ∈ Finset.range n, (walkFillInv δF γ ρ (wRowsBR δF chals E cells rI preads k)).xInv =
      Quad.mk _ (pubs 0) (pubs 1))
    (hPt : ∑ k ∈ Finset.range n, wpTermV δF (walkFillInv δF γ ρ (wRowsBR δF chals E cells rI preads k)) =
      Quad.mk _ (pubs 2) (pubs 3)) :
    RAP.SatisfiesWithPreprocessing (walkChipOk δF (krW cells preads) b hn nodes orbit chals pubs true)
      (fun j => honestQ hn nodes (wColBR δF b chals E γ ρ cells rI preads) 132
        (Fin.cast (walkChipOk_w δF (krW cells preads) b hn nodes orbit chals pubs true) j)) := by
  have h62 := walkDepth62 h61
  exact walkOk_sat δF (krW cells preads) b hn nodes orbit chals pubs (wValsBR δF chals E γ ρ cells rI preads) hF
    hinj hadj γ ρ hok
    (fun i => walkBaseFacts_fill δF γ ρ (wRowsBR δF chals E cells rI preads) (krW cells preads) i
      (walkRow0R_base δF E cells rI preads (chals 0) (chals 1) h62 hkp hN i))
    (fun i => walkKFacts_fill δF γ ρ (wRowsBR δF chals E cells rI preads) (krW cells preads) _ _ i
      (walkRow0R_K δF E cells rI preads (chals 0) (chals 1) hF hq hcells hrI h62 hN i))
    (fun i => walkFill_mixed δF γ ρ (wRowsBR δF chals E cells rI preads) (krW cells preads) pubs i
      (fun j hj hk => wRowsBR_root δF chals E cells rI preads (hN ▸ hj) hk) hx hL hR hXt hPt)

theorem walkChip_honest_listR (E : Noun → FP 𝕂′) (γ ρ : 𝕂′) (cells : List Noun) (rI : Noun → ℕ) (preads : List (Noun × ℕ))
    (hF : GeneratedField.PrimeFieldElems F) (hq : 2 ^ 63 < ringChar F) (hcells : cells.length < ringChar F) (hrI : ∀ n, rI n ≤ cells.length)
    (h61 : WalkDepthOK preads) (hkp : krW cells preads + (walkRows cells preads).length < ringChar F)
    (hN : n = (walkRows cells preads).length)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hok : ChalsOK δF chals γ ρ 11)
    (hx : ∀ j < n, FiniteIO.compress (m := 11) ⟨γ, ρ⟩ (wxKeyV δF (wRowsBR δF chals E cells rI preads j)) ≠ 0)
    (hL : ∀ j < n, FiniteIO.compress (m := 8) ⟨γ, ρ⟩ (wrecLV δF (wRowsBR δF chals E cells rI preads j)) ≠ 0)
    (hR : ∀ j < n, FiniteIO.compress (m := 8) ⟨γ, ρ⟩ (wrecRV δF (wRowsBR δF chals E cells rI preads j)) ≠ 0)
    (hXt : ∑ k ∈ Finset.range n, (walkFillInv δF γ ρ (wRowsBR δF chals E cells rI preads k)).xInv =
      Quad.mk _ (pubs 0) (pubs 1))
    (hPt : ∑ k ∈ Finset.range n, wpTermV δF (walkFillInv δF γ ρ (wRowsBR δF chals E cells rI preads k)) =
      Quad.mk _ (pubs 2) (pubs 3)) :
    (walkChip δF (krW cells preads) b hn nodes orbit chals pubs).rap.Satisfies
      (honestQ hn nodes (wColBR δF b chals E γ ρ cells rI preads) _) := by
  exact (walkChipOk_sat δF (krW cells preads) b hn nodes orbit chals pubs true _
    (walkOk_honest_listR δF b hn nodes orbit chals pubs E γ ρ cells rI preads hF hq hcells hrI h61 hkp hN hinj hadj hok
      hx hL hR hXt hPt)).2.1

/-- **`walkChipHQK_honest_listR`: the ternary-kind handle walk twin accepts `walkTraceHQ`** at the honest walk
columns and ANY child handle columns with kinds in `{0, 1, 2}`, given the three handle poles and the two `𝕂′`
publics equal to the totals. -/
theorem walkChipHQK_honest_listR (E : Noun → FP 𝕂′) (γ ρ : 𝕂′) (cells : List Noun) (rI : Noun → ℕ) (preads : List (Noun × ℕ))
    (kLv vLv kRv vRv : Fin n → F)
    (hF : GeneratedField.PrimeFieldElems F) (hq : 2 ^ 63 < ringChar F) (hcells : cells.length < ringChar F) (hrI : ∀ n, rI n ≤ cells.length)
    (h61 : WalkDepthOK preads) (hkp : krW cells preads + (walkRows cells preads).length < ringChar F)
    (hN : n = (walkRows cells preads).length)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hok : ChalsOK δF chals γ ρ 11)
    (hx : ∀ j < n, FiniteIO.compress (m := 11) ⟨γ, ρ⟩ (wxKeyV δF (wRowsBR δF chals E cells rI preads j)) ≠ 0)
    (hL : ∀ j < n, FiniteIO.compress (m := 8) ⟨γ, ρ⟩ (wrecLV δF (wRowsBR δF chals E cells rI preads j)) ≠ 0)
    (hR : ∀ j < n, FiniteIO.compress (m := 8) ⟨γ, ρ⟩ (wrecRV δF (wRowsBR δF chals E cells rI preads j)) ≠ 0)
    (hXt : ∑ k ∈ Finset.range n, (walkFillInv δF γ ρ (wRowsBR δF chals E cells rI preads k)).xInv =
      Quad.mk _ (pubs 0) (pubs 1))
    (hPt : ∑ k ∈ Finset.range n, wpTermV δF (walkFillInv δF γ ρ (wRowsBR δF chals E cells rI preads k)) =
      Quad.mk _ (pubs 2) (pubs 3))
    (hkL : ∀ i, kLv i = 0 ∨ kLv i = 1 ∨ kLv i = 2) (hkR : ∀ i, kRv i = 0 ∨ kRv i = 1 ∨ kRv i = 2)
    (hpX : ∀ i, WalkTraceHQ.dRow δF (krW cells preads) b hn nodes orbit chals pubs WalkHC.xKeyH
      (wColBR δF b chals E γ ρ cells rI preads) kLv vLv kRv vRv i ≠ 0)
    (hpL : ∀ i, WalkTraceHQ.dRow δF (krW cells preads) b hn nodes orbit chals pubs WalkHC.recLH
      (wColBR δF b chals E γ ρ cells rI preads) kLv vLv kRv vRv i ≠ 0)
    (hpR : ∀ i, WalkTraceHQ.dRow δF (krW cells preads) b hn nodes orbit chals pubs WalkHC.recRH
      (wColBR δF b chals E γ ρ cells rI preads) kLv vLv kRv vRv i ≠ 0)
    (hpubX : Quad.mk _ (pubs WalkHQ.pubXQ) (pubs (WalkHQ.pubXQ + 1)) = ∑ j ∈ Finset.range n,
      (WalkTraceHQ.dN δF (krW cells preads) b hn nodes orbit chals pubs (wColBR δF b chals E γ ρ cells rI preads)
        kLv vLv kRv vRv WalkHC.xKeyH j)⁻¹)
    (hpubP : Quad.mk _ (pubs WalkHQ.pubPQ) (pubs (WalkHQ.pubPQ + 1)) = ∑ j ∈ Finset.range n,
      (liftQ δF (WalkTraceH.cN j (wColBR (n := n) δF b chals E γ ρ cells rI preads WChip.mL)) *
          (WalkTraceHQ.dN δF (krW cells preads) b hn nodes orbit chals pubs (wColBR δF b chals E γ ρ cells rI preads)
            kLv vLv kRv vRv WalkHC.recLH j)⁻¹ +
        liftQ δF (WalkTraceH.cN j (wColBR (n := n) δF b chals E γ ρ cells rI preads WChip.mR)) *
          (WalkTraceHQ.dN δF (krW cells preads) b hn nodes orbit chals pubs (wColBR δF b chals E γ ρ cells rI preads)
            kLv vLv kRv vRv WalkHC.recRH j)⁻¹)) :
    (CellTwinK.walkChipHQK δF (krW cells preads) b hn nodes orbit chals pubs).rap.Satisfies
      (WalkTraceHQ.walkTraceHQ δF (krW cells preads) b hn nodes orbit chals pubs
        (wColBR δF b chals E γ ρ cells rI preads) kLv vLv kRv vRv) :=
  WalkTraceHQ.walkChipHQK_accepts_honest δF (krW cells preads) b hn nodes orbit chals pubs _ kLv vLv kRv vRv hinj hadj
    (walkChip_honest_listR δF b hn nodes orbit chals pubs E γ ρ cells rI preads hF hq hcells hrI h61 hkp hN hinj hadj hok
      hx hL hR hXt hPt)
    hkL hkR hpX hpL hpR hpubX hpubP

end WalkR


section StageWR
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [FiniteDimensional F K] [DecidableEq F]
  [DecidableEq K] [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n)
  (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h)

/-- The honest walk columns `< 93`: base coin-free, fingerprint roles read `E` only. -/
theorem wColBR_cong (chals chals' : ℕ → K) (E E' : Noun → FP (Quad (algebraMap F K δF))) (γ ρ γ' ρ' : Quad (algebraMap F K δF)) (cells : List Noun) (rI : Noun → ℕ)
    (preads : List (Noun × ℕ)) (k : ℕ) (hk : k < 93) (hz : 21 ≤ k → E = E') :
    wColBR (n := n) δF b chals E γ ρ cells rI preads k = wColBR (n := n) δF b chals' E' γ' ρ' cells rI preads k := by
  funext i
  unfold wColBR walkCol
  by_cases h1 : k < 21
  · simp only [if_pos h1]
    simp only [wValsBR, wRowsBR, walkFill, walkFillInv, walkRow0R, WalkVals.base, WalkVals.named]
  · simp only [if_neg h1]
    obtain rfl := hz (by omega)
    congr 1
    unfold wroleVal
    have hρ : (k - 21) / 3 < 24 := by omega
    simp only [hρ, if_true]
    have e : ∀ s, (wValsBR (n := n) δF chals E γ ρ cells rI preads i).fpSlot s =
        (wValsBR (n := n) δF chals' E γ' ρ' cells rI preads i).fpSlot s := fun s => fpSlot_congr' _ _ rfl rfl rfl rfl s
    rw [e]


end StageWR

/-! ## 4. The atom walk at the variant rows -/

section AWList
open Nock.NockVMROM.Thm54.VclL.GenWalk (krW walkRows one_le_krW krW_le_rows)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Walk
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinK
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V (AWChipOK)

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {hV nV : ℕ} (hnV : 0 < nV) (nodesV : Fin nV → ZMod p)
  (orbitV : StrictOrbitDomain (ZMod p) 3 hV) (chals pubs : ℕ → K)

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **The atom walk at the spec rows** (`krootsV = krW cells preads ≥ 1`, `nV = |walkRows cells preads|`): the honest
atom-walk trace (L2's `wColB` at the atom cell list `cells` and the atom-walk reads `preads`) is accepted and bound
by `walkChipHQK`, so `AWChipOK` holds.  Inputs: L2's `walkOk_honest_list` hypotheses (depth `≤ 61` reads
`WalkDepthOK preads`, the IO poles and terminals), the child kinds, the handle poles and terminals. -/
theorem awOK_listR (E : Noun → FP 𝕂′) (γ ρ : 𝕂′) (cells : List Noun) (rI : Noun → ℕ) (preads : List (Noun × ℕ)) (kLv vLv kRv vRv : Fin nV → ZMod p)
    (hq : 2 ^ 63 < ringChar (ZMod p)) (hcells : cells.length < ringChar (ZMod p)) (hrI : ∀ n, rI n ≤ cells.length)
    (h61 : WalkDepthOK preads) (hkp : krW cells preads + (walkRows cells preads).length < ringChar (ZMod p))
    (hN : nV = (walkRows cells preads).length)
    (hinj : Function.Injective nodesV)
    (hadj : ∀ (i : Fin nV) (hi : (i : ℕ) + 1 < nV), nodesV ⟨(i : ℕ) + 1, hi⟩ = nodesV i * orbitV.ω)
    (hok : ChalsOK δ chals γ ρ 11)
    (hx : ∀ j < nV, FiniteIO.compress (m := 11) ⟨γ, ρ⟩ (wxKeyV δ (wRowsBR δ chals E cells rI preads j)) ≠ 0)
    (hL : ∀ j < nV, FiniteIO.compress (m := 8) ⟨γ, ρ⟩ (wrecLV δ (wRowsBR δ chals E cells rI preads j)) ≠ 0)
    (hR : ∀ j < nV, FiniteIO.compress (m := 8) ⟨γ, ρ⟩ (wrecRV δ (wRowsBR δ chals E cells rI preads j)) ≠ 0)
    (hXt : ∑ k ∈ Finset.range nV, (walkFillInv δ γ ρ (wRowsBR δ chals E cells rI preads k)).xInv =
      Quad.mk _ (pubs 0) (pubs 1))
    (hPt : ∑ k ∈ Finset.range nV, wpTermV δ (walkFillInv δ γ ρ (wRowsBR δ chals E cells rI preads k)) =
      Quad.mk _ (pubs 2) (pubs 3))
    (hkL : ∀ i, kLv i = 0 ∨ kLv i = 1 ∨ kLv i = 2) (hkR : ∀ i, kRv i = 0 ∨ kRv i = 1 ∨ kRv i = 2)
    (hpX : ∀ i, WalkTraceHQ.dRow δ (krW cells preads) b hnV nodesV orbitV chals pubs WalkHC.xKeyH
      (wColBR δ b chals E γ ρ cells rI preads) kLv vLv kRv vRv i ≠ 0)
    (hpL : ∀ i, WalkTraceHQ.dRow δ (krW cells preads) b hnV nodesV orbitV chals pubs WalkHC.recLH
      (wColBR δ b chals E γ ρ cells rI preads) kLv vLv kRv vRv i ≠ 0)
    (hpR : ∀ i, WalkTraceHQ.dRow δ (krW cells preads) b hnV nodesV orbitV chals pubs WalkHC.recRH
      (wColBR δ b chals E γ ρ cells rI preads) kLv vLv kRv vRv i ≠ 0)
    (hpubX : Quad.mk _ (pubs WalkHQ.pubXQ) (pubs (WalkHQ.pubXQ + 1)) = ∑ j ∈ Finset.range nV,
      (WalkTraceHQ.dN δ (krW cells preads) b hnV nodesV orbitV chals pubs (wColBR δ b chals E γ ρ cells rI preads)
        kLv vLv kRv vRv WalkHC.xKeyH j)⁻¹)
    (hpubP : Quad.mk _ (pubs WalkHQ.pubPQ) (pubs (WalkHQ.pubPQ + 1)) = ∑ j ∈ Finset.range nV,
      (liftQ δ (WalkTraceH.cN j (wColBR (n := nV) δ b chals E γ ρ cells rI preads WChip.mL)) *
          (WalkTraceHQ.dN δ (krW cells preads) b hnV nodesV orbitV chals pubs (wColBR δ b chals E γ ρ cells rI preads)
            kLv vLv kRv vRv WalkHC.recLH j)⁻¹ +
        liftQ δ (WalkTraceH.cN j (wColBR (n := nV) δ b chals E γ ρ cells rI preads WChip.mR)) *
          (WalkTraceHQ.dN δ (krW cells preads) b hnV nodesV orbitV chals pubs (wColBR δ b chals E γ ρ cells rI preads)
            kLv vLv kRv vRv WalkHC.recRH j)⁻¹)) :
    AWChipOK δ b (krW cells preads) hnV nodesV orbitV chals pubs
      (fun j => WalkTraceHQ.walkTraceHQ δ (krW cells preads) b hnV nodesV orbitV chals pubs
        (wColBR δ b chals E γ ρ cells rI preads) kLv vLv kRv vRv
        (Fin.cast (walkChipHQK_width δ (krW cells preads) b hnV nodesV orbitV chals pubs) j)) :=
  ComplJ8AW.awOK_present δ b (krW cells preads) hnV nodesV orbitV chals pubs _ kLv vLv kRv vRv hinj hadj
    (walkOk_honest_listR δ b hnV nodesV orbitV chals pubs E γ ρ cells rI preads
      (GeneratedField.primeFieldElems_zmod p) hq hcells hrI h61 hkp hN hinj hadj hok hx hL hR hXt hPt)
    hkL hkR hpX hpL hpR hpubX hpubP (one_le_krW cells preads) (hN ▸ krW_le_rows cells preads) (by omega)

end AWList

/-! ## 5. Sanity: the variant at `rI = idxOf` is the J-8 row -/

section Sanity
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq F] [DecidableEq K]
  [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  (cells : List Noun) (preads : List (Noun × ℕ)) (α γ : K)

/-- **At `rI = idxOf` the variant rows are `ComplJ8Enc.walkRow0E`** (any encoder). -/
theorem walkRow0R_idxOf (E : Noun → FP (Quad (algebraMap F K δF))) :
    walkRow0R δF E cells (fun n => cells.idxOf n) preads α γ = ComplJ8Enc.walkRow0E δF E cells preads α γ := by
  funext j
  have h : idxRW cells (fun n => cells.idxOf n) (wTrie cells preads j) =
      cells.idxOf (wTrie cells preads j).label.node := by
    unfold idxRW; split_ifs <;> rfl
  unfold walkRow0R ComplJ8Enc.walkRow0E
  rw [h]
  rfl

/-- **`walkRow0E` at the plain fingerprint encoder is `HonestWalkGen.walkRow0`** (the J-8 atom-walk rows). -/
theorem walkRow0E_enc (z : Quad (algebraMap F K δF)) :
    ComplJ8Enc.walkRow0E δF (GlobalCarryRecognizer.enc z) cells preads α γ = walkRow0 δF z cells preads α γ := rfl

/-- **The variant agrees with the J-8 atom-walk rows when `rI` is the first occurrence** (J-8's binders give
`rIAP = idxN`, and `idxN = idxOf` on the atom cells). -/
theorem walkRow0R_eq_j8 (z : Quad (algebraMap F K δF)) (rI : Noun → ℕ) (hrI : ∀ n, rI n = cells.idxOf n) :
    walkRow0R δF (GlobalCarryRecognizer.enc z) cells rI preads α γ = walkRow0 δF z cells preads α γ := by
  have e : rI = fun n => cells.idxOf n := funext hrI
  subst e
  rw [walkRow0R_idxOf, walkRow0E_enc]

end Sanity

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BAWR
