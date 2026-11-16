/-
  Nock/NockVMROM/Thm54/VclL/Handle/ComplJ8Enc.lean

  * Walk: `keyWE / dtWE / lblWE` (`GenWalkLabels` at `E`), `walkRow0E` (`HonestWalkGen.walkRow0` with the four
    fingerprints `E node / E hd / E tl / E root`), its base and `𝕂` facts, and the J-8 walk chips' honest lists
    (`ComplJ8Walk` at `E`).  The walk needs NO property of `E`.
  * Cell: `cellRowBE` (`ComplJ8Cell.cellRowB` with `p l r := E n, E hd, E tl`) and the cell chips' honest lists;
    these need `E (cell a b) = cons z (E a) (E b)` and `E (atom v) = atomFP z v` on small atoms.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Walk

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Enc

open Nock Nock.Walk Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Walk
open Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8 Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8
open Nock.ComputeTable (FP)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Cell (isBig wOf idOf aOf kbOf wOf_bool wOf_zero cellCol_lt limbs_ne_zero sideOK_child kbLB kbRB rank_children)

noncomputable section

/-! ## 1. The walk labels at `E` -/

section Labels
variable {q : ℕ} {Kfp : Type} [Field Kfp] (E : Noun → FP Kfp) (cells : List Noun)
/-- The export key a walk row consumes: `(fp p, fp l, fp r, idx)`. -/
def keyWE (t : NTree WN) : XKey Kfp :=
  (E t.label.node, E (hdN t.label.node),
    E (tlN t.label.node), cells.idxOf t.label.node)

def dtWE (t : NTree WN) : WalkVCL.DT q Kfp :=
  ⟨E t.label.node, (axisFold t.label.bits : ZMod q),
    E t.label.root, (cells.idxOf t.label.root : ZMod q),
    (t.label.bits.length : ZMod q)⟩

def lblWE (t : NTree WN) : WalkVCL.LT q Kfp := ((t.label.cL, t.label.cR), dtWE (q := q) E cells t)

theorem dtWE_child (root l r : Noun) (bs : List Bool) (T : List (List Bool)) (b : Bool) :
    dtWE (q := q) E cells (trie root (if b then r else l) (bs ++ [b]) (contT b T)) =
      Chips.ChipRAP.childDT (keyWE E cells (trie root (.cell l r) bs T)) b
        (dtWE (q := q) E cells (trie root (.cell l r) bs T)) := by
  obtain ⟨n1, b1, r1⟩ := trie_label root (if b then r else l) (bs ++ [b]) (contT b T)
  obtain ⟨n0, b0, r0⟩ := trie_label root (.cell l r) bs T
  simp only [dtWE, keyWE, Chips.ChipRAP.childDT, WalkVCL.tgt, WalkVCL.keyEdge, childOf, n1, b1, r1, n0, b0, r0,
    hdN, tlN, axisFold_append, WalkVCL.bitZ, List.length_append, List.length_singleton]
  congr 1
  · cases b <;> simp
  · cases b <;> push_cast <;> ring
  · push_cast; ring

/-- The root rows' data: prefix `1`, `len 0`, `node = root` (the root gate's values). -/
theorem dtWE_root {t : NTree WN} (hb : t.label.bits = []) (hn : t.label.node = t.label.root) :
    (dtWE (q := q) E cells t).pre = 1 ∧ (dtWE (q := q) E cells t).len = 0 ∧
      (dtWE (q := q) E cells t).node = (dtWE (q := q) E cells t).root ∧
      (dtWE (q := q) E cells t).ridx = ((keyWE E cells t).2.2.2 : ZMod q) := by
  simp [dtWE, keyWE, hb, hn, axisFold]

end Labels

/-! ## 2. The walk rows at `E` -/

section Vals
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq F] [DecidableEq K]
  [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  (E : Noun → FP (Quad (algebraMap F K δF))) (cells : List Noun) (preads : List (Noun × ℕ))
/-- The walk's node valuation `RLC^γ(enc(lblWE t))`. -/
def wNodeValE (γ : K) (t : NTree WN) : K :=
  Nock.Walk.rlc γ (WalkVCL.enc (algebraMap F K δF) (lblWE (q := ringChar F) E cells t))

/-- **The honest values of walk row `j`** (B2 IO quantities `0`; `walkFill` sets them). -/
def walkRow0E (α γ : K) (j : ℕ) : WalkVals F K (Quad (algebraMap F K δF)) where
  idx := ((cells.idxOf (wTrie cells preads j).label.node : ℕ) : F)
  pre := ((axisFold (wTrie cells preads j).label.bits : ℕ) : F)
  ridx := ((cells.idxOf (wTrie cells preads j).label.root : ℕ) : F)
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
  acc := accH (curCol (wNodeValE δF E cells γ) (walkRows cells preads))
    (chldCol (wNodeValE δF E cells γ) (walkRows cells preads)) (foCol (walkRows cells preads)) α
    (krW cells preads) (j + 1)
  xInv := 0
  pInvL := 0
  pInvR := 0
  xAcc := 0
  pAcc := 0

end Vals

section BaseE
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq F] [DecidableEq K]
  [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  (E : Noun → FP (Quad (algebraMap F K δF))) (cells : List Noun) (preads : List (Noun × ℕ)) (α γ : K)

/-- **`WalkBaseFacts` on every honest walk row** (`kr = krW`). -/
theorem walkRow0E_base (h62 : ∀ r ∈ pathReads preads, depthOf r.2 ≤ 62)
    (hkp : krW cells preads + (walkRows cells preads).length < ringChar F)
    {n : ℕ} (hn : n = (walkRows cells preads).length) (i : Fin n) :
    WalkBaseFacts (krW cells preads)
      (fun j : Fin n => walkRow0E δF E cells preads α γ j) i := by
  subst hn
  have hi := i.isLt
  have hmem := wTrie_mem cells preads hi
  have hlen := walkRows_len_le h62 hmem
  have hq1 := walk_q_id cells preads
  refine
    { cL_bool := by simp only [walkRow0E]; split_ifs <;> simp
      cR_bool := by simp only [walkRow0E]; split_ifs <;> simp
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
    obtain ⟨t, ht, -, hn⟩ := walkRows_root cells preads i hk
    have : wTrie cells preads i = t := by
      unfold wTrie; rw [List.getD_eq_getElem _ _ hi]; exact Option.some_injective _ ((List.getElem?_eq_getElem hi).symm.trans ht)
    show ((cells.idxOf (wTrie cells preads i).label.root : ℕ) : F) = ((cells.idxOf (wTrie cells preads i).label.node : ℕ) : F)
    rw [this, hn]
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

end BaseE

section KFactsE
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq F] [DecidableEq K]
  [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  (E : Noun → FP (Quad (algebraMap F K δF))) (cells : List Noun) (preads : List (Noun × ℕ)) (α γ : K)
  (hF : GeneratedField.PrimeFieldElems F)
include hF

theorem zq_natCastE {k : ℕ} (hk : k < ringChar F) : zq (k : F) = (k : ZMod (ringChar F)) := by
  unfold zq; rw [natOf_natCast hF hk]

omit hF in
theorem decide_ite_oneE (b : Bool) : decide ((if b then (1 : F) else 0) = 1) = b := by
  cases b <;> simp

/-- **The honest row's label is the trie node's `lblWE`.** -/
theorem lblV_walkRow0E (hq : 2 ^ 63 < ringChar F) (hcells : cells.length < ringChar F)
    (h62 : ∀ r ∈ pathReads preads, depthOf r.2 ≤ 62) {j : ℕ} (hj : j < (walkRows cells preads).length) :
    lblV δF (walkRow0E δF E cells preads α γ j) = lblWE (q := ringChar F) E cells (wTrie cells preads j) := by
  have hlen := walkRows_len_le h62 (wTrie_mem cells preads hj)
  have hax := axisFold_lt (wTrie cells preads j).label.bits
  have h2 : 2 ^ ((wTrie cells preads j).label.bits.length + 1) ≤ 2 ^ 62 :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : (2 : ℕ) ^ 62 < 2 ^ 63 := by norm_num
  have hri := List.idxOf_le_length (a := (wTrie cells preads j).label.root) (l := cells)
  simp only [lblV, walkRow0E, lblWE, dtWE]
  rw [zq_natCastE hF (by omega), zq_natCastE hF (by omega), zq_natCastE hF (by omega)]
  congr 2
  · exact decide_ite_oneE _
  · exact decide_ite_oneE _

/-- **The honest row's consumed key is the trie node's `keyWE`.** -/
theorem keyV_walkRow0E (hcells : cells.length < ringChar F) (j : ℕ) :
    keyV δF (walkRow0E δF E cells preads α γ j) = keyWE E cells (wTrie cells preads j) := by
  have hi := List.idxOf_le_length (a := (wTrie cells preads j).label.node) (l := cells)
  simp only [keyV, walkRow0E, keyWE]
  rw [natOf_natCast hF (by omega)]

theorem curV_walkRow0E (hq : 2 ^ 63 < ringChar F) (hcells : cells.length < ringChar F)
    (h62 : ∀ r ∈ pathReads preads, depthOf r.2 ≤ 62) {j : ℕ} (hj : j < (walkRows cells preads).length) :
    curV δF γ (walkRow0E δF E cells preads α γ j) =
      curCol (wNodeValE δF E cells γ) (walkRows cells preads) (j + 1) := by
  rw [curCol_succ, List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map, curV,
    lblV_walkRow0E δF E cells preads α γ hF hq hcells h62 hj]
  unfold wNodeValE wTrie
  rw [List.getD_eq_getElem _ _ hj]

theorem fanout_walkRow0E (hq : 2 ^ 63 < ringChar F) (hcells : cells.length < ringChar F)
    (h62 : ∀ r ∈ pathReads preads, depthOf r.2 ≤ 62) {j : ℕ} (hj : j < (walkRows cells preads).length) :
    WalkVCL.fanout (lblV δF (walkRow0E δF E cells preads α γ j)).1 = foCol (walkRows cells preads) (j + 1) := by
  rw [lblV_walkRow0E δF E cells preads α γ hF hq hcells h62 hj, foCol_walk cells preads hj,
    walkRows_fanout (wTrie_mem cells preads hj)]
  rfl

theorem ccV_walkRow0E (hq : 2 ^ 63 < ringChar F) (hcells : cells.length < ringChar F)
    (h62 : ∀ r ∈ pathReads preads, depthOf r.2 ≤ 62) {j : ℕ} (hj : j < (walkRows cells preads).length) :
    ccV δF α γ (walkRow0E δF E cells preads α γ j) =
      ∑ l ∈ Finset.Icc 1 (foCol (walkRows cells preads) (j + 1)), α ^ l *
        chldCol (wNodeValE δF E cells γ) (walkRows cells preads) (j + 1) l := by
  unfold ccV
  rw [fanout_walkRow0E δF E cells preads α γ hF hq hcells h62 hj]
  refine Finset.sum_congr rfl fun l hl => ?_
  obtain ⟨hl1, hl2⟩ := Finset.mem_Icc.mp hl
  congr 1
  have hlbl := lblV_walkRow0E δF E cells preads α γ hF hq hcells h62 hj
  have hkey := keyV_walkRow0E δF E cells preads α γ hF hcells j
  rw [hlbl, hkey]
  obtain ⟨root, n, bs, T, hT⟩ := walkRows_trie (wTrie_mem cells preads hj)
  rw [foCol_walk cells preads hj, walkRows_fanout (wTrie_mem cells preads hj)] at hl2
  rw [hT] at hl2 ⊢
  obtain ⟨a, c, rfl, hc⟩ := trie_child_get root n bs T l hl1 hl2
  have hch : chldCol (wNodeValE δF E cells γ) (walkRows cells preads) (j + 1) l =
      wNodeValE δF E cells γ (trie root
        (if sideOf ((trie root (.cell a c) bs T).label.cL, (trie root (.cell a c) bs T).label.cR) l then c else a)
        (bs ++ [sideOf ((trie root (.cell a c) bs T).label.cL, (trie root (.cell a c) bs T).label.cR) l])
        (contT (sideOf ((trie root (.cell a c) bs T).label.cL, (trie root (.cell a c) bs T).label.cR) l) T)) := by
    unfold chldCol
    have hw : (walkRows cells preads)[j]? = some (trie root (.cell a c) bs T) := by
      rw [List.getElem?_eq_getElem hj, ← hT]; unfold wTrie; rw [List.getD_eq_getElem _ _ hj]
    rw [Nat.add_sub_cancel, hw]
    simp [hc]
  rw [hch]
  unfold wNodeValE
  congr 1
  show WalkVCL.enc (algebraMap F K δF) (((false, false), _) : WalkVCL.LT (ringChar F) _) =
    WalkVCL.enc (algebraMap F K δF) ((_, dtWE (q := ringChar F) E cells _) : WalkVCL.LT (ringChar F) _)
  rw [dtWE_child]
  rfl

/-- **`WalkKFacts` on every honest walk row**, at every coin pair `(α, γ)` (no coin event). -/
theorem walkRow0E_K (hq : 2 ^ 63 < ringChar F) (hcells : cells.length < ringChar F)
    (h62 : ∀ r ∈ pathReads preads, depthOf r.2 ≤ 62) {n : ℕ} (hn : n = (walkRows cells preads).length)
    (i : Fin n) :
    WalkKFacts δF (krW cells preads) (fun j : Fin n => walkRow0E δF E cells preads α γ j) α γ i := by
  subst hn
  have hi := i.isLt
  obtain ⟨hw, hz⟩ := honest_walk_acc_zero (wNodeValE δF E cells γ) (walkForest cells preads)
    (walkForest_ne_nil cells preads) α
  change WalkSatInGate (curCol (wNodeValE δF E cells γ) (walkRows cells preads))
    (chldCol (wNodeValE δF E cells γ) (walkRows cells preads)) (foCol (walkRows cells preads)) (lnH α)
    (countH (foCol (walkRows cells preads)) α (krW cells preads))
    (accH (curCol (wNodeValE δF E cells γ) (walkRows cells preads))
      (chldCol (wNodeValE δF E cells γ) (walkRows cells preads)) (foCol (walkRows cells preads)) α (krW cells preads))
    α (α ^ krW cells preads) (krW cells preads) (walkRows cells preads).length at hw
  change accH (curCol (wNodeValE δF E cells γ) (walkRows cells preads))
      (chldCol (wNodeValE δF E cells γ) (walkRows cells preads)) (foCol (walkRows cells preads)) α (krW cells preads)
      (walkRows cells preads).length = 0 at hz
  have fo := fun (j : ℕ) (hj : j < (walkRows cells preads).length) =>
    fanout_walkRow0E δF E cells preads α γ hF hq hcells h62 hj
  have cc := fun (j : ℕ) (hj : j < (walkRows cells preads).length) =>
    ccV_walkRow0E δF E cells preads α γ hF hq hcells h62 hj
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
    have hcu := curV_walkRow0E δF E cells preads α γ hF hq hcells h62 hi'
    show algebraMap F K (1 - if (i : ℕ) + 1 < krW cells preads then 1 else 0) * α ^ ((i : ℕ) + 1 + 1) *
        curV δF γ (walkRow0E δF E cells preads α γ ((i : ℕ) + 1)) +
        (accH _ _ _ α (krW cells preads) ((i : ℕ) + 1 + 1) - accH _ _ _ α (krW cells preads) ((i : ℕ) + 1)) =
      countH (foCol (walkRows cells preads)) α (krW cells preads) ((i : ℕ) + 1) *
        ccV δF α γ (walkRow0E δF E cells preads α γ ((i : ℕ) + 1))
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
          chldCol (wNodeValE δF E cells γ) (walkRows cells preads) ((i : ℕ) + 1 + 1) l) =
        ∑ l ∈ Finset.Icc 1 (foCol (walkRows cells preads) ((i : ℕ) + 1 + 1)),
          countH (foCol (walkRows cells preads)) α (krW cells preads) ((i : ℕ) + 1) *
            (α ^ l * chldCol (wNodeValE δF E cells γ) (walkRows cells preads) ((i : ℕ) + 1 + 1) l) :=
      Finset.sum_congr rfl fun l _ => by ring
    rw [hsum] at hs
    linear_combination hs
  · intro hl
    show accH _ _ _ α (krW cells preads) ((i : ℕ) + 1) = 0
    rw [hl]; exact hz

end KFactsE

section WalkE
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [FiniteDimensional F K] [DecidableEq F]
  [DecidableEq K] [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n)
  (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)

local notation "𝕂′" => Quad (algebraMap F K δF)

/-- The honest (unfilled) walk rows at the chip's walk coins `(chals 0, chals 1)`. -/
abbrev wRowsBE (E : Noun → FP (Quad (algebraMap F K δF))) (cells : List Noun) (preads : List (Noun × ℕ)) :
    ℕ → WalkVals F K (Quad (algebraMap F K δF)) :=
  walkRow0E δF E cells preads (chals 0) (chals 1)

/-- The honest filled walk rows. -/
abbrev wValsBE (E : Noun → FP (Quad (algebraMap F K δF))) (γ ρ : Quad (algebraMap F K δF)) (cells : List Noun) (preads : List (Noun × ℕ)) :
    Fin n → WalkVals F K (Quad (algebraMap F K δF)) :=
  fun i => walkFill δF γ ρ (wRowsBE δF chals E cells preads) i

/-- The honest 132-column walk column function. -/
abbrev wColBE (E : Noun → FP (Quad (algebraMap F K δF))) (γ ρ : Quad (algebraMap F K δF)) (cells : List Noun) (preads : List (Noun × ℕ)) :
    ℕ → Fin n → F :=
  walkCol δF b (krW cells preads) (wValsBE δF chals E γ ρ cells preads)

theorem wRowsBE_root (E : Noun → FP 𝕂′) (cells : List Noun) (preads : List (Noun × ℕ)) {j : ℕ}
    (hj : j < (walkRows cells preads).length) (hk : j < krW cells preads) :
    (wRowsBE δF chals E cells preads j).root = (wRowsBE δF chals E cells preads j).p := by
  obtain ⟨t, ht, -, hnr⟩ := walkRows_root cells preads j hk
  have : wTrie cells preads j = t := by
    unfold wTrie; rw [List.getD_eq_getElem _ _ hj]
    exact Option.some_injective _ ((List.getElem?_eq_getElem hj).symm.trans ht)
  show E (wTrie cells preads j).label.root =
    E (wTrie cells preads j).label.node
  rw [this, hnr]

/-- The `ok`-gated walk chip at the honest rows (`walkOk_sat` at `walkRow0E`). -/
theorem walkOk_honest_listE (E : Noun → FP 𝕂′) (γ ρ : 𝕂′) (cells : List Noun) (preads : List (Noun × ℕ))
    (hF : GeneratedField.PrimeFieldElems F) (hq : 2 ^ 63 < ringChar F) (hcells : cells.length < ringChar F)
    (h61 : WalkDepthOK preads) (hkp : krW cells preads + (walkRows cells preads).length < ringChar F)
    (hN : n = (walkRows cells preads).length)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hok : ChalsOK δF chals γ ρ 11)
    (hx : ∀ j < n, FiniteIO.compress (m := 11) ⟨γ, ρ⟩ (wxKeyV δF (wRowsBE δF chals E cells preads j)) ≠ 0)
    (hL : ∀ j < n, FiniteIO.compress (m := 8) ⟨γ, ρ⟩ (wrecLV δF (wRowsBE δF chals E cells preads j)) ≠ 0)
    (hR : ∀ j < n, FiniteIO.compress (m := 8) ⟨γ, ρ⟩ (wrecRV δF (wRowsBE δF chals E cells preads j)) ≠ 0)
    (hXt : ∑ k ∈ Finset.range n, (walkFillInv δF γ ρ (wRowsBE δF chals E cells preads k)).xInv =
      Quad.mk _ (pubs 0) (pubs 1))
    (hPt : ∑ k ∈ Finset.range n, wpTermV δF (walkFillInv δF γ ρ (wRowsBE δF chals E cells preads k)) =
      Quad.mk _ (pubs 2) (pubs 3)) :
    RAP.SatisfiesWithPreprocessing (walkChipOk δF (krW cells preads) b hn nodes orbit chals pubs true)
      (fun j => honestQ hn nodes (wColBE δF b chals E γ ρ cells preads) 132
        (Fin.cast (walkChipOk_w δF (krW cells preads) b hn nodes orbit chals pubs true) j)) := by
  have h62 := walkDepth62 h61
  exact walkOk_sat δF (krW cells preads) b hn nodes orbit chals pubs (wValsBE δF chals E γ ρ cells preads) hF
    hinj hadj γ ρ hok
    (fun i => walkBaseFacts_fill δF γ ρ (wRowsBE δF chals E cells preads) (krW cells preads) i
      (walkRow0E_base δF E cells preads (chals 0) (chals 1) h62 hkp hN i))
    (fun i => walkKFacts_fill δF γ ρ (wRowsBE δF chals E cells preads) (krW cells preads) _ _ i
      (walkRow0E_K δF E cells preads (chals 0) (chals 1) hF hq hcells h62 hN i))
    (fun i => walkFill_mixed δF γ ρ (wRowsBE δF chals E cells preads) (krW cells preads) pubs i
      (fun j hj hk => wRowsBE_root δF chals E cells preads (hN ▸ hj) hk) hx hL hR hXt hPt)

theorem walkChip_honest_listE (E : Noun → FP 𝕂′) (γ ρ : 𝕂′) (cells : List Noun) (preads : List (Noun × ℕ))
    (hF : GeneratedField.PrimeFieldElems F) (hq : 2 ^ 63 < ringChar F) (hcells : cells.length < ringChar F)
    (h61 : WalkDepthOK preads) (hkp : krW cells preads + (walkRows cells preads).length < ringChar F)
    (hN : n = (walkRows cells preads).length)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hok : ChalsOK δF chals γ ρ 11)
    (hx : ∀ j < n, FiniteIO.compress (m := 11) ⟨γ, ρ⟩ (wxKeyV δF (wRowsBE δF chals E cells preads j)) ≠ 0)
    (hL : ∀ j < n, FiniteIO.compress (m := 8) ⟨γ, ρ⟩ (wrecLV δF (wRowsBE δF chals E cells preads j)) ≠ 0)
    (hR : ∀ j < n, FiniteIO.compress (m := 8) ⟨γ, ρ⟩ (wrecRV δF (wRowsBE δF chals E cells preads j)) ≠ 0)
    (hXt : ∑ k ∈ Finset.range n, (walkFillInv δF γ ρ (wRowsBE δF chals E cells preads k)).xInv =
      Quad.mk _ (pubs 0) (pubs 1))
    (hPt : ∑ k ∈ Finset.range n, wpTermV δF (walkFillInv δF γ ρ (wRowsBE δF chals E cells preads k)) =
      Quad.mk _ (pubs 2) (pubs 3)) :
    (walkChip δF (krW cells preads) b hn nodes orbit chals pubs).rap.Satisfies
      (honestQ hn nodes (wColBE δF b chals E γ ρ cells preads) _) := by
  exact (walkChipOk_sat δF (krW cells preads) b hn nodes orbit chals pubs true _
    (walkOk_honest_listE δF b hn nodes orbit chals pubs E γ ρ cells preads hF hq hcells h61 hkp hN hinj hadj hok
      hx hL hR hXt hPt)).2.1

/-- **`walkChipHQK_honest_listE`: the ternary-kind handle walk twin accepts `walkTraceHQ`** at the honest walk
columns and ANY child handle columns with kinds in `{0, 1, 2}`, given the three handle poles and the two `𝕂′`
publics equal to the totals. -/
theorem walkChipHQK_honest_listE (E : Noun → FP 𝕂′) (γ ρ : 𝕂′) (cells : List Noun) (preads : List (Noun × ℕ))
    (kLv vLv kRv vRv : Fin n → F)
    (hF : GeneratedField.PrimeFieldElems F) (hq : 2 ^ 63 < ringChar F) (hcells : cells.length < ringChar F)
    (h61 : WalkDepthOK preads) (hkp : krW cells preads + (walkRows cells preads).length < ringChar F)
    (hN : n = (walkRows cells preads).length)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hok : ChalsOK δF chals γ ρ 11)
    (hx : ∀ j < n, FiniteIO.compress (m := 11) ⟨γ, ρ⟩ (wxKeyV δF (wRowsBE δF chals E cells preads j)) ≠ 0)
    (hL : ∀ j < n, FiniteIO.compress (m := 8) ⟨γ, ρ⟩ (wrecLV δF (wRowsBE δF chals E cells preads j)) ≠ 0)
    (hR : ∀ j < n, FiniteIO.compress (m := 8) ⟨γ, ρ⟩ (wrecRV δF (wRowsBE δF chals E cells preads j)) ≠ 0)
    (hXt : ∑ k ∈ Finset.range n, (walkFillInv δF γ ρ (wRowsBE δF chals E cells preads k)).xInv =
      Quad.mk _ (pubs 0) (pubs 1))
    (hPt : ∑ k ∈ Finset.range n, wpTermV δF (walkFillInv δF γ ρ (wRowsBE δF chals E cells preads k)) =
      Quad.mk _ (pubs 2) (pubs 3))
    (hkL : ∀ i, kLv i = 0 ∨ kLv i = 1 ∨ kLv i = 2) (hkR : ∀ i, kRv i = 0 ∨ kRv i = 1 ∨ kRv i = 2)
    (hpX : ∀ i, WalkTraceHQ.dRow δF (krW cells preads) b hn nodes orbit chals pubs WalkHC.xKeyH
      (wColBE δF b chals E γ ρ cells preads) kLv vLv kRv vRv i ≠ 0)
    (hpL : ∀ i, WalkTraceHQ.dRow δF (krW cells preads) b hn nodes orbit chals pubs WalkHC.recLH
      (wColBE δF b chals E γ ρ cells preads) kLv vLv kRv vRv i ≠ 0)
    (hpR : ∀ i, WalkTraceHQ.dRow δF (krW cells preads) b hn nodes orbit chals pubs WalkHC.recRH
      (wColBE δF b chals E γ ρ cells preads) kLv vLv kRv vRv i ≠ 0)
    (hpubX : Quad.mk _ (pubs WalkHQ.pubXQ) (pubs (WalkHQ.pubXQ + 1)) = ∑ j ∈ Finset.range n,
      (WalkTraceHQ.dN δF (krW cells preads) b hn nodes orbit chals pubs (wColBE δF b chals E γ ρ cells preads)
        kLv vLv kRv vRv WalkHC.xKeyH j)⁻¹)
    (hpubP : Quad.mk _ (pubs WalkHQ.pubPQ) (pubs (WalkHQ.pubPQ + 1)) = ∑ j ∈ Finset.range n,
      (liftQ δF (WalkTraceH.cN j (wColBE (n := n) δF b chals E γ ρ cells preads WChip.mL)) *
          (WalkTraceHQ.dN δF (krW cells preads) b hn nodes orbit chals pubs (wColBE δF b chals E γ ρ cells preads)
            kLv vLv kRv vRv WalkHC.recLH j)⁻¹ +
        liftQ δF (WalkTraceH.cN j (wColBE (n := n) δF b chals E γ ρ cells preads WChip.mR)) *
          (WalkTraceHQ.dN δF (krW cells preads) b hn nodes orbit chals pubs (wColBE δF b chals E γ ρ cells preads)
            kLv vLv kRv vRv WalkHC.recRH j)⁻¹)) :
    (CellTwinK.walkChipHQK δF (krW cells preads) b hn nodes orbit chals pubs).rap.Satisfies
      (WalkTraceHQ.walkTraceHQ δF (krW cells preads) b hn nodes orbit chals pubs
        (wColBE δF b chals E γ ρ cells preads) kLv vLv kRv vRv) :=
  WalkTraceHQ.walkChipHQK_accepts_honest δF (krW cells preads) b hn nodes orbit chals pubs _ kLv vLv kRv vRv hinj hadj
    (walkChip_honest_listE δF b hn nodes orbit chals pubs E γ ρ cells preads hF hq hcells h61 hkp hN hinj hadj hok
      hx hL hR hXt hPt)
    hkL hkR hpX hpL hpR hpubX hpubP

/-- The 166-column handle-twin column function (`walkTraceHQ`'s columns). -/
abbrev wColHQBE (E : Noun → FP 𝕂′) (γ ρ : 𝕂′) (cells : List Noun) (preads : List (Noun × ℕ)) (kLv vLv kRv vRv : Fin n → F) :
    ℕ → Fin n → F :=
  WalkTraceHQ.colHQ δF (krW cells preads) b (wColBE δF b chals E γ ρ cells preads) kLv vLv kRv vRv
    (WalkTraceHQ.rolesF δF (krW cells preads) b hn nodes orbit chals pubs (wColBE δF b chals E γ ρ cells preads)
      kLv vLv kRv vRv)

/-- **`walkChipJ8_honest_listE`: the J-8 walk chip accepts the honest J-8 walk trace** of any cell list and read
list under `hwalk`, with the hypotheses of `walkChipHQK_honest_listE`. -/
theorem walkChipJ8_honest_listE (E : Noun → FP 𝕂′) (γ ρ : 𝕂′) (cells : List Noun) (preads : List (Noun × ℕ))
    (kLv vLv kRv vRv : Fin n → F)
    (hF : GeneratedField.PrimeFieldElems F) (hq : 2 ^ 63 < ringChar F) (hcells : cells.length < ringChar F)
    (h61 : WalkDepthOK preads) (hkp : krW cells preads + (walkRows cells preads).length < ringChar F)
    (hN : n = (walkRows cells preads).length)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hok : ChalsOK δF chals γ ρ 11)
    (hx : ∀ j < n, FiniteIO.compress (m := 11) ⟨γ, ρ⟩ (wxKeyV δF (wRowsBE δF chals E cells preads j)) ≠ 0)
    (hL : ∀ j < n, FiniteIO.compress (m := 8) ⟨γ, ρ⟩ (wrecLV δF (wRowsBE δF chals E cells preads j)) ≠ 0)
    (hR : ∀ j < n, FiniteIO.compress (m := 8) ⟨γ, ρ⟩ (wrecRV δF (wRowsBE δF chals E cells preads j)) ≠ 0)
    (hXt : ∑ k ∈ Finset.range n, (walkFillInv δF γ ρ (wRowsBE δF chals E cells preads k)).xInv =
      Quad.mk _ (pubs 0) (pubs 1))
    (hPt : ∑ k ∈ Finset.range n, wpTermV δF (walkFillInv δF γ ρ (wRowsBE δF chals E cells preads k)) =
      Quad.mk _ (pubs 2) (pubs 3))
    (hkL : ∀ i, kLv i = 0 ∨ kLv i = 1 ∨ kLv i = 2) (hkR : ∀ i, kRv i = 0 ∨ kRv i = 1 ∨ kRv i = 2)
    (hpX : ∀ i, WalkTraceHQ.dRow δF (krW cells preads) b hn nodes orbit chals pubs WalkHC.xKeyH
      (wColBE δF b chals E γ ρ cells preads) kLv vLv kRv vRv i ≠ 0)
    (hpL : ∀ i, WalkTraceHQ.dRow δF (krW cells preads) b hn nodes orbit chals pubs WalkHC.recLH
      (wColBE δF b chals E γ ρ cells preads) kLv vLv kRv vRv i ≠ 0)
    (hpR : ∀ i, WalkTraceHQ.dRow δF (krW cells preads) b hn nodes orbit chals pubs WalkHC.recRH
      (wColBE δF b chals E γ ρ cells preads) kLv vLv kRv vRv i ≠ 0)
    (hpubX : Quad.mk _ (pubs WalkHQ.pubXQ) (pubs (WalkHQ.pubXQ + 1)) = ∑ j ∈ Finset.range n,
      (WalkTraceHQ.dN δF (krW cells preads) b hn nodes orbit chals pubs (wColBE δF b chals E γ ρ cells preads)
        kLv vLv kRv vRv WalkHC.xKeyH j)⁻¹)
    (hpubP : Quad.mk _ (pubs WalkHQ.pubPQ) (pubs (WalkHQ.pubPQ + 1)) = ∑ j ∈ Finset.range n,
      (liftQ δF (WalkTraceH.cN j (wColBE (n := n) δF b chals E γ ρ cells preads WChip.mL)) *
          (WalkTraceHQ.dN δF (krW cells preads) b hn nodes orbit chals pubs (wColBE δF b chals E γ ρ cells preads)
            kLv vLv kRv vRv WalkHC.recLH j)⁻¹ +
        liftQ δF (WalkTraceH.cN j (wColBE (n := n) δF b chals E γ ρ cells preads WChip.mR)) *
          (WalkTraceHQ.dN δF (krW cells preads) b hn nodes orbit chals pubs (wColBE δF b chals E γ ρ cells preads)
            kLv vLv kRv vRv WalkHC.recRH j)⁻¹)) :
    RAP.SatisfiesWithPreprocessing (WalkJ8.walkChipJ8 δF (krW cells preads) b hn nodes orbit chals pubs)
      (fun j => honestQ hn nodes
        (HonestK8.certUp (wColHQBE δF b hn nodes orbit chals pubs E γ ρ cells preads kLv vLv kRv vRv) (lenB cells preads))
        166 (Fin.cast (WalkJ8.walkChipJ8_width δF (krW cells preads) b hn nodes orbit chals pubs) j)) :=
  HonestK8.walkTwinJ8_accepted δF (krW cells preads) b hn nodes orbit chals pubs _ kLv vLv kRv vRv hinj hadj
    (walkOk_honest_listE δF b hn nodes orbit chals pubs E γ ρ cells preads hF hq hcells h61 hkp hN hinj hadj hok
      hx hL hR hXt hPt)
    hkL hkR hpX hpL hpR hpubX hpubP (lenB cells preads)
    (fun i => by simp [walkCol, WalkVals.base, WalkVals.named, WChip.len, walkFill, walkFillInv, walkRow0E])
    (fun i => walkRows_len_le60 h61 (wTrie_mem cells preads (hN ▸ i.isLt)))

end WalkE


/-! ## 4. Staging of the honest J-8 walk trace (`StJ8`'s `W` component) -/


section StageWE
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [FiniteDimensional F K] [DecidableEq F]
  [DecidableEq K] [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n)
  (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h)

/-- The honest walk columns `< 93`: base coin-free, fingerprint roles read `E` only. -/
theorem wColBE_cong (chals chals' : ℕ → K) (E E' : Noun → FP (Quad (algebraMap F K δF))) (γ ρ γ' ρ' : Quad (algebraMap F K δF)) (cells : List Noun)
    (preads : List (Noun × ℕ)) (k : ℕ) (hk : k < 93) (hz : 21 ≤ k → E = E') :
    wColBE (n := n) δF b chals E γ ρ cells preads k = wColBE (n := n) δF b chals' E' γ' ρ' cells preads k := by
  funext i
  unfold wColBE walkCol
  by_cases h1 : k < 21
  · simp only [if_pos h1]
    simp only [wValsBE, wRowsBE, walkFill, walkFillInv, walkRow0E, WalkVals.base, WalkVals.named]
  · simp only [if_neg h1]
    obtain rfl := hz (by omega)
    congr 1
    unfold wroleVal
    have hρ : (k - 21) / 3 < 24 := by omega
    simp only [hρ, if_true]
    have e : ∀ s, (wValsBE (n := n) δF chals E γ ρ cells preads i).fpSlot s =
        (wValsBE (n := n) δF chals' E γ' ρ' cells preads i).fpSlot s := fun s => fpSlot_congr' _ _ rfl rfl rfl rfl s
    rw [e]

/-- **The honest J-8 walk trace at a coin vector** (166 columns). -/
def walkTrWE (chalsF pubsF : Coins frameJ8 K → ℕ → K) (γF ρF : Coins frameJ8 K → Quad (algebraMap F K δF)) (EF : Coins frameJ8 K → Noun → FP (Quad (algebraMap F K δF)))
    (cells : List Noun) (preads : List (Noun × ℕ)) (kLv vLv kRv vRv : Fin n → F) (χ : Coins frameJ8 K) :
    Fin 166 → F[X] :=
  honestQ hn nodes (HonestK8.certUp (wColHQBE δF b hn nodes orbit (chalsF χ) (pubsF χ) (EF χ) (γF χ) (ρF χ) cells preads
    kLv vLv kRv vRv) (lenB cells preads)) 166

/-- **The honest J-8 walk trace map is staged** (`StJ8`'s `W`), when the fingerprint seed reads only round-0
coins. -/
theorem walkTrWE_staged (chalsF pubsF : Coins frameJ8 K → ℕ → K) (γF ρF : Coins frameJ8 K → Quad (algebraMap F K δF)) (EF : Coins frameJ8 K → Noun → FP (Quad (algebraMap F K δF)))
    (cells : List Noun) (preads : List (Noun × ℕ)) (kLv vLv kRv vRv : Fin n → F)
    (hz : ∀ χ χ' : Coins frameJ8 K, (∀ i : Fin frameJ8.n, frameJ8.sampledAfter i = 0 → χ i = χ' i) → EF χ = EF χ') :
    StagedCols frameJ8 crW (walkTrWE δF b hn nodes orbit chalsF pubsF γF ρF EF cells preads kLv vLv kRv vRv) := by
  intro j χ χ' hχ
  by_cases h2 : 97 ≤ (j : ℕ)
  · rw [coins_eq_of_two χ χ' (crW j) (by simp only [crW]; split_ifs <;> omega) hχ]
  · unfold walkTrWE
    refine honestQ_congr _ _ _ _ _ _ ?_
    funext i
    unfold HonestK8.certUp
    split_ifs with hc
    · rfl
    · refine congrFun (walkColHQ_cong δF b (krW cells preads) _ _ _ _ _ _ _ _ j (by omega)
        (fun hj => wColBE_cong δF b _ _ _ _ _ _ _ _ cells preads j (by omega) (fun h' => absurd h' (by omega)))
        (fun hj => wColBE_cong δF b _ _ _ _ _ _ _ _ cells preads _ (by omega) (fun _ => ?_))) i
      exact hz χ χ' (round0_of_one χ χ' (crW j) (by simp only [crW]; split_ifs <;> omega) hχ)

end StageWE

/-! ## 3. The cell rows at `E` -/

section RowsE
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] (δF : F)
  [Fact (¬ IsSquare (algebraMap F K δF))]

local notation "𝕂′" => Quad (algebraMap F K δF)

/-- **The cell row of `n` at serial `j` under the encoder `E`** (`ComplJ8Cell.cellRowB` with the three
fingerprints `E n`, `E (hd n)`, `E (tl n)`). -/
def cellRowBE (E : Noun → FP 𝕂′) (z : 𝕂′) (big : Noun → Option ℕ) (cells : List Noun) (mv mx mx1 : ℕ → ℕ)
    (n : Noun) (j : ℕ) : CellVals F 𝕂′ :=
  { ComplJ8Cell.cellRowB δF 0 big cells mv mx mx1 n j with p := E n, l := E (hdN n), r := E (tlN n) }

def cellRowsBE (E : Noun → FP 𝕂′) (z : 𝕂′) (big : Noun → Option ℕ) (cells : List Noun) (mv mx mx1 : ℕ → ℕ)
    (j : ℕ) : CellVals F 𝕂′ :=
  cellRowBE δF E z big cells mv mx mx1 (cells.getD j (.atom 0)) j

variable {δF}

theorem cellRowsBE_getElem (E : Noun → FP 𝕂′) (z : 𝕂′) (big : Noun → Option ℕ) (cells : List Noun)
    (mv mx mx1 : ℕ → ℕ) {j : ℕ} (hj : j < cells.length) :
    cellRowsBE δF E z big cells mv mx mx1 j = cellRowBE δF E z big cells mv mx mx1 cells[j] j := by
  simp [cellRowsBE, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

end RowsE

section FactsE
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] {δF : F}
  [Fact (¬ IsSquare (algebraMap F K δF))]

local notation "𝕂′" => Quad (algebraMap F K δF)

variable (E : Noun → FP (Quad (algebraMap F K δF))) (z : Quad (algebraMap F K δF)) (big : Noun → Option ℕ) (cells : List Noun) (mv mx mx1 : ℕ → ℕ)

theorem cellRowsBE_shape (hcell : ∀ c ∈ cells, c.isCell = true) {j : ℕ} (hj : j < cells.length) :
    ∃ a b, cells[j] = .cell a b ∧
      cellRowsBE δF E z big cells mv mx mx1 j = cellRowBE δF E z big cells mv mx mx1 (.cell a b) j := by
  have hc := hcell _ (List.getElem_mem hj)
  generalize hn : cells[j] = n at hc
  cases n with
  | atom _ => simp [Noun.isCell] at hc
  | cell a b => exact ⟨a, b, rfl, by rw [cellRowsBE_getElem E z big cells mv mx mx1 hj, hn]⟩

theorem cellRowsBE_idx (j : ℕ) : (cellRowsBE δF E z big cells mv mx mx1 j).idx = (j : F) := rfl

/-- **`CellBaseFacts` of the rows** (any list of cells of rank `< 2^110`). -/
theorem cellRowsBE_baseFacts (hcell : ∀ c ∈ cells, c.isCell = true) (hrank : ∀ n ∈ cells, rankOf n < 2 ^ 110) {N : ℕ}
    (hN : N = cells.length) (i : Fin N) :
    CellBaseFacts (fun j : Fin N => cellRowsBE δF E z big cells mv mx mx1 j) i := by
  subst hN
  have hi : (i : ℕ) < cells.length := i.isLt
  obtain ⟨a, b, hab, hrow⟩ := cellRowsBE_shape E z big cells mv mx mx1 hcell hi
  have hr : rankOf (.cell a b) < 2 ^ 110 := hab ▸ hrank _ (List.getElem_mem hi)
  obtain ⟨l1, l2, l3, l4, l5, l6⟩ := cellRow0_limbs (δF := δF) z cells [] [] [] a b hr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h0
    show (cellRowsBE δF E z big cells mv mx mx1 i).idx = 0
    rw [cellRowsBE_idx E z big cells mv mx mx1, h0]; simp
  · intro hi'
    show (cellRowsBE δF E z big cells mv mx mx1 ((i : ℕ) + 1)).idx = (cellRowsBE δF E z big cells mv mx mx1 i).idx + 1
    rw [cellRowsBE_idx E z big cells mv mx mx1, cellRowsBE_idx E z big cells mv mx mx1]
    simp
  · show (cellRowsBE δF E z big cells mv mx mx1 i).lo + _ * (cellRowsBE δF E z big cells mv mx mx1 i).carry = _
    rw [hrow]; exact l1
  · show (cellRowsBE δF E z big cells mv mx mx1 i).hi = _
    rw [hrow]; exact l2
  · show (cellRowsBE δF E z big cells mv mx mx1 i).carry * _ = 0
    rw [hrow]; exact l3
  · show (cellRowsBE δF E z big cells mv mx mx1 i).wL * ((cellRowsBE δF E z big cells mv mx mx1 i).wL - 1) = 0
    rw [hrow]; exact wOf_bool big _
  · show (cellRowsBE δF E z big cells mv mx mx1 i).wR * ((cellRowsBE δF E z big cells mv mx mx1 i).wR - 1) = 0
    rw [hrow]; exact wOf_bool big _
  · show (cellRowsBE δF E z big cells mv mx mx1 i).lo =
      ∑ k ∈ Finset.range 62, _ * (cellRowsBE δF E z big cells mv mx mx1 i).bit k
    rw [hrow]; exact l4
  · show (cellRowsBE δF E z big cells mv mx mx1 i).hi =
      ∑ k ∈ Finset.range 48, _ * (cellRowsBE δF E z big cells mv mx mx1 i).bit (62 + k)
    rw [hrow]; exact l5
  · intro k hk
    show (cellRowsBE δF E z big cells mv mx mx1 i).bit k * ((cellRowsBE δF E z big cells mv mx mx1 i).bit k - 1) = 0
    rw [hrow]; exact l6 k hk
  · intro hw
    have hw' : (cellRowsBE δF E z big cells mv mx mx1 i).wL = 0 := hw
    rw [hrow] at hw'
    obtain ⟨v, hv, -⟩ := wOf_zero hw'
    show (cellRowsBE δF E z big cells mv mx mx1 i).loL = 0 ∧ (cellRowsBE δF E z big cells mv mx mx1 i).hiL = 0
    rw [hrow]
    simp only [hdN] at hv
    subst hv
    simp [cellRowBE, ComplJ8Cell.cellRowB, cellRow0, hdN, rankOf, Noun.internal]
  · intro hw
    have hw' : (cellRowsBE δF E z big cells mv mx mx1 i).wR = 0 := hw
    rw [hrow] at hw'
    obtain ⟨v, hv, -⟩ := wOf_zero hw'
    show (cellRowsBE δF E z big cells mv mx mx1 i).loR = 0 ∧ (cellRowsBE δF E z big cells mv mx mx1 i).hiR = 0
    rw [hrow]
    simp only [tlN] at hv
    subst hv
    simp [cellRowBE, ComplJ8Cell.cellRowB, cellRow0, tlN, rankOf, Noun.internal]

theorem cellRowsBE_cons (hcell : ∀ c ∈ cells, c.isCell = true) (hEc : ∀ a c, E (.cell a c) = FP.cons z (E a) (E c)) {j : ℕ} (hj : j < cells.length) :
    (cellRowsBE δF E z big cells mv mx mx1 j).p =
      FP.cons z (cellRowsBE δF E z big cells mv mx mx1 j).l (cellRowsBE δF E z big cells mv mx mx1 j).r := by
  obtain ⟨a, b, -, hrow⟩ := cellRowsBE_shape E z big cells mv mx mx1 hcell hj
  rw [hrow]
  exact hEc a b

theorem cellRowsBE_atomL (hcell : ∀ c ∈ cells, c.isCell = true)
    (hEa : ∀ v, ComplJ8Cell.isBig big (.atom v) = false → E (.atom v) = FP.atomFP z (liftQ δF ((v : ℕ) : F))) {j : ℕ} (hj : j < cells.length) :
    (cellRowsBE δF E z big cells mv mx mx1 j).wL = 0 →
      (cellRowsBE δF E z big cells mv mx mx1 j).l = FP.atomFP z (liftQ δF (cellRowsBE δF E z big cells mv mx mx1 j).aL) := by
  obtain ⟨a, b, -, hrow⟩ := cellRowsBE_shape E z big cells mv mx mx1 hcell hj
  rw [hrow]
  intro hw
  obtain ⟨v, hv, hb⟩ := wOf_zero hw
  simp only [hdN] at hv hb
  subst hv
  show E (.atom v) = FP.atomFP z (liftQ δF (aOf big (.atom v)))
  rw [hEa v hb]
  simp only [aOf, hb, Bool.false_eq_true, if_false]

theorem cellRowsBE_atomR (hcell : ∀ c ∈ cells, c.isCell = true)
    (hEa : ∀ v, ComplJ8Cell.isBig big (.atom v) = false → E (.atom v) = FP.atomFP z (liftQ δF ((v : ℕ) : F))) {j : ℕ} (hj : j < cells.length) :
    (cellRowsBE δF E z big cells mv mx mx1 j).wR = 0 →
      (cellRowsBE δF E z big cells mv mx mx1 j).r = FP.atomFP z (liftQ δF (cellRowsBE δF E z big cells mv mx mx1 j).aR) := by
  obtain ⟨a, b, -, hrow⟩ := cellRowsBE_shape E z big cells mv mx mx1 hcell hj
  rw [hrow]
  intro hw
  obtain ⟨v, hv, hb⟩ := wOf_zero hw
  simp only [tlN] at hv hb
  subst hv
  show E (.atom v) = FP.atomFP z (liftQ δF (aOf big (.atom v)))
  rw [hEa v hb]
  simp only [aOf, hb, Bool.false_eq_true, if_false]

end FactsE

/-! ## 2. -/

section AcceptE
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [FiniteDimensional F K] [DecidableEq F]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n)
  (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)

local notation "𝕂′" => Quad (algebraMap F K δF)

/-- The filled honest rows (`cellFill`: the five inverses and the two accumulators). -/
abbrev valsBE (γ ρ : 𝕂′) (E : Noun → FP 𝕂′) (z : 𝕂′) (big : Noun → Option ℕ) (cells : List Noun) (mv mx mx1 : ℕ → ℕ) :
    Fin n → CellVals F 𝕂′ :=
  fun i => cellFill δF γ ρ (cellRowsBE δF E z big cells mv mx mx1) i

theorem cellChip_honest_listE (γ ρ : 𝕂′) (E : Noun → FP 𝕂′) (z : 𝕂′) (big : Noun → Option ℕ) (cells : List Noun) (mv mx mx1 : ℕ → ℕ)
    (hcell : ∀ c ∈ cells, c.isCell = true) (hrank : ∀ c ∈ cells, rankOf c < 2 ^ 110)
    (hN : n = cells.length)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hok : ChalsOK δF chals γ ρ 11) (hzc : Quad.mk _ (chals 2) (chals 3) = z) (hz : z ≠ 0)
    (hEc : ∀ a c, E (.cell a c) = FP.cons z (E a) (E c))
    (hEa : ∀ v, ComplJ8Cell.isBig big (.atom v) = false → E (.atom v) = FP.atomFP z (liftQ δF ((v : ℕ) : F)))
    (hv : ∀ j < n, FiniteIO.compress (m := 5) ⟨γ, ρ⟩ (vKeyOf δF (cellRowsBE δF E z big cells mv mx mx1 j)) ≠ 0)
    (hl : ∀ j < n, (cellRowsBE δF E z big cells mv mx mx1 j).wL ≠ 0 →
      FiniteIO.compress (m := 5) ⟨γ, ρ⟩ (lKeyOf δF (cellRowsBE δF E z big cells mv mx mx1 j)) ≠ 0)
    (hr : ∀ j < n, (cellRowsBE δF E z big cells mv mx mx1 j).wR ≠ 0 →
      FiniteIO.compress (m := 5) ⟨γ, ρ⟩ (rKeyOf δF (cellRowsBE δF E z big cells mv mx mx1 j)) ≠ 0)
    (hx0 : ∀ j < n, FiniteIO.compress (m := 11) ⟨γ, ρ⟩ (xKeyOf δF (cellRowsBE δF E z big cells mv mx mx1 j) 0) ≠ 0)
    (hx1 : ∀ j < n, FiniteIO.compress (m := 11) ⟨γ, ρ⟩ (xKeyOf δF (cellRowsBE δF E z big cells mv mx mx1 j) 1) ≠ 0)
    (hV : ∑ k ∈ Finset.range n, vTermOf δF (cellFillInv δF γ ρ (cellRowsBE δF E z big cells mv mx mx1 k)) =
      Quad.mk _ (pubs 0) (pubs 1))
    (hX : ∑ k ∈ Finset.range n, xTermOf δF (cellFillInv δF γ ρ (cellRowsBE δF E z big cells mv mx mx1 k)) =
      Quad.mk _ (pubs 2) (pubs 3)) :
    (cellChip δF b hn nodes orbit chals pubs).rap.Satisfies
      (honestQ hn nodes (cellCol δF b (valsBE δF γ ρ E z big cells mv mx mx1)) _) := by
  have hlt : ∀ j < n, j < cells.length := fun j hj => hN ▸ hj
  have hok0 := cellOk_sat δF b hn nodes orbit chals pubs (valsBE δF γ ρ E z big cells mv mx mx1) hinj hadj γ ρ z hok
    hzc (fun i => cellBaseFacts_fill δF γ ρ (cellRowsBE δF E z big cells mv mx mx1) i
      (cellRowsBE_baseFacts E z big cells mv mx mx1 hcell hrank hN i))
    (fun i => cellFill_facts γ ρ (cellRowsBE δF E z big cells mv mx mx1) z pubs i hz
      (fun j hj => cellRowsBE_cons E z big cells mv mx mx1 hcell hEc (hlt j hj))
      (fun j hj => cellRowsBE_atomL E z big cells mv mx mx1 hcell hEa (hlt j hj))
      (fun j hj => cellRowsBE_atomR E z big cells mv mx mx1 hcell hEa (hlt j hj)) hv hl hr hx0 hx1 hV hX)
  exact (cellChipOk_sat δF b hn nodes orbit chals pubs true _ hok0).2.1

/-- This is the `hsat0` of `HonestA8.atomChipHQ_accepts_honest` / `AtomChipHQL.atomChipHQL_accepts_honest`
(`col := CellTraceHQ.colHQ … (cellCol … (valsB …)) mhv (ivF …) (avF …)`). -/
theorem cellChipHQ_honest_listE (γ ρ : 𝕂′) (E : Noun → FP 𝕂′) (z : 𝕂′) (big : Noun → Option ℕ) (cells : List Noun) (mv mx mx1 : ℕ → ℕ)
    (mhv : Fin n → F)
    (hcell : ∀ c ∈ cells, c.isCell = true) (hrank : ∀ c ∈ cells, rankOf c < 2 ^ 110)
    (hN : n = cells.length)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hok : ChalsOK δF chals γ ρ 11) (hzc : Quad.mk _ (chals 2) (chals 3) = z) (hz : z ≠ 0)
    (hEc : ∀ a c, E (.cell a c) = FP.cons z (E a) (E c))
    (hEa : ∀ v, ComplJ8Cell.isBig big (.atom v) = false → E (.atom v) = FP.atomFP z (liftQ δF ((v : ℕ) : F)))
    (hv : ∀ j < n, FiniteIO.compress (m := 5) ⟨γ, ρ⟩ (vKeyOf δF (cellRowsBE δF E z big cells mv mx mx1 j)) ≠ 0)
    (hl : ∀ j < n, (cellRowsBE δF E z big cells mv mx mx1 j).wL ≠ 0 →
      FiniteIO.compress (m := 5) ⟨γ, ρ⟩ (lKeyOf δF (cellRowsBE δF E z big cells mv mx mx1 j)) ≠ 0)
    (hr : ∀ j < n, (cellRowsBE δF E z big cells mv mx mx1 j).wR ≠ 0 →
      FiniteIO.compress (m := 5) ⟨γ, ρ⟩ (rKeyOf δF (cellRowsBE δF E z big cells mv mx mx1 j)) ≠ 0)
    (hx0 : ∀ j < n, FiniteIO.compress (m := 11) ⟨γ, ρ⟩ (xKeyOf δF (cellRowsBE δF E z big cells mv mx mx1 j) 0) ≠ 0)
    (hx1 : ∀ j < n, FiniteIO.compress (m := 11) ⟨γ, ρ⟩ (xKeyOf δF (cellRowsBE δF E z big cells mv mx mx1 j) 1) ≠ 0)
    (hV : ∑ k ∈ Finset.range n, vTermOf δF (cellFillInv δF γ ρ (cellRowsBE δF E z big cells mv mx mx1 k)) =
      Quad.mk _ (pubs 0) (pubs 1))
    (hX : ∑ k ∈ Finset.range n, xTermOf δF (cellFillInv δF γ ρ (cellRowsBE δF E z big cells mv mx mx1 k)) =
      Quad.mk _ (pubs 2) (pubs 3))
    (hpole : ∀ i, CellTraceHQ.dRow δF b hn nodes orbit chals pubs (cellCol δF b (valsBE δF γ ρ E z big cells mv mx mx1))
      mhv i ≠ 0)
    (hpub : Quad.mk _ (pubs CellHQ.pubHQ) (pubs (CellHQ.pubHQ + 1)) = ∑ j ∈ Finset.range n,
      liftQ δF (CellTraceH.mN mhv j) *
        (CellTraceHQ.dN δF b hn nodes orbit chals pubs (cellCol δF b (valsBE δF γ ρ E z big cells mv mx mx1)) mhv j)⁻¹) :
    (cellChipHQ δF b hn nodes orbit chals pubs).rap.Satisfies
      (CellTraceHQ.cellTraceHQ δF b hn nodes orbit chals pubs (cellCol δF b (valsBE δF γ ρ E z big cells mv mx mx1)) mhv) :=
  CellTraceHQ.cellChipHQ_accepts_honest δF b hn nodes orbit chals pubs _ mhv hinj hadj
    (cellChip_honest_listE δF b hn nodes orbit chals pubs γ ρ E z big cells mv mx mx1 hcell hrank hN hinj hadj
      hok hzc hz hEc hEa hv hl hr hx0 hx1 hV hX) hpole hpub

/-- The preprocessing of the honest trace (both masks). -/
theorem cellChip_honest_list_bindE (γ ρ : 𝕂′) (E : Noun → FP 𝕂′) (z : 𝕂′) (big : Noun → Option ℕ) (cells : List Noun)
    (mv mx mx1 : ℕ → ℕ) :
    (cellChip δF b hn nodes orbit chals pubs).BindsPreprocessing
      (honestQ hn nodes (cellCol δF b (valsBE δF γ ρ E z big cells mv mx mx1)) _) := by
  intro j
  fin_cases j
  · exact honestQ_zero hn nodes _ (by rw [(cellChip_fingerprint δF b hn nodes orbit chals pubs).1]; omega)
  · exact honestQ_one hn nodes _ (by rw [(cellChip_fingerprint δF b hn nodes orbit chals pubs).1]; omega)

end AcceptE

/-! ## 3. The side condition and `cellChipHQKW` (the J-8 wire-key cell twin) at the list -/

section KWE
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [FiniteDimensional F K] [DecidableEq F]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n)
  (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)

local notation "𝕂′" => Quad (algebraMap F K δF)

theorem sideOK_rowsB_LE (hp : 2 ^ 63 < ringChar F) (γ ρ : 𝕂′) (E : Noun → FP 𝕂′) (z : 𝕂′) (big : Noun → Option ℕ) (cells : List Noun)
    (mv mx mx1 : ℕ → ℕ) (hcell : ∀ c ∈ cells, c.isCell = true) (hrank : ∀ c ∈ cells, rankOf c < 2 ^ 110)
    (hN : n = cells.length) (i : Fin n) :
    HonestK8.SideOK (kbLB big cells i)
      (cellCol δF b (valsBE δF γ ρ E z big cells mv mx mx1) Cell.wL i)
      (cellCol δF b (valsBE δF γ ρ E z big cells mv mx mx1) Cell.loL i)
      (cellCol δF b (valsBE δF γ ρ E z big cells mv mx mx1) Cell.hiL i) := by
  have hi : (i : ℕ) < cells.length := hN ▸ i.isLt
  obtain ⟨a, c, hac, hrow⟩ := cellRowsBE_shape (δF := δF) E z big cells mv mx mx1 hcell hi
  have hr := hac ▸ hrank _ (List.getElem_mem hi)
  have hg : cells.getD i (.atom 0) = .cell a c := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, hac]
  rw [cellCol_lt δF b _ (by simp [Cell.wL]), cellCol_lt δF b _ (by simp [Cell.loL]),
    cellCol_lt δF b _ (by simp [Cell.hiL])]
  simp only [valsBE, cellFill, cellFillInv, CellVals.base, Cell.wL, Cell.loL, Cell.hiL, hrow]
  simp only [kbLB, hg]
  exact sideOK_child hp big a (rank_children hr).1

theorem sideOK_rowsB_RE (hp : 2 ^ 63 < ringChar F) (γ ρ : 𝕂′) (E : Noun → FP 𝕂′) (z : 𝕂′) (big : Noun → Option ℕ) (cells : List Noun)
    (mv mx mx1 : ℕ → ℕ) (hcell : ∀ c ∈ cells, c.isCell = true) (hrank : ∀ c ∈ cells, rankOf c < 2 ^ 110)
    (hN : n = cells.length) (i : Fin n) :
    HonestK8.SideOK (kbRB big cells i)
      (cellCol δF b (valsBE δF γ ρ E z big cells mv mx mx1) Cell.wR i)
      (cellCol δF b (valsBE δF γ ρ E z big cells mv mx mx1) Cell.loR i)
      (cellCol δF b (valsBE δF γ ρ E z big cells mv mx mx1) Cell.hiR i) := by
  have hi : (i : ℕ) < cells.length := hN ▸ i.isLt
  obtain ⟨a, c, hac, hrow⟩ := cellRowsBE_shape (δF := δF) E z big cells mv mx mx1 hcell hi
  have hr := hac ▸ hrank _ (List.getElem_mem hi)
  have hg : cells.getD i (.atom 0) = .cell a c := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, hac]
  rw [cellCol_lt δF b _ (by simp [Cell.wR]), cellCol_lt δF b _ (by simp [Cell.loR]),
    cellCol_lt δF b _ (by simp [Cell.hiR])]
  simp only [valsBE, cellFill, cellFillInv, CellVals.base, Cell.wR, Cell.loR, Cell.hiR, hrow]
  simp only [kbRB, hg]
  exact sideOK_child hp big c (rank_children hr).2

/-- **The honest J-8 cell trace at the list** (242 columns). -/
abbrev cellTraceBE (γ ρ : 𝕂′) (E : Noun → FP 𝕂′) (z : 𝕂′) (big : Noun → Option ℕ) (cells : List Noun) (mv mx mx1 mh : ℕ → ℕ) :=
  HonestKW.cellTraceHQKW δF b hn nodes orbit chals pubs (cellCol δF b (valsBE δF γ ρ E z big cells mv mx mx1))
    (fun i : Fin n => (mh i : F)) (kbLB big cells) (kbRB big cells)

/-- **`cellChipHQKW_honest_list`: the J-8 cell chip accepts the honest trace of any list of cells of rank
`< 2^110` with big-atom children**: `cellChip_honest_list`'s hypotheses, `2^63 < char F`, the wire-key poles,
and the `𝕂′` public `pubHQ` equal to the handle total. -/
theorem cellChipHQKW_honest_listE (hp : 2 ^ 63 < ringChar F) (γ ρ : 𝕂′) (E : Noun → FP 𝕂′) (z : 𝕂′) (big : Noun → Option ℕ)
    (cells : List Noun) (mv mx mx1 mh : ℕ → ℕ)
    (hcell : ∀ c ∈ cells, c.isCell = true) (hrank : ∀ c ∈ cells, rankOf c < 2 ^ 110)
    (hN : n = cells.length)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hok : ChalsOK δF chals γ ρ 11) (hzc : Quad.mk _ (chals 2) (chals 3) = z) (hz : z ≠ 0)
    (hEc : ∀ a c, E (.cell a c) = FP.cons z (E a) (E c))
    (hEa : ∀ v, ComplJ8Cell.isBig big (.atom v) = false → E (.atom v) = FP.atomFP z (liftQ δF ((v : ℕ) : F)))
    (hv : ∀ j < n, FiniteIO.compress (m := 5) ⟨γ, ρ⟩ (vKeyOf δF (cellRowsBE δF E z big cells mv mx mx1 j)) ≠ 0)
    (hl : ∀ j < n, (cellRowsBE δF E z big cells mv mx mx1 j).wL ≠ 0 →
      FiniteIO.compress (m := 5) ⟨γ, ρ⟩ (lKeyOf δF (cellRowsBE δF E z big cells mv mx mx1 j)) ≠ 0)
    (hr : ∀ j < n, (cellRowsBE δF E z big cells mv mx mx1 j).wR ≠ 0 →
      FiniteIO.compress (m := 5) ⟨γ, ρ⟩ (rKeyOf δF (cellRowsBE δF E z big cells mv mx mx1 j)) ≠ 0)
    (hx0 : ∀ j < n, FiniteIO.compress (m := 11) ⟨γ, ρ⟩ (xKeyOf δF (cellRowsBE δF E z big cells mv mx mx1 j) 0) ≠ 0)
    (hx1 : ∀ j < n, FiniteIO.compress (m := 11) ⟨γ, ρ⟩ (xKeyOf δF (cellRowsBE δF E z big cells mv mx mx1 j) 1) ≠ 0)
    (hV : ∑ k ∈ Finset.range n, vTermOf δF (cellFillInv δF γ ρ (cellRowsBE δF E z big cells mv mx mx1 k)) =
      Quad.mk _ (pubs 0) (pubs 1))
    (hX : ∑ k ∈ Finset.range n, xTermOf δF (cellFillInv δF γ ρ (cellRowsBE δF E z big cells mv mx mx1 k)) =
      Quad.mk _ (pubs 2) (pubs 3))
    (hpole : ∀ i, HonestKW.dRowW δF b hn nodes orbit chals pubs (cellCol δF b (valsBE δF γ ρ E z big cells mv mx mx1))
      (fun i : Fin n => (mh i : F)) (kbLB big cells) (kbRB big cells) i ≠ 0)
    (hpub : Quad.mk _ (pubs CellHQ.pubHQ) (pubs (CellHQ.pubHQ + 1)) = ∑ j ∈ Finset.range n,
      liftQ δF (CellTraceH.mN (fun i : Fin n => (mh i : F)) j) *
        (HonestKW.dNW δF b hn nodes orbit chals pubs (cellCol δF b (valsBE δF γ ρ E z big cells mv mx mx1))
          (fun i : Fin n => (mh i : F)) (kbLB big cells) (kbRB big cells) j)⁻¹) :
    (HonestKW.cellChipHQKW δF b hn nodes orbit chals pubs).rap.Satisfies
      (cellTraceBE δF b hn nodes orbit chals pubs γ ρ E z big cells mv mx mx1 mh) :=
  HonestKW.cellChipHQKW_accepts_honest δF b hn nodes orbit chals pubs _ _ _ _ hinj hadj
    (cellChip_honest_listE δF b hn nodes orbit chals pubs γ ρ E z big cells mv mx mx1 hcell hrank hN hinj hadj
      hok hzc hz hEc hEa hv hl hr hx0 hx1 hV hX)
    (sideOK_rowsB_LE δF b hp γ ρ E z big cells mv mx mx1 hcell hrank hN)
    (sideOK_rowsB_RE δF b hp γ ρ E z big cells mv mx mx1 hcell hrank hN) hpole hpub

/-- The preprocessing of the honest J-8 cell trace (both masks). -/
theorem cellChipHQKW_honest_list_bindE (γ ρ : 𝕂′) (E : Noun → FP 𝕂′) (z : 𝕂′) (big : Noun → Option ℕ) (cells : List Noun)
    (mv mx mx1 mh : ℕ → ℕ) :
    (HonestKW.cellChipHQKW δF b hn nodes orbit chals pubs).BindsPreprocessing
      (cellTraceBE δF b hn nodes orbit chals pubs γ ρ E z big cells mv mx mx1 mh) := by
  intro j
  fin_cases j
  · exact honestQ_zero hn nodes _ (by rw [HonestKW.cellTemplateHQKW_width]; omega)
  · exact honestQ_one hn nodes _ (by rw [HonestKW.cellTemplateHQKW_width]; omega)

end KWE

/-! ## 4. Staging of the honest cell trace at `E` -/

section StageME
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K] [DecidableEq F]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n)
  (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h)

/-- **The honest cell trace at a coin vector, encoder `EF χ`** (`ComplJ8Walk.cellTrM` at `E`). -/
def cellTrME (chalsF pubsF : Coins frameJ8 K → ℕ → K) (γF ρF zF : Coins frameJ8 K → Quad (algebraMap F K δF))
    (EF : Coins frameJ8 K → Noun → FP (Quad (algebraMap F K δF)))
    (big : Noun → Option ℕ) (cells : List Noun) (mv mx mx1 mh : ℕ → ℕ) (χ : Coins frameJ8 K) : Fin 242 → F[X] :=
  honestQ hn nodes (HonestKW.colW δF b (cellCol δF b (valsBE δF (γF χ) (ρF χ) (EF χ) (zF χ) big cells mv mx mx1))
    (fun i : Fin n => (mh i : F)) (kbLB big cells) (kbRB big cells)
    (HonestKW.ivW δF b hn nodes orbit (chalsF χ) (pubsF χ)
      (cellCol δF b (valsBE δF (γF χ) (ρF χ) (EF χ) (zF χ) big cells mv mx mx1))
      (fun i : Fin n => (mh i : F)) (kbLB big cells) (kbRB big cells))
    (HonestKW.avW δF b hn nodes orbit (chalsF χ) (pubsF χ)
      (cellCol δF b (valsBE δF (γF χ) (ρF χ) (EF χ) (zF χ) big cells mv mx mx1))
      (fun i : Fin n => (mh i : F)) (kbLB big cells) (kbRB big cells))) 242

theorem rowsBE_base (E E' : Noun → FP (Quad (algebraMap F K δF))) (z z' : Quad (algebraMap F K δF))
    (big : Noun → Option ℕ) (cells : List Noun) (mv mx mx1 : ℕ → ℕ) (j k : ℕ) :
    (cellRowsBE δF E z big cells mv mx mx1 j).base k = (cellRowsBE δF E' z' big cells mv mx mx1 j).base k := by
  simp only [cellRowsBE, cellRowBE, ComplJ8Cell.cellRowB, CellVals.base, cellRow0]

/-- **The honest cell trace map at `E` is staged**, when the encoder reads only round-0 coins. -/
theorem cellTrME_staged (chalsF pubsF : Coins frameJ8 K → ℕ → K) (γF ρF zF : Coins frameJ8 K → Quad (algebraMap F K δF))
    (EF : Coins frameJ8 K → Noun → FP (Quad (algebraMap F K δF)))
    (big : Noun → Option ℕ) (cells : List Noun) (mv mx mx1 mh : ℕ → ℕ)
    (hz : ∀ χ χ' : Coins frameJ8 K, (∀ i : Fin frameJ8.n, frameJ8.sampledAfter i = 0 → χ i = χ' i) → EF χ = EF χ') :
    StagedCols frameJ8 crM (cellTrME δF b hn nodes orbit chalsF pubsF γF ρF zF EF big cells mv mx mx1 mh) := by
  intro j χ χ' hχ
  by_cases h2 : 188 ≤ (j : ℕ)
  · rw [coins_eq_of_two χ χ' (crM j) (by simp only [crM]; split_ifs <;> omega) hχ]
  · unfold cellTrME
    refine honestQ_congr _ _ _ _ _ _ ?_
    have hcol : ∀ k, k < 183 → (129 ≤ k → EF χ = EF χ') →
        cellCol δF b (valsBE (n := n) δF (γF χ) (ρF χ) (EF χ) (zF χ) big cells mv mx mx1) k =
          cellCol δF b (valsBE (n := n) δF (γF χ') (ρF χ') (EF χ') (zF χ') big cells mv mx mx1) k := by
      intro k hk hzk
      funext i
      exact cellCol_round1 b _ _ _ _ _ _ k (fun i k => rowsBE_base δF _ _ _ _ big cells mv mx mx1 i k)
        (fun h1 _ _ _ => by simp only [cellRowsBE, cellRowBE]; rw [hzk h1]) i hk
    refine colW_cong δF b _ _ _ _ _ _ _ _ _ _ (by omega) (fun k hk => hcol k (by omega)
      (fun h => absurd h (by omega))) (fun hj => hcol _ (by omega) (fun _ => ?_))
    exact hz χ χ' (round0_of_one χ χ' (crM j) (by simp only [crM]; split_ifs <;> omega) hχ)

end StageME

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Enc
