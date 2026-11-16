/-
  Nock/NockVMROM/Thm54/VclL/Chips/HonestWalkGen.lean

  **The honest walk table's values and its row
  facts.**

  * `walkRow0 z cells preads α γ j`: the honest values of walk row `j` (the `j`-th node of
    `GenWalk.walkRows` = the read trie in BFS order): `idx = idxOf node`, `pre = axisFold bits`,
    `ridx = idxOf root`, `len = |bits|`, `cL cR` the trie states, `e = cL·cR`, `mL mR` the record
    multiplicities, `q = qH`, `qinv = q⁻¹`, the six bits of `61 − len` and `u = b₁b₂`; the four
    fingerprints at the seed `z`; the walk's explicit `ln = α^{j+1}`, `count = countH`,
    `acc = accH` at `nodeVal t = RLC^γ(enc(lblW t))`.
  * `walkFill γ′ ρ′`: the two path-provide inverses, the export-consume inverse and the two prefix
    sums (`pathFill`'s twin).
  * `walkRow0_base` (`WalkBaseFacts` on every row: from `walkRows_queue`, `walkRows_root`,
    `walkRows_len_le`), **`walkRow0_K`** (`WalkKFacts` at every coin pair `(α, γ)`: the explicit
    in-gate walk of trunk `honest_walk_acc_zero`, the trie child = in-gate child `dtW_child`),
    `walkFill_mixed` (`WalkMixedFacts` given non-zero denominators and the two terminals).
-/
import Nock.NockVMROM.Thm54.VclL.Chips.HonestWalkCol
import Nock.NockVMROM.Thm54.VclL.Chips.HonestMemGenCell
import Nock.NockVMROM.Thm54.VclL.Walk.GenWalkLabels

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP

open Nock Nock.Walk
open Nock.Reified
open Nock.Framework
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.VclL.GenWalk
open Module
open scoped Polynomial

noncomputable section

/-! ## 1. Trie facts at the honest rows -/

section Trie

/-- Every honest walk row is a trie node. -/
theorem walkRows_trie {cells : List Noun} {preads : List (Noun × ℕ)} {t : NTree WN}
    (ht : t ∈ walkRows cells preads) : ∃ root n bs T, t = trie root n bs T := by
  obtain ⟨c, hc, hct⟩ := (mem_bfsForest _ t).mp ht
  rcases mem_walkForest hc with ⟨-, rfl⟩ | ⟨r, -, rfl⟩
  · obtain ⟨n', bs', T', h, -⟩ := inTree_trie_inv _ (fun _ _ _ => True)
      (fun _ _ _ _ _ _ _ => trivial) hct _ _ _ rfl trivial
    exact ⟨_, n', bs', T', h⟩
  · obtain ⟨n', bs', T', h, -⟩ := inTree_trie_inv _ (fun _ _ _ => True)
      (fun _ _ _ _ _ _ _ => trivial) hct _ _ _ rfl trivial
    exact ⟨_, n', bs', T', h⟩

/-- The fanout of an honest row is `cL + cR`. -/
theorem walkRows_fanout {cells : List Noun} {preads : List (Noun × ℕ)} {t : NTree WN}
    (ht : t ∈ walkRows cells preads) :
    t.children.length = WalkVCL.fanout (t.label.cL, t.label.cR) := by
  obtain ⟨root, n, bs, T, rfl⟩ := walkRows_trie ht
  rw [trie_fanout]; rfl

/-- **The `l`-th child of a trie node is the side-`sideOf s l` trie child.** -/
theorem trie_child_get (root n : Noun) (bs : List Bool) (T : List (List Bool)) (l : ℕ) (h1 : 1 ≤ l)
    (hl : l ≤ WalkVCL.fanout ((trie root n bs T).label.cL, (trie root n bs T).label.cR)) :
    ∃ a c, n = .cell a c ∧
      (trie root n bs T).children[l - 1]? =
        some (trie root (if sideOf ((trie root n bs T).label.cL, (trie root n bs T).label.cR) l then c else a)
          (bs ++ [sideOf ((trie root n bs T).label.cL, (trie root n bs T).label.cR) l])
          (contT (sideOf ((trie root n bs T).label.cL, (trie root n bs T).label.cR) l) T)) := by
  cases n with
  | atom v => simp [trie, WalkVCL.fanout] at hl; omega
  | cell a c =>
    refine ⟨a, c, rfl, ?_⟩
    have hs := trie_states_cell root a c bs T
    rw [hs.1, hs.2] at hl ⊢
    rw [trie_children_cell]
    have hl2 : l ≤ 2 := by
      simp only [WalkVCL.fanout] at hl; split_ifs at hl <;> omega
    interval_cases l <;> cases hL : cont false T <;> cases hR : cont true T <;>
      simp_all [WalkVCL.fanout, sideOf]

end Trie

/-! ## 2. The honest values -/

section Vals
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq F] [DecidableEq K]
  [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  (z : Quad (algebraMap F K δF)) (cells : List Noun) (preads : List (Noun × ℕ))

/-- The honest walk row `j`'s trie node (rows past the table read a dummy, never used). -/
def wTrie (j : ℕ) : NTree WN := (walkRows cells preads).getD j (trie (.atom 0) (.atom 0) [] [])

theorem wTrie_mem {j : ℕ} (hj : j < (walkRows cells preads).length) : wTrie cells preads j ∈ walkRows cells preads := by
  unfold wTrie; rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj

/-- The walk's node valuation `RLC^γ(enc(lblW t))`. -/
def wNodeVal (γ : K) (t : NTree WN) : K :=
  Nock.Walk.rlc γ (WalkVCL.enc (algebraMap F K δF) (lblW (q := ringChar F) z cells t))

/-- Certificate bit `k` of `m`. -/
def certBit (m k : ℕ) : F := if m.testBit k then 1 else 0

/-- **The honest values of walk row `j`** (B2 IO quantities `0`; `walkFill` sets them). -/
def walkRow0 (α γ : K) (j : ℕ) : WalkVals F K (Quad (algebraMap F K δF)) where
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
  p := GlobalCarryRecognizer.enc z (wTrie cells preads j).label.node
  l := GlobalCarryRecognizer.enc z (hdN (wTrie cells preads j).label.node)
  r := GlobalCarryRecognizer.enc z (tlN (wTrie cells preads j).label.node)
  root := GlobalCarryRecognizer.enc z (wTrie cells preads j).label.root
  ln := α ^ (j + 1)
  cnt := countH (foCol (walkRows cells preads)) α (krW cells preads) (j + 1)
  acc := accH (curCol (wNodeVal δF z cells γ) (walkRows cells preads))
    (chldCol (wNodeVal δF z cells γ) (walkRows cells preads)) (foCol (walkRows cells preads)) α
    (krW cells preads) (j + 1)
  xInv := 0
  pInvL := 0
  pInvR := 0
  xAcc := 0
  pAcc := 0

end Vals

/-! ## 3. The base facts -/

section Base
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq F] [DecidableEq K]
  [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  (z : Quad (algebraMap F K δF)) (cells : List Noun) (preads : List (Noun × ℕ)) (α γ : K)

omit [Fact (ringChar F).Prime] in
theorem certBit_excl {m : ℕ} (hm : m ≤ 61) :
    certBit (F := F) m 1 * certBit m 2 * certBit m 3 * (certBit m 4 * certBit m 5) = 0 := by
  have key : ∀ m < 62, (m.testBit 1 && m.testBit 2 && m.testBit 3 && m.testBit 4 && m.testBit 5) = false := by
    decide
  have := key m (by omega)
  unfold certBit
  split_ifs <;> simp_all

omit [Fact (ringChar F).Prime] in
theorem certBit_bool (m k : ℕ) : certBit (F := F) m k * (certBit m k - 1) = 0 := by
  unfold certBit; split_ifs <;> simp

omit [Fact (ringChar F).Prime] in
theorem certBit_sum {m : ℕ} (hm : m < 2 ^ 6) :
    ∑ k ∈ Finset.range 6, (2 : F) ^ k * certBit m k = (m : F) :=
  (sum_testBit_cast 6 m hm).symm

omit [Fact (ringChar F).Prime] in
theorem cast_ite_bool (b : Bool) : (((if b then 1 else 0 : ℕ)) : F) = if b then 1 else 0 := by
  split_ifs <;> simp

/-- The `ℕ` queue identity at every row `1 ≤ i ≤ n`: `i + q_i = kr + Sf i`. -/
theorem walk_q_id (i : ℕ) (h1 : 1 ≤ i) (hi : i ≤ (walkRows cells preads).length) :
    i + qH (krW cells preads) (foCol (walkRows cells preads)) i =
      krW cells preads + Sf (foCol (walkRows cells preads)) i := by
  obtain ⟨hlt, hlast, htile, -⟩ := walkRows_queue cells preads
  rcases Nat.lt_or_ge i (walkRows cells preads).length with h | h
  · exact (hlt i h1 h).2
  · have : i = (walkRows cells preads).length := le_antisymm hi h
    subst this
    rw [hlast, add_zero, htile]

theorem foCol_walk {j : ℕ} (hj : j < (walkRows cells preads).length) :
    foCol (walkRows cells preads) (j + 1) = (wTrie cells preads j).children.length := by
  unfold foCol wTrie
  rw [Nat.add_sub_cancel, List.getElem?_eq_getElem hj, List.getD_eq_getElem _ _ hj]
  rfl

theorem foCol_walk_cast {j : ℕ} (hj : j < (walkRows cells preads).length) :
    ((foCol (walkRows cells preads) (j + 1) : ℕ) : F) =
      (if (wTrie cells preads j).label.cL then 1 else 0) + (if (wTrie cells preads j).label.cR then 1 else 0) := by
  rw [foCol_walk cells preads hj, walkRows_fanout (wTrie_mem cells preads hj)]
  simp only [WalkVCL.fanout, Nat.cast_add, cast_ite_bool]

/-- **`WalkBaseFacts` on every honest walk row** (`kr = krW`). -/
theorem walkRow0_base (h62 : ∀ r ∈ pathReads preads, depthOf r.2 ≤ 62)
    (hkp : krW cells preads + (walkRows cells preads).length < ringChar F)
    {n : ℕ} (hn : n = (walkRows cells preads).length) (i : Fin n) :
    WalkBaseFacts (krW cells preads)
      (fun j : Fin n => walkRow0 δF z cells preads α γ j) i := by
  subst hn
  have hi := i.isLt
  have hmem := wTrie_mem cells preads hi
  have hlen := walkRows_len_le h62 hmem
  have hq1 := walk_q_id cells preads
  refine
    { cL_bool := by simp only [walkRow0]; split_ifs <;> simp
      cR_bool := by simp only [walkRow0]; split_ifs <;> simp
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

end Base

/-! ## 4. The label bridge and the walk facts -/

section KFacts
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq F] [DecidableEq K]
  [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  (z : Quad (algebraMap F K δF)) (cells : List Noun) (preads : List (Noun × ℕ)) (α γ : K)
  (hF : GeneratedField.PrimeFieldElems F)
include hF

theorem zq_natCast {k : ℕ} (hk : k < ringChar F) : zq (k : F) = (k : ZMod (ringChar F)) := by
  unfold zq; rw [natOf_natCast hF hk]

omit hF in
theorem decide_ite_one (b : Bool) : decide ((if b then (1 : F) else 0) = 1) = b := by
  cases b <;> simp

/-- **The honest row's label is the trie node's `lblW`.** -/
theorem lblV_walkRow0 (hq : 2 ^ 63 < ringChar F) (hcells : cells.length < ringChar F)
    (h62 : ∀ r ∈ pathReads preads, depthOf r.2 ≤ 62) {j : ℕ} (hj : j < (walkRows cells preads).length) :
    lblV δF (walkRow0 δF z cells preads α γ j) = lblW (q := ringChar F) z cells (wTrie cells preads j) := by
  have hlen := walkRows_len_le h62 (wTrie_mem cells preads hj)
  have hax := axisFold_lt (wTrie cells preads j).label.bits
  have h2 : 2 ^ ((wTrie cells preads j).label.bits.length + 1) ≤ 2 ^ 62 :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : (2 : ℕ) ^ 62 < 2 ^ 63 := by norm_num
  have hri := List.idxOf_le_length (a := (wTrie cells preads j).label.root) (l := cells)
  simp only [lblV, walkRow0, lblW, dtW]
  rw [zq_natCast hF (by omega), zq_natCast hF (by omega), zq_natCast hF (by omega)]
  congr 2
  · exact decide_ite_one _
  · exact decide_ite_one _

/-- **The honest row's consumed key is the trie node's `keyW`.** -/
theorem keyV_walkRow0 (hcells : cells.length < ringChar F) (j : ℕ) :
    keyV δF (walkRow0 δF z cells preads α γ j) = keyW z cells (wTrie cells preads j) := by
  have hi := List.idxOf_le_length (a := (wTrie cells preads j).label.node) (l := cells)
  simp only [keyV, walkRow0, keyW]
  rw [natOf_natCast hF (by omega)]

theorem curV_walkRow0 (hq : 2 ^ 63 < ringChar F) (hcells : cells.length < ringChar F)
    (h62 : ∀ r ∈ pathReads preads, depthOf r.2 ≤ 62) {j : ℕ} (hj : j < (walkRows cells preads).length) :
    curV δF γ (walkRow0 δF z cells preads α γ j) =
      curCol (wNodeVal δF z cells γ) (walkRows cells preads) (j + 1) := by
  rw [curCol_succ, List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map, curV,
    lblV_walkRow0 δF z cells preads α γ hF hq hcells h62 hj]
  unfold wNodeVal wTrie
  rw [List.getD_eq_getElem _ _ hj]

theorem fanout_walkRow0 (hq : 2 ^ 63 < ringChar F) (hcells : cells.length < ringChar F)
    (h62 : ∀ r ∈ pathReads preads, depthOf r.2 ≤ 62) {j : ℕ} (hj : j < (walkRows cells preads).length) :
    WalkVCL.fanout (lblV δF (walkRow0 δF z cells preads α γ j)).1 = foCol (walkRows cells preads) (j + 1) := by
  rw [lblV_walkRow0 δF z cells preads α γ hF hq hcells h62 hj, foCol_walk cells preads hj,
    walkRows_fanout (wTrie_mem cells preads hj)]
  rfl

theorem ccV_walkRow0 (hq : 2 ^ 63 < ringChar F) (hcells : cells.length < ringChar F)
    (h62 : ∀ r ∈ pathReads preads, depthOf r.2 ≤ 62) {j : ℕ} (hj : j < (walkRows cells preads).length) :
    ccV δF α γ (walkRow0 δF z cells preads α γ j) =
      ∑ l ∈ Finset.Icc 1 (foCol (walkRows cells preads) (j + 1)), α ^ l *
        chldCol (wNodeVal δF z cells γ) (walkRows cells preads) (j + 1) l := by
  unfold ccV
  rw [fanout_walkRow0 δF z cells preads α γ hF hq hcells h62 hj]
  refine Finset.sum_congr rfl fun l hl => ?_
  obtain ⟨hl1, hl2⟩ := Finset.mem_Icc.mp hl
  congr 1
  have hlbl := lblV_walkRow0 δF z cells preads α γ hF hq hcells h62 hj
  have hkey := keyV_walkRow0 δF z cells preads α γ hF hcells j
  rw [hlbl, hkey]
  obtain ⟨root, n, bs, T, hT⟩ := walkRows_trie (wTrie_mem cells preads hj)
  rw [foCol_walk cells preads hj, walkRows_fanout (wTrie_mem cells preads hj)] at hl2
  rw [hT] at hl2 ⊢
  obtain ⟨a, c, rfl, hc⟩ := trie_child_get root n bs T l hl1 hl2
  have hch : chldCol (wNodeVal δF z cells γ) (walkRows cells preads) (j + 1) l =
      wNodeVal δF z cells γ (trie root
        (if sideOf ((trie root (.cell a c) bs T).label.cL, (trie root (.cell a c) bs T).label.cR) l then c else a)
        (bs ++ [sideOf ((trie root (.cell a c) bs T).label.cL, (trie root (.cell a c) bs T).label.cR) l])
        (contT (sideOf ((trie root (.cell a c) bs T).label.cL, (trie root (.cell a c) bs T).label.cR) l) T)) := by
    unfold chldCol
    have hw : (walkRows cells preads)[j]? = some (trie root (.cell a c) bs T) := by
      rw [List.getElem?_eq_getElem hj, ← hT]; unfold wTrie; rw [List.getD_eq_getElem _ _ hj]
    rw [Nat.add_sub_cancel, hw]
    simp [hc]
  rw [hch]
  unfold wNodeVal
  congr 1
  show WalkVCL.enc (algebraMap F K δF) (((false, false), _) : WalkVCL.LT (ringChar F) _) =
    WalkVCL.enc (algebraMap F K δF) ((_, dtW (q := ringChar F) z cells _) : WalkVCL.LT (ringChar F) _)
  rw [dtW_child]
  rfl

/-- **`WalkKFacts` on every honest walk row**, at every coin pair `(α, γ)` (no coin event). -/
theorem walkRow0_K (hq : 2 ^ 63 < ringChar F) (hcells : cells.length < ringChar F)
    (h62 : ∀ r ∈ pathReads preads, depthOf r.2 ≤ 62) {n : ℕ} (hn : n = (walkRows cells preads).length)
    (i : Fin n) :
    WalkKFacts δF (krW cells preads) (fun j : Fin n => walkRow0 δF z cells preads α γ j) α γ i := by
  subst hn
  have hi := i.isLt
  obtain ⟨hw, hz⟩ := honest_walk_acc_zero (wNodeVal δF z cells γ) (walkForest cells preads)
    (walkForest_ne_nil cells preads) α
  change WalkSatInGate (curCol (wNodeVal δF z cells γ) (walkRows cells preads))
    (chldCol (wNodeVal δF z cells γ) (walkRows cells preads)) (foCol (walkRows cells preads)) (lnH α)
    (countH (foCol (walkRows cells preads)) α (krW cells preads))
    (accH (curCol (wNodeVal δF z cells γ) (walkRows cells preads))
      (chldCol (wNodeVal δF z cells γ) (walkRows cells preads)) (foCol (walkRows cells preads)) α (krW cells preads))
    α (α ^ krW cells preads) (krW cells preads) (walkRows cells preads).length at hw
  change accH (curCol (wNodeVal δF z cells γ) (walkRows cells preads))
      (chldCol (wNodeVal δF z cells γ) (walkRows cells preads)) (foCol (walkRows cells preads)) α (krW cells preads)
      (walkRows cells preads).length = 0 at hz
  have fo := fun (j : ℕ) (hj : j < (walkRows cells preads).length) =>
    fanout_walkRow0 δF z cells preads α γ hF hq hcells h62 hj
  have cc := fun (j : ℕ) (hj : j < (walkRows cells preads).length) =>
    ccV_walkRow0 δF z cells preads α γ hF hq hcells h62 hj
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
    have hcu := curV_walkRow0 δF z cells preads α γ hF hq hcells h62 hi'
    show algebraMap F K (1 - if (i : ℕ) + 1 < krW cells preads then 1 else 0) * α ^ ((i : ℕ) + 1 + 1) *
        curV δF γ (walkRow0 δF z cells preads α γ ((i : ℕ) + 1)) +
        (accH _ _ _ α (krW cells preads) ((i : ℕ) + 1 + 1) - accH _ _ _ α (krW cells preads) ((i : ℕ) + 1)) =
      countH (foCol (walkRows cells preads)) α (krW cells preads) ((i : ℕ) + 1) *
        ccV δF α γ (walkRow0 δF z cells preads α γ ((i : ℕ) + 1))
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
          chldCol (wNodeVal δF z cells γ) (walkRows cells preads) ((i : ℕ) + 1 + 1) l) =
        ∑ l ∈ Finset.Icc 1 (foCol (walkRows cells preads) ((i : ℕ) + 1 + 1)),
          countH (foCol (walkRows cells preads)) α (krW cells preads) ((i : ℕ) + 1) *
            (α ^ l * chldCol (wNodeVal δF z cells γ) (walkRows cells preads) ((i : ℕ) + 1 + 1) l) :=
      Finset.sum_congr rfl fun l _ => by ring
    rw [hsum] at hs
    linear_combination hs
  · intro hl
    show accH _ _ _ α (krW cells preads) ((i : ℕ) + 1) = 0
    rw [hl]; exact hz

end KFacts

/-! ## 5. The fill (inverses and prefix sums) and the mixed facts -/

section Fill
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] (δF : F)
  [Fact (¬ IsSquare (algebraMap F K δF))]

/-- The three inverses of a walk row. -/
def walkFillInv (γ ρ : Quad (algebraMap F K δF)) (c : WalkVals F K (Quad (algebraMap F K δF))) :
    WalkVals F K (Quad (algebraMap F K δF)) :=
  { c with
    xInv := (FiniteIO.compress (m := 11) ⟨γ, ρ⟩ (wxKeyV δF c))⁻¹
    pInvL := (FiniteIO.compress (m := 8) ⟨γ, ρ⟩ (wrecLV δF c))⁻¹
    pInvR := (FiniteIO.compress (m := 8) ⟨γ, ρ⟩ (wrecRV δF c))⁻¹ }

/-- **The honest filled walk row `j`**: inverses and the two prefix-sum accumulators. -/
def walkFill (γ ρ : Quad (algebraMap F K δF)) (rows : ℕ → WalkVals F K (Quad (algebraMap F K δF)))
    (j : ℕ) : WalkVals F K (Quad (algebraMap F K δF)) :=
  { walkFillInv δF γ ρ (rows j) with
    xAcc := ∑ k ∈ Finset.range (j + 1), (walkFillInv δF γ ρ (rows k)).xInv
    pAcc := ∑ k ∈ Finset.range (j + 1), wpTermV δF (walkFillInv δF γ ρ (rows k)) }

variable (γ ρ : Quad (algebraMap F K δF)) (rows : ℕ → WalkVals F K (Quad (algebraMap F K δF))) (kr : ℕ)

theorem walkBaseFacts_fill {n : ℕ} (i : Fin n)
    (h : WalkBaseFacts kr (fun j : Fin n => rows j) i) :
    WalkBaseFacts kr (fun j : Fin n => walkFill δF γ ρ rows j) i :=
  { cL_bool := h.cL_bool, cR_bool := h.cR_bool, e_eq := h.e_eq, u_eq := h.u_eq, excl := h.excl,
    cert := h.cert, root_pre := h.root_pre, root_len := h.root_len, root_ridx := h.root_ridx,
    q_first := h.q_first, q_step := h.q_step, q_inv := h.q_inv, q_last := h.q_last,
    bit_bool := h.bit_bool }

theorem walkKFacts_fill [DecidableEq F] [DecidableEq K] [Fact (ringChar F).Prime]
    [Algebra (ZMod (ringChar F)) K] {n : ℕ} (α γK : K) (i : Fin n)
    (h : WalkKFacts δF kr (fun j : Fin n => rows j) α γK i) :
    WalkKFacts δF kr (fun j : Fin n => walkFill δF γ ρ rows j) α γK i :=
  { ln_first := h.ln_first, ln_step := h.ln_step, cnt_first := h.cnt_first, cnt_step := h.cnt_step,
    acc_first := h.acc_first, acc_step := h.acc_step, acc_last := h.acc_last }

/-- **`WalkMixedFacts` of the filled walk table**, given the root rows' `root = p`, non-zero
denominators on every row (both path records — the unconditional inverses) and the two terminals. -/
theorem walkFill_mixed (pubs : ℕ → K) {n : ℕ} (i : Fin n)
    (hroot : ∀ j < n, j < kr → (rows j).root = (rows j).p)
    (hx : ∀ j < n, FiniteIO.compress (m := 11) ⟨γ, ρ⟩ (wxKeyV δF (rows j)) ≠ 0)
    (hL : ∀ j < n, FiniteIO.compress (m := 8) ⟨γ, ρ⟩ (wrecLV δF (rows j)) ≠ 0)
    (hR : ∀ j < n, FiniteIO.compress (m := 8) ⟨γ, ρ⟩ (wrecRV δF (rows j)) ≠ 0)
    (hXt : ∑ k ∈ Finset.range n, (walkFillInv δF γ ρ (rows k)).xInv = Quad.mk _ (pubs 0) (pubs 1))
    (hPt : ∑ k ∈ Finset.range n, wpTermV δF (walkFillInv δF γ ρ (rows k)) = Quad.mk _ (pubs 2) (pubs 3)) :
    WalkMixedFacts δF kr pubs (fun j : Fin n => walkFill δF γ ρ rows j) γ ρ i := by
  have hi : (i : ℕ) < n := i.isLt
  refine ⟨hroot i hi, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact inv_mul_cancel₀ (hx i hi)
  · exact inv_mul_cancel₀ (hL i hi)
  · exact inv_mul_cancel₀ (hR i hi)
  · intro h0
    show ∑ k ∈ Finset.range ((i : ℕ) + 1), _ = _
    rw [h0, Finset.sum_range_one]; rfl
  · intro hi'
    show ∑ k ∈ Finset.range ((i : ℕ) + 1 + 1), _ = ∑ k ∈ Finset.range ((i : ℕ) + 1), _ + _
    exact Finset.sum_range_succ _ _
  · intro hi'
    show ∑ k ∈ Finset.range ((i : ℕ) + 1), _ = _
    rw [hi', hXt]
  · intro h0
    show ∑ k ∈ Finset.range ((i : ℕ) + 1), _ = _
    rw [h0, Finset.sum_range_one]; rfl
  · intro hi'
    show ∑ k ∈ Finset.range ((i : ℕ) + 1 + 1), _ = ∑ k ∈ Finset.range ((i : ℕ) + 1), _ + _
    exact Finset.sum_range_succ _ _
  · intro hi'
    show ∑ k ∈ Finset.range ((i : ℕ) + 1), _ = _
    rw [hi', hPt]

end Fill

end

end Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
