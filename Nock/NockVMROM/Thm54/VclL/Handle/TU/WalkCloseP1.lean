/-
 Nock/NockVMROM/Thm54/VclL/Handle/TU/WalkCloseP1.lean

 **Trace uniqueness on the P1 fragment: closing the walk hypotheses of `r0W_auxW_r1W`.**

 * §1 abstract BFS rows: every row's prefix ancestors are rows (`anc`), the prefix bound `a < 2^(len+1)`
 (`a_lt`), the read closure `readClosure R` (the proper prefixes of each read path, rooted at its root serial)
 and its cover by any BFS family providing each read's parent node (`covers_closure`).
 * §2 abstract label determination along the BFS order (`labels_det`): the cell rows the walk rows name (`idx`)
 and the four fingerprints `p l r root` of two walk tables over one trie agree, given they agree on the roots,
 each row's fingerprints are its named cell row's, children carry their parent's side fingerprint (as a key of
 some row with the parent's fingerprint), and the cell fingerprints are injective.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenCoreWP1
import Nock.NockVMROM.Thm54.VclL.Handle.TU.CountsP1
import Nock.NockVMROM.Thm54.VclL.Handle.TU.RoundsCellP1

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.TU.WalkCloseP1

noncomputable section

open Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenCoreWP1 (BFSRows fo side bit P P_congr)

/-! ## 1. Abstract BFS rows: ancestors and the read closure -/

section Abs
variable {n kr : ℕ} {st : ℕ → Bool × Bool} {r a d : ℕ → ℕ}

theorem div_two_child (x : ℕ) (b : Bool) : (2 * x + bit b) / 2 = x := by
  unfold bit; split_ifs <;> omega

/-- **Every prefix ancestor of a row is a row**: `(r j, a j / 2^k)` is a row's key whenever `a j / 2^k ≥ 1`. -/
theorem anc (B : BFSRows n kr st r a d) :
    ∀ j < n, ∀ k, 1 ≤ a j / 2 ^ k → ∃ j' < n, r j' = r j ∧ a j' = a j / 2 ^ k := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj k hk
    cases k with
    | zero => exact ⟨j, hj, rfl, by simp⟩
    | succ k =>
      by_cases hr : j < kr
      · exfalso
        rw [(B.root j hr).1] at hk
        have : 1 / 2 ^ (k + 1) = 0 := Nat.div_eq_of_lt (Nat.one_lt_two_pow (by omega))
        omega
      · obtain ⟨i, hi, l, hl, rfl⟩ := B.parent j (by omega) hj
        obtain ⟨-, ri, ai, -⟩ := B.child i (by omega) l hl
        have e : a (kr + P st i + l) / 2 ^ (k + 1) = a i / 2 ^ k := by
          rw [ai, pow_succ', ← Nat.div_div_eq_div_mul, div_two_child]
        rw [e] at hk ⊢
        obtain ⟨j', hj', h1, h2⟩ := ih i hi (by omega) k hk
        exact ⟨j', hj', h1.trans ri.symm, h2⟩

/-- **The prefix bound**: `a j < 2^(d j + 1)`. -/
theorem a_lt (B : BFSRows n kr st r a d) : ∀ j < n, a j < 2 ^ (d j + 1) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    by_cases hr : j < kr
    · rw [(B.root j hr).1, (B.root j hr).2]; norm_num
    · obtain ⟨i, hi, l, hl, rfl⟩ := B.parent j (by omega) hj
      obtain ⟨-, -, ai, di⟩ := B.child i (by omega) l hl
      rw [ai, di, pow_succ]
      have := ih i hi (by omega)
      unfold bit; split_ifs <;> omega

/-- The proper prefixes `a / 2, a / 4, …, 1` of one read `(root, a)`, each rooted at the read's root serial. -/
def pref (s : ℕ × ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range s.2).filter fun k => 1 ≤ s.2 / 2 ^ (k + 1)).image fun k => (s.1, s.2 / 2 ^ (k + 1))

/-- **The read closure** of a set of reads `(root serial, axis)`: the proper prefixes of every read path. -/
def readClosure (R : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) := R.biUnion pref

/-- **The read closure is covered** by any BFS family in which every read's parent node `(root, a / 2)` is a row. -/
theorem covers_closure (B : BFSRows n kr st r a d) (R : Finset (ℕ × ℕ))
    (hprov : ∀ s ∈ R, ∃ j < n, r j = s.1 ∧ a j = s.2 / 2) :
    ∀ s ∈ readClosure R, ∃ j < n, r j = s.1 ∧ a j = s.2 := by
  intro s hs
  obtain ⟨t, ht, hst⟩ := Finset.mem_biUnion.mp hs
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hst
  have hk1 := (Finset.mem_filter.mp hk).2
  obtain ⟨j, hj, h1, h2⟩ := hprov t ht
  have e : t.2 / 2 ^ (k + 1) = a j / 2 ^ k := by
    rw [h2, pow_succ', ← Nat.div_div_eq_div_mul]
  rw [e] at hk1 ⊢
  obtain ⟨j', hj', e1, e2⟩ := anc B j hj k hk1
  exact ⟨j', hj', e1.trans h1, e2⟩

end Abs

/-! ## 2. Abstract label determination along the BFS order -/

section Labels
variable {n kr : ℕ} {st : ℕ → Bool × Bool} {r a d : ℕ → ℕ}

/-- **The named cell rows and the fingerprints of two walk tables over one trie agree.** Per table: row `j` names
the cell row `ix j < nC` and carries that row's fingerprints `p l r` (`hx`); a root's root fingerprint is its own
(`hrt`); a child's fingerprint is the side fingerprint of a key of some row with the parent's fingerprint, and its
root fingerprint is the parent's (`hch`). With injective cell fingerprints `cp` and equal named rows on the roots,
everything agrees on every row. -/
theorem labels_det {Φ : Type*} (B : BFSRows n kr st r a d) {nC : ℕ} (cp cl cr : ℕ → Φ)
    (hcp : ∀ i < nC, ∀ i' < nC, cp i = cp i' → i = i')
    (ix ix' : ℕ → ℕ) (Pn L R Rt Pn' L' R' Rt' : ℕ → Φ)
    (hx : ∀ j < n, ix j < nC ∧ Pn j = cp (ix j) ∧ L j = cl (ix j) ∧ R j = cr (ix j))
    (hx' : ∀ j < n, ix' j < nC ∧ Pn' j = cp (ix' j) ∧ L' j = cl (ix' j) ∧ R' j = cr (ix' j))
    (hrt : ∀ j < kr, Rt j = Pn j) (hrt' : ∀ j < kr, Rt' j = Pn' j)
    (hch : ∀ i < n, ∀ l < fo (st i), ∃ j' < n, Pn j' = Pn i ∧
      Pn (kr + P st i + l) = (if side (st i) l then R j' else L j') ∧ Rt (kr + P st i + l) = Rt i)
    (hch' : ∀ i < n, ∀ l < fo (st i), ∃ j' < n, Pn' j' = Pn' i ∧
      Pn' (kr + P st i + l) = (if side (st i) l then R' j' else L' j') ∧ Rt' (kr + P st i + l) = Rt' i)
    (h0 : ∀ j < kr, ix j = ix' j) :
    ∀ j < n, ix j = ix' j ∧ Pn j = Pn' j ∧ L j = L' j ∧ R j = R' j ∧ Rt j = Rt' j := by
  -- a child's fingerprint is the side fingerprint of its parent's named cell row
  have hside : ∀ (ix : ℕ → ℕ) (Pn L R Rt : ℕ → Φ),
      (∀ j < n, ix j < nC ∧ Pn j = cp (ix j) ∧ L j = cl (ix j) ∧ R j = cr (ix j)) →
      (∀ i < n, ∀ l < fo (st i), ∃ j' < n, Pn j' = Pn i ∧
        Pn (kr + P st i + l) = (if side (st i) l then R j' else L j') ∧ Rt (kr + P st i + l) = Rt i) →
      ∀ i < n, ∀ l < fo (st i), Pn (kr + P st i + l) = (if side (st i) l then cr (ix i) else cl (ix i)) ∧
        Rt (kr + P st i + l) = Rt i := by
    intro ix Pn L R Rt hx hch i hi l hl
    obtain ⟨j', hj', e1, e2, e3⟩ := hch i hi l hl
    obtain ⟨a1, b1, c1, d1⟩ := hx j' hj'
    obtain ⟨a2, b2, -, -⟩ := hx i hi
    have hix : ix j' = ix i := hcp _ a1 _ a2 (b1.symm.trans (e1.trans b2))
    refine ⟨?_, e3⟩
    rw [e2, c1, d1, hix]
  have S := hside ix Pn L R Rt hx hch
  have S' := hside ix' Pn' L' R' Rt' hx' hch'
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    have hfin : ix j = ix' j → Pn j = Pn' j ∧ L j = L' j ∧ R j = R' j := by
      intro e
      obtain ⟨-, b1, c1, d1⟩ := hx j hj
      obtain ⟨-, b2, c2, d2⟩ := hx' j hj
      exact ⟨by rw [b1, b2, e], by rw [c1, c2, e], by rw [d1, d2, e]⟩
    by_cases hjk : j < kr
    · have e := h0 j hjk
      obtain ⟨f1, f2, f3⟩ := hfin e
      exact ⟨e, f1, f2, f3, by rw [hrt j hjk, hrt' j hjk, f1]⟩
    · obtain ⟨i, hi, l, hl, rfl⟩ := B.parent j (by omega) hj
      obtain ⟨u1, -, -, -, u5⟩ := ih i hi (by omega)
      obtain ⟨s1, s2⟩ := S i (by omega) l hl
      obtain ⟨s1', s2'⟩ := S' i (by omega) l hl
      have hP : Pn (kr + P st i + l) = Pn' (kr + P st i + l) := by rw [s1, s1', u1]
      have e : ix (kr + P st i + l) = ix' (kr + P st i + l) := by
        obtain ⟨a1, b1, -, -⟩ := hx _ hj
        obtain ⟨a2, b2, -, -⟩ := hx' _ hj
        exact hcp _ a1 _ a2 (b1.symm.trans (hP.trans b2))
      obtain ⟨f1, f2, f3⟩ := hfin e
      exact ⟨e, f1, f2, f3, by rw [s2, s2', u5]⟩

/-- **`labels_det`, relational cell table.** The cell table is a relation `Cell i p l r` (row `i` has fingerprints
`p l r`), functional in `i` (`hfun`) with `p` determining `i` (`hinj`). Per walk table: row `j` names the cell row
`ix j` with its fingerprints (`hx`); roots have `root = p` (`hrt`); a child's `p` is the side fingerprint of a key
`(l, r)` of some row with the parent's `p`, and its root is the parent's (`hch`). Two tables over one trie that agree
on the named cell rows of the roots agree everywhere. -/
theorem labels_det2 {Φ : Type*} (B : BFSRows n kr st r a d) (Cell : ℕ → Φ → Φ → Φ → Prop)
    (hfun : ∀ i p l r p' l' r', Cell i p l r → Cell i p' l' r' → p = p' ∧ l = l' ∧ r = r')
    (hinj : ∀ i i' p l r l' r', Cell i p l r → Cell i' p l' r' → i = i')
    (ix ix' : ℕ → ℕ) (Pn L R Rt Pn' L' R' Rt' : ℕ → Φ)
    (hx : ∀ j < n, Cell (ix j) (Pn j) (L j) (R j))
    (hx' : ∀ j < n, Cell (ix' j) (Pn' j) (L' j) (R' j))
    (hrt : ∀ j < kr, Rt j = Pn j) (hrt' : ∀ j < kr, Rt' j = Pn' j)
    (hch : ∀ i < n, ∀ l < fo (st i), ∃ j' < n, Pn j' = Pn i ∧
      Pn (kr + P st i + l) = (if side (st i) l then R j' else L j') ∧ Rt (kr + P st i + l) = Rt i)
    (hch' : ∀ i < n, ∀ l < fo (st i), ∃ j' < n, Pn' j' = Pn' i ∧
      Pn' (kr + P st i + l) = (if side (st i) l then R' j' else L' j') ∧ Rt' (kr + P st i + l) = Rt' i)
    (h0 : ∀ j < kr, ix j = ix' j) :
    ∀ j < n, ix j = ix' j ∧ Pn j = Pn' j ∧ L j = L' j ∧ R j = R' j ∧ Rt j = Rt' j := by
  have hside : ∀ (ix : ℕ → ℕ) (Pn L R Rt : ℕ → Φ),
      (∀ j < n, Cell (ix j) (Pn j) (L j) (R j)) →
      (∀ i < n, ∀ l < fo (st i), ∃ j' < n, Pn j' = Pn i ∧
        Pn (kr + P st i + l) = (if side (st i) l then R j' else L j') ∧ Rt (kr + P st i + l) = Rt i) →
      ∀ i < n, ∀ l < fo (st i), Pn (kr + P st i + l) = (if side (st i) l then R i else L i) ∧
        Rt (kr + P st i + l) = Rt i := by
    intro ix Pn L R Rt hx hch i hi l hl
    obtain ⟨j', hj', e1, e2, e3⟩ := hch i hi l hl
    have c1 := hx j' hj'
    have c2 := hx i hi
    rw [e1] at c1
    have hix := hinj _ _ _ _ _ _ _ c1 c2
    rw [hix] at c1
    obtain ⟨-, hl2, hr2⟩ := hfun _ _ _ _ _ _ _ c1 c2
    refine ⟨?_, e3⟩
    rw [e2, hl2, hr2]
  have S := hside ix Pn L R Rt hx hch
  have S' := hside ix' Pn' L' R' Rt' hx' hch'
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    have hfin : ix j = ix' j → Pn j = Pn' j ∧ L j = L' j ∧ R j = R' j := by
      intro e
      have c1 := hx j hj
      have c2 := hx' j hj
      rw [← e] at c2
      exact hfun _ _ _ _ _ _ _ c1 c2
    by_cases hjk : j < kr
    · have e := h0 j hjk
      obtain ⟨f1, f2, f3⟩ := hfin e
      exact ⟨e, f1, f2, f3, by rw [hrt j hjk, hrt' j hjk, f1]⟩
    · obtain ⟨i, hi, l, hl, rfl⟩ := B.parent j (by omega) hj
      obtain ⟨u1, u2, u3, u4, u5⟩ := ih i hi (by omega)
      obtain ⟨s1, s2⟩ := S i (by omega) l hl
      obtain ⟨s1', s2'⟩ := S' i (by omega) l hl
      have hP : Pn (kr + P st i + l) = Pn' (kr + P st i + l) := by
        rw [s1, s1']; split_ifs
        · exact u4
        · exact u3
      have e : ix (kr + P st i + l) = ix' (kr + P st i + l) :=
        hinj _ _ _ _ _ _ _ (hx _ hj) (hP ▸ hx' _ hj)
      obtain ⟨f1, f2, f3⟩ := hfin e
      exact ⟨e, f1, f2, f3, by rw [s2, s2', u5]⟩


/-- **`labels_det2` for two tables with their own flag families** (equal on the rows). -/
theorem labels_pair {Φ : Type*} (B : BFSRows n kr st r a d) (Cell : ℕ → Φ → Φ → Φ → Prop)
    (hfun : ∀ i p l r p' l' r', Cell i p l r → Cell i p' l' r' → p = p' ∧ l = l' ∧ r = r')
    (hinj : ∀ i i' p l r l' r', Cell i p l r → Cell i' p l' r' → i = i')
    (ix ix' : ℕ → ℕ) (Pn L R Rt Pn' L' R' Rt' : ℕ → Φ) (st' : ℕ → Bool × Bool)
    (hst : ∀ j < n, st' j = st j)
    (hx : ∀ j < n, Cell (ix j) (Pn j) (L j) (R j))
    (hx' : ∀ j < n, Cell (ix' j) (Pn' j) (L' j) (R' j))
    (hrt : ∀ j < kr, Rt j = Pn j) (hrt' : ∀ j < kr, Rt' j = Pn' j)
    (hch : ∀ i < n, ∀ l < fo (st i), ∃ j' < n, Pn j' = Pn i ∧
      Pn (kr + P st i + l) = (if side (st i) l then R j' else L j') ∧ Rt (kr + P st i + l) = Rt i)
    (hch' : ∀ i < n, ∀ l < fo (st' i), ∃ j' < n, Pn' j' = Pn' i ∧
      Pn' (kr + P st' i + l) = (if side (st' i) l then R' j' else L' j') ∧ Rt' (kr + P st' i + l) = Rt' i)
    (h0 : ∀ j < kr, ix j = ix' j) :
    ∀ j < n, ix j = ix' j ∧ Pn j = Pn' j ∧ L j = L' j ∧ R j = R' j ∧ Rt j = Rt' j := by
  refine labels_det2 B Cell hfun hinj ix ix' Pn L R Rt Pn' L' R' Rt' hx hx' hrt hrt' hch ?_ h0
  intro i hi l hl
  have hP : P st' i = P st i := (P_congr (fun j hj => (hst j (by omega)).symm)).symm
  obtain ⟨j', hj', e1, e2, e3⟩ := hch' i hi l (by rw [hst i hi]; exact hl)
  refine ⟨j', hj', e1, ?_, ?_⟩
  · rw [hP, hst i hi] at e2; exact e2
  · rw [hP] at e3; exact e3

end Labels

/-- **The read cover from provenance.** If every read `s ∈ R` (root serial, axis) has its parent node `(s.1, s.2/2)`
as a row of each of two BFS tables of `n` rows, the closure of `R` is covered by both, and `S = readClosure R` is a
key set of `n` keys when `n = |readClosure R|` (the canonical size). -/
theorem reads_cover {n kr n' kr' : ℕ} {st st' : ℕ → Bool × Bool} {r a d r' a' d' : ℕ → ℕ}
    (B : BFSRows n kr st r a d) (B' : BFSRows n' kr' st' r' a' d') (R : Finset (ℕ × ℕ))
    (hprov : ∀ s ∈ R, ∃ j < n, r j = s.1 ∧ a j = s.2 / 2)
    (hprov' : ∀ s ∈ R, ∃ j < n', r' j = s.1 ∧ a' j = s.2 / 2) :
    (∀ s ∈ readClosure R, ∃ j < n, r j = s.1 ∧ a j = s.2) ∧
      (∀ s ∈ readClosure R, ∃ j < n', r' j = s.1 ∧ a' j = s.2) :=
  ⟨covers_closure B R hprov, covers_closure B' R hprov'⟩


/-! ## 3. The walk forest as BFS rows, with the child relation -/

section Goal
open Nock.Walk Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.WalkVCL
open Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenCoreWP1 (flatMap_getElem?_pos flatMap_decomp take_flatMap_length val_lin
  val_succ val_one' side_false side_true fo_le_two P_succ P_mono pos_inj)
variable {q : ℕ} {Kfp : Type} [Field Kfp] [DecidableEq Kfp]

/-- **`bfsRows_of_goal` with the child relation kept**: besides the BFS rows, every child slot `l` of row `i` is the
child step of row `i` under an export key `k ∈ X` (`ChildOK`: node `tgt k side`, prefix `2 pre + side`, same root and
serial, length `+ 1`). -/
theorem bfsRowsN_of_goal {X : List (XKey Kfp)} {lbl : ℕ → LT q Kfp} {kroots h : ℕ} {fo' : ℕ → ℕ}
    (hq : 2 ^ 63 < q) (hk : 1 ≤ kroots)
    (hG : ForestReconGoal (stateSep (q := q) X 62) lbl kroots h)
    (hroot : ∀ i, 1 ≤ i → i ≤ kroots → RootOK (lbl i).2)
    (hvalid : BFSValidF kroots fo' h) (hfo : ∀ i, 1 ≤ i → i ≤ h → fo' i = WalkVCL.fanout (lbl i).1)
    (haxis : ∀ i, 1 ≤ i → i ≤ h → ∀ b, (2 * (lbl i).2.pre + bitZ b).val < 2 ^ 62) :
    BFSRows h kroots (fun j => (lbl (j + 1)).1) (fun j => (lbl (j + 1)).2.ridx.val)
      (fun j => (lbl (j + 1)).2.pre.val) (fun j => (lbl (j + 1)).2.len.val) ∧
    (∀ i < h, ∀ l < fo (lbl (i + 1)).1, ∃ k ∈ X, k.1 = (lbl (i + 1)).2.node ∧
      WalkVCL.ChildOK k (side ((lbl (i + 1)).1) l) (lbl (i + 1)).2
        (lbl (kroots + P (fun j => (lbl (j + 1)).1) i + l + 1))) := by
  obtain ⟨ts, hlen, hrvt, hlab, hfan, -⟩ := hG
  set st : ℕ → Bool × Bool := fun j => (lbl (j + 1)).1 with hst
  set W := bfsForest ts with hW
  have hne : ts ≠ [] := by intro e; rw [e] at hlen; simp at hlen; omega
  have hsplit : W = ts ++ W.flatMap NTree.children := bfsForest_eq_append_flatMap ts hne
  have hWlen : W.length = h := by have := congrArg List.length hlab; simpa using this
  have hWl : ∀ j (hj : j < W.length), W[j].label = lbl (j + 1) := by
    intro j hj
    have e := congrArg (fun l => l[j]?) hlab
    simp only [List.getElem?_map, List.getElem?_eq_getElem hj, List.getElem?_range' (by omega : j < h)] at e
    simp only [Option.map_some, Option.some.injEq] at e
    rw [e]; congr 1; omega
  have hrvtW : ∀ t ∈ W, RVT (WalkVCL.F (q := q) X 62) t := by
    intro t ht
    obtain ⟨c, hc, hin⟩ := (mem_bfsForest ts t).mp ht
    exact RVT_of_InTree (hrvt c hc) hin
  have hch : ∀ j (hj : j < W.length), (W[j].children).length = fo (st j) := by
    intro j hj
    rw [← hfan _ (List.getElem_mem hj), hWl j hj]
    rfl
  have hP : ∀ i ≤ W.length, ((W.take i).flatMap NTree.children).length = P st i := fun i hi =>
    take_flatMap_length NTree.children W (fun j => fo (st j)) hch i hi
  have hkh : kroots ≤ h := by
    have := congrArg List.length hsplit
    rw [List.length_append] at this; omega
  -- the child slots
  have hpos : ∀ i (hi : i < W.length) l (hl : l < (W[i].children).length),
      W[kroots + P st i + l]? = some ((W[i].children)[l]) := by
    intro i hi l hl
    have e1 : W[kroots + P st i + l]? = (ts ++ W.flatMap NTree.children)[kroots + P st i + l]? :=
      congrArg (fun L => L[kroots + P st i + l]?) hsplit
    rw [e1, List.getElem?_append_right (by omega), hlen,
      show kroots + P st i + l - kroots = ((W.take i).flatMap NTree.children).length + l by
        rw [hP i (by omega)]; omega,
      flatMap_getElem?_pos NTree.children W i l hi hl, List.getElem?_eq_getElem hl]
  -- the child relation (field form)
  have hrel : ∀ i (hi : i < W.length) l (hl : l < fo (st i)),
      ∃ k ∈ X, k.1 = (lbl (i + 1)).2.node ∧
        WalkVCL.ChildOK k (side (st i) l) (lbl (i + 1)).2 (lbl (kroots + P st i + l + 1)) ∧
        (lbl (i + 1)).2.len.val < 62 := by
    intro i hi l hl
    have hl' : l < (W[i].children).length := by rw [hch i hi]; exact hl
    have hm := hpos i hi l hl'
    have hmlt : kroots + P st i + l < W.length := by
      by_contra hc; rw [List.getElem?_eq_none (by omega)] at hm; simp at hm
    have hml : (W[i].children)[l].label = lbl (kroots + P st i + l + 1) := by
      rw [← hWl _ hmlt]
      rw [List.getElem?_eq_getElem hmlt, Option.some.injEq] at hm
      rw [hm]
    have hF := F_of_rvt (hrvtW _ (List.getElem_mem hi))
    rw [hWl i hi] at hF
    obtain ⟨h62, -, k, hkX, hk1, h1, h2⟩ := hF
    have hcl : W[i].childLabel l = some (lbl (kroots + P st i + l + 1)) := by
      simp only [NTree.childLabel, NTree.childOpt, List.getElem?_eq_getElem hl', Option.map_some, hml]
    refine ⟨k, hkX, hk1, ?_, h62⟩
    have hsi : (lbl (i + 1)).1 = st i := rfl
    rcases hs : st i with ⟨s1, s2⟩
    rw [hs] at hl
    rw [hsi, hs] at h1 h2
    have hfo2 : fo (s1, s2) ≤ 2 := fo_le_two
    rcases (by have := lt_of_lt_of_le hl hfo2; omega : l = 0 ∨ l = 1) with rfl | rfl
    · cases s1
      · have hs2 : s2 = true := by cases s2 <;> simp [fo] at hl ⊢
        obtain ⟨c, hc, hok⟩ := h2 hs2
        have hc' : W[i].childLabel 0 = some c := by simpa using hc
        have : c = lbl (kroots + P st i + 0 + 1) := Option.some.inj (hc'.symm.trans hcl)
        subst this; simpa [side] using hok
      · obtain ⟨c, hc, hok⟩ := h1 rfl
        have hc' : W[i].childLabel 0 = some c := by simpa using hc
        have : c = lbl (kroots + P st i + 0 + 1) := Option.some.inj (hc'.symm.trans hcl)
        subst this; simpa [side] using hok
    · have hb : s1 = true ∧ s2 = true := by cases s1 <;> cases s2 <;> simp [fo] at hl ⊢
      obtain ⟨rfl, rfl⟩ := hb
      obtain ⟨c, hc, hok⟩ := h2 rfl
      have hc' : W[i].childLabel 1 = some c := by simpa using hc
      have : c = lbl (kroots + P st i + 1 + 1) := Option.some.inj (hc'.symm.trans hcl)
      subst this; simpa [side] using hok
  have hSf : ∀ i ≤ h, Sf fo' i = P st i := by
    intro i
    induction i with
    | zero => intro _; simp [Sf, P]
    | succ i ih =>
      intro hi
      rw [Sf_succ, P_succ, ih (by omega), hfo (i + 1) (by omega) hi]
      rfl
  have hparent : ∀ m, kroots ≤ m → m < h → ∃ i < m, ∃ l < fo (st i), m = kroots + P st i + l := by
    intro m hkm hm
    have hlenF : m - kroots < (W.flatMap NTree.children).length := by
      have := congrArg List.length hsplit
      rw [List.length_append] at this; omega
    obtain ⟨i, hi, l, hl, e⟩ := flatMap_decomp NTree.children W (m - kroots) hlenF
    rw [hP i (by omega)] at e
    have hv := hvalid (i + 1) (by omega) (by omega)
    simp only [Nat.add_sub_cancel] at hv
    rw [hSf i (by omega)] at hv
    exact ⟨i, by omega, l, by rw [← hch i hi]; exact hl, by omega⟩
  have hprel : ∀ j < h, (lbl (j + 1)).2.pre.val < 2 ^ 62 := by
    intro j hj
    by_cases hjk : j < kroots
    · rw [(hroot (j + 1) (by omega) (by omega)).1, val_one' hq]; norm_num
    · obtain ⟨i, hi, l, hl, rfl⟩ := hparent j (by omega) hj
      obtain ⟨k, -, -, hok, -⟩ := hrel i (by omega) l hl
      rw [hok.2.1]
      exact haxis (i + 1) (by omega) (by omega) _
  refine ⟨⟨hkh, fun j hj => ?_, fun i hi l hl => ?_, hparent⟩, fun i hi l hl => ?_⟩
  · obtain ⟨h1, h2, -⟩ := hroot (j + 1) (by omega) (by omega)
    exact ⟨by rw [h1, val_one' hq], by rw [h2, ZMod.val_zero]⟩
  · obtain ⟨k, -, -, hok, h62⟩ := hrel i (by omega) l hl
    have hl' : l < (W[i]'(by omega)).children.length := by rw [hch i (by omega)]; exact hl
    have hm := hpos i (by omega) l hl'
    have hmlt : kroots + P st i + l < h := by
      by_contra hc; rw [List.getElem?_eq_none (by omega)] at hm; simp at hm
    refine ⟨hmlt, by rw [hok.2.2.2.1], ?_, ?_⟩
    · rw [hok.2.1, val_lin hq (hprel i hi)]
    · rw [hok.2.2.2.2, val_succ hq h62]
  · obtain ⟨k, hkX, hk1, hok, -⟩ := hrel i (by omega) l hl
    exact ⟨k, hkX, hk1, hok⟩

end Goal

/-! ## 4. The J-8 walk chip: rows, labels, keys -/

section Chip
open Nock Nock.Reified Nock.Framework Nock.Walk Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.WalkVCL
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.WalkJ8
open Nock.NockVMROM.Thm54.VclL.Handle.TU.WalkForestP1 (walkW walkJ8_forest)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenCoreWP1 (walkJ8_bfsRows)

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  (kroots : ℕ) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)
  (Q : Fin (walkChipJ8 δF kroots b hn nodes orbit chals pubs).rap.w → F[X])

open Nock.NockVMROM.Thm54.VclL.Handle.AtomWalkAW (restrictWalkK)
open Nock.NockVMROM.Thm54.VclL.Handle (shiftCol envOfTrace_restrict_trace)
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP (envOfTrace_trace)

/-- Row `j`'s base environment of the walk data of the J-8 trace (the `bitFix`ed, restricted trace). -/
abbrev rowF (j : ℕ) : Env F :=
  Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.walkEnvF b hn nodes orbit chals pubs
    (restrictWalkK δF kroots b hn nodes orbit chals pubs (bitFix δF kroots b hn nodes orbit chals pubs Q)) j

/-- Row `j`'s gathered `𝕂` environment of the walk data. -/
abbrev rowK (j : ℕ) : Env K :=
  Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.walkEnvK δF kroots b hn nodes orbit chals pubs
    (restrictWalkK δF kroots b hn nodes orbit chals pubs (bitFix δF kroots b hn nodes orbit chals pubs Q)) j

open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinK (walkChipHQK walkChipHQK_width)

/-- **The walk data's base column `c` is the `bitFix`ed trace's column `shiftCol 21 25 c`** (`c < 132`). -/
theorem rowF_shift {j : ℕ} (hj : j < n) {c : ℕ} (hc : c < 132) :
    (rowF δF kroots b hn nodes orbit chals pubs Q j).trace c =
      ((bitFix δF kroots b hn nodes orbit chals pubs Q)
        ⟨shiftCol 21 25 c, by rw [walkChipHQK_width]; simp only [shiftCol]; split_ifs <;> omega⟩).eval
        (nodes ⟨j, hj⟩) := by
  have hw : (walkChip δF kroots b hn nodes orbit chals pubs).rap.w = 132 :=
    (walkChip_fingerprint δF kroots b hn nodes orbit chals pubs).1
  have hlt : shiftCol 21 25 c < (walkChipHQK δF kroots b hn nodes orbit chals pubs).rap.w := by
    rw [walkChipHQK_width]; simp only [shiftCol]; split_ifs <;> omega
  unfold rowF Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.walkEnvF
  rw [dif_pos hj]
  have e := envOfTrace_restrict_trace (F := F) 21 25 (AtomWalkAW.walkHQK_shift δF kroots)
    (bitFix δF kroots b hn nodes orbit chals pubs Q) orbit.ω (nodes ⟨j, hj⟩) (slotVal b 21 chals) (slotVal b 21 pubs)
    (slotVal b 25 chals) (slotVal b 25 pubs) (j := c) (by rw [hw] at *; exact (by omega : c < 132) |>.trans_eq hw.symm)
  refine e.trans ?_
  exact envOfTrace_trace (bitFix δF kroots b hn nodes orbit chals pubs Q) _ _ _ _ hlt

/-- The walk data's base columns `< 14` are the J-8 trace's. -/
theorem rowF_lo {j : ℕ} (hj : j < n) {c : ℕ} (hc : c < 14) :
    (rowF δF kroots b hn nodes orbit chals pubs Q j).trace c =
      (Q ⟨c, by rw [walkChipJ8_width]; omega⟩).eval (nodes ⟨j, hj⟩) := by
  rw [rowF_shift δF kroots b hn nodes orbit chals pubs Q hj (by omega)]
  have key := bitFix_off δF kroots b hn nodes orbit chals pubs Q
    ⟨shiftCol 21 25 c, by rw [walkChipHQK_width]; simp only [shiftCol]; split_ifs <;> omega⟩
    (by simp only [shiftCol]; split_ifs <;> omega)
  rw [key]
  congr 2
  apply Fin.ext
  simp only [shiftCol]; split_ifs <;> omega

/-- The walk data's base columns `21 ≤ c < 132` are the J-8 trace's column `c + 4`. -/
theorem rowF_hi {j : ℕ} (hj : j < n) {c : ℕ} (hc : 21 ≤ c) (hc2 : c < 132) :
    (rowF δF kroots b hn nodes orbit chals pubs Q j).trace c =
      (Q ⟨c + 4, by rw [walkChipJ8_width]; omega⟩).eval (nodes ⟨j, hj⟩) := by
  rw [rowF_shift δF kroots b hn nodes orbit chals pubs Q hj hc2]
  have key := bitFix_off δF kroots b hn nodes orbit chals pubs Q
    ⟨shiftCol 21 25 c, by rw [walkChipHQK_width]; simp only [shiftCol]; split_ifs <;> omega⟩
    (by simp only [shiftCol]; split_ifs <;> omega)
  rw [key]
  congr 2
  apply Fin.ext
  simp only [shiftCol]; split_ifs <;> omega

open Nock.NockVMROM.Thm54.VclL.Handle.TU.RoundsP1 (trace_cols_eq_of_gather)

/-- The `𝕂′`-fingerprint block at role `r` (`QFP.var r`) of walk row `j` of the walk data. -/
abbrev fpAt (j r : ℕ) : Nock.ComputeTable.FP (Quad (algebraMap F K δF)) :=
  (QFP.var r : QFP F).ev δF (rowK δF kroots b hn nodes orbit chals pubs Q j)
    (rowF δF kroots b hn nodes orbit chals pubs Q j)

theorem lbl_node (j : ℕ) :
    ((walkW δF kroots b hn nodes orbit chals pubs Q).lbl (j + 1)).2.node =
      fpAt δF kroots b hn nodes orbit chals pubs Q j WChip.pR := by
  simp only [walkW, walkDataOf, lblRow, fpAt, rowK, rowF, Nat.add_sub_cancel]

theorem lbl_root (j : ℕ) :
    ((walkW δF kroots b hn nodes orbit chals pubs Q).lbl (j + 1)).2.root =
      fpAt δF kroots b hn nodes orbit chals pubs Q j WChip.rootR := by
  simp only [walkW, walkDataOf, lblRow, fpAt, rowK, rowF, Nat.add_sub_cancel]

/-- **The walk data's consumed keys**: row `i` consumes `(p, l, r, idx)`. -/
theorem X_eq :
    (walkW δF kroots b hn nodes orbit chals pubs Q).X =
      List.ofFn fun i : Fin n => (fpAt δF kroots b hn nodes orbit chals pubs Q i WChip.pR,
        fpAt δF kroots b hn nodes orbit chals pubs Q i WChip.lR,
        fpAt δF kroots b hn nodes orbit chals pubs Q i WChip.rR,
        natOf ((rowF δF kroots b hn nodes orbit chals pubs Q i).trace WChip.idx)) := rfl

/-- **Equal fingerprint blocks give equal base columns.** Two walk row environments whose `𝕂′`-fingerprint blocks
at role `r₀` agree (the `FP` of the roles `r₀ .. r₀ + 5`) agree on the base columns `21 + 3 (r₀ + t) + k`, `t < 6`,
`k < 3`. -/
theorem fp_cols (eF eF' : Env F) {r₀ : ℕ}
    (h : (QFP.var r₀ : QFP F).ev δF (gatherEnv b ((walkTemplate δF kroots).col0 3) eF) eF =
      (QFP.var r₀ : QFP F).ev δF (gatherEnv b ((walkTemplate δF kroots).col0 3) eF') eF')
    (t : ℕ) (ht : t < 6) (k : ℕ) (hk : k < 3) :
    eF.trace (21 + 3 * (r₀ + t) + k) = eF'.trace (21 + 3 * (r₀ + t) + k) := by
  rw [QFP.ev_var, QFP.ev_var] at h
  have h1 := congrArg (fun x : Nock.ComputeTable.FP (Quad (algebraMap F K δF)) => x.size) h
  have h2 := congrArg (fun x : Nock.ComputeTable.FP (Quad (algebraMap F K δF)) => x.dyck) h
  have h3 := congrArg (fun x : Nock.ComputeTable.FP (Quad (algebraMap F K δF)) => x.leaf) h
  simp only [QE.ev, ev_var] at h1 h2 h3
  have hr : ∀ r, (gatherEnv b ((walkTemplate δF kroots).col0 3) eF).trace r =
      (gatherEnv b ((walkTemplate δF kroots).col0 3) eF').trace r →
      eF.trace (21 + 3 * r + k) = eF'.trace (21 + 3 * r + k) := fun r hr => by
    have := trace_cols_eq_of_gather b ((walkTemplate δF kroots).col0 3) eF eF' r hr ⟨k, hk⟩
    simpa [ChipTemplate.col0, walkTemplate_baseCols] using this
  have e1 := (Quad.mk_eq_mk_iff _ _ _ _ _).mp h1
  have e2 := (Quad.mk_eq_mk_iff _ _ _ _ _).mp h2
  have e3 := (Quad.mk_eq_mk_iff _ _ _ _ _).mp h3
  interval_cases t
  · exact hr _ e1.1
  · exact hr _ e1.2
  · exact hr _ e2.1
  · exact hr _ e2.2
  · exact hr _ e3.1
  · exact hr _ e3.2


open Nock.NockVMROM.Thm54.VclL.Handle.AtomWalkAW (walkEnvFA)

/-- The twin row environment of the `bitFix`ed trace reads the J-8 trace on the columns `< 14` and `≥ 21`. -/
theorem walkEnvFA_col {j : ℕ} (hj : j < n) {c : ℕ} (hc : c < 14 ∨ 21 ≤ c) (hc2 : c < 166) :
    (walkEnvFA δF kroots b hn nodes orbit chals pubs (bitFix δF kroots b hn nodes orbit chals pubs Q) j).trace c =
      (Q ⟨c, by rw [walkChipJ8_width]; exact hc2⟩).eval (nodes ⟨j, hj⟩) := by
  rw [walkEnvFA_bitFix δF kroots b hn nodes orbit chals pubs Q j c hc]
  simp only [dif_pos hj]
  exact envOfTrace_trace Q _ _ _ _ (by rw [walkChipJ8_width]; exact hc2)


open scoped Classical in
/-- **The rows of an accepted J-8 walk trace are BFS rows, with the child relation** (outside the walk event). -/
theorem walkJ8_bfsRowsN
    (hsat : (walkChipJ8 δF kroots b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (walkChipJ8 δF kroots b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hF : GeneratedField.PrimeFieldElems F)
    (hk : 1 ≤ kroots) (hkn : kroots ≤ n) (hkp : kroots + n < ringChar F) (hq : 2 ^ 63 < ringChar F)
    (hout : (chals 0, chals 1) ∉ walkEvent (algebraMap F K δF) (walkW δF kroots b hn nodes orbit chals pubs Q)) :
    let W := walkW δF kroots b hn nodes orbit chals pubs Q
    (∀ i < n, ∀ l < fo (W.lbl (i + 1)).1, ∃ k ∈ W.X, k.1 = (W.lbl (i + 1)).2.node ∧
      WalkVCL.ChildOK k (side (W.lbl (i + 1)).1 l) (W.lbl (i + 1)).2
        (W.lbl (kroots + P (fun j => (W.lbl (j + 1)).1) i + l + 1))) := by
  intro W
  obtain ⟨hyp, hRG, hG⟩ := walkJ8_forest δF kroots b hn nodes orbit chals pubs Q hsat hbind hinj hadj hF hk hkn
    hkp hq hout
  have hax := walkJ8_axis_lt δF kroots b hn nodes orbit chals pubs Q hsat hbind hinj hadj hF hk hkn hkp hq hout
  exact (bfsRowsN_of_goal hq hk hG (fun i h1 h2 => (hRG i h1 h2).1) hyp.2.2.1 hyp.2.2.2.2.1
    (fun i h1 h2 bb => (hax i h1 h2 bb).2)).2

open scoped Classical in
/-- **The root rows satisfy `RootOK`** (prefix `1`, length `0`, `root = node`), outside the walk event. -/
theorem walkJ8_rootOK
    (hsat : (walkChipJ8 δF kroots b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (walkChipJ8 δF kroots b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hF : GeneratedField.PrimeFieldElems F)
    (hk : 1 ≤ kroots) (hkn : kroots ≤ n) (hkp : kroots + n < ringChar F) (hq : 2 ^ 63 < ringChar F)
    (hout : (chals 0, chals 1) ∉ walkEvent (algebraMap F K δF) (walkW δF kroots b hn nodes orbit chals pubs Q)) :
    ∀ j < kroots, RootOK ((walkW δF kroots b hn nodes orbit chals pubs Q).lbl (j + 1)).2 := by
  intro j hj
  obtain ⟨-, hRG, -⟩ := walkJ8_forest δF kroots b hn nodes orbit chals pubs Q hsat hbind hinj hadj hF hk hkn
    hkp hq hout
  exact (hRG (j + 1) (by omega) (show j + 1 ≤ kroots by omega)).1


end Chip

section Serial
variable {q : ℕ} {Kfp : Type*}

theorem serial_unique {tb : List (CellRow q Kfp)} (hs : SerialOK (tb.map (·.b0))) :
    ∀ c ∈ tb, ∀ c' ∈ tb, c.b0.idx = c'.b0.idx → c = c' := by
  unfold SerialOK at hs
  have hnd : (tb.map fun c => c.b0.idx).Nodup := by
    have h2 : tb.map (fun c => c.b0.idx) = List.range (tb.map (·.b0)).length := by
      rw [← hs, List.map_map]; rfl
    rw [h2]; exact List.nodup_range
  exact fun c hc c' hc' e => List.inj_on_of_nodup_map hnd hc hc' e

theorem serial_lt {tb : List (CellRow q Kfp)} (hs : SerialOK (tb.map (·.b0))) :
    ∀ c ∈ tb, c.b0.idx < tb.length := by
  unfold SerialOK at hs
  intro c hc
  have hm : c.b0.idx ∈ (tb.map (·.b0)).map (·.idx) := List.mem_map.mpr ⟨c.b0, List.mem_map.mpr ⟨c, hc, rfl⟩, rfl⟩
  rw [hs, List.mem_range] at hm
  simpa using hm

end Serial


section CellRel
variable {q : ℕ} {Kfp : Type*}

/-- The relation `Cell i p l r` of a cell table: some row has serial `i` and fingerprints `p l r`. -/
def CellRel (tb : List (CellRow q Kfp)) (i : ℕ) (pp l r : Nock.ComputeTable.FP Kfp) : Prop :=
  ∃ c ∈ tb, c.b0.idx = i ∧ c.p = pp ∧ c.l = l ∧ c.r = r

theorem cellRel_fun {tb : List (CellRow q Kfp)} (hs : SerialOK (tb.map (·.b0))) :
    ∀ i pp l r pp' l' r', CellRel tb i pp l r → CellRel tb i pp' l' r' → pp = pp' ∧ l = l' ∧ r = r' := by
  rintro i pp l r pp' l' r' ⟨c, hc, e1, e2, e3, e4⟩ ⟨c', hc', e1', e2', e3', e4'⟩
  have := serial_unique hs c hc c' hc' (e1.trans e1'.symm)
  subst this
  exact ⟨e2.symm.trans e2', e3.symm.trans e3', e4.symm.trans e4'⟩

theorem cellRel_inj {tb : List (CellRow q Kfp)}
    (hfp : ∀ c ∈ tb, ∀ c' ∈ tb, c.p = c'.p → c.b0.idx = c'.b0.idx) :
    ∀ i i' pp l r l' r', CellRel tb i pp l r → CellRel tb i' pp l' r' → i = i' := by
  rintro i i' pp l r l' r' ⟨c, hc, e1, e2, e3, e4⟩ ⟨c', hc', e1', e2', e3', e4'⟩
  rw [← e1, ← e1']
  exact hfp c hc c' hc' (e2.trans e2'.symm)

end CellRel


/-! ## 5. Two accepted tuples: the walk's `idx` and round-1 labels -/

section TU
open Nock Nock.Reified Nock.Framework Nock.Walk Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.WalkVCL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8 Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (PubJ8 qW qM)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (MsgJ8')
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V (AcceptsJ8V)
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8 (chalsMJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkJ8
open Nock.NockVMROM.Thm54.VclL.Handle.TU.StatementP1
open Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueP1
open Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenR0WP1
open Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenCoreWP1 (WT envQ_eq lbl_cols pF CoversW trieW AgreeW)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.WalkForestP1 (walkW)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.RoundsWalkP1 (rowIx rowIx_val)

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K) [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  {Pb : PubJ8 p}

/-- Row `i` of the J-8 tuple's walk data: the `idx` column is the trace's. -/
theorem rowF_idx (tr : TrJ8 (ZMod p)) (chals pubs : ℕ → K) {i : ℕ} (hi : i < Pb.nW) :
    (rowF δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW chals pubs (qW δ b Pb tr chals pubs) i).trace WChip.idx =
      (tr.W ⟨WChip.idx, by decide⟩).eval (Pb.nodesW ⟨i, hi⟩) :=
  rowF_lo δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW chals pubs (qW δ b Pb tr chals pubs) hi (by decide)

/-- The cell table of a J-8 tuple (restricted to the cell chip), at the cell publics `pubsC`. -/
abbrev cellTab (χ : Coins frameJ8 K) (pubsC : ℕ → K) (tr : TrJ8 (ZMod p)) :=
  cellTableOf δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) pubsC
    (CellTwinKW.restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) pubsC
      (qM δ b Pb tr (chalsMJ8 δ χ) pubsC))

/-- **The cell table of an accepted tuple is serial** (`idx` of row `i` is `i`). -/
theorem cellTab_serial {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K} {M : MsgJ8' p K δ}
    {tr : TrJ8 (ZMod p)} {r : RowsJ8} {g : ℕ} (hA : AcceptsJ8V δ b Pb Rg c χ M tr r g) :
    SerialOK ((cellTab δ b (Pb := Pb) χ M.pubsC tr).map (·.b0)) := by
  have hsatC := CellTwinKW.cellChipHQKW_restrict_cell_sat δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC _
    hA.hsatC
  have hbindC := CellTwinKW.cellChipHQKW_restrict_bind δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC _
    hA.hbindC
  exact cellTable_serial δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC _ hsatC (pF) hbindC hA.hinjC
    hA.hadjC hA.hnpC

open Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenCoreWP1 (walkJ8_bfsRows P fo side)

/-- The `𝕂′`-fingerprint block at role `r` of walk row `j` of the tuple's walk data. -/
abbrev fpW (tr : TrJ8 (ZMod p)) (chals pubs : ℕ → K) (j r : ℕ) :=
  fpAt δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW chals pubs (qW δ b Pb tr chals pubs) j r

/-- The flags, serial, prefix and length of row `j` of the tuple's walk data. -/
abbrev stW (tr : TrJ8 (ZMod p)) (chals pubs : ℕ → K) (j : ℕ) : Bool × Bool :=
  ((WT δ b Pb chals pubs tr).lbl (j + 1)).1
abbrev rdW (tr : TrJ8 (ZMod p)) (chals pubs : ℕ → K) (j : ℕ) : ℕ :=
  ((WT δ b Pb chals pubs tr).lbl (j + 1)).2.ridx.val
abbrev paW (tr : TrJ8 (ZMod p)) (chals pubs : ℕ → K) (j : ℕ) : ℕ :=
  ((WT δ b Pb chals pubs tr).lbl (j + 1)).2.pre.val
abbrev lnW (tr : TrJ8 (ZMod p)) (chals pubs : ℕ → K) (j : ℕ) : ℕ :=
  ((WT δ b Pb chals pubs tr).lbl (j + 1)).2.len.val

/-- The row-`j` `idx` of the tuple's walk data, as a natural. -/
abbrev ixW (tr : TrJ8 (ZMod p)) (chals pubs : ℕ → K) (j : ℕ) : ℕ :=
  natOf ((rowF δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW chals pubs (qW δ b Pb tr chals pubs) j).trace WChip.idx)

/-- **The abstract label data of one accepted tuple** (outside the walk event): the BFS rows; every row's key
`(p, l, r, idx)` is a row of the cell table (`hx`, from `KeysExported`); root rows have `root = p`; every child's `p`
is the side fingerprint of a key of a row with the parent's `p`, and carries the parent's root. -/
theorem walk_label_data {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K} {M : MsgJ8' p K δ}
    {tr : TrJ8 (ZMod p)} {r : RowsJ8} {g : ℕ} (hA : AcceptsJ8V δ b Pb Rg c χ M tr r g)
    (hq : 2 ^ 63 < ringChar (ZMod p))
    (hk : 1 ≤ Pb.kroots) (hkn : Pb.kroots ≤ Pb.nW) (hkp : Pb.kroots + Pb.nW < ringChar (ZMod p))
    (hout : (chalsMJ8 δ χ 0, chalsMJ8 δ χ 1) ∉ walkEvent (algebraMap (ZMod p) K δ)
      (WT δ b Pb (chalsMJ8 δ χ) M.pubsW tr))
    (hX : KeysExported (cellTab δ b (Pb := Pb) χ M.pubsC tr) (WT δ b Pb (chalsMJ8 δ χ) M.pubsW tr).X) :
    BFSRows Pb.nW Pb.kroots (stW δ b (Pb := Pb) tr (chalsMJ8 δ χ) M.pubsW)
        (rdW δ b (Pb := Pb) tr (chalsMJ8 δ χ) M.pubsW) (paW δ b (Pb := Pb) tr (chalsMJ8 δ χ) M.pubsW)
        (lnW δ b (Pb := Pb) tr (chalsMJ8 δ χ) M.pubsW) ∧
      (∀ j < Pb.nW, CellRel (cellTab δ b (Pb := Pb) χ M.pubsC tr) (ixW δ b (Pb := Pb) tr (chalsMJ8 δ χ) M.pubsW j)
        (fpW δ b (Pb := Pb) tr (chalsMJ8 δ χ) M.pubsW j WChip.pR)
        (fpW δ b (Pb := Pb) tr (chalsMJ8 δ χ) M.pubsW j WChip.lR)
        (fpW δ b (Pb := Pb) tr (chalsMJ8 δ χ) M.pubsW j WChip.rR)) ∧
      (∀ j < Pb.kroots, fpW δ b (Pb := Pb) tr (chalsMJ8 δ χ) M.pubsW j WChip.rootR =
        fpW δ b (Pb := Pb) tr (chalsMJ8 δ χ) M.pubsW j WChip.pR) ∧
      (∀ i < Pb.nW, ∀ l < fo (stW δ b (Pb := Pb) tr (chalsMJ8 δ χ) M.pubsW i), ∃ j' < Pb.nW,
        fpW δ b (Pb := Pb) tr (chalsMJ8 δ χ) M.pubsW j' WChip.pR =
          fpW δ b (Pb := Pb) tr (chalsMJ8 δ χ) M.pubsW i WChip.pR ∧
        fpW δ b (Pb := Pb) tr (chalsMJ8 δ χ) M.pubsW
            (Pb.kroots + P (stW δ b (Pb := Pb) tr (chalsMJ8 δ χ) M.pubsW) i + l) WChip.pR =
          (if side (stW δ b (Pb := Pb) tr (chalsMJ8 δ χ) M.pubsW i) l
            then fpW δ b (Pb := Pb) tr (chalsMJ8 δ χ) M.pubsW j' WChip.rR
            else fpW δ b (Pb := Pb) tr (chalsMJ8 δ χ) M.pubsW j' WChip.lR) ∧
        fpW δ b (Pb := Pb) tr (chalsMJ8 δ χ) M.pubsW
            (Pb.kroots + P (stW δ b (Pb := Pb) tr (chalsMJ8 δ χ) M.pubsW) i + l) WChip.rootR =
          fpW δ b (Pb := Pb) tr (chalsMJ8 δ χ) M.pubsW i WChip.rootR) := by
  set chals := chalsMJ8 δ χ with hchals
  refine ⟨walkJ8_bfsRows δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW chals M.pubsW _ hA.hsatW hA.hbindW hA.hinjW
    hA.hadjW pF hk hkn hkp hq hout, ?_, ?_, ?_⟩
  · intro j hj
    have hm : (fpW δ b (Pb := Pb) tr chals M.pubsW j WChip.pR, fpW δ b (Pb := Pb) tr chals M.pubsW j WChip.lR,
        fpW δ b (Pb := Pb) tr chals M.pubsW j WChip.rR, ixW δ b (Pb := Pb) tr chals M.pubsW j) ∈
        (WT δ b Pb chals M.pubsW tr).X := by
      rw [show (WT δ b Pb chals M.pubsW tr).X = _ from
        X_eq δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW chals M.pubsW (qW δ b Pb tr chals M.pubsW)]
      exact List.mem_ofFn.mpr ⟨⟨j, hj⟩, rfl⟩
    obtain ⟨c', hc', e1, e2, e3, e4⟩ := hX _ hm
    exact ⟨c', hc', e1, e2, e3, e4⟩
  · intro j hj
    have := walkJ8_rootOK δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW chals M.pubsW _ hA.hsatW hA.hbindW hA.hinjW
      hA.hadjW pF hk hkn hkp hq hout j hj
    simp only [fpW]
    rw [← lbl_node δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW chals M.pubsW (qW δ b Pb tr chals M.pubsW) j,
      ← lbl_root δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW chals M.pubsW (qW δ b Pb tr chals M.pubsW) j]
    exact this.2.2
  · intro i hi l hl
    have hrel := walkJ8_bfsRowsN δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW chals M.pubsW _ hA.hsatW hA.hbindW
      hA.hinjW hA.hadjW pF hk hkn hkp hq hout i hi l hl
    obtain ⟨k, hkX, hk1, hok⟩ := hrel
    rw [X_eq δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW chals M.pubsW (qW δ b Pb tr chals M.pubsW)] at hkX
    obtain ⟨⟨j', hj'⟩, rfl⟩ := List.mem_ofFn.mp hkX
    refine ⟨j', hj', ?_, ?_, ?_⟩ <;> simp only [fpW]
    · rw [← lbl_node δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW chals M.pubsW (qW δ b Pb tr chals M.pubsW) i]
      exact hk1
    · rw [← lbl_node δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW chals M.pubsW (qW δ b Pb tr chals M.pubsW)]
      have := hok.1
      rw [this]
      simp only [WalkVCL.tgt, WalkVCL.keyEdge, Nock.NockVMROM.Thm54.VclL.childOf]
      rfl
    · rw [← lbl_root δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW chals M.pubsW (qW δ b Pb tr chals M.pubsW),
        ← lbl_root δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW chals M.pubsW (qW δ b Pb tr chals M.pubsW)]
      exact hok.2.2.1

open Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenCoreWP1 (P_congr)

/-- **The walk's `idx` and round-1 labels agree** for two tuples accepted by `AcceptsCanon2` at one layout, claim and
coin, outside the walk event, given the trie agreement (`trie_eq`: the trie columns, and `idx` on the root rows) and
* `hX`, `hX'`: every key a walk row consumes is a row of the cell table (`KeysExported`, the IO-balance consequence
 `LinkJ8.hXW`, outside the export failure event),
* `hcell`: the two cell tables are equal (the cell round-0 columns agree, `RoundsCellP1.cell_cols_eq`),
* `hfp`: the cell fingerprints `p` determine the serial (collision-freeness of the encoder, outside its failure event).
Conclusion: the walk `idx` agrees on every row, and so do the label columns `25 .. 96`. -/
theorem walk_labels_eq {hpG : p = Nock.Atoms.p} {sz : P8PublicClaim → SizesP1} {Rg : Nock.Jet.Registry}
    {c : P8PublicClaim} {χ : Coins frameJ8 K} {r : RowsJ8} {g : ℕ} {M M' : MsgJ8' p K δ}
    {tr tr' : TrJ8 (ZMod p)} {ax ax' : AuxP1 (ZMod p)}
    (h : AcceptsCanon2 δ b hpG sz Pb Rg c χ M tr ax r g) (h' : AcceptsCanon2 δ b hpG sz Pb Rg c χ M' tr' ax' r g)
    (hk : 1 ≤ Pb.kroots) (hkn : Pb.kroots ≤ Pb.nW) (hkp : Pb.kroots + Pb.nW < p)
    (hout : (chalsMJ8 δ χ 0, chalsMJ8 δ χ 1) ∉ walkEvent (algebraMap (ZMod p) K δ)
      (WT δ b Pb (chalsMJ8 δ χ) M.pubsW tr))
    (hout' : (chalsMJ8 δ χ 0, chalsMJ8 δ χ 1) ∉ walkEvent (algebraMap (ZMod p) K δ)
      (WT δ b Pb (chalsMJ8 δ χ) M'.pubsW tr'))
    (hTr : ∀ j < Pb.nW, ∀ col ∈ trieW, (envB δ b Pb tr (chalsMJ8 δ χ) M.pubsW j).trace col =
      (envB δ b Pb tr' (chalsMJ8 δ χ) M'.pubsW j).trace col)
    (hIr : ∀ j < Pb.kroots, (envB δ b Pb tr (chalsMJ8 δ χ) M.pubsW j).trace WChip.idx =
      (envB δ b Pb tr' (chalsMJ8 δ χ) M'.pubsW j).trace WChip.idx)
    (hX : KeysExported (cellTab δ b (Pb := Pb) χ M.pubsC tr) (WT δ b Pb (chalsMJ8 δ χ) M.pubsW tr).X)
    (hX' : KeysExported (cellTab δ b (Pb := Pb) χ M'.pubsC tr') (WT δ b Pb (chalsMJ8 δ χ) M'.pubsW tr').X)
    (hcell : cellTab δ b (Pb := Pb) χ M.pubsC tr = cellTab δ b (Pb := Pb) χ M'.pubsC tr')
    (hfp : ∀ c1 ∈ cellTab δ b (Pb := Pb) χ M.pubsC tr, ∀ c2 ∈ cellTab δ b (Pb := Pb) χ M.pubsC tr,
      c1.p = c2.p → c1.b0.idx = c2.b0.idx) :
    (∀ i : Fin Pb.nW, (tr.W ⟨WChip.idx, by decide⟩).eval (Pb.nodesW i) =
      (tr'.W ⟨WChip.idx, by decide⟩).eval (Pb.nodesW i)) ∧
    (∀ j : Fin 166, 25 ≤ (j : ℕ) → (j : ℕ) < 97 →
      ∀ i, (tr.W j).eval (Pb.nodesW i) = (tr'.W j).eval (Pb.nodesW i)) := by
  have hA := h.1.1
  have hA' := h'.1.1
  have hq : 2 ^ 63 < ringChar (ZMod p) := two63_lt_ringChar hpG
  have hkp' : Pb.kroots + Pb.nW < ringChar (ZMod p) := by rw [ZMod.ringChar_zmod_n]; exact hkp
  obtain ⟨B, hx, hrt, hch⟩ := walk_label_data δ b hA hq hk hkn hkp' hout hX
  obtain ⟨B', hx', hrt', hch'⟩ := walk_label_data δ b hA' hq hk hkn hkp' hout' hX'
  set chals := chalsMJ8 δ χ with hchals
  have hflag : ∀ j < Pb.nW, stW δ b (Pb := Pb) tr' chals M'.pubsW j = stW δ b (Pb := Pb) tr chals M.pubsW j := by
    intro j hj
    have l1 := lbl_cols δ b Pb tr chals M.pubsW hj
    have l2 := lbl_cols δ b Pb tr' chals M'.pubsW hj
    show ((WT δ b Pb chals M'.pubsW tr').lbl (j + 1)).1 = ((WT δ b Pb chals M.pubsW tr).lbl (j + 1)).1
    rw [l1.1, l2.1]
    have c1 := hTr j hj WChip.cL (by simp [trieW, WChip.cL])
    have c2 := hTr j hj WChip.cR (by simp [trieW, WChip.cR])
    rw [c1, c2]
  have hs := cellTab_serial δ b hA
  have hfun := cellRel_fun hs
  have hinj := cellRel_inj hfp
  have key := labels_pair B (CellRel (cellTab δ b (Pb := Pb) χ M.pubsC tr)) hfun hinj
    (ixW δ b (Pb := Pb) tr chals M.pubsW) (ixW δ b (Pb := Pb) tr' chals M'.pubsW)
    (fun j => fpW δ b (Pb := Pb) tr chals M.pubsW j WChip.pR)
    (fun j => fpW δ b (Pb := Pb) tr chals M.pubsW j WChip.lR)
    (fun j => fpW δ b (Pb := Pb) tr chals M.pubsW j WChip.rR)
    (fun j => fpW δ b (Pb := Pb) tr chals M.pubsW j WChip.rootR)
    (fun j => fpW δ b (Pb := Pb) tr' chals M'.pubsW j WChip.pR)
    (fun j => fpW δ b (Pb := Pb) tr' chals M'.pubsW j WChip.lR)
    (fun j => fpW δ b (Pb := Pb) tr' chals M'.pubsW j WChip.rR)
    (fun j => fpW δ b (Pb := Pb) tr' chals M'.pubsW j WChip.rootR)
    (stW δ b (Pb := Pb) tr' chals M'.pubsW) hflag hx
    (fun j hj => by
      have := hx' j hj
      rw [← hcell] at this
      exact this)
    hrt hrt' hch hch'
    (fun j hj => by
      have e := hIr j hj
      simp only [ixW]
      rw [rowF_idx δ b tr chals M.pubsW (by omega), rowF_idx δ b tr' chals M'.pubsW (by omega)]
      rw [envB_eval δ b Pb tr _ _ (by decide) (by omega), envB_eval δ b Pb tr' _ _ (by decide) (by omega)] at e
      rw [e])
  have hidx : ∀ i : Fin Pb.nW, (tr.W ⟨WChip.idx, by decide⟩).eval (Pb.nodesW i) =
      (tr'.W ⟨WChip.idx, by decide⟩).eval (Pb.nodesW i) := by
    intro i
    obtain ⟨e, -⟩ := key i i.isLt
    simp only [ixW] at e
    rw [rowF_idx δ b tr chals M.pubsW i.isLt, rowF_idx δ b tr' chals M'.pubsW i.isLt] at e
    exact natOf_inj pF e
  refine ⟨hidx, ?_⟩
  intro jc h25 h97 i
  obtain ⟨-, hP, hL, hR, hRt⟩ := key i i.isLt
  have main : ∀ r0 t k : ℕ, fpW δ b (Pb := Pb) tr chals M.pubsW i r0 = fpW δ b (Pb := Pb) tr' chals M'.pubsW i r0 →
      t < 6 → k < 3 → (jc : ℕ) = 21 + 3 * (r0 + t) + k + 4 →
      (tr.W jc).eval (Pb.nodesW i) = (tr'.W jc).eval (Pb.nodesW i) := by
    intro r0 t k hr0 ht hk hjc
    have h1 := fp_cols δ Pb.kroots b
      (rowF δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW chals M.pubsW (qW δ b Pb tr chals M.pubsW) i)
      (rowF δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW chals M'.pubsW (qW δ b Pb tr' chals M'.pubsW) i)
      hr0 t ht k hk
    have hlt : 21 + 3 * (r0 + t) + k < 132 := by
      have := jc.isLt; omega
    rw [rowF_hi δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW chals M.pubsW (qW δ b Pb tr chals M.pubsW) i.isLt
        (by omega) hlt,
      rowF_hi δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW chals M'.pubsW (qW δ b Pb tr' chals M'.pubsW) i.isLt
        (by omega) hlt] at h1
    have hjc' : jc = ⟨21 + 3 * (r0 + t) + k + 4, by have := jc.isLt; omega⟩ := Fin.ext hjc
    rw [hjc']
    exact h1
  have hq4 : ((jc : ℕ) - 25) / 3 / 6 = 0 ∨ ((jc : ℕ) - 25) / 3 / 6 = 1 ∨ ((jc : ℕ) - 25) / 3 / 6 = 2 ∨ ((jc : ℕ) - 25) / 3 / 6 = 3 := by
    have := jc.isLt; omega
  rcases hq4 with e | e | e | e
  · exact main 0 (((jc : ℕ) - 25) / 3 % 6) (((jc : ℕ) - 25) % 3) hP (by omega) (by omega) (by omega)
  · exact main 6 (((jc : ℕ) - 25) / 3 % 6) (((jc : ℕ) - 25) % 3) hL (by omega) (by omega) (by omega)
  · exact main 12 (((jc : ℕ) - 25) / 3 % 6) (((jc : ℕ) - 25) % 3) hR (by omega) (by omega) (by omega)
  · exact main 18 (((jc : ℕ) - 25) / 3 % 6) (((jc : ℕ) - 25) % 3) hRt (by omega) (by omega) (by omega)


open Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenCoreWP1 (root_cols)

/-- **The walk rows' `idx` are cell serials**: every key a walk row consumes is a cell row, whose serial is below the
cell table's height. -/
theorem ix_lt_of_exported {χ : Coins frameJ8 K} {M : MsgJ8' p K δ} {tr : TrJ8 (ZMod p)} {Rg : Nock.Jet.Registry}
    {c : P8PublicClaim} {r : RowsJ8} {g : ℕ} (hA : AcceptsJ8V δ b Pb Rg c χ M tr r g)
    (hX : KeysExported (cellTab δ b (Pb := Pb) χ M.pubsC tr) (WT δ b Pb (chalsMJ8 δ χ) M.pubsW tr).X) :
    ∀ j < Pb.nW, ixW δ b (Pb := Pb) tr (chalsMJ8 δ χ) M.pubsW j < Pb.nC := by
  intro j hj
  have hm : (fpW δ b (Pb := Pb) tr (chalsMJ8 δ χ) M.pubsW j WChip.pR,
      fpW δ b (Pb := Pb) tr (chalsMJ8 δ χ) M.pubsW j WChip.lR,
      fpW δ b (Pb := Pb) tr (chalsMJ8 δ χ) M.pubsW j WChip.rR, ixW δ b (Pb := Pb) tr (chalsMJ8 δ χ) M.pubsW j) ∈
      (WT δ b Pb (chalsMJ8 δ χ) M.pubsW tr).X := by
    rw [show (WT δ b Pb (chalsMJ8 δ χ) M.pubsW tr).X = _ from
      X_eq δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW)]
    exact List.mem_ofFn.mpr ⟨⟨j, hj⟩, rfl⟩
  obtain ⟨c', hc', e1, -⟩ := hX _ hm
  have := serial_lt (cellTab_serial δ b hA) c' hc'
  rw [e1] at this
  simpa [cellTab, cellTableOf] using this

/-- **Root-order side condition `hrb`**: the root serials are below `2^32` (they are cell serials, and the cell table has
at most `2^32` rows). -/
theorem roots_lt {hpG : p = Nock.Atoms.p} {sz : P8PublicClaim → SizesP1} {Rg : Nock.Jet.Registry}
    {c : P8PublicClaim} {χ : Coins frameJ8 K} {r : RowsJ8} {g : ℕ} {M : MsgJ8' p K δ}
    {tr : TrJ8 (ZMod p)} {ax : AuxP1 (ZMod p)}
    (h : AcceptsCanon2 δ b hpG sz Pb Rg c χ M tr ax r g) (hkn : Pb.kroots ≤ Pb.nW)
    (hX : KeysExported (cellTab δ b (Pb := Pb) χ M.pubsC tr) (WT δ b Pb (chalsMJ8 δ χ) M.pubsW tr).X) :
    ∀ j < Pb.kroots, natOf ((envB δ b Pb tr (chalsMJ8 δ χ) M.pubsW j).trace WChip.ridx) < 2 ^ 32 := by
  intro j hj
  have hA := h.1.1
  have hnC : Pb.nC ≤ 2 ^ 32 := by
    have h1 := (sz c).hfit
    have h2 : Pb.nC = (sz c).nC := by rw [h.1.2.hPb]; rfl
    rw [h2]
    exact le_trans (le_max_of_le_right (le_max_left _ _)) h1
  obtain ⟨e1, -⟩ := root_cols δ b hA h.1.2.hW hj (by omega)
  have hl := ix_lt_of_exported δ b hA hX j (by omega)
  have e2 : ixW δ b (Pb := Pb) tr (chalsMJ8 δ χ) M.pubsW j =
      natOf ((envB δ b Pb tr (chalsMJ8 δ χ) M.pubsW j).trace WChip.idx) := by
    simp only [ixW]
    rw [rowF_idx δ b tr _ _ (by omega), envB_eval δ b Pb tr _ _ (by decide) (by omega)]
  rw [e1, ← e2]
  omega

/-- **The read closure is covered** by an accepted tuple whose walk contains every read's parent node: each read
`s = (root serial, axis)` of `R` has a walk row with `(ridx, pre) = (s.1, s.2 / 2)` (`hprov`, from the compute side:
the read's path record is consumed against the walk's path provider). Then every proper prefix of every read path
is a walk row (`WalkCloseP1.covers_closure`, the walk rows being a BFS forest). -/
theorem coversW_of_reads {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K} {M : MsgJ8' p K δ}
    {tr : TrJ8 (ZMod p)} {r : RowsJ8} {g : ℕ} (hA : AcceptsJ8V δ b Pb Rg c χ M tr r g)
    (hq : 2 ^ 63 < ringChar (ZMod p))
    (hk : 1 ≤ Pb.kroots) (hkn : Pb.kroots ≤ Pb.nW) (hkp : Pb.kroots + Pb.nW < ringChar (ZMod p))
    (hout : (chalsMJ8 δ χ 0, chalsMJ8 δ χ 1) ∉ walkEvent (algebraMap (ZMod p) K δ)
      (WT δ b Pb (chalsMJ8 δ χ) M.pubsW tr))
    (R : Finset (ℕ × ℕ))
    (hprov : ∀ s ∈ R, ∃ j < Pb.nW, natOf ((envB δ b Pb tr (chalsMJ8 δ χ) M.pubsW j).trace WChip.ridx) = s.1 ∧
      natOf ((envB δ b Pb tr (chalsMJ8 δ χ) M.pubsW j).trace WChip.pre) = s.2 / 2) :
    CoversW δ b (Pb := Pb) (χ := χ) (readClosure R) M tr := by
  have B := walkJ8_bfsRows δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW _ hA.hsatW hA.hbindW
    hA.hinjW hA.hadjW pF hk hkn hkp hq hout
  have L := fun j (hj : j < Pb.nW) => lbl_cols δ b Pb tr (chalsMJ8 δ χ) M.pubsW hj
  have := covers_closure B R (fun s hs => by
    obtain ⟨j, hj, e1, e2⟩ := hprov s hs
    exact ⟨j, hj, by rw [(L j hj).2.1]; exact e1, by rw [(L j hj).2.2.1]; exact e2⟩)
  intro s hs
  obtain ⟨j, hj, e1, e2⟩ := this s hs
  exact ⟨j, hj, by rw [← (L j hj).2.1]; exact e1, by rw [← (L j hj).2.2.1]; exact e2⟩

section Keys
variable {F K : Type} [Field F] [Field K] [Algebra F K]

theorem keyVec5_recLH_congr (eF eF' : Env F) (h1 : eF.trace WChip.ridx = eF'.trace WChip.ridx)
    (h2 : eF.trace WChip.pre = eF'.trace WChip.pre) (h3 : eF.trace WalkHC.kL = eF'.trace WalkHC.kL)
    (h4 : eF.trace WalkHC.vL = eF'.trace WalkHC.vL) :
    ServeH.keyVec5 (K := K) WalkHC.recLH eF = ServeH.keyVec5 (K := K) WalkHC.recLH eF' := by
  funext c
  fin_cases c <;> simp [ServeH.keyVec5, WalkHC.recLH, cv, CoeffExpr.eval, h1, h2, h3, h4]

theorem keyVec5_recRH_congr (eF eF' : Env F) (h1 : eF.trace WChip.ridx = eF'.trace WChip.ridx)
    (h2 : eF.trace WChip.pre = eF'.trace WChip.pre) (h3 : eF.trace WalkHC.kR = eF'.trace WalkHC.kR)
    (h4 : eF.trace WalkHC.vR = eF'.trace WalkHC.vR) :
    ServeH.keyVec5 (K := K) WalkHC.recRH eF = ServeH.keyVec5 (K := K) WalkHC.recRH eF' := by
  funext c
  fin_cases c <;> simp [ServeH.keyVec5, WalkHC.recRH, cv, CoeffExpr.eval, h1, h2, h3, h4]

end Keys

open Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenCoreWP1 (AgreeW)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkKJ8 (childHOfK)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomWalkAW (walkEnvFA)

/-- **`kL vL kR vR` agree**: both tuples' walk rows carry, for their `idx`, the handles of the cell row of that serial
(`hH`, `hH'`: the handle-export premise `LinkJ8.hHXW`, outside the handle-export failure event); the cell tables
being equal and serial, the walk rows with equal `idx` carry equal handles. -/
theorem walk_kv_eq {χ : Coins frameJ8 K} {M M' : MsgJ8' p K δ} {tr tr' : TrJ8 (ZMod p)} {Rg : Nock.Jet.Registry}
    {c : P8PublicClaim} {r : RowsJ8} {g : ℕ} (hA : AcceptsJ8V δ b Pb Rg c χ M tr r g)
    (hidx : ∀ i : Fin Pb.nW, (tr.W ⟨WChip.idx, by decide⟩).eval (Pb.nodesW i) =
      (tr'.W ⟨WChip.idx, by decide⟩).eval (Pb.nodesW i))
    (hH : ∀ j < Pb.nW, ∃ c' ∈ cellTab δ b (Pb := Pb) χ M.pubsC tr,
      (natOf ((walkEnvFA δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
          (bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
            (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW)) j).trace WChip.idx),
        childHOfK (walkEnvFA δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
          (bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
            (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW)) j) false,
        childHOfK (walkEnvFA δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
          (bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
            (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW)) j) true) = exportRecK c'.b0)
    (hH' : ∀ j < Pb.nW, ∃ c' ∈ cellTab δ b (Pb := Pb) χ M'.pubsC tr',
      (natOf ((walkEnvFA δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M'.pubsW
          (bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M'.pubsW
            (qW δ b Pb tr' (chalsMJ8 δ χ) M'.pubsW)) j).trace WChip.idx),
        childHOfK (walkEnvFA δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M'.pubsW
          (bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M'.pubsW
            (qW δ b Pb tr' (chalsMJ8 δ χ) M'.pubsW)) j) false,
        childHOfK (walkEnvFA δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M'.pubsW
          (bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M'.pubsW
            (qW δ b Pb tr' (chalsMJ8 δ χ) M'.pubsW)) j) true) = exportRecK c'.b0)
    (hcell : cellTab δ b (Pb := Pb) χ M.pubsC tr = cellTab δ b (Pb := Pb) χ M'.pubsC tr') :
    AgreeW Pb tr tr' [21, 22, 23, 24] := by
  have hs := cellTab_serial δ b hA
  intro jc hjc i
  obtain ⟨c1, hc1, e1⟩ := hH i i.isLt
  obtain ⟨c2, hc2, e2⟩ := hH' i i.isLt
  rw [← hcell] at hc2
  simp only [exportRecK, Prod.mk.injEq] at e1 e2
  have hid : c1.b0.idx = c2.b0.idx := by
    rw [← e1.1, ← e2.1, walkEnvFA_col δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW _ _ _ i.isLt (Or.inl (by decide))
      (by decide), walkEnvFA_col δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW _ _ _ i.isLt (Or.inl (by decide))
      (by decide)]
    exact congrArg natOf (hidx i)
  have hcc := serial_unique hs c1 hc1 c2 hc2 hid
  subst hcc
  have eL := e1.2.1.trans e2.2.1.symm
  have eR := e1.2.2.trans e2.2.2.symm
  simp only [childHOfK, Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq] at eL eR
  have col : ∀ (cc : ℕ) (hcc : cc < 166), (cc = 21 ∨ cc = 22 ∨ cc = 23 ∨ cc = 24) →
      natOf ((walkEnvFA δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
          (bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
            (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW)) i).trace cc) =
        natOf ((walkEnvFA δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M'.pubsW
          (bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M'.pubsW
            (qW δ b Pb tr' (chalsMJ8 δ χ) M'.pubsW)) i).trace cc) →
      (tr.W ⟨cc, hcc⟩).eval (Pb.nodesW i) = (tr'.W ⟨cc, hcc⟩).eval (Pb.nodesW i) := by
    intro cc hcc hc hn
    rw [walkEnvFA_col δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW _ _ _ i.isLt (Or.inr (by omega)) hcc,
      walkEnvFA_col δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW _ _ _ i.isLt (Or.inr (by omega)) hcc] at hn
    exact natOf_inj pF hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hjc
  have hj166 := jc.isLt
  have hjce : jc = ⟨(jc : ℕ), hj166⟩ := rfl
  rw [hjce]
  refine col jc hj166 (by omega) ?_
  rcases hjc with e | e | e | e
  · rw [e]; exact eL.1
  · rw [e]; exact eL.2
  · rw [e]; exact eR.1
  · rw [e]; exact eR.2

open Nock.NockVMROM.Thm54.VclL.Handle.TU.CountsP1 (mL_eq_count mR_eq_count)
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (pw)

/-- **`mL mR` agree**: each is the exact number of consumers of the row's path record (`CountsP1.mL_eq_count`), the
record's key `(ridx, 2 pre (+ 1), k, v)` agrees (trie and `kL vL kR vR` agree), and the two consumer multisets
`reqs`, `reqs'` agree (`hreq`: the compute side's path requests, a run-side fact). The balances `hbal`, `hbal'` with
distinct provider keys `hd`, `hd'` are the IO-balance consequences outside the path failure event. -/
theorem walk_mLR_eq {χ : Coins frameJ8 K} {M M' : MsgJ8' p K δ} {tr tr' : TrJ8 (ZMod p)}
    (reqs reqs' : List (Fin 5 → K)) (provs provs' : List ((Fin 5 → K) × K))
    (hbal : ∀ r, (reqs.count r : K) = pw provs r) (hd : (provs.map Prod.fst).Nodup)
    (hsub : ∀ q ∈ ServeH.walkPProvs b Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
      (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW), q ∈ provs)
    (hbal' : ∀ r, (reqs'.count r : K) = pw provs' r) (hd' : (provs'.map Prod.fst).Nodup)
    (hsub' : ∀ q ∈ ServeH.walkPProvs b Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M'.pubsW
      (qW δ b Pb tr' (chalsMJ8 δ χ) M'.pubsW), q ∈ provs')
    (hreq : ∀ r, reqs.count r = reqs'.count r)
    (hTr : AgreeW Pb tr tr' trieW) (hKV : AgreeW Pb tr tr' [21, 22, 23, 24]) :
    AgreeW Pb tr tr' [WChip.mL, WChip.mR] := by
  intro jc hjc i
  have ev : ∀ (T : TrJ8 (ZMod p)) (pb : ℕ → K) (c : ℕ) (hc : c < 166),
      (TeleH.wEF b Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) pb (qW δ b Pb T (chalsMJ8 δ χ) pb) i).trace c =
        (T.W ⟨c, hc⟩).eval (Pb.nodesW i) := fun T pb c hc =>
    envOfTrace_trace (qW δ b Pb T (chalsMJ8 δ χ) pb) _ _ _ _ (by rw [walkChipJ8_width]; exact hc)
  have a4 := hTr ⟨4, by omega⟩ (by simp [trieW]) i
  have a5 := hTr ⟨5, by omega⟩ (by simp [trieW]) i
  have a21 := hKV ⟨21, by omega⟩ (by simp) i
  have a22 := hKV ⟨22, by omega⟩ (by simp) i
  have a23 := hKV ⟨23, by omega⟩ (by simp) i
  have a24 := hKV ⟨24, by omega⟩ (by simp) i
  rw [← ev tr M.pubsW 4 (by omega), ← ev tr' M'.pubsW 4 (by omega)] at a4
  rw [← ev tr M.pubsW 5 (by omega), ← ev tr' M'.pubsW 5 (by omega)] at a5
  rw [← ev tr M.pubsW 21 (by omega), ← ev tr' M'.pubsW 21 (by omega)] at a21
  rw [← ev tr M.pubsW 22 (by omega), ← ev tr' M'.pubsW 22 (by omega)] at a22
  rw [← ev tr M.pubsW 23 (by omega), ← ev tr' M'.pubsW 23 (by omega)] at a23
  rw [← ev tr M.pubsW 24 (by omega), ← ev tr' M'.pubsW 24 (by omega)] at a24
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hjc
  rcases hjc with e | e
  · have hjc' : jc = ⟨WChip.mL, by decide⟩ := Fin.ext e
    rw [hjc', ← ev tr M.pubsW _ (by decide), ← ev tr' M'.pubsW _ (by decide)]
    rw [mL_eq_count b Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW _ reqs provs hbal hd hsub i,
      mL_eq_count b Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M'.pubsW _ reqs' provs' hbal' hd' hsub' i]
    rw [keyVec5_recLH_congr _ (TeleH.wEF b Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M'.pubsW
      (qW δ b Pb tr' (chalsMJ8 δ χ) M'.pubsW) i) a5 a4 a21 a22, hreq]
  · have hjc' : jc = ⟨WChip.mR, by decide⟩ := Fin.ext e
    rw [hjc', ← ev tr M.pubsW _ (by decide), ← ev tr' M'.pubsW _ (by decide)]
    rw [mR_eq_count b Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW _ reqs provs hbal hd hsub i,
      mR_eq_count b Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M'.pubsW _ reqs' provs' hbal' hd' hsub' i]
    rw [keyVec5_recRH_congr _ (TeleH.wEF b Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M'.pubsW
      (qW δ b Pb tr' (chalsMJ8 δ χ) M'.pubsW) i) a5 a4 a23 a24, hreq]

open Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenCoreWP1 (r0W_auxW_r1W)

theorem agreeW_to_envB {χ : Coins frameJ8 K} {M M' : MsgJ8' p K δ} {tr tr' : TrJ8 (ZMod p)}
    (hTr : AgreeW Pb tr tr' trieW) :
    ∀ j < Pb.nW, ∀ col ∈ trieW, (envB δ b Pb tr (chalsMJ8 δ χ) M.pubsW j).trace col =
      (envB δ b Pb tr' (chalsMJ8 δ χ) M'.pubsW j).trace col := by
  intro j hj col hcol
  have hc : col < 166 := by
    simp only [trieW, List.mem_cons, List.not_mem_nil, or_false] at hcol; omega
  rw [envB_eval δ b Pb tr _ _ hc hj, envB_eval δ b Pb tr' _ _ hc hj]
  exact hTr ⟨col, hc⟩ hcol ⟨j, hj⟩

theorem rootIdx_of_trie {hpG : p = Nock.Atoms.p} {sz : P8PublicClaim → SizesP1} {Rg : Nock.Jet.Registry}
    {c : P8PublicClaim} {χ : Coins frameJ8 K} {r : RowsJ8} {g : ℕ} {M M' : MsgJ8' p K δ}
    {tr tr' : TrJ8 (ZMod p)} {ax ax' : AuxP1 (ZMod p)}
    (h : AcceptsCanon2 δ b hpG sz Pb Rg c χ M tr ax r g) (h' : AcceptsCanon2 δ b hpG sz Pb Rg c χ M' tr' ax' r g)
    (hkn : Pb.kroots ≤ Pb.nW) (hTr : AgreeW Pb tr tr' trieW) :
    ∀ j < Pb.kroots, (envB δ b Pb tr (chalsMJ8 δ χ) M.pubsW j).trace WChip.idx =
      (envB δ b Pb tr' (chalsMJ8 δ χ) M'.pubsW j).trace WChip.idx := by
  intro j hj
  rw [← (root_cols δ b h.1.1 h.1.2.hW hj (by omega)).1, ← (root_cols δ b h'.1.1 h'.1.2.hW hj (by omega)).1]
  exact agreeW_to_envB δ b hTr j (by omega) WChip.ridx (by simp [trieW, WChip.ridx])

/-- **`walk_closed`: the walk's round-0, aux and round-1 columns agree**, for two tuples accepted by `AcceptsCanon2`
at one layout, claim and coin, outside the walk event at both traces. This is `OpenCoreWP1.r0W_auxW_r1W` with its
walk hypotheses `hrb`, `hidxN`, `hmLR`, `hkv`, `hr1` discharged and `hreadsEq` reduced to the read provenance.

What is derived: `hrb` (`roots_lt`), the trie (`trie_eq`), the non-root `idx` and the labels `25 .. 96`
(`walk_labels_eq`), `kL vL kR vR` (`walk_kv_eq`), `mL mR` (`walk_mLR_eq`), the cover (`coversW_of_reads`).

What stays a hypothesis, each a premise already carried by the J-8 link (`LinkJ8'`) or a run-side fact:
* `hX`, `hX'`: `KeysExported` (`hXW`, outside the export IO failure event);
* `hH`, `hH'`: the handle-export record (`hHXW`, outside the handle-export failure event);
* `hcell`: the two cell tables are equal (cell round-0 columns agree; `RoundsCellP1.cell_cols_eq` with `r0M`);
* `hfp`: the cell fingerprint `p` determines the serial (encoder collision-freeness outside its failure event);
* the path-record balance of both tuples (`hbal hd hsub`, outside the path failure event) and `hreq`: the compute
 side's path-request multisets agree (run-side: both are the requests of the one run, `r0C`);
* the reads: `R` (the claim's path reads `(root serial, axis)`), `hsz` (the canonical `nW` is the size of the read
 closure) and `hprov`, `hprov'` (the parent node of every read is a walk row of each tuple: the read's path record is
 consumed against the walk's path provider), or the pin E10 (`noPath`: `idx = 0` on row `0`, `nW = 1`). -/
theorem walk_closed {hpG : p = Nock.Atoms.p} {sz : P8PublicClaim → SizesP1} {Rg : Nock.Jet.Registry}
    {c : P8PublicClaim} {χ : Coins frameJ8 K} {r : RowsJ8} {g : ℕ} {M M' : MsgJ8' p K δ}
    {tr tr' : TrJ8 (ZMod p)} {ax ax' : AuxP1 (ZMod p)}
    (h : AcceptsCanon2 δ b hpG sz Pb Rg c χ M tr ax r g) (h' : AcceptsCanon2 δ b hpG sz Pb Rg c χ M' tr' ax' r g)
    (hk : 1 ≤ Pb.kroots) (hkn : Pb.kroots ≤ Pb.nW) (hkp : Pb.kroots + Pb.nW < p)
    (hout : (chalsMJ8 δ χ 0, chalsMJ8 δ χ 1) ∉ walkEvent (algebraMap (ZMod p) K δ)
      (WT δ b Pb (chalsMJ8 δ χ) M.pubsW tr))
    (hout' : (chalsMJ8 δ χ 0, chalsMJ8 δ χ 1) ∉ walkEvent (algebraMap (ZMod p) K δ)
      (WT δ b Pb (chalsMJ8 δ χ) M'.pubsW tr'))
    -- the walk's export keys are cell rows, the cell tables agree, fingerprints are collision-free
    (hX : KeysExported (cellTab δ b (Pb := Pb) χ M.pubsC tr) (WT δ b Pb (chalsMJ8 δ χ) M.pubsW tr).X)
    (hX' : KeysExported (cellTab δ b (Pb := Pb) χ M'.pubsC tr') (WT δ b Pb (chalsMJ8 δ χ) M'.pubsW tr').X)
    (hcell : cellTab δ b (Pb := Pb) χ M.pubsC tr = cellTab δ b (Pb := Pb) χ M'.pubsC tr')
    (hfp : ∀ c1 ∈ cellTab δ b (Pb := Pb) χ M.pubsC tr, ∀ c2 ∈ cellTab δ b (Pb := Pb) χ M.pubsC tr,
      c1.p = c2.p → c1.b0.idx = c2.b0.idx)
    -- the handle-export records
    (hH : ∀ j < Pb.nW, ∃ c' ∈ cellTab δ b (Pb := Pb) χ M.pubsC tr,
      (natOf ((walkEnvFA δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
          (bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
            (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW)) j).trace WChip.idx),
        childHOfK (walkEnvFA δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
          (bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
            (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW)) j) false,
        childHOfK (walkEnvFA δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
          (bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
            (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW)) j) true) = exportRecK c'.b0)
    (hH' : ∀ j < Pb.nW, ∃ c' ∈ cellTab δ b (Pb := Pb) χ M'.pubsC tr',
      (natOf ((walkEnvFA δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M'.pubsW
          (bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M'.pubsW
            (qW δ b Pb tr' (chalsMJ8 δ χ) M'.pubsW)) j).trace WChip.idx),
        childHOfK (walkEnvFA δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M'.pubsW
          (bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M'.pubsW
            (qW δ b Pb tr' (chalsMJ8 δ χ) M'.pubsW)) j) false,
        childHOfK (walkEnvFA δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M'.pubsW
          (bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M'.pubsW
            (qW δ b Pb tr' (chalsMJ8 δ χ) M'.pubsW)) j) true) = exportRecK c'.b0)
    -- the path-record balance
    (reqs reqs' : List (Fin 5 → K)) (provs provs' : List ((Fin 5 → K) × K))
    (hbal : ∀ r, (reqs.count r : K) = pw provs r) (hd : (provs.map Prod.fst).Nodup)
    (hsub : ∀ q ∈ ServeH.walkPProvs b Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
      (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW), q ∈ provs)
    (hbal' : ∀ r, (reqs'.count r : K) = pw provs' r) (hd' : (provs'.map Prod.fst).Nodup)
    (hsub' : ∀ q ∈ ServeH.walkPProvs b Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M'.pubsW
      (qW δ b Pb tr' (chalsMJ8 δ χ) M'.pubsW), q ∈ provs')
    (hreq : ∀ r, reqs.count r = reqs'.count r)
    -- the reads, or the extra pin (E10)
    (noPath : Prop)
    (hE10 : noPath → (tr.W ⟨WChip.idx, by decide⟩).eval (Pb.nodesW ⟨0, by omega⟩) = 0)
    (hE10' : noPath → (tr'.W ⟨WChip.idx, by decide⟩).eval (Pb.nodesW ⟨0, by omega⟩) = 0)
    (hnW1 : noPath → Pb.nW = 1)
    (R : Finset (ℕ × ℕ)) (hsz : ¬ noPath → (readClosure R).card = Pb.nW)
    (hprov : ¬ noPath → ∀ s ∈ R, ∃ j < Pb.nW,
      natOf ((envB δ b Pb tr (chalsMJ8 δ χ) M.pubsW j).trace WChip.ridx) = s.1 ∧
        natOf ((envB δ b Pb tr (chalsMJ8 δ χ) M.pubsW j).trace WChip.pre) = s.2 / 2)
    (hprov' : ¬ noPath → ∀ s ∈ R, ∃ j < Pb.nW,
      natOf ((envB δ b Pb tr' (chalsMJ8 δ χ) M'.pubsW j).trace WChip.ridx) = s.1 ∧
        natOf ((envB δ b Pb tr' (chalsMJ8 δ χ) M'.pubsW j).trace WChip.pre) = s.2 / 2) :
    (∀ j : Fin 166, (j : ℕ) < 25 → ∀ i, (tr.W j).eval (Pb.nodesW i) = (tr'.W j).eval (Pb.nodesW i)) ∧
      (∀ j i, (ax.W j).eval (Pb.nodesW i) = (ax'.W j).eval (Pb.nodesW i)) ∧
      (∀ j : Fin 166, 25 ≤ (j : ℕ) → (j : ℕ) < 97 →
        ∀ i, (tr.W j).eval (Pb.nodesW i) = (tr'.W j).eval (Pb.nodesW i)) := by
  have hq : 2 ^ 63 < ringChar (ZMod p) := two63_lt_ringChar hpG
  have hkp' : Pb.kroots + Pb.nW < ringChar (ZMod p) := by rw [ZMod.ringChar_zmod_n]; exact hkp
  -- the labels, from the trie
  have lab : AgreeW Pb tr tr' trieW →
      (∀ i : Fin Pb.nW, (tr.W ⟨WChip.idx, by decide⟩).eval (Pb.nodesW i) =
        (tr'.W ⟨WChip.idx, by decide⟩).eval (Pb.nodesW i)) ∧
      (∀ j : Fin 166, 25 ≤ (j : ℕ) → (j : ℕ) < 97 →
        ∀ i, (tr.W j).eval (Pb.nodesW i) = (tr'.W j).eval (Pb.nodesW i)) := fun hTr =>
    walk_labels_eq δ b h h' hk hkn hkp hout hout' (agreeW_to_envB δ b hTr)
      (rootIdx_of_trie δ b h h' hkn hTr) hX hX' hcell hfp
  refine r0W_auxW_r1W δ b h h' hk hkn hkp hout hout' (roots_lt δ b h hkn hX) (roots_lt δ b h' hkn hX')
    noPath hE10 hE10' hnW1 ?_ (fun hTr i _ => (lab hTr).1 i) ?_ ?_ (fun hTr _ => (lab hTr).2)
  · intro hnp
    exact ⟨readClosure R, hsz hnp,
      coversW_of_reads δ b h.1.1 hq hk hkn hkp' hout R (hprov hnp),
      coversW_of_reads δ b h'.1.1 hq hk hkn hkp' hout' R (hprov' hnp)⟩
  · intro hTr
    exact walk_mLR_eq δ b reqs reqs' provs provs' hbal hd hsub hbal' hd' hsub' hreq hTr
      (walk_kv_eq δ b h.1.1 (lab hTr).1 hH hH' hcell)
  · intro hTr
    exact walk_kv_eq δ b h.1.1 (lab hTr).1 hH hH' hcell

end TU

end

end Nock.NockVMROM.Thm54.VclL.Handle.TU.WalkCloseP1
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.WalkCloseP1.anc
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.WalkCloseP1.covers_closure
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.WalkCloseP1.labels_det
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.WalkCloseP1.labels_det2
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.WalkCloseP1.reads_cover
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.WalkCloseP1.bfsRowsN_of_goal
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.WalkCloseP1.walkJ8_bfsRowsN
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.WalkCloseP1.walkJ8_rootOK
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.WalkCloseP1.walk_labels_eq
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.WalkCloseP1.roots_lt
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.WalkCloseP1.coversW_of_reads
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.WalkCloseP1.walk_kv_eq
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.WalkCloseP1.walk_mLR_eq
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.WalkCloseP1.walk_closed
