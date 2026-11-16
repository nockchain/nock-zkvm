/-
 Nock/NockVMROM/Thm54/VclL/Handle/TU/CanonGenP1.lean

 **The canonical generator and the converse key-order bridge of the cell sort.**

 * §1 `ord8Canon`: the cell order `sortKey` (the noun order `nlt`) and the read order `ordRS` (a stable merge sort
 by root serial, read through the handle map); `j8DataCanon := j8DataGen … ord8Canon`; `j8DataCanon_ok`;
 `complJ8_closed_canon` (the instance of `complJ8_closed'`).
 * §2 the converse key-order bridge, over any cell list `cs` that is `Pairwise nlt`, child-closed, made of cells
 with small atom children: the honest key of a cell (`key8`: rank limbs, then per side the kind and the two
 32-bit limbs of the child value, the child's list position for a cell child) is strictly `LexLt`-increasing
 along the list (`key8_lexLt_of_nlt`, the reverse of `TableM.nouns_sorted`'s case split).
 * §3 `HRow`: the row-local honest values a cell table row carries; `honestM_of_rows`: rows carrying them form an
 `HonestM` table.
 * §4 the honest cell trace columns (`HonestKW.colW` over `cellCol (valsBE …)`) carry `HRow` (`hrow_colW`).
 * §5 at the canonical layout: the aux interpolants `auxMOf`; `canonM_of_trace` (the honest cell trace at the
 canonical nodes satisfies `canonM` with aux `auxH`); `canonM_canon` at `j8DataCanon`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.TU.J8GenClosed
import Nock.NockVMROM.Thm54.VclL.Handle.TU.CellOrderP1

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonGenP1

open Nock Nock.Reified Nock.Framework Polynomial Module
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.TU.StatementP1
open Nock.NockVMROM.Thm54.VclL.Handle.TU.CellOrderP1
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8)

noncomputable section

/-! ## 1. The canonical generator -/

section Gen
open Nock.NockVMROM.Thm54.VclL.Handle.TU.J8Gen
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data)
open Nock.Edit.GenX

/-- The root serial of a read `(root, axis)`, through a handle map: the second component of the root's handle. -/
def serialOf (H : Noun → ℕ × ℕ) (x : Noun × ℕ) : ℕ := (H x.1).2

/-- **The read order**: a stable merge sort by root serial. -/
def ordRS (H : Noun → ℕ × ℕ) (l : List (Noun × ℕ)) : List (Noun × ℕ) :=
  l.mergeSort fun a b => decide (serialOf H a ≤ serialOf H b)

/-- **The canonical list orders**: cells by the noun order (`sortKey`), reads stably by root serial. -/
def ord8Canon : Ord8 where
  ordC := sortKey
  ordR := ordRS
  permC := sortKey_perm
  permR := fun H l => List.mergeSort_perm l _

/-- **The canonical generator**: `j8DataGen` at the canonical list orders. -/
abbrev j8DataCanon (p : ℕ) [Fact p.Prime] (Rg : Nock.Jet.VerifiedRegistry) (Rt : ℕ → Nock.Jet.Autogen.Tpl)
    {fuel : ℕ} {s f r : Noun} {t : Nock.Walk.NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) :
    J8Data p Rg fuel s f r :=
  j8DataGen p Rg Rt hgen ord8Canon

/-- **The canonical generator is admissible** (`J8DataOK`: its two orders are permutations). -/
def j8DataCanon_ok (p : ℕ) [Fact p.Prime] (Rg : Nock.Jet.VerifiedRegistry) (Rt : ℕ → Nock.Jet.Autogen.Tpl)
    {fuel : ℕ} {s f r : Noun} {t : Nock.Walk.NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) :
    J8DataOK (j8DataCanon p Rg Rt hgen) :=
  ⟨Rt, t, hgen, ord8Canon, rfl⟩

theorem j8DataCanon_cells (p : ℕ) [Fact p.Prime] (Rg : Nock.Jet.VerifiedRegistry) (Rt : ℕ → Nock.Jet.Autogen.Tpl)
    {fuel : ℕ} {s f r : Noun} {t : Nock.Walk.NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) :
    (j8DataCanon p Rg Rt hgen).cells = sortKey (Nock.V1J8.Gen.cellsOfRoots (j8DataCanon p Rg Rt hgen).roots) := rfl

/-- **The canonical cell list is strictly increasing in the noun order.** -/
theorem j8DataCanon_pairwise (p : ℕ) [Fact p.Prime] (Rg : Nock.Jet.VerifiedRegistry)
    (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun} {t : Nock.Walk.NTree SkelX}
    (hgen : genX Rg.R fuel s f = some (t, r)) : (j8DataCanon p Rg Rt hgen).cells.Pairwise nlt :=
  sortKey_pairwise (ComplJ8Data.cells_nodup _)

end Gen

section ClosedCanon
open Nock.NockVMROM.Thm54.VclL.Handle.TU.J8Gen
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Closed
open Nock Nock.Walk Nock.Edit Nock.Edit.GenX Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8 (cJ ProgAxOK ProgOp5OK)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Jet (CalledIds)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of (Rows31)

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}

open Classical in
/-- **J-8 completeness at the canonical generator** (`complJ8_closed'` at `j8DataCanon`). -/
theorem complJ8_closed_canon {Rt : ℕ → Nock.Jet.Autogen.Tpl} {t : NTree SkelX}
    (hgen : genX Rg.R fuel s f = some (t, r))
    (hpG : p = Nock.Atoms.p) (hax : ProgAxOK p t) (hop5 : ProgOp5OK p t)
    (hclA : ∀ k : Fin 3, ∀ v ∈ (FrameVS.claimNoun (cJ s f r) k).leafList, v < p)
    (hleaf : ComplJ8Walk.RootsLeafOK (j8DataCanon p Rg Rt hgen).roots)
    (hwalk : ComplJ8Walk.WalkDepthOK (j8DataCanon p Rg Rt hgen).reads)
    (hwalkA : ComplJ8Walk.WalkDepthOK (j8DataCanon p Rg Rt hgen).preads)
    (hRt : ∀ id ∈ CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (hregAx : ∀ id ∈ CalledIds t, ∀ i, (Rt id).ax i < p)
    (h31 : Rows31 (j8DataCanon p Rg Rt hgen)) :
    let B := BRunA' δ b (j8DataCanon p Rg Rt hgen) (j8DataCanon_ok p Rg Rt hgen)
      (Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of.orbJ8 _ (Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of.dvdOK_of_rows hpG _ h31)) (K := K)
    (∀ χ, B.Good χ → AcceptsJ8V.AcceptsJ8V δ b B.Pb Rg.R (cJ s f r) χ (B.M χ) (B.tr χ) B.rows B.g) ∧
    (((Finset.univ.filter fun χ : Coins frameJ8 K => ¬ B.Good χ).card : ℚ) /
      Fintype.card (Coins frameJ8 K) ≤ B.epsC) ∧
    StJ8 B.tr ∧ Nock.Jet.HoldsN (cJ s f r) ∧
    (Fintype.card K = VclL.Events.cK →
      B.epsC < 1 / 2 ^ 120 ∧
      ∃ χ, AcceptsJ8V.AcceptsJ8V δ b B.Pb Rg.R (cJ s f r) χ (B.M χ) (B.tr χ) B.rows B.g) :=
  complJ8_closed' δ b (j8DataCanon p Rg Rt hgen) (j8DataCanon_ok p Rg Rt hgen)
    (Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of.orbJ8 _ (Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of.dvdOK_of_rows hpG _ h31)) hpG hax hop5 hclA hleaf hwalk
    hwalkA hRt hregAx h31

end ClosedCanon

/-! ## 2. The converse key-order bridge -/

section Key

/-- `internal` (the rank the cell table records) is `nCells`. -/
theorem internal_eq_nCells : ∀ n : Noun, n.internal = nCells n
  | .atom _ => rfl
  | .cell a b => by simp only [Noun.internal, nCells, internal_eq_nCells a, internal_eq_nCells b]; omega

/-- The honest kind of a child: `1` for a cell, `0` for an atom. -/
def cw (x : Noun) : ℕ := if x.isCell then 1 else 0

/-- The honest value of a child in the cell list `cs`: the atom, or the cell's list position. -/
def cx (cs : List Noun) : Noun → ℕ
  | .atom v => v
  | x@(.cell _ _) => cs.idxOf x

/-- **The honest 8-component key** from the rank `r` and the two sides' kinds and values. -/
def key8 (r wa xa wb xb : ℕ) : ℕ → ℕ
  | 0 => r / 2 ^ 62
  | 1 => r % 2 ^ 62
  | 2 => wa
  | 3 => xa / 2 ^ 32
  | 4 => xa % 2 ^ 32
  | 5 => wb
  | 6 => xb / 2 ^ 32
  | _ => xb % 2 ^ 32

/-- The honest key of a cell `n` in the list `cs`. -/
def keyOf (cs : List Noun) (n : Noun) : ℕ → ℕ :=
  key8 n.internal (cw (VclL.hdN n)) (cx cs (VclL.hdN n)) (cw (VclL.tlN n)) (cx cs (VclL.tlN n))

theorem key8_lexLt {r wa xa wb xb r' wa' xa' wb' xb' : ℕ}
    (h : r < r' ∨ (r = r' ∧ ((wa < wa' ∨ (wa = wa' ∧ xa < xa')) ∨
      (wa = wa' ∧ xa = xa' ∧ (wb < wb' ∨ (wb = wb' ∧ xb < xb')))))) :
    LexLt (key8 r wa xa wb xb) (key8 r' wa' xa' wb' xb') := by
  rcases h with h | ⟨rfl, (h | ⟨rfl, h⟩) | ⟨rfl, rfl, h | ⟨rfl, h⟩⟩⟩
  · by_cases h0 : r / 2 ^ 62 < r' / 2 ^ 62
    · exact ⟨0, by norm_num, fun j hj => by omega, h0⟩
    · refine ⟨1, by norm_num, fun j hj => ?_, ?_⟩
      · interval_cases j; simp only [key8]; rw [two62] at h0 ⊢; omega
      · simp only [key8]; rw [two62] at h0 ⊢; omega
  · exact ⟨2, by norm_num, fun j hj => by interval_cases j <;> rfl, h⟩
  · by_cases h3 : xa / 2 ^ 32 < xa' / 2 ^ 32
    · exact ⟨3, by norm_num, fun j hj => by interval_cases j <;> rfl, h3⟩
    · refine ⟨4, by norm_num, fun j hj => ?_, ?_⟩
      · interval_cases j
        all_goals first | rfl | (simp only [key8]; rw [two32] at h3 ⊢; omega)
      · simp only [key8]; rw [two32] at h3 ⊢; omega
  · exact ⟨5, by norm_num, fun j hj => by interval_cases j <;> rfl, h⟩
  · by_cases h6 : xb / 2 ^ 32 < xb' / 2 ^ 32
    · exact ⟨6, by norm_num, fun j hj => by interval_cases j <;> rfl, h6⟩
    · refine ⟨7, by norm_num, fun j hj => ?_, ?_⟩
      · interval_cases j
        all_goals first | rfl | (simp only [key8]; rw [two32] at h6 ⊢; omega)
      · simp only [key8]; rw [two32] at h6 ⊢; omega

/-- In a list `Pairwise` in an asymmetric relation, the relation orders positions. -/
theorem idxOf_lt_of_pairwise {R : Noun → Noun → Prop} (hasymm : ∀ a b, R a b → R b a → False)
    {l : List Noun} (hl : l.Pairwise R) {x y : Noun} (hx : x ∈ l) (hy : y ∈ l) (hxy : R x y) :
    l.idxOf x < l.idxOf y := by
  have hix := List.idxOf_lt_length_iff.mpr hx
  have hiy := List.idxOf_lt_length_iff.mpr hy
  have ex : l[l.idxOf x] = x := List.getElem_idxOf hix
  have ey : l[l.idxOf y] = y := List.getElem_idxOf hiy
  rcases lt_trichotomy (l.idxOf x) (l.idxOf y) with h | h | h
  · exact h
  · have : x = y := by rw [← ex, ← ey]; simp only [h]
    subst this; exact (hasymm x x hxy hxy).elim
  · have := List.pairwise_iff_getElem.mp hl _ _ hiy hix h
    rw [ex, ey] at this
    exact (hasymm x y hxy this).elim

/-- A child of a cell of `cs`: a cell in `cs`, or an atom below `p`. -/
def ChildOK (p : ℕ) (cs : List Noun) (x : Noun) : Prop :=
  (x.isCell = true → x ∈ cs) ∧ ∀ v, x = .atom v → v < p

/-- **Children in `nlt` order have lexicographically ordered honest `(kind, value)`.** -/
theorem child_lt {p : ℕ} {cs : List Noun} (hcs : cs.Pairwise nlt) {x y : Noun} (hx : ChildOK p cs x)
    (hy : ChildOK p cs y) (hxy : nlt x y) : cw x < cw y ∨ (cw x = cw y ∧ cx cs x < cx cs y) := by
  cases x with
  | atom v =>
    cases y with
    | atom w => right; exact ⟨rfl, nlt_atom_atom.mp hxy⟩
    | cell c d => left; simp [cw, Noun.isCell]
  | cell a b =>
    cases y with
    | atom w => exact (not_nlt_cell_atom hxy).elim
    | cell c d =>
      right
      refine ⟨rfl, ?_⟩
      exact idxOf_lt_of_pairwise nlt_asymm hcs (hx.1 rfl) (hy.1 rfl) hxy

/-- **The converse key-order bridge**: two cells in `nlt` order (children OK) have `LexLt` honest keys. -/
theorem key8_lexLt_of_nlt {p : ℕ} {cs : List Noun} (hcs : cs.Pairwise nlt) {a b a' b' : Noun}
    (ha : ChildOK p cs a) (hb : ChildOK p cs b) (ha' : ChildOK p cs a') (hb' : ChildOK p cs b')
    (h : nlt (.cell a b) (.cell a' b')) : LexLt (keyOf cs (.cell a b)) (keyOf cs (.cell a' b')) := by
  unfold keyOf
  simp only [VclL.hdN, VclL.tlN]
  apply key8_lexLt
  rw [nlt_cell] at h
  simp only [Noun.internal, internal_eq_nCells]
  rcases h with h | ⟨e, h | ⟨rfl, h⟩⟩
  · left; omega
  · right; refine ⟨by omega, Or.inl ?_⟩
    exact child_lt hcs ha ha' h
  · right; refine ⟨by omega, Or.inr ⟨rfl, rfl, ?_⟩⟩
    exact child_lt hcs hb hb' h

end Key

/-! ## 3. Honest rows -/

section Rows
variable {p : ℕ} [Fact p.Prime]

/-- The atom value of a child (`0` for a cell). -/
def aval : Noun → ℕ
  | .atom v => v
  | .cell _ _ => 0

/-- The id of a child (the cell's list position, `0` for an atom). -/
def idv (cs : List Noun) (x : Noun) : ℕ := if x.isCell then cs.idxOf x else 0

/-- **The row-local honest values** of the cell table row of the cell `n` (list `cs`): the rank limbs, and per
side the kind, the id, the atom value, the kind bit `0` (no big atoms) and the rank inverse `0` at an atom child. -/
structure HRow (t : ℕ → ZMod p) (cs : List Noun) (n : Noun) : Prop where
  hi : t Cell.hi = ((n.internal / 2 ^ 62 : ℕ) : ZMod p)
  lo : t Cell.lo = ((n.internal % 2 ^ 62 : ℕ) : ZMod p)
  wL : t Cell.wL = ((cw (VclL.hdN n) : ℕ) : ZMod p)
  idL : t Cell.idL = ((idv cs (VclL.hdN n) : ℕ) : ZMod p)
  aL : t Cell.aL = ((aval (VclL.hdN n) : ℕ) : ZMod p)
  kbL : t CellTwinK.kbL = 0
  invL : (VclL.hdN n).isCell = false → t CellTwinK.invL = 0
  wR : t Cell.wR = ((cw (VclL.tlN n) : ℕ) : ZMod p)
  idR : t Cell.idR = ((idv cs (VclL.tlN n) : ℕ) : ZMod p)
  aR : t Cell.aR = ((aval (VclL.tlN n) : ℕ) : ZMod p)
  kbR : t CellTwinK.kbR = 0
  invR : (VclL.tlN n).isCell = false → t CellTwinK.invR = 0

theorem LexLt.congr {a b a' b' : ℕ → ℕ} (ha : ∀ k < 8, a k = a' k) (hb : ∀ k < 8, b k = b' k)
    (h : LexLt a b) : LexLt a' b' := by
  obtain ⟨k, hk8, hk, hlt⟩ := h
  exact ⟨k, hk8, fun j hj => by rw [← ha j (by omega), ← hb j (by omega)]; exact hk j hj,
    by rw [← ha k hk8, ← hb k hk8]; exact hlt⟩

theorem cw_cast_bool (x : Noun) : ((cw x : ℕ) : ZMod p) = 0 ∨ ((cw x : ℕ) : ZMod p) = 1 := by
  unfold cw; split_ifs <;> simp

/-- The honest child value `x = w·id + (1−w)·a` is the child's `cx`. -/
theorem xF_side {cs : List Noun} {x : Noun} (hx : ChildOK p cs x) (hlen : cs.length < p)
    {r : ℕ → ZMod p} {w id a : ℕ} (hw : r w = ((cw x : ℕ) : ZMod p)) (hid : r id = ((idv cs x : ℕ) : ZMod p))
    (ha : r a = ((aval x : ℕ) : ZMod p)) : (xF r w id a).val = cx cs x := by
  unfold xF
  rw [hw, hid, ha]
  cases x with
  | atom v =>
    simp only [cw, idv, aval, cx, Noun.isCell]
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.cast_zero, zero_mul, sub_zero, one_mul, zero_add]
    exact val_natCast_lt (hx.2 v rfl)
  | cell c d =>
    simp only [cw, idv, aval, cx, Noun.isCell, ↓reduceIte, Nat.cast_one, one_mul, sub_self, zero_mul, add_zero]
    have hm := hx.1 rfl
    exact val_natCast_lt ((List.idxOf_lt_length_iff.mpr hm).trans hlen)

/-- The honest key of a row carrying `HRow` is the noun's `keyOf` (components `< 8`). -/
theorem keyH_eq {cs : List Noun} {a b : Noun} (hp63 : 2 ^ 63 < p) (hlen : cs.length < p)
    (ha : ChildOK p cs a) (hb : ChildOK p cs b) (hrk : (Noun.cell a b).internal < 2 ^ 124) {r : ℕ → ZMod p}
    (h : HRow r cs (.cell a b)) : ∀ k < 8, keyH r k = keyOf cs (.cell a b) k := by
  have hxL := xF_side (r := r) ha hlen h.wL h.idL h.aL
  have hxR := xF_side (r := r) hb hlen h.wR h.idR h.aR
  have hcw : ∀ x : Noun, cw x < p := fun x => by unfold cw; split_ifs <;> omega
  intro k hk
  interval_cases k
  · show (r Cell.hi).val = _
    rw [h.hi]; refine val_natCast_lt ?_
    have : (Noun.cell a b).internal / 2 ^ 62 < 2 ^ 62 := by rw [two62]; rw [show (2:ℕ) ^ 124 = 2 ^ 62 * 2 ^ 62 by norm_num, two62] at hrk; omega
    rw [two62] at this; rw [two63] at hp63; simp only [two62, keyOf, key8]; omega
  · show (r Cell.lo).val = _
    rw [h.lo]; refine val_natCast_lt ?_
    have := Nat.mod_lt (Noun.cell a b).internal (show 0 < 2 ^ 62 by norm_num)
    rw [two62] at this; rw [two63] at hp63; rw [two62]; omega
  · show (r Cell.wL).val = _
    rw [h.wL]; exact val_natCast_lt (hcw _)
  · show xv r Cell.wL Cell.idL Cell.aL / 2 ^ 32 = _
    unfold xv; rw [hxL]; rfl
  · show xv r Cell.wL Cell.idL Cell.aL % 2 ^ 32 = _
    unfold xv; rw [hxL]; rfl
  · show (r Cell.wR).val = _
    rw [h.wR]; exact val_natCast_lt (hcw _)
  · show xv r Cell.wR Cell.idR Cell.aR / 2 ^ 32 = _
    unfold xv; rw [hxR]; rfl
  · show xv r Cell.wR Cell.idR Cell.aR % 2 ^ 32 = _
    unfold xv; rw [hxR]; rfl

/-- The honest side pins hold at a row carrying `HRow`. -/
theorem pins_side {cs : List Noun} {x : Noun} {r : ℕ → ZMod p} {w id a kb inv : ℕ}
    (hw : r w = ((cw x : ℕ) : ZMod p)) (hid : r id = ((idv cs x : ℕ) : ZMod p))
    (ha : r a = ((aval x : ℕ) : ZMod p)) (hkb : r kb = 0) (hinv : x.isCell = false → r inv = 0) :
    (1 - r w) * r id = 0 ∧ r w * r a = 0 ∧ (1 - r w + r w * r kb) * r inv = 0 := by
  rw [hw, hid, ha, hkb]
  cases x with
  | atom v =>
    simp only [cw, idv, aval, Noun.isCell, Bool.false_eq_true, ↓reduceIte, Nat.cast_zero]
    rw [hinv rfl]; simp
  | cell c d =>
    simp [cw, idv, aval, Noun.isCell]

/-- **Rows carrying `HRow` form an honest sorted table** (`HonestM`) over a `Pairwise nlt`, child-closed list of
cells with small atom children, fewer than `p` cells, ranks below `2^124`. -/
theorem honestM_of_rows (hpG : p = Nock.Atoms.p) {cs : List Noun} (hcs : cs.Pairwise nlt)
    (hcell : ∀ c ∈ cs, ∃ a b, c = .cell a b)
    (hch : ∀ a b, Noun.cell a b ∈ cs → ChildOK p cs a ∧ ChildOK p cs b)
    (hlen : cs.length < p) (hrk : ∀ c ∈ cs, c.internal < 2 ^ 124) {t : ℕ → ℕ → ZMod p}
    (hisL : ∀ i < cs.length, t i Cell.isL = if i + 1 = cs.length then 1 else 0)
    (hrow : ∀ i (hi : i < cs.length), HRow (t i) cs cs[i]) : HonestM t cs.length := by
  have hp63 := hp63_of hpG
  have hlt62 : ∀ i (hi : i < cs.length), (t i Cell.hi).val < 2 ^ 62 ∧ (t i Cell.lo).val < 2 ^ 62 := by
    intro i hi
    have hr := hrk _ (List.getElem_mem hi)
    rw [(hrow i hi).hi, (hrow i hi).lo]
    have h1 : cs[i].internal / 2 ^ 62 < 2 ^ 62 := by
      rw [show (2:ℕ) ^ 124 = 2 ^ 62 * 2 ^ 62 by norm_num] at hr
      exact Nat.div_lt_of_lt_mul hr
    have h2 := Nat.mod_lt cs[i].internal (show 0 < 2 ^ 62 by norm_num)
    have hq : (2:ℕ) ^ 62 < p := by rw [two62]; rw [two63] at hp63; omega
    rw [val_natCast_lt (h1.trans hq), val_natCast_lt (h2.trans hq)]
    exact ⟨h1, h2⟩
  refine ⟨hisL, fun i hi => ?_, fun i hi => ?_, fun i hi => (hlt62 i hi).1, fun i hi => (hlt62 i hi).2,
    fun i hi => ?_, fun i hi => ?_, fun i hi1 => ?_⟩
  · rw [(hrow i hi).wL]; exact cw_cast_bool _
  · rw [(hrow i hi).wR]; exact cw_cast_bool _
  · have h := hrow i hi
    exact pins_side h.wL h.idL h.aL h.kbL h.invL
  · have h := hrow i hi
    exact pins_side h.wR h.idR h.aR h.kbR h.invR
  · have hi : i < cs.length := by omega
    obtain ⟨a, b, hab⟩ := hcell _ (List.getElem_mem hi)
    obtain ⟨a', b', hab'⟩ := hcell _ (List.getElem_mem hi1)
    have hmem := List.getElem_mem hi
    have hmem' := List.getElem_mem hi1
    rw [hab] at hmem; rw [hab'] at hmem'
    obtain ⟨ha, hb⟩ := hch a b hmem
    obtain ⟨ha', hb'⟩ := hch a' b' hmem'
    have hnlt : nlt cs[i] cs[i + 1] := List.pairwise_iff_getElem.mp hcs _ _ hi hi1 (by omega)
    rw [hab, hab'] at hnlt
    have hr := hrow i hi
    have hr' := hrow (i + 1) hi1
    rw [hab] at hr; rw [hab'] at hr'
    have hk := keyH_eq hp63 hlen ha hb (hab ▸ hrk _ (List.getElem_mem hi)) hr
    have hk' := keyH_eq hp63 hlen ha' hb' (hab' ▸ hrk _ (List.getElem_mem hi1)) hr'
    exact LexLt.congr (fun k hk8 => (hk k hk8).symm) (fun k hk8 => (hk' k hk8).symm)
      (key8_lexLt_of_nlt hcs ha hb ha' hb' hnlt)

end Rows

/-! ## 4. The honest cell trace columns carry `HRow` -/

section Cols
open Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Cell (isBig wOf idOf aOf kbOf kbLB kbRB)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [Fintype K]
  (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))] (b : Basis (Fin 3) (ZMod p) K)

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- The honest row values of the cell trace `colW` over `cellCol (valsBE …)`: column `j` of row `i` (`0` past the
table). -/
def rowsOf {n : ℕ} (hn : 0 < n) (colF : ℕ → Fin n → ZMod p) : ℕ → ℕ → ZMod p := fun i j =>
  if h : i < n then fullCol hn colF j ⟨i, h⟩ else 0

/-- The honest cell column function: `HonestKW.colW` over the filled honest rows. -/
abbrev colH (γ ρ : 𝕂′) (E : Noun → Nock.ComputeTable.FP 𝕂′) (z : 𝕂′) (big : Noun → Option ℕ)
    (cells : List Noun) (mv mx mx1 : ℕ → ℕ) (mhv : Fin cells.length → ZMod p)
    (iv av : Fin cells.length → 𝕂′) : ℕ → Fin cells.length → ZMod p :=
  HonestKW.colW δ b (cellCol δ b (ComplJ8Enc.valsBE δ γ ρ E z big cells mv mx mx1)) mhv (kbLB big cells)
    (kbRB big cells) iv av

variable {γ ρ : Quad (algebraMap (ZMod p) K δ)} {E : Noun → Nock.ComputeTable.FP (Quad (algebraMap (ZMod p) K δ))}
  {z : Quad (algebraMap (ZMod p) K δ)} {big : Noun → Option ℕ} {cells : List Noun} {mv mx mx1 : ℕ → ℕ}
  {mhv : Fin cells.length → ZMod p} {iv av : Fin cells.length → Quad (algebraMap (ZMod p) K δ)}

theorem colH_base (hn : 0 < cells.length) {j : ℕ} (h2 : 2 ≤ j) (hj : j < 129) (i : Fin cells.length) :
    fullCol hn (colH δ b γ ρ E z big cells mv mx mx1 mhv iv av) j i =
      (ComplJ8Enc.cellRowsBE δ E z big cells mv mx mx1 i).base j := by
  have h0 : j ≠ 0 := by omega
  have h1 : j ≠ 1 := by omega
  simp only [fullCol, h0, h1, ↓reduceIte, colH, HonestKW.colW, extColF, hj, cellCol]
  rfl

theorem colH_new (hn : 0 < cells.length) {j : ℕ} (h1 : 129 ≤ j) (hj : j < 134) (i : Fin cells.length) :
    fullCol hn (colH δ b γ ρ E z big cells mv mx mx1 mhv iv av) j i =
      HonestKW.newW δ b (cellCol δ b (ComplJ8Enc.valsBE δ γ ρ E z big cells mv mx mx1)) mhv (kbLB big cells)
        (kbRB big cells) iv av j i := by
  have h0 : j ≠ 0 := by omega
  have h1' : j ≠ 1 := by omega
  have hn129 : ¬ j < 129 := by omega
  simp only [fullCol, h0, h1', ↓reduceIte, colH, HonestKW.colW, extColF, hn129, hj]

theorem rowsOf_base (hn : 0 < cells.length) {i : ℕ} (hi : i < cells.length) {k : ℕ} (h2 : 2 ≤ k)
    (hk : k < 129) :
    rowsOf hn (colH δ b γ ρ E z big cells mv mx mx1 mhv iv av) i k =
      (ComplJ8Enc.cellRowBE δ E z big cells mv mx mx1 cells[i] i).base k := by
  simp only [rowsOf, hi, ↓reduceDIte]
  rw [colH_base δ b hn h2 hk, ComplJ8Enc.cellRowsBE_getElem _ _ _ _ _ _ _ hi]

theorem rowsOf_new (hn : 0 < cells.length) {i : ℕ} (hi : i < cells.length) {k : ℕ} (h1 : 129 ≤ k)
    (hk : k < 134) :
    rowsOf hn (colH δ b γ ρ E z big cells mv mx mx1 mhv iv av) i k =
      HonestKW.newW δ b (cellCol δ b (ComplJ8Enc.valsBE δ γ ρ E z big cells mv mx mx1)) mhv (kbLB big cells)
        (kbRB big cells) iv av k ⟨i, hi⟩ := by
  simp only [rowsOf, hi, ↓reduceDIte]
  rw [colH_new δ b hn h1 hk]

theorem rowsOf_isL (hn : 0 < cells.length) {i : ℕ} (hi : i < cells.length) :
    rowsOf hn (colH δ b γ ρ E z big cells mv mx mx1 mhv iv av) i Cell.isL =
      if i + 1 = cells.length then 1 else 0 := by
  simp only [rowsOf, hi, ↓reduceDIte, fullCol, Cell.isL, one_ne_zero, ↓reduceIte, Fin.ext_iff]
  by_cases h : i + 1 = cells.length
  · rw [ite_eq_left (by omega), ite_eq_left h]
  · rw [ite_eq_right (by omega), ite_eq_right h]

theorem wOf_small {x : Noun} (hx : isBig big x = false) : wOf (F := ZMod p) big x = ((cw x : ℕ) : ZMod p) := by
  simp only [wOf, hx, Bool.or_false, cw]; split_ifs <;> simp

theorem idOf_small {x : Noun} (hx : isBig big x = false) :
    idOf (F := ZMod p) cells big x = ((idv cells x : ℕ) : ZMod p) := by
  unfold idOf idv
  by_cases hc : x.isCell = true
  · simp only [hc, ↓reduceIte]
  · simp only [hc, Bool.false_eq_true, ↓reduceIte, Nat.cast_zero]
    have : (big x).isSome = false := by
      simpa [isBig, hc] using hx
    rw [Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at this
    simp [this]

theorem aOf_small {x : Noun} (hx : isBig big x = false) : aOf (F := ZMod p) big x = ((aval x : ℕ) : ZMod p) := by
  unfold aOf
  rw [hx]
  cases x <;> simp [aval]

theorem kbOf_small {x : Noun} (hx : isBig big x = false) : kbOf (F := ZMod p) big x = 0 := by
  simp [kbOf, hx]

/-- **The honest cell trace rows carry `HRow`** (no big-atom children). -/
theorem hrow_colH (hn : 0 < cells.length)
    (hnb : ∀ i (hi : i < cells.length), isBig big (VclL.hdN cells[i]) = false ∧ isBig big (VclL.tlN cells[i]) = false)
    (i : ℕ) (hi : i < cells.length) :
    HRow (rowsOf hn (colH δ b γ ρ E z big cells mv mx mx1 mhv iv av) i) cells cells[i] := by
  obtain ⟨hbL, hbR⟩ := hnb i hi
  have hg : cells.getD i (.atom 0) = cells[i] := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  have hloL : ∀ x : Noun, x.isCell = false → (Noun.internal x % 2 ^ 62 : ℕ) = 0 ∧ (Noun.internal x / 2 ^ 62 : ℕ) = 0 := by
    intro x hx; cases x <;> simp_all [Noun.internal, Noun.isCell]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [rowsOf_base δ b hn hi (by decide) (by decide)]
    simp [CellVals.base, Cell.hi, ComplJ8Enc.cellRowBE, ComplJ8Cell.cellRowB, cellRow0, rankOf]
  · rw [rowsOf_base δ b hn hi (by decide) (by decide)]
    simp [CellVals.base, Cell.lo, ComplJ8Enc.cellRowBE, ComplJ8Cell.cellRowB, cellRow0, rankOf]
  · rw [rowsOf_base δ b hn hi (by decide) (by decide)]
    simp only [CellVals.base, Cell.wL, ComplJ8Enc.cellRowBE, ComplJ8Cell.cellRowB]
    simp only [show (5 : ℕ) ≠ 2 by decide, show (5 : ℕ) ≠ 3 by decide, show (5 : ℕ) ≠ 4 by decide, ↓reduceIte]
    exact wOf_small hbL
  · rw [rowsOf_base δ b hn hi (by decide) (by decide)]
    simp only [CellVals.base, Cell.idL, ComplJ8Enc.cellRowBE, ComplJ8Cell.cellRowB]
    simp only [show (3 : ℕ) ≠ 2 by decide, ↓reduceIte]
    exact idOf_small hbL
  · rw [rowsOf_base δ b hn hi (by decide) (by decide)]
    simp only [CellVals.base, Cell.aL, ComplJ8Enc.cellRowBE, ComplJ8Cell.cellRowB]
    simp only [show (7 : ℕ) ≠ 2 by decide, show (7 : ℕ) ≠ 3 by decide, show (7 : ℕ) ≠ 4 by decide,
      show (7 : ℕ) ≠ 5 by decide, show (7 : ℕ) ≠ 6 by decide, ↓reduceIte]
    exact aOf_small hbL
  · rw [rowsOf_new δ b hn hi (by decide) (by decide)]
    simp only [HonestKW.newW, CellTwinK.kbL, show (130 : ℕ) ≠ 129 by decide, ↓reduceIte, kbLB, hg]
    exact kbOf_small hbL
  · intro hc
    rw [rowsOf_new δ b hn hi (by decide) (by decide)]
    simp only [HonestKW.newW, CellTwinK.invL, CellTwinK.kbL, CellTwinK.kbR, show (132 : ℕ) ≠ 129 by decide,
      show (132 : ℕ) ≠ 130 by decide, show (132 : ℕ) ≠ 131 by decide, ↓reduceIte]
    simp only [cellCol, Cell.loL, Cell.hiL, show (11 : ℕ) < 129 by decide, show (12 : ℕ) < 129 by decide,
      ↓reduceIte, ComplJ8Enc.valsBE, cellFill, cellFillInv, ComplJ8Enc.cellRowsBE, hg, CellVals.base,
      ComplJ8Enc.cellRowBE, ComplJ8Cell.cellRowB, cellRow0, rankOf]
    obtain ⟨h1, h2⟩ := hloL _ hc
    rw [two62] at h1 h2; simp [h1, h2]
  · rw [rowsOf_base δ b hn hi (by decide) (by decide)]
    simp only [CellVals.base, Cell.wR, ComplJ8Enc.cellRowBE, ComplJ8Cell.cellRowB]
    simp only [show (6 : ℕ) ≠ 2 by decide, show (6 : ℕ) ≠ 3 by decide, show (6 : ℕ) ≠ 4 by decide,
      show (6 : ℕ) ≠ 5 by decide, ↓reduceIte]
    exact wOf_small hbR
  · rw [rowsOf_base δ b hn hi (by decide) (by decide)]
    simp only [CellVals.base, Cell.idR, ComplJ8Enc.cellRowBE, ComplJ8Cell.cellRowB]
    simp only [show (4 : ℕ) ≠ 2 by decide, show (4 : ℕ) ≠ 3 by decide, ↓reduceIte]
    exact idOf_small hbR
  · rw [rowsOf_base δ b hn hi (by decide) (by decide)]
    simp only [CellVals.base, Cell.aR, ComplJ8Enc.cellRowBE, ComplJ8Cell.cellRowB]
    simp only [show (8 : ℕ) ≠ 2 by decide, show (8 : ℕ) ≠ 3 by decide, show (8 : ℕ) ≠ 4 by decide,
      show (8 : ℕ) ≠ 5 by decide, show (8 : ℕ) ≠ 6 by decide, show (8 : ℕ) ≠ 7 by decide, ↓reduceIte]
    exact aOf_small hbR
  · rw [rowsOf_new δ b hn hi (by decide) (by decide)]
    simp only [HonestKW.newW, CellTwinK.kbL, CellTwinK.kbR, show (131 : ℕ) ≠ 129 by decide,
      show (131 : ℕ) ≠ 130 by decide, ↓reduceIte, kbRB, hg]
    exact kbOf_small hbR
  · intro hc
    rw [rowsOf_new δ b hn hi (by decide) (by decide)]
    simp only [HonestKW.newW, CellTwinK.invL, CellTwinK.invR, CellTwinK.kbL, CellTwinK.kbR,
      show (133 : ℕ) ≠ 129 by decide, show (133 : ℕ) ≠ 130 by decide, show (133 : ℕ) ≠ 131 by decide,
      show (133 : ℕ) ≠ 132 by decide, ↓reduceIte]
    simp only [cellCol, Cell.loR, Cell.hiR, show (13 : ℕ) < 129 by decide, show (14 : ℕ) < 129 by decide,
      ↓reduceIte, ComplJ8Enc.valsBE, cellFill, cellFillInv, ComplJ8Enc.cellRowsBE, hg, CellVals.base,
      ComplJ8Enc.cellRowBE, ComplJ8Cell.cellRowB, cellRow0, rankOf]
    obtain ⟨h1, h2⟩ := hloL _ hc
    rw [two62] at h1 h2; simp [h1, h2]

end Cols


/-! ## 5. At the canonical layout -/

section Canon
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]

/-- The nodes `i ↦ ω^i` of an `n`-row table. -/
def nodesN (ω : ZMod p) (n : ℕ) : Fin n → ZMod p := fun i => ω ^ (i : ℕ)

/-- **The honest cell aux interpolants**: aux column `c` interpolates `auxH t n · c` at the nodes. -/
def auxMOf {n : ℕ} (nodes : Fin n → ZMod p) (t : ℕ → ℕ → ZMod p) : Fin 200 → (ZMod p)[X] :=
  fun c => Lagrange.interpolate Finset.univ nodes (fun i => auxH t n i c)

/-- The canonical layout's cell nodes are distinct (`nC ≤ 2^ht < 3·2^ht = ord ω`). -/
theorem nodesC_inj (hpG : p = Nock.Atoms.p) (sz : P8PublicClaim → SizesP1) (c : P8PublicClaim) :
    Function.Injective (nodesN (canonPb hpG sz c).orbitC.ω (canonPb hpG sz c).nC) := by
  intro a a' h
  have hord : orderOf (canonPb hpG sz c).orbitC.ω = 3 * 2 ^ (sz c).ht := (canonPb hpG sz c).orbitC.order_ω
  have hfit := (sz c).fit_ht
  have hn : (sz c).nC ≤ 2 ^ (sz c).ht := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hfit
  have ha : (a : ℕ) < (sz c).nC := a.isLt
  have ha' : (a' : ℕ) < (sz c).nC := a'.isLt
  exact Fin.ext (pow_injOn_Iio_orderOf (by rw [Set.mem_Iio, hord]; omega)
    (by rw [Set.mem_Iio, hord]; omega) h)

/-- **`canonM` at an honest column function**: if the cell trace interpolates `fullCol colF` at the canonical
nodes, the aux columns interpolate `auxH`, and the row values form an `HonestM` table, then `canonM` holds. -/
theorem canonM_of_cols (b : Basis (Fin 3) (ZMod p) K) {hpG : p = Nock.Atoms.p} {sz : P8PublicClaim → SizesP1}
    {c : P8PublicClaim} {n : ℕ} (hn : 0 < n) (hnC : (canonPb hpG sz c).nC = n) (colF : ℕ → Fin n → ZMod p)
    {tr : TrJ8 (ZMod p)} {ax : AuxP1 (ZMod p)}
    (hM : ∀ j, tr.M j = honestQ hn (nodesN (canonPb hpG sz c).orbitC.ω n) colF 242 j)
    (hax : ax.M = auxMOf (nodesN (canonPb hpG sz c).orbitC.ω n) (rowsOf hn colF))
    (H : HonestM (rowsOf hn colF) n) :
    (canonM b (canonPb hpG sz c)).Satisfies (sideMQ tr ax) := by
  subst hnC
  refine canonM_of_honest b H fun i hi => ?_
  have hinj := nodesC_inj hpG sz c
  funext j
  by_cases hj : j < 134
  · rw [vM_base _ _ _ _ hj, hM, fullH_base hj]
    have := honestQ_eval hn (nodesN _ _) hinj colF (w := 242) ⟨j, by omega⟩ ⟨i, hi⟩
    simp only [nodesN] at this
    rw [this]; simp [rowsOf, hi]
  · by_cases hj2 : j < 334
    · obtain ⟨c', rfl⟩ : ∃ c', j = SideM.A + c' := ⟨j - 134, by simp only [SideM.A]; omega⟩
      have hc : c' < 200 := by simp only [SideM.A] at hj2; omega
      rw [vM_aux _ _ _ _ hc, fullH_aux hc, hax]
      exact Lagrange.eval_interpolate_at_node (fun k : Fin _ => auxH (rowsOf hn colF) _ k c') hinj.injOn
        (Finset.mem_univ (⟨i, hi⟩ : Fin _))
    · have hw : ¬ j < (canonMT (F := ZMod p)).width 3 := by rw [canonMT_width]; exact hj2
      have h1 : vM tr ax (canonPb hpG sz c).orbitC.ω i j = 0 := by
        unfold vM Reify.envOfTrace; simp only [hw, ↓reduceDIte]
      rw [h1]; unfold fullH; simp [hj, hj2]

open Nock.NockVMROM.Thm54.T0Tower in
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Cell (isBig kbLB kbRB) in
/-- **The honest cell trace at the canonical layout satisfies `canonM` with aux `auxH`** (`cellTrME` at the
canonical nodes; the cell list `Pairwise nlt`, child-closed, small atom children that are not big, fewer than `p`
cells, ranks below `2^124`). -/
theorem canonM_cellTr [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
    (b : Basis (Fin 3) (ZMod p) K) (hpG : p = Nock.Atoms.p) (sz : P8PublicClaim → SizesP1) (c : P8PublicClaim)
    (chalsF pubsF : SVFrame.Coins FrameJ8.frameJ8 K → ℕ → K)
    (γF ρF zF : SVFrame.Coins FrameJ8.frameJ8 K → Quad (algebraMap (ZMod p) K δ))
    (EF : SVFrame.Coins FrameJ8.frameJ8 K → Noun → Nock.ComputeTable.FP (Quad (algebraMap (ZMod p) K δ)))
    (big : Noun → Option ℕ) (cells : List Noun) (mv mx mx1 mh : ℕ → ℕ) (χ : SVFrame.Coins FrameJ8.frameJ8 K)
    (hn : 0 < cells.length) (hnC : (canonPb hpG sz c).nC = cells.length)
    (hcs : cells.Pairwise nlt) (hcell : ∀ x ∈ cells, ∃ a b, x = .cell a b)
    (hch : ∀ a b, Noun.cell a b ∈ cells → ChildOK p cells a ∧ ChildOK p cells b)
    (hnb : ∀ i (hi : i < cells.length), isBig big (VclL.hdN cells[i]) = false ∧
      isBig big (VclL.tlN cells[i]) = false)
    (hlen : cells.length < p) (hrk : ∀ x ∈ cells, x.internal < 2 ^ 124)
    {tr : TrJ8 (ZMod p)} {ax : AuxP1 (ZMod p)}
    (htr : tr.M = ComplJ8Enc.cellTrME δ b hn (nodesN (canonPb hpG sz c).orbitC.ω cells.length)
      (canonPb hpG sz c).orbitC chalsF pubsF γF ρF zF EF big cells mv mx mx1 mh χ)
    (hax : ax.M = auxMOf (nodesN (canonPb hpG sz c).orbitC.ω cells.length)
      (rowsOf hn (colH δ b (γF χ) (ρF χ) (EF χ) (zF χ) big cells mv mx mx1 (fun i => (mh i : ZMod p))
        (HonestKW.ivW δ b hn (nodesN (canonPb hpG sz c).orbitC.ω cells.length) (canonPb hpG sz c).orbitC
          (chalsF χ) (pubsF χ) (cellCol δ b (ComplJ8Enc.valsBE δ (γF χ) (ρF χ) (EF χ) (zF χ) big cells mv mx mx1))
          (fun i => (mh i : ZMod p)) (kbLB big cells) (kbRB big cells))
        (HonestKW.avW δ b hn (nodesN (canonPb hpG sz c).orbitC.ω cells.length) (canonPb hpG sz c).orbitC
          (chalsF χ) (pubsF χ) (cellCol δ b (ComplJ8Enc.valsBE δ (γF χ) (ρF χ) (EF χ) (zF χ) big cells mv mx mx1))
          (fun i => (mh i : ZMod p)) (kbLB big cells) (kbRB big cells))))) :
    (canonM b (canonPb hpG sz c)).Satisfies (sideMQ tr ax) := by
  refine canonM_of_cols b hn hnC _ (fun j => by rw [htr]; rfl) hax ?_
  exact honestM_of_rows hpG hcs hcell hch hlen hrk (fun i hi => rowsOf_isL δ b hn hi)
    (fun i hi => hrow_colH δ b hn hnb i hi)

end Canon


section CanonCells
open Nock.NockVMROM.Thm54.VclL.Handle.TU.J8Gen
open Nock.Edit.GenX
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Cell (isBig)

/-- **The canonical cell list meets the hypotheses of `canonM_cellTr`** (big map `bigIdOfP p acs`), given that
every atom child of a cell is below `p`. -/
theorem canon_cells_facts (p : ℕ) [Fact p.Prime] (Rg : Nock.Jet.VerifiedRegistry) (Rt : ℕ → Nock.Jet.Autogen.Tpl)
    {fuel : ℕ} {s f r : Noun} {t : Nock.Walk.NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))
    (hsmall : ∀ a b, Noun.cell a b ∈ (j8DataCanon p Rg Rt hgen).cells → ∀ v, (a = .atom v ∨ b = .atom v) → v < p) :
    let cs := (j8DataCanon p Rg Rt hgen).cells
    cs.Pairwise nlt ∧ (∀ x ∈ cs, ∃ a b, x = .cell a b) ∧
      (∀ a b, Noun.cell a b ∈ cs → ChildOK p cs a ∧ ChildOK p cs b) ∧
      (∀ i (hi : i < cs.length),
        isBig (ComplJ8Data.bigIdOfP p (j8DataCanon p Rg Rt hgen).acs) (VclL.hdN cs[i]) = false ∧
        isBig (ComplJ8Data.bigIdOfP p (j8DataCanon p Rg Rt hgen).acs) (VclL.tlN cs[i]) = false) := by
  intro cs
  have hcellAll : ∀ x ∈ cs, ∃ a b, x = .cell a b := fun x hx => by
    have hx' := (mem_cells_iff p Rg Rt hgen ord8Canon x).mp hx
    have h := (ComplJ8Walk.cellsOfRoots_mem _ x hx').1
    cases x with
    | atom _ => simp [Noun.isCell] at h
    | cell a b => exact ⟨a, b, rfl⟩
  have hcl := cells_closedG p Rg Rt hgen ord8Canon
  have hch : ∀ a b, Noun.cell a b ∈ cs → ChildOK p cs a ∧ ChildOK p cs b := by
    intro a b hab
    obtain ⟨h1, h2⟩ := hcl a b hab (by simp)
    refine ⟨⟨fun hc => ?_, fun v hv => hsmall a b hab v (Or.inl hv)⟩,
      ⟨fun hc => ?_, fun v hv => hsmall a b hab v (Or.inr hv)⟩⟩
    · cases a with
      | atom _ => simp [Noun.isCell] at hc
      | cell x y => exact h1 x y rfl
    · cases b with
      | atom _ => simp [Noun.isCell] at hc
      | cell x y => exact h2 x y rfl
  refine ⟨j8DataCanon_pairwise p Rg Rt hgen, hcellAll, hch, fun i hi => ?_⟩
  obtain ⟨a, b, hab⟩ := hcellAll _ (List.getElem_mem hi)
  have hmem := List.getElem_mem hi
  rw [hab] at hmem ⊢
  obtain ⟨ha, hb⟩ := hch a b hmem
  have key : ∀ x : Noun, ChildOK p cs x →
      isBig (ComplJ8Data.bigIdOfP p (j8DataCanon p Rg Rt hgen).acs) x = false := by
    intro x hx
    cases x with
    | cell _ _ => simp [isBig, Noun.isCell]
    | atom v => simp [isBig, Noun.isCell, ComplJ8Data.bigIdOfP, hx.2 v rfl]
  exact ⟨key a ha, key b hb⟩

/-- **(D) for the honest aux columns**: degree `< n`. -/
theorem auxMOf_degree_lt {p : ℕ} [Fact p.Prime] {n : ℕ} (nodes : Fin n → ZMod p) (hinj : Function.Injective nodes) (t : ℕ → ℕ → ZMod p) (c : Fin 200) :
    (auxMOf nodes t c).degree < (n : WithBot ℕ) := by
  have := Lagrange.degree_interpolate_lt (s := Finset.univ) (fun i : Fin n => auxH t n i c) hinj.injOn
  rw [Finset.card_univ, Fintype.card_fin] at this
  exact this

end CanonCells


/-! ## 6. The canonical sizes; root-sorted reads keep the walk sizes -/

section Sizes
open Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.Walk (NTree bfsForest bfsForest_length totalSize)

/-- `sideTails` of a permutation is a permutation. -/
theorem sideTails_perm (b : Bool) {T T' : List (List Bool)} (h : T.Perm T') :
    (sideTails b T).Perm (sideTails b T') := h.filterMap _

theorem contT_perm (b : Bool) {T T' : List (List Bool)} (h : T.Perm T') : (contT b T).Perm (contT b T') :=
  (sideTails_perm b h).filter _

theorem cont_perm (b : Bool) {T T' : List (List Bool)} (h : T.Perm T') : cont b T = cont b T' := by
  unfold cont
  have hl := (contT_perm b h).length_eq
  cases h1 : contT b T <;> cases h2 : contT b T' <;> simp_all

theorem multT_perm (b : Bool) {T T' : List (List Bool)} (h : T.Perm T') : multT b T = multT b T' :=
  (sideTails_perm b h).count_eq _

/-- **The read trie depends on its targets only up to permutation.** -/
theorem trie_perm (root : Noun) : ∀ (n : Noun) (bs : List Bool) {T T' : List (List Bool)}, T.Perm T' →
    trie root n bs T = trie root n bs T'
  | .atom a, bs, T, T', h => by simp only [trie, multT_perm false h, multT_perm true h]
  | .cell l r, bs, T, T', h => by
    simp only [trie, cont_perm false h, cont_perm true h, multT_perm false h, multT_perm true h,
      trie_perm root l (bs ++ [false]) (contT_perm false h), trie_perm root r (bs ++ [true]) (contT_perm true h)]

theorem targetsOf_perm {reads reads' : List (Noun × ℕ)} (h : reads.Perm reads') (r : Noun) :
    (targetsOf reads r).Perm (targetsOf reads' r) :=
  ((h.filter _).filter _).map _

theorem walkRoots_perm {reads reads' : List (Noun × ℕ)} (h : reads.Perm reads') :
    (walkRoots reads).Perm (walkRoots reads') :=
  ((h.filter _).map _).dedup

/-- A trie with no targets is a single node. -/
theorem trie_nil_size (root n : Noun) (bs : List Bool) : (trie root n bs []).size = 1 := by
  cases n <;> simp [trie, cont, contT, sideTails, NTree.size]

/-- **Root-sorted reads keep the walk sizes**: for any two cell lists and two read lists that are permutations of
each other, the walk forests are permutations of each other up to the dummy root, so `krW` and the walk row
count agree. -/
theorem walk_sizes_perm (cells cells' : List Noun) {reads reads' : List (Noun × ℕ)} (h : reads.Perm reads') :
    krW cells reads = krW cells' reads' ∧
      (walkRows cells reads).length = (walkRows cells' reads').length := by
  have hR := walkRoots_perm h
  by_cases h0 : walkRoots reads = []
  · have h0' : walkRoots reads' = [] := List.Perm.eq_nil (hR.symm.trans (by rw [h0]))
    refine ⟨by unfold krW walkForest; rw [ite_eq_left h0, ite_eq_left h0']; rfl, ?_⟩
    unfold walkRows walkForest
    rw [ite_eq_left h0, ite_eq_left h0', bfsForest_length, bfsForest_length]
    simp [totalSize, trie_nil_size]
  · have h0' : walkRoots reads' ≠ [] := fun e => h0 (List.Perm.eq_nil (hR.trans (by rw [e])))
    have hF : (walkForest cells reads).Perm (walkForest cells' reads') := by
      unfold walkForest
      rw [ite_eq_right h0, ite_eq_right h0']
      have : ((walkRoots reads').map fun r => trie r r [] (targetsOf reads r)) =
          (walkRoots reads').map fun r => trie r r [] (targetsOf reads' r) :=
        List.map_congr_left fun r _ => trie_perm r r [] (targetsOf_perm h r)
      rw [← this]
      exact hR.map _
    refine ⟨hF.length_eq, ?_⟩
    unfold walkRows
    rw [bfsForest_length, bfsForest_length]
    exact (hF.map _).sum_eq

/-- **The four sizes of an admissible datum** (compute rows, cell rows, walk rows, walk roots). -/
def szOf {p : ℕ} [Fact p.Prime] {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}
    (D : ComplJ8Data.J8Data p Rg fuel s f r) (hC : 0 < D.cells.length)
    (hfit : max (bfsForest [D.t]).length (max D.cells.length (walkRows D.cells D.reads).length) ≤ 2 ^ 32) :
    SizesP1 where
  n := (bfsForest [D.t]).length
  nC := D.cells.length
  nW := (walkRows D.cells D.reads).length
  kroots := krW D.cells D.reads
  hn := ComplJ8Of.bfs_pos D.t
  hnC := hC
  hnW := ComplJ8Of.walk_pos _ _
  hfit := hfit

section Run
open Nock.NockVMROM.Thm54.VclL.Handle.TU.J8Gen
open Nock.Edit.GenX
variable (p : ℕ) [Fact p.Prime] (Rg : Nock.Jet.VerifiedRegistry) (Rt : ℕ → Nock.Jet.Autogen.Tpl)
  {fuel : ℕ} {s f r : Noun} {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

/-- **`szCanon`**: the sizes of the canonical generator. -/
abbrev szCanon [Fact (ringChar (ZMod p)).Prime] (hfit : max (bfsForest [(j8DataCanon p Rg Rt hgen).t]).length
      (max (j8DataCanon p Rg Rt hgen).cells.length
        (walkRows (j8DataCanon p Rg Rt hgen).cells (j8DataCanon p Rg Rt hgen).reads).length) ≤ 2 ^ 32) :
    SizesP1 :=
  szOf (j8DataCanon p Rg Rt hgen) (cells_posG Rt hgen ord8Canon) hfit

/-- **The canonical sizes are the honest walk's**: `nW` is the walk row count and `kroots` is `krW` of the
canonical data. -/
theorem szCanon_eq [Fact (ringChar (ZMod p)).Prime] (hfit) :
    (szCanon p Rg Rt hgen hfit).n = (bfsForest [t]).length ∧
      (szCanon p Rg Rt hgen hfit).nC = (j8DataCanon p Rg Rt hgen).cells.length ∧
      (szCanon p Rg Rt hgen hfit).nW =
        (walkRows (j8DataCanon p Rg Rt hgen).cells (j8DataCanon p Rg Rt hgen).reads).length ∧
      (szCanon p Rg Rt hgen hfit).kroots =
        krW (j8DataCanon p Rg Rt hgen).cells (j8DataCanon p Rg Rt hgen).reads :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **Root-sorted reads keep `nW`, `kroots` (and `nC`)**: the canonical generator's sizes equal the honest
generator `j8DataOf`'s. -/
theorem canon_sizes_eq :
    (j8DataCanon p Rg Rt hgen).cells.length = (ComplJ8Data.j8DataOf p Rg Rt hgen).cells.length ∧
      krW (j8DataCanon p Rg Rt hgen).cells (j8DataCanon p Rg Rt hgen).reads =
        krW (ComplJ8Data.j8DataOf p Rg Rt hgen).cells (ComplJ8Data.j8DataOf p Rg Rt hgen).reads ∧
      (walkRows (j8DataCanon p Rg Rt hgen).cells (j8DataCanon p Rg Rt hgen).reads).length =
        (walkRows (ComplJ8Data.j8DataOf p Rg Rt hgen).cells (ComplJ8Data.j8DataOf p Rg Rt hgen).reads).length := by
  rw [← j8DataGen_ordId p Rg Rt hgen]
  have h : (j8DataGen p Rg Rt hgen ord8Canon).reads.Perm (j8DataGen p Rg Rt hgen ordId).reads :=
    ord8Canon.permR _ _
  obtain ⟨h1, h2⟩ := walk_sizes_perm (j8DataGen p Rg Rt hgen ord8Canon).cells
    (j8DataGen p Rg Rt hgen ordId).cells h
  exact ⟨(ord8Canon.permC _).length_eq, h1, h2⟩

end Run

end Sizes


/-! ## 7. The canonical reads are sorted by root serial -/

section ReadOrder
open Nock.NockVMROM.Thm54.VclL.GenWalk

/-- **`ordRS` sorts by root serial.** -/
theorem ordRS_pairwise (H : Noun → ℕ × ℕ) (l : List (Noun × ℕ)) :
    (ordRS H l).Pairwise fun a b => serialOf H a ≤ serialOf H b := by
  have h := List.pairwise_mergeSort (le := fun a b : Noun × ℕ => decide (serialOf H a ≤ serialOf H b))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) l
  exact h.imp fun h' => by simpa using h'

theorem idxD_eq_idxOf : ∀ (cs : List Noun) (n : Noun), Nock.V1J8.Gen.idxD cs n = cs.idxOf n
  | [], _ => rfl
  | c :: cs, n => by
    simp only [Nock.V1J8.Gen.idxD, List.idxOf_cons, idxD_eq_idxOf cs n]
    by_cases h : c = n <;> simp [h]

/-- The handle serial of a cell of the list is its list position. -/
theorem hdlP_serial (p : ℕ) (cs acs : List Noun) {a b : Noun} (h : Noun.cell a b ∈ cs) :
    (ComplJ8Data.hdlP p cs acs (.cell a b)).2 = cs.idxOf (.cell a b) := by
  simp [ComplJ8Data.hdlP, Nock.V1J8.Gen.idxOf, h, idxD_eq_idxOf]

/-- **The path-kind roots of reads sorted by `hdlP` serial are non-decreasing in list position**, when every
path-kind root is a cell of the list. -/
theorem roots_sorted (p : ℕ) (cs acs : List Noun) (l : List (Noun × ℕ))
    (hroot : ∀ x ∈ l, isPathAx x.2 = true → ∃ a b, x.1 = .cell a b ∧ Noun.cell a b ∈ cs) :
    ((pathKind (ordRS (ComplJ8Data.hdlP p cs acs) l)).map Prod.fst).Pairwise
      fun a b => cs.idxOf a ≤ cs.idxOf b := by
  have hs := ordRS_pairwise (ComplJ8Data.hdlP p cs acs) l
  have hf := hs.filter (fun r => isPathAx r.2)
  rw [List.pairwise_map]
  refine hf.imp_of_mem fun {x y} hx hy hxy => ?_
  have hx' := List.mem_filter.mp hx
  have hy' := List.mem_filter.mp hy
  obtain ⟨a, b, hxe, hxm⟩ := hroot x ((List.mergeSort_perm _ _).mem_iff.mp hx'.1) hx'.2
  obtain ⟨c, d, hye, hym⟩ := hroot y ((List.mergeSort_perm _ _).mem_iff.mp hy'.1) hy'.2
  unfold serialOf at hxy
  rw [hxe, hye, hdlP_serial p cs acs hxm, hdlP_serial p cs acs hym] at hxy
  rw [hxe, hye]; exact hxy

end ReadOrder

end

end Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonGenP1

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonGenP1.j8DataCanon_ok
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonGenP1.j8DataCanon_pairwise
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonGenP1.complJ8_closed_canon
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonGenP1.key8_lexLt_of_nlt
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonGenP1.honestM_of_rows
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonGenP1.hrow_colH
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonGenP1.nodesC_inj
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonGenP1.canonM_of_cols
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonGenP1.canonM_cellTr
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonGenP1.canon_cells_facts
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonGenP1.walk_sizes_perm
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonGenP1.szCanon_eq
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonGenP1.canon_sizes_eq
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonGenP1.roots_sorted
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonGenP1.auxMOf_degree_lt
