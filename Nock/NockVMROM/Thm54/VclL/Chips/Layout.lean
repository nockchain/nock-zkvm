/-
  Nock/NockVMROM/Thm54/VclL/Chips/Layout.lean

  Imports Mathlib only, so the frame's `shapeVCL` (L-C) can import it.

  Units.  A base-field column is one `𝔽` column.  A `𝕂`-role is `e = 3` `𝔽` columns.
  A tower element of `𝕂′ = 𝕂(√δ)` (T0, `Quad`) is two `𝕂`-roles (Re/Im).  A fingerprint
  `FP 𝕂′ = (size, dyck, leaf)` is therefore `3 · 2 · 3 = 18` `𝔽` columns.

  Rounds:
  * round 0 (B0, before any coin): the two verifier-fixed masks `isFirst`, `isLast`, serials, side
    and weight bits, atom values, rank limbs and their 110 range bits, multiplicities, the axis fold;
  * round 1 (B1, after `z₁ z₂ a b c`, i.e. `frameVCL.sampledAfter = 0`): the fingerprints;
  * round 2 (B2, after `αC γ IOγ IOpole`): the LogUp inverses and accumulators.

  **Cell table**: B0 `128` = masks 2, `idx idL idR` 3, `wL wR` 2, `aL aR` 2, `lo hi` 2,
  `loL hiL loR hiR` 4, `carry` 1, rank bits `62 + 48 = 110`, `mv mx` 2; B1 `54` = `p l r`;
  B2 `18` = six `𝕂`-roles (validity provide inverse, validity consume-L and consume-R inverses,
  export provide inverse, validity accumulator, export accumulator).  **Width 200.**
  The children's limbs `loL … hiR` carry no range bits: a weighted child's limbs equal its provider's
  (validity key), and a zero-weight child's are pinned to `0` by the atom gate.

  **Path chip**: B0 `16` = masks 2, `side first last` 3, `len` 1, `acc` 1, the six certificate
  bits of `62 − len`, `m` 1, `cellIdx` 1, `rootIdx` 1; B1 `72` = `root p l r`; B2 `12` = four `𝕂`-roles
  (export consume inverse, path provide inverse, export accumulator, path accumulator).
  **Width 100**.
-/
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.DeriveFintype
import Nock.Tactic.DeriveFintypeFix

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.VclL.Chips

/-! ## Units -/

/-- `e`: `𝔽` columns per `𝕂`-role. -/
def eK : ℕ := 3
/-- `𝔽` columns per tower element (two `𝕂`-roles). -/
def towerCols : ℕ := 2 * eK
/-- `𝔽` columns per fingerprint `FP 𝕂′`. -/
def fpCols : ℕ := 3 * towerCols

theorem fpCols_eq : fpCols = 18 := rfl

/-! ## The cell table (memory table 0) -/

namespace Cell

/-- Round-0 base columns, in order. -/
inductive B0Col
  | isFirst | isLast | idx | idL | idR | wL | wR | aL | aR
  | lo | hi | loL | hiL | loR | hiR | carry | mv | mx
  deriving DecidableEq, Fintype

/-- The rank bits: `62` for `lo`, `48` for `hi`. -/
def loBits : ℕ := 62
def hiBits : ℕ := 48

def b0Named : ℕ := Fintype.card B0Col
theorem b0Named_eq : b0Named = 18 := rfl

def b0Count : ℕ := b0Named + loBits + hiBits
/-- B1: `p l r`. -/
def b1Count : ℕ := 3 * fpCols
/-- B2: six `𝕂`-roles. -/
def kRolesB2 : ℕ := 6
def b2Count : ℕ := kRolesB2 * eK

def width : ℕ := b0Count + b1Count + b2Count

theorem b0Count_eq : b0Count = 128 := rfl
theorem b1Count_eq : b1Count = 54 := rfl
theorem b2Count_eq : b2Count = 18 := rfl
theorem width_eq : width = 200 := rfl

/-- The column → round map. -/
def colRound (j : Fin width) : ℕ :=
  if (j : ℕ) < b0Count then 0 else if (j : ℕ) < b0Count + b1Count then 1 else 2

/-- Position of a named B0 column. -/
def b0Pos : B0Col → ℕ
  | .isFirst => 0 | .isLast => 1 | .idx => 2 | .idL => 3 | .idR => 4 | .wL => 5 | .wR => 6
  | .aL => 7 | .aR => 8 | .lo => 9 | .hi => 10 | .loL => 11 | .hiL => 12 | .loR => 13
  | .hiR => 14 | .carry => 15 | .mv => 16 | .mx => 17

/-- Rank bit `i` (`i < 110`; `lo` bits first). -/
def bitPos (i : ℕ) : ℕ := b0Named + i

/-- B1 fingerprint `k ∈ {p, l, r} = {0, 1, 2}`, coordinate `c ∈ {size, dyck, leaf}`,
Re/Im `ri`, `𝕂` coordinate `u < 3`. -/
def fpPos (k c ri u : ℕ) : ℕ := b0Count + fpCols * k + towerCols * c + eK * ri + u

/-- B2 `𝕂`-role `r < 6`, coordinate `u < 3`: `0` validity provide inverse, `1` consume-L inverse,
`2` consume-R inverse, `3` export provide inverse, `4` validity accumulator, `5` export accumulator. -/
def b2Pos (r u : ℕ) : ℕ := b0Count + b1Count + eK * r + u

theorem b0Pos_lt (c : B0Col) : b0Pos c < b0Named := by cases c <;> decide
theorem b0Pos_injective : Function.Injective b0Pos := by
  intro a b h; cases a <;> cases b <;> first | rfl | (simp [b0Pos] at h)

theorem colRound_b0 (c : B0Col) (h : b0Pos c < width) : colRound ⟨b0Pos c, h⟩ = 0 := by
  have := b0Pos_lt c
  unfold colRound
  rw [if_pos (by unfold b0Count; simp only; omega)]

/-- Round counts: `128 / 54 / 18`. -/
theorem card_round0 : (Finset.univ.filter fun j : Fin width => colRound j = 0).card = 128 := by
  decide +kernel
theorem card_round1 : (Finset.univ.filter fun j : Fin width => colRound j = 1).card = 54 := by
  decide +kernel
theorem card_round2 : (Finset.univ.filter fun j : Fin width => colRound j = 2).card = 18 := by
  decide +kernel

end Cell

/-! ## The path chip (memory table 1) -/

namespace Path

inductive B0Col
  | isFirst | isLast | side | first | last | len | acc | m | cellIdx | rootIdx
  deriving DecidableEq, Fintype


def lenBits : ℕ := 6

def b0Named : ℕ := Fintype.card B0Col
theorem b0Named_eq : b0Named = 10 := rfl

def b0Count : ℕ := b0Named + lenBits
/-- B1: `root p l r`. -/
def b1Count : ℕ := 4 * fpCols
def kRolesB2 : ℕ := 4
def b2Count : ℕ := kRolesB2 * eK

def width : ℕ := b0Count + b1Count + b2Count

theorem b0Count_eq : b0Count = 16 := rfl
theorem b1Count_eq : b1Count = 72 := rfl
theorem b2Count_eq : b2Count = 12 := rfl
theorem width_eq : width = 100 := rfl

def colRound (j : Fin width) : ℕ :=
  if (j : ℕ) < b0Count then 0 else if (j : ℕ) < b0Count + b1Count then 1 else 2

def b0Pos : B0Col → ℕ
  | .isFirst => 0 | .isLast => 1 | .side => 2 | .first => 3 | .last => 4 | .len => 5 | .acc => 6
  | .m => 7 | .cellIdx => 8 | .rootIdx => 9

def bitPos (i : ℕ) : ℕ := b0Named + i

/-- B1 fingerprint `k ∈ {root, p, l, r} = {0, 1, 2, 3}`. -/
def fpPos (k c ri u : ℕ) : ℕ := b0Count + fpCols * k + towerCols * c + eK * ri + u

/-- B2 `𝕂`-role `r < 4`: `0` export consume inverse, `1` path provide inverse, `2` export
accumulator, `3` path accumulator. -/
def b2Pos (r u : ℕ) : ℕ := b0Count + b1Count + eK * r + u

theorem b0Pos_lt (c : B0Col) : b0Pos c < b0Named := by cases c <;> decide
theorem b0Pos_injective : Function.Injective b0Pos := by
  intro a b h; cases a <;> cases b <;> first | rfl | (simp [b0Pos] at h)

theorem card_round0 : (Finset.univ.filter fun j : Fin width => colRound j = 0).card = 16 := by
  decide +kernel
theorem card_round1 : (Finset.univ.filter fun j : Fin width => colRound j = 1).card = 72 := by
  decide +kernel
theorem card_round2 : (Finset.univ.filter fun j : Fin width => colRound j = 2).card = 12 := by
  decide +kernel

end Path

/-! ## The record widths these layouts force (over `𝕂`, the IO coins' field) -/

/-- Validity key `(p, hi, lo, idx)`: a fingerprint is `3` tower elements = `6` `𝕂` entries. -/
def mValidity : ℕ := 3 * 2 + 3
/-- Export key `(p, l, r, idx)`. -/
def mExport : ℕ := 3 * (3 * 2) + 1
/-- Path record `(root, child, acc, rootIdx)`. -/
def mPath : ℕ := 2 * (3 * 2) + 2


theorem record_widths : mValidity = 9 ∧ mExport = 19 ∧ mPath = 14 := ⟨rfl, rfl, rfl⟩

end Nock.NockVMROM.Thm54.VclL.Chips
