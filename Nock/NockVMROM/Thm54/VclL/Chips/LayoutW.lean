/-
  Nock/NockVMROM/Thm54/VclL/Chips/LayoutW.lean

  Imports Mathlib only (as `Layout.lean`).

  Units as `Layout.lean`: a `𝕂`-role is `e = 3` `𝔽` columns; a `𝕂′ = 𝕂(√δ)` value is two `𝕂`-roles
  (Re/Im); a fingerprint `FP 𝕂′` is `18` `𝔽` columns.

  **B0 (round 0) `21`** = the three verifier-fixed masks `isFirst isLast rootMask`; the label's base
  entries `prefix rootIdx len`; the consumed export key's cell serial `idx`; the 2-bit state `cL cR`
  and its product `e = cL·cR`; the record multiplicities `mL mR`; the base-field queue counter
  `q qinv`; the six certificate bits of `61 − len` and the helper
  `u = b₁·b₂` of the `{62, 63}` exclusion.
  **B1 (round 1) `72`** = `p l r root` (four fingerprints, `24` `𝕂`-roles).
  **B2 (round 2) `39`** = the walk's `ln count acc` (three `𝕂`-roles), and five `𝕂′` quantities (ten
  `𝕂`-roles): the export-consume inverse, the two path-provide inverses (left / right record), the
  export accumulator and the path accumulator.
  **Width 132** (path chip: `112` = `ChipRAP.pathChip_fingerprint`).

  Deviations from WALK-F §9's `19 / 72 / 24 = 115` (MEASURED here, `width_eq`):
  * B2 `24 → 39`: WALK-F counted each LogUp inverse / accumulator as one `𝕂`-role; the IO coins are `𝕂′` (`ChipRAP` `ρ′ = (χ₅, χ₇)`, `γ′` powers), so
    each is two `𝕂`-roles, exactly as the path chip's B2 (`8` roles).
  * B0 `19 → 21`: `e = cL·cR` keeps the walk accumulator step at degree 4 (`count · cc′` under
    `1 − isLast`; with `cL·cR` inline it is degree 5), and `u = b₁·b₂` excludes the certificate values
    `62, 63` (six bits of `61 − len` alone admit `len ≡ −1, −2`, i.e. `len.val ≥ 62`; the path chip
    avoided this with a chain-length bound the walk does not have before the forest exists). -/
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.DeriveFintype
import Nock.Tactic.DeriveFintypeFix

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.VclL.Chips.WalkW

/-- `e`: `𝔽` columns per `𝕂`-role. -/
def eK : ℕ := 3

/-- Round-0 named base columns, in order. -/
inductive B0Col
  | isFirst | isLast | rootMask | idx | pre | ridx | len | cL | cR | e | mL | mR | q | qinv | u
  deriving DecidableEq, Fintype

def b0Pos : B0Col → ℕ
  | .isFirst => 0 | .isLast => 1 | .rootMask => 2 | .idx => 3 | .pre => 4 | .ridx => 5
  | .len => 6 | .cL => 7 | .cR => 8 | .e => 9 | .mL => 10 | .mR => 11 | .q => 12 | .qinv => 13
  | .u => 14

/-- The six certificate bits of `61 − len`. -/
def lenBits : ℕ := 6

def b0Named : ℕ := Fintype.card B0Col
theorem b0Named_eq : b0Named = 15 := rfl

/-- Certificate bit `i` (`i < 6`). -/
def bitPos (i : ℕ) : ℕ := b0Named + i

/-- `𝕂`-roles of round 1: `p l r root`, a fingerprint each (`6` roles). -/
def kRolesB1 : ℕ := 4 * 6
/-- `𝕂`-roles of round 2: `ln count acc` (3) and five `𝕂′` quantities (10). -/
def kRolesB2 : ℕ := 3 + 5 * 2

def b0Count : ℕ := b0Named + lenBits
def b1Count : ℕ := kRolesB1 * eK
def b2Count : ℕ := kRolesB2 * eK

def width : ℕ := b0Count + b1Count + b2Count

theorem b0Count_eq : b0Count = 21 := rfl
theorem b1Count_eq : b1Count = 72 := rfl
theorem b2Count_eq : b2Count = 39 := rfl
/-- **The walk chip's width, MEASURED: `132`** (`21 / 72 / 39`). -/
theorem width_eq : width = 132 := rfl

theorem width_le_stop : width * 10 ≤ 12 * 115 := by decide

/-- The column → round map. -/
def colRound (j : Fin width) : ℕ :=
  if (j : ℕ) < b0Count then 0 else if (j : ℕ) < b0Count + b1Count then 1 else 2

theorem b0Pos_lt (c : B0Col) : b0Pos c < b0Named := by cases c <;> decide
theorem b0Pos_injective : Function.Injective b0Pos := by
  intro a b h; cases a <;> cases b <;> first | rfl | (simp [b0Pos] at h)

theorem card_round0 : (Finset.univ.filter fun j : Fin width => colRound j = 0).card = 21 := by
  decide +kernel
theorem card_round1 : (Finset.univ.filter fun j : Fin width => colRound j = 1).card = 72 := by
  decide +kernel
theorem card_round2 : (Finset.univ.filter fun j : Fin width => colRound j = 2).card = 39 := by
  decide +kernel

end Nock.NockVMROM.Thm54.VclL.Chips.WalkW
