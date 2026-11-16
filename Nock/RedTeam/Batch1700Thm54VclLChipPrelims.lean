/-
  Nock/RedTeam/Batch1700Thm54VclLChipPrelims.lean

  **Receipts for the VCL-L chip layouts and the
  interface-independent preliminaries of `vclMemFamily`.**  Production:
  `Thm54/VclL/Chips/{Layout, Prelim}.lean`.

  §A  `#print axioms` of the layout counts (cell table `128 / 54 / 18 = 200`, path chip
      `17 / 72 / 12 = 101`), `quad_ringChar`, `decodeB0_boundedBy`, `decode_exists`,
      `zero_mem_cellDyckRootSeeds`, `seed_ne_zero_of_not_mem_dyck`.
  §B  **The record widths at the tower (finding).**  A fingerprint over `𝕂′ = 𝕂(√δ)` is six `𝕂`
      entries, so the IO records over `𝕂` (the IO coins' field) have widths `9 / 19 / 14`
      (validity `(p, hi, lo, idx)`, export `(p, l, r, idx)`, path `(root, child, acc, rootIdx)`),
      not V3's `mVCL = 6 / 10 / 8` (pre-tower `𝕂` coordinates).  At V3's closed form with these
      widths the budget figure is `< 2^-121` and NOT `≤ 2^-122` (lane scratch: 121.13 at `2^31`,
      119.13 at `2^32`; the design script `epsilon_vcll.py` at `mv 9 / mx 19 / mp 14`).
-/
import Nock.NockVMROM.Thm54.VclL.Chips.Layout
import Nock.NockVMROM.Thm54.VclL.Chips.Prelim
import Nock.NockVMROM.Thm54.VclL.Events.Bound
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.Unhosted309Events

set_option autoImplicit false

namespace Nock.RedTeam.Batch1700

open Nock.NockVMROM.Thm54.VclL.Events
open Nock.NockVMROM.Thm54.VclL.Chips
open Nock.NockVMROM.Thm54.FiniteIO

/-! ## §A -/

#print axioms Cell.width_eq
#print axioms Cell.card_round0
#print axioms Cell.card_round1
#print axioms Cell.card_round2
#print axioms Path.width_eq
#print axioms Path.card_round0
#print axioms Path.card_round1
#print axioms Path.card_round2
#print axioms record_widths
#print axioms quad_ringChar
#print axioms decodeB0_boundedBy
#print axioms preZNounOfTable_getD_boundedBy
#print axioms decode_exists
#print axioms zero_mem_cellDyckRootSeeds
#print axioms seed_ne_zero_of_not_mem_dyck

/-! ## §B  The tower record widths -/

/-- The three IO summands at the tower record widths `9 / 19 / 14` (T5's `kc = 2`). -/
def ioWorkTower (c N D P : ℕ) : ℕ :=
  ioFailureUnionBound mValidity 0 (3 * D + 2) c + ioFailureUnionBound mExport 0 (2 * N + P + D) c +
    ioFailureUnionBound mPath 0 (N + P) c

/-- **At the tower widths the budget figure is NOT 122** (121.13). -/
theorem figTower_not_122 :
    ¬ boundGen cK (2 ^ 31) (2 ^ 31) 0 (2 ^ 110) (ioWorkTower cK (2 ^ 31) (2 ^ 31) (2 ^ 31)) ≤
      1 / (2 : ℚ) ^ 122 := by
  apply not_boundGen_le_of_num
  rw [numGen_corner_eval, cK_eq]
  decide +kernel

/-- It is 121 (a figure, not a floor: the corner value). -/
theorem figTower_121 :
    boundGen cK (2 ^ 31) (2 ^ 31) 0 (2 ^ 110) (ioWorkTower cK (2 ^ 31) (2 ^ 31) (2 ^ 31)) <
      1 / (2 : ℚ) ^ 121 := by
  apply boundGen_lt_of_num
  rw [numGen_corner_eval, cK_eq]
  decide +kernel

/-- At `2^32` the tower widths give 119, not 120. -/
theorem figTower_not_120_at_32 :
    ¬ boundGen cK (2 ^ 32) (2 ^ 32) 0 (2 ^ 110) (ioWorkTower cK (2 ^ 32) (2 ^ 32) (2 ^ 32)) ≤
      1 / (2 : ℚ) ^ 120 := by
  apply not_boundGen_le_of_num
  rw [numGen_corner_eval, cK_eq]
  decide +kernel

#print axioms figTower_not_122
#print axioms figTower_121
#print axioms figTower_not_120_at_32

end Nock.RedTeam.Batch1700
