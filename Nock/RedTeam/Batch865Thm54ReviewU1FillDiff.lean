/-
  Nock/RedTeam/Batch865Thm54ReviewU1FillDiff.lean

  Notes only; no production edit.

  So the honest fill
  changes exactly where `certEqRun` changes.  Fixture `p = 769`, leaf `768` (shift `9 = n − 1`):

  * `E0_new`: the re-indexed (production) `certEqRun 768 3 = 1`;
  * `E0_old`: a verbatim replica of the pre-"A" witness (`p_{n−1−j}`) gives `0`.
-/
import Nock.RedTeam.Batch781Thm54U1Reproduce

set_option autoImplicit false

namespace Nock.RedTeam.Batch865

open Nock
open Nock.NockVMROM.Thm54.OptimizedComputeRangeCertificate
open Nock.RedTeam.Batch781

variable {F : Type*} [Field F]

/-- Pre-"A" `certLin`, verbatim (`p_{n−1−j}`). -/
noncomputable def certLinOld (a j : ℕ) : F :=
  if pBit F (formRN F - 1 - j) then bit01 (certCBit a j) else (1 : F) - bit01 (certCBit a j)

/-- Pre-"A" `certEqRun`, verbatim. -/
noncomputable def certEqRunOld (a : ℕ) : ℕ → F
  | 0 => (1 : F)
  | n + 1 => certEqRunOld a n * certLinOld a n

theorem size_768 : Nat.size 768 = 10 :=
  le_antisymm (Nat.size_le.mpr (by norm_num)) (Nat.lt_size.mpr (by norm_num))

theorem cbits (j : ℕ) (hj : j < 3) : certCBit 768 j = decide (j = 0) := by
  have h : certShift 768 = 9 := by simp [certShift, size_768]
  interval_cases j <;> simp [certCBit, h] <;> decide

theorem E0_new : certEqRun (F := F769) 768 3 = 1 := by
  simp only [certEqRun, certLin, pBit, formRN_769, ringChar_769,
    cbits 0 (by norm_num), cbits 1 (by norm_num), cbits 2 (by norm_num)]
  norm_num [bit01]
  decide

theorem E0_old : certEqRunOld (F := F769) 768 3 = 0 := by
  simp only [certEqRunOld, certLinOld, pBit, formRN_769, ringChar_769,
    cbits 0 (by norm_num), cbits 1 (by norm_num), cbits 2 (by norm_num)]
  norm_num [bit01]
  decide

end Nock.RedTeam.Batch865

#print axioms Nock.RedTeam.Batch865.E0_new
#print axioms Nock.RedTeam.Batch865.E0_old
