/-
  Nock/V1J8/FillX.lean

  **The executable compute fill (S6, compute).**

  `HonestCompX.colX` (the honest round-0 columns `0.. 68` of a `genX` noun row) is `noncomputable` in effect: its
  case splits decide propositions with `Classical`.  `colXE` is the same formula with the decidable instances, over any
  field with `DecidableEq`; **`colXE_eq : colXE H pd r fst lst = HonestCompX.colX H pd r fst lst`**.  The S6 native
  harness (`docs/j8/tgj8-check-harness.lean.txt`) fills the example's compute row with it.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.HonestCompX

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Nock.V1J8.FillX

open Nock Nock.Edit Nock.Edit.GenX
open Nock.NockVMROM.Thm54.VclL.Handle.HonestCompX
open Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVSX (stIdx)

section ColX
variable {F : Type} [Field F] [DecidableEq F] (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ))

def isPairB (r : RowNX) : Bool :=
  decide (r.st = .s5) && decide (r.e = .atom 1) && decide ((H r.ftth).1 = 2) && decide ((H r.fttt).1 = 2)

def op5TE (r : RowNX) : F × F × F :=
  if (H r.ftth).1 = 2 ∧ (H r.fttt).1 = 2 then
    let l1 := (pd r).2.1
    let l2 := (pd r).2.2
    let pv : F := if l1.1 = 0 then (l1.2 : F) else (l2.2 : F) + 1
    let pv2 : F := if l2.1 = 0 then (l2.2 : F) else pv - 1
    (pv, pv2, (pv - pv2)⁻¹)
  else if (H r.ftth).1 = 0 ∧ (H r.fttt).1 = 0 then
    (hv H r.ftth, hv H r.fttt, (hv H r.ftth - hv H r.fttt)⁻¹)
  else if ((H r.ftth).1 = 1 ∧ (H r.fttt).1 = 2) ∨ ((H r.ftth).1 = 2 ∧ (H r.fttt).1 = 1) then
    (1, 0, -1)
  else (hv H r.ftth, hv H r.fttt, 0)

def cZ1E (r : RowNX) : F :=
  match r.st with
  | .s0 => if r.ft = .atom 1 then 1 else 0
  | .s5 => if r.e = .atom 1 ∧ r.m = .atom 1 then 1 else 0
  | .s9 => if r.fth = .atom 1 then 1 else 0
  | .s10 => if r.ftth = .atom 1 then 1 else 0
  | _ => 0

def cVE (r : RowNX) : F :=
  match r.st with
  | .s0 => hv H r.ft
  | .s4 => hv H r.sf1
  | .s5 => if r.e = .atom 1 then (op5TE H pd r).1 else 0
  | .s6 => hv H r.sf2
  | .s9 => hv H r.fth
  | .s10 => hv H r.ftth
  | .s10L => ((chainAxis r.f / 2 : ℕ) : F)
  | _ => 0

def cBE (r : RowNX) : F :=
  match r.st with
  | .s3 => if r.sf1.isCell then 0 else 1
  | .s5 => if r.e = .atom 1 then 1 else 0
  | .s10L => ((chainAxis r.f % 2 : ℕ) : F)
  | _ => 0

def cV2E (r : RowNX) : F :=
  match r.st with
  | .s4 => hv H r.sf1 + 1
  | .s5 => if r.e = .atom 1 then (op5TE H pd r).2.1 else 0
  | .s10L => ((chainAxis r.f : ℕ) : F)
  | _ => 0

def cWE (r : RowNX) : F :=
  match r.st with
  | .s5 => if r.e = .atom 1 then (op5TE H pd r).2.2 else 0
  | .s10L => (((chainAxis r.f : ℕ) : F) - 1)⁻¹
  | _ => 0

def cPrE (r : RowNX) : F :=
  match r.st with
  | .s5 => if r.e = .atom 1 ∧ r.m ≠ .atom 1 then 1 else 0
  | .s10L => 1
  | _ => 0

def cFastE (r : RowNX) : F :=
  match r.st with
  | .s4 => if (H r.e).1 = 0 then 1 else 0
  | _ => 0

def cInv4E (r : RowNX) : F :=
  match r.st with
  | .s4 => (hv H r.sf1 + 1)⁻¹
  | _ => 0

def cAx2E (r : RowNX) : F :=
  match r.st with
  | .s10L => ((chainAxis r.f ^^^ 1 : ℕ) : F)
  | .s5 => if isPairB H r then ((pd r).1 : F) else 0
  | _ => 0

def cPr2E (r : RowNX) : F := if isPairB H r then 1 else 0

def cLE (r : RowNX) (j : ℕ) : F :=
  if isPairB H r then
    (match j with
     | 0 => ((pd r).2.1.1 : F) | 1 => ((pd r).2.1.2 : F) | 2 => ((pd r).2.2.1 : F) | _ => ((pd r).2.2.2 : F))
  else 0

def colXE (r : RowNX) (fst lst : F) : ℕ → F := fun i =>
  if i < 17 then (if stIdx r.st = i then 1 else 0)
  else if i = 17 then fst else if i = 18 then lst
  else if i = 19 then cZ1E r else if i = 20 then cVE H pd r else if i = 21 then cBE r
  else if i = 22 then cV2E H pd r else if i = 23 then cWE H pd r else if i = 24 then cPrE r
  else if i < 49 then
    (if (i - 25) % 2 = 0 then hk H (hN r ((i - 25) / 2)) else hv H (hN r ((i - 25) / 2)))
  else if i < 61 then hb H (hN r (i - 49))
  else if i = 61 then cFastE H r else if i = 62 then cInv4E H r
  else if i = 63 then cAx2E H pd r else if i = 64 then cPr2E H r
  else if i < 69 then cLE H pd r (i - 65)
  else 0


/-! ## Equal to the honest builder -/

theorem isPairB_iff (r : RowNX) : isPairB H r = true ↔ isPair H r := by
  simp [isPairB, isPair, and_assoc]

theorem op5TE_eq (r : RowNX) : op5TE (F := F) H pd r = op5T H pd r := by
  unfold op5TE op5T
  split_ifs <;> rfl

theorem cZ1E_eq (r : RowNX) : cZ1E (F := F) r = cZ1 r := by
  unfold cZ1E cZ1
  cases r.st <;> simp only <;> first | rfl | (split_ifs <;> rfl)

theorem cVE_eq (r : RowNX) : cVE (F := F) H pd r = cV H pd r := by
  unfold cVE cV
  cases r.st <;> simp only [op5TE_eq] <;> first | rfl | (split_ifs <;> rfl)

theorem cBE_eq (r : RowNX) : cBE (F := F) r = cB r := by
  unfold cBE cB
  cases r.st <;> simp only <;> first | rfl | (split_ifs <;> rfl)

theorem cV2E_eq (r : RowNX) : cV2E (F := F) H pd r = cV2 H pd r := by
  unfold cV2E cV2
  cases r.st <;> simp only [op5TE_eq] <;> first | rfl | (split_ifs <;> rfl)

theorem cWE_eq (r : RowNX) : cWE (F := F) H pd r = cW H pd r := by
  unfold cWE cW
  cases r.st <;> simp only [op5TE_eq] <;> first | rfl | (split_ifs <;> rfl)

theorem cPrE_eq (r : RowNX) : cPrE (F := F) r = cPr r := by
  unfold cPrE cPr
  cases r.st <;> simp only <;> first | rfl | (split_ifs <;> rfl)

theorem cFastE_eq (r : RowNX) : cFastE (F := F) H r = cFast H r := by
  unfold cFastE cFast
  cases r.st <;> simp only <;> first | rfl | (split_ifs <;> rfl)

theorem cInv4E_eq (r : RowNX) : cInv4E (F := F) H r = cInv4 H r := by
  unfold cInv4E cInv4
  cases r.st <;> rfl

theorem cAx2E_eq (r : RowNX) : cAx2E (F := F) H pd r = cAx2 H pd r := by
  unfold cAx2E cAx2
  have := isPairB_iff H r
  cases r.st <;> simp only <;> split_ifs <;> simp_all

theorem cPr2E_eq (r : RowNX) : cPr2E (F := F) H r = cPr2 H r := by
  unfold cPr2E cPr2
  have := isPairB_iff H r
  split_ifs <;> simp_all

theorem cLE_eq (r : RowNX) (j : ℕ) : cLE (F := F) H pd r j = cL H pd r j := by
  unfold cLE cL
  have := isPairB_iff H r
  split_ifs
  · rcases j with _ | _ | _ | j <;> rfl
  all_goals simp_all

/-- **`colXE_eq`: the executable compute fill is the honest builder `colX`.** -/
theorem colXE_eq (r : RowNX) (fst lst : F) : colXE H pd r fst lst = colX H pd r fst lst := by
  funext i
  unfold colXE colX
  rw [cZ1E_eq, cVE_eq, cBE_eq, cV2E_eq, cWE_eq, cPrE_eq, cFastE_eq, cInv4E_eq, cAx2E_eq, cPr2E_eq, cLE_eq]

end ColX

end Nock.V1J8.FillX
