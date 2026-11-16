/-
  Nock/NockVMROM/Thm54/VclL/Handle/RowDecodeVSX.lean

  **Card C-2 part 2 : a `computeChipVCLHX` row decodes to
  `LocalVSX.RowVSX`, and the kid-kind clause is a gate fact.**  New module, additive.

  * `stIdx` — the one-hot column of a `StateX` (`cons` at `10`, the J-8 states at `11..16`);
    `rowOfX env st` — the decoded row: state `st`, twelve handles `hdV env (hdX j)` over `ZMod p`.
  * **`kidKinds_of_gates`** — on a row whose base gates vanish, in state `st` (`tr env (stIdx st) = 1`),
    every REAL child position's formula handle has wire kind `1`: `KidKinds (rowOfX env st)`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.LocalOKX

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVSX

open Nock Nock.Reified Nock.Edit
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH (Hd)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX
open Nock.NockVMROM.Thm54.VclL.Handle.LocalOKX (hdV)

/-- The one-hot column of a state (`ChipHX` layout: `OP_0..OP_9` at `0..9`, `cons` at `10`,
`s10 s10L s10T s11s s11d s11j` at `11..16`). -/
def stIdx : StateX → ℕ
  | .s0 => 0 | .s1 => 1 | .s2 => 2 | .s3 => 3 | .s4 => 4 | .s5 => 5 | .s6 => 6 | .s7 => 7
  | .s8 => 8 | .s9 => 9 | .cons => 10 | .s10 => 11 | .s10L => 12 | .s10T => 13 | .s11s => 14
  | .s11d => 15 | .s11j => 16

theorem stIdx_lt (st : StateX) : stIdx st < nStates := by cases st <;> decide

theorem stIdx_injective : Function.Injective stIdx := by
  intro a b h; cases a <;> cases b <;> first | rfl | (simp [stIdx] at h)

variable {p : ℕ} [Fact p.Prime]

/-- **The decoded row** of `computeChipVCLHX` in state `st`. -/
def rowOfX (env : Env (ZMod p)) (st : StateX) : RowVSX :=
  ⟨st, hdV env xS, hdV env xF, hdV env xE, hdV env xSf1, hdV env xSf2, hdV env xFh, hdV env xFt,
    hdV env xFth, hdV env xFtt, hdV env xFtth, hdV env xFttt, hdV env xM⟩

/-- A kid-kind gate's handle decodes to wire kind `1`. -/
theorem kid_val {env : Env (ZMod p)} (hB : BaseHoldsX env) {j : ℕ} {h : Hd} (hj : tr env j = 1)
    (hm : (j, h) ∈ kidFormsX) : (hdV env h).1 = 1 := by
  haveI : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  simp only [hdV, kid_cell hB hj hm, ZMod.val_one]

/-- **`KidKinds` from the gates** (C-2 part 2, the FINDING's repair). -/
theorem kidKinds_of_gates {env : Env (ZMod p)} (hB : BaseHoldsX env) (st : StateX)
    (hst : tr env (stIdx st) = 1) : KidKinds (rowOfX env st) := by
  have k : ∀ h : Hd, (stIdx st, h) ∈ kidFormsX → (hdV env h).1 = 1 := fun h hm => kid_val hB hst hm
  intro i hi hc
  cases st <;> simp only [kidsX, rowOfX, List.length_cons, List.length_nil] at hi hc ⊢ <;>
    first
    | omega
    | (interval_cases i <;>
        simp only [List.getElem_cons_zero, List.getElem_cons_succ, chainPosX,
          Bool.true_eq_false] at hc ⊢ <;>
        exact k _ (by decide))

end Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVSX
