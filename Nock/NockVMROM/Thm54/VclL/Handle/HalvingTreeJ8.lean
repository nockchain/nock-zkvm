/-
  Nock/NockVMROM/Thm54/VclL/Handle/HalvingTreeJ8.lean

  **`HalvingOK` from the chain child, at the
  chip-row level.**

  `RowSemChipX.rowSemX_of_chip` carries the named hypothesis `HalvingOK` on `s10L` rows.  Here it is
  discharged from the parent's walk-tree CHILD row (the `labAtom xS vX xE` child: formula handle
  `(0, v)`), with no hypothesis on the parent beyond the link:

  * `chainChild_state`: a row whose formula handle has wire kind `0` is a chain row (`s10L` or
    `s10T`) — the gate `xF.k − 1 + s10L + s10T` (`svG`), no other input.
  * `halvingOK_of_child`: if the child row is accepted (`BaseHoldsX`, one-hot), its formula handle is
    `(0, v_parent)` (the label link), and — when the child is `s10L` — its sibling read `m.v` is a
    walk record axis in `[2, 2^62)` (what `WalkJ8.walkJ8_axis_lt` gives every provided record under
    the narrowed certificate), then `HalvingOK` holds on the parent.

  The label link (`hk`, `hv`: the chip-to-`encT` bridge of C-2) and
  the axis fact `hax` (the walk balance identifies the consumed `walkRecX xSf1 xM.v _` with a provided
  record, whose axis `walkJ8_axis_lt` bounds).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.HalvingJ8

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.HalvingTreeJ8

open Nock Nock.Reified Nock.Edit
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVSX
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX
open Nock.NockVMROM.Thm54.VclL.Handle.HalvingJ8

section
variable {p : ℕ} [Fact p.Prime]

/-- **A row with an atom formula handle is a chain row** (gate `xF.k − 1 + s10L + s10T`). -/
theorem chainChild_state {env : Env (ZMod p)} (hB : BaseHoldsX env) {st : StateX}
    (hOH : OneHotAt env (stIdx st)) (hk : env.trace xF.k = 0) : st = .s10L ∨ st = .s10T := by
  have aF := arith_of_base (F := ZMod p) hB (svG_sub _ (by simp [svG] :
    (.add (.add (.sub (cc xF.k) (.const 1)) (cc sS10L)) (cc sS10T)) ∈ (svG (F := ℚ))))
  simp only [cc, evalQX, Rat.cast_one] at aF
  by_contra hne
  push_neg at hne
  have h12 : env.trace sS10L = 0 :=
    oh_zero hOH (by decide) (by cases st <;> simp_all [stIdx, sS10L])
  have h13 : env.trace sS10T = 0 :=
    oh_zero hOH (by decide) (by cases st <;> simp_all [stIdx, sS10T])
  rw [hk, h12, h13] at aF
  simp at aF

/-- **`HalvingOK` on an `s10L` parent from its chain child.**  The child row `ce` is accepted
(`hB`, one-hot at `stc`), its formula handle is `(0, v)` with `v` the parent's `vX` (the label
link), and if it is `s10L` its sibling-read axis `m.v` is a walk record axis in `[2, 2^62)`. -/
theorem halvingOK_of_child (hp : 2 ^ 63 + 1 < p) {pe ce : Env (ZMod p)} (hB : BaseHoldsX ce)
    {stc : StateX} (hOH : OneHotAt ce (stIdx stc)) (hk : ce.trace xF.k = 0)
    (hv : ce.trace xF.v = pe.trace vX)
    (hax : stc = .s10L → 2 ≤ (ce.trace xM.v).val ∧ (ce.trace xM.v).val < 2 ^ 62) :
    HalvingOK pe .s10L := by
  rcases chainChild_state hB hOH hk with rfl | rfl
  · obtain ⟨-, -, -, hmv, -⟩ := s10L_row hB (oh_one hOH (by decide))
      (oh_zero hOH (by decide) (by decide)) (oh_zero hOH (by decide) (by decide))
    have hβ := col_bool hB (i := betaX) (by simp [oneHotG])
    obtain ⟨hlo, hhi⟩ := hax rfl
    simp only [tr] at hmv
    refine halvingOK_of_child_s10L_env hp hβ (ax2' := ce.trace xM.v) ?_ hlo hhi
    rw [hmv, hv]; ring
  · obtain ⟨-, h1⟩ := s10T_row hB (oh_one hOH (by decide)) (oh_zero hOH (by decide) (by decide))
    simp only [tr] at h1
    exact halvingOK_of_child_s10T_env (by omega) (by rw [← hv, h1])

end

end Nock.NockVMROM.Thm54.VclL.Handle.HalvingTreeJ8
