/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9AL/AluBaseAL.lean

  **`AluSZEvent`'s mirror reads only the ALU's base columns.**

  `AluSZEvent`'s `arithBadC` (`AluSZEvent`) is a function of the ALU rows `al : List (ARow q)` through `cl al i j` at base
  columns `j < 94` and `al.length` only.  `arithBadC_agree`: two row lists that agree on the base columns (and in
  length) have the same bad set.  The assembly uses it to meet `AluSZOps`'s `Ctx.hal : Readout R al` (which fixes EVERY column `j`,
  so it cannot hold for a coin-free readout) while the consumed summand (`RR49AL.arithAL`) is built on the coin-free
  base readout `RR49AL.aluAL`: `AluSZOps`'s `op_sound6` is applied at the constant readout `fun _ => X.al`, and its event
  is the consumed one by `arithBadC_agree`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.AluSZEvent

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.AluBaseAL

open Polynomial
open Nock.NockVMROM.Thm54.VclL.Handle.AluSZEvent
open Nock.NockVMROM.Thm54.VclL.Handle.AluSZChipJ9
  (sH sL fst eos f1 f2 mR mS mV mW mQ1 mQM bt0 sv cf1 cf2 oLt oDiv oMod lb)

noncomputable section

variable {q : ℕ}

/-- Two ALU row lists with the same length and the same base columns (`< 94`). -/
def Agree94 (al al' : List (ARow q)) : Prop :=
  al.length = al'.length ∧ ∀ i j, j < 94 → cl al i j = cl al' i j

section Agree
variable {al al' : List (ARow q)} (h : Agree94 al al') (t : List (CellRowB0 q))
include h

theorem onb_eq {j : ℕ} (hj : j < 94) (i : ℕ) : onb al i j = onb al' i j := by
  simp only [onb, h.2 i j hj]

theorem laneL_eq (i : ℕ) : laneL al i = laneL al' i := by
  unfold laneL
  refine Finset.sum_congr rfl fun t ht => ?_
  have := Finset.mem_range.mp ht
  rw [h.2 i (bt0 + t) (by simp only [bt0]; omega)]

theorem laneO_eq (i : ℕ) : laneO al i = laneO al' i := by
  unfold laneO
  refine Finset.sum_congr rfl fun t ht => ?_
  have := Finset.mem_range.mp ht
  rw [h.2 i (bt0 + 16 + t) (by simp only [bt0]; omega)]

theorem laneBits_eq (i : ℕ) : laneBits al i = laneBits al' i := by
  unfold laneBits
  refine List.map_congr_left fun t ht => ?_
  have := List.mem_range.mp ht
  rw [h.2 i (bt0 + t) (by simp only [bt0]; omega)]

theorem hornerP_eq {lane lane' : ℕ → ℕ} (hl : ∀ i, lane i = lane' i) :
    ∀ f i, hornerP al lane f i = hornerP al' lane' f i
  | 0, _ => rfl
  | f + 1, i => by
    simp only [hornerP, onb_eq h (show eos < 94 by decide), hl i, hornerP_eq hl f (i + 1)]

theorem packP_eq (i : ℕ) : packP al i = packP al' i := by
  simp only [packP, laneBits_eq h i]

theorem hpackP_eq : ∀ f i, hpackP al f i = hpackP al' f i
  | 0, _ => rfl
  | f + 1, i => by
    simp only [hpackP, onb_eq h (show eos < 94 by decide), packP_eq h i, hpackP_eq f (i + 1)]

theorem Hp_eq (i : ℕ) : Hp al i = Hp al' i := by
  unfold Hp; rw [h.1]; exact hornerP_eq h (laneL_eq h) _ i

theorem HOp_eq (i : ℕ) : HOp al i = HOp al' i := by
  unfold HOp; rw [h.1]; exact hornerP_eq h (laneO_eq h) _ i

theorem Lp_eq (i : ℕ) : Lp al t i = Lp al' t i := by
  unfold Lp
  rw [onb_eq h (show mR < 94 by decide), onb_eq h (show mV < 94 by decide), onb_eq h (show mQ1 < 94 by decide),
    onb_eq h (show mQM < 94 by decide), onb_eq h (show mS < 94 by decide), onb_eq h (show mW < 94 by decide),
    h.2 i sv (by decide), Hp_eq h i, h.1, hpackP_eq h]

theorem Lf_eq (i : ℕ) : Lf al t i = Lf al' t i := by
  unfold Lf
  rw [onb_eq h (show mR < 94 by decide), onb_eq h (show mV < 94 by decide), onb_eq h (show mS < 94 by decide),
    onb_eq h (show mW < 94 by decide), h.2 i sv (by decide), Hp_eq h i]

theorem RLp_eq : ∀ i, RLp al t i = RLp al' t i
  | 0 => by simp only [RLp, onb_eq h (show f1 < 94 by decide), Lf_eq h t]
  | i + 1 => by
    simp only [RLp, onb_eq h (show f1 < 94 by decide), onb_eq h (show sL < 94 by decide), Lf_eq h t, RLp_eq i]

theorem ROp_eq : ∀ i, ROp al i = ROp al' i
  | 0 => by simp only [ROp, onb_eq h (show f1 < 94 by decide), HOp_eq h]
  | i + 1 => by
    simp only [ROp, onb_eq h (show f1 < 94 by decide), onb_eq h (show sL < 94 by decide), HOp_eq h, ROp_eq i]

theorem D1p_eq (i : ℕ) : D1p al t i = D1p al' t i := by
  unfold D1p
  rw [onb_eq h (show sH < 94 by decide), onb_eq h (show fst < 94 by decide), onb_eq h (show f2 < 94 by decide),
    h.2 i oLt (by decide), h.2 i lb (by decide), h.2 i cf1 (by decide), RLp_eq h t, Lf_eq h t, ROp_eq h, HOp_eq h,
    Lp_eq h t]

theorem D2p_eq (i : ℕ) : D2p al t i = D2p al' t i := by
  unfold D2p
  rw [onb_eq h (show sH < 94 by decide), onb_eq h (show fst < 94 by decide), h.2 i oDiv (by decide),
    h.2 i oMod (by decide), h.2 i cf2 (by decide), Lp_eq h t]

theorem blockSum_eq {D D' : ℕ → (ZMod q)[X]} (hD : ∀ i, D i = D' i) :
    ∀ f i, blockSum al D f i = blockSum al' D' f i
  | 0, _ => rfl
  | f + 1, i => by
    simp only [blockSum, onb_eq h (show sL < 94 by decide), hD i, blockSum_eq hD f (i + 1)]

theorem blockRows_eq : ∀ f i, blockRows al f i = blockRows al' f i
  | 0, _ => rfl
  | f + 1, i => by
    simp only [blockRows, onb_eq h (show sL < 94 by decide), blockRows_eq f (i + 1)]

theorem linkP_eq (j : ℕ) : linkP al t j = linkP al' t j := by
  unfold linkP
  rw [onb_eq h (show fst < 94 by decide), onb_eq h (show mV < 94 by decide), Hp_eq h j, h.2 j sv (by decide)]

theorem callPolys_eq (hh : ℕ) : callPolys al t hh = callPolys al' t hh := by
  unfold callPolys
  rw [h.1, blockSum_eq h (D1p_eq h t), blockSum_eq h (D2p_eq h t), blockRows_eq h]
  congr 1
  exact List.map_congr_left fun j _ => linkP_eq h t j

theorem hdrs_eq : hdrs al = hdrs al' := by
  unfold hdrs
  rw [h.1]
  exact List.filter_congr fun i _ => by rw [onb_eq h (show sH < 94 by decide)]

/-- **`AluSZEvent`'s per-call bad set reads only the base columns.** -/
theorem arithBadC_agree [Fact q.Prime] {Kq : Type} [Field Kq] [Algebra (ZMod q) Kq] [DecidableEq Kq] :
    arithBadC (Kq := Kq) al t = arithBadC (Kq := Kq) al' t := by
  unfold arithBadC
  rw [hdrs_eq h]
  congr 1
  exact List.map_congr_left fun hh _ => by rw [callPolys_eq h t hh]

end Agree

end

end Nock.NockVMROM.Thm54.VclL.Handle.AluBaseAL

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.AluBaseAL
#print axioms arithBadC_agree
end Axioms
