/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/WitX9.lean

  Each row satisfies
  EVERY base gate of the twin (`BaseHoldsX9`, `decide +kernel`) and is one-hot at its state.

  * `witS0B` — `*[s [0 n]]` with a BIG axis: `f = [f_h f_t]` cell serial `5`, `f_h = (0, 0)`, `f_t` a
    kind-2 atom-table row `(2, 7)`, subject / result cells `(1, 11)` / `(1, 13)`, `xId = 3`.
  * `witS10B` — `[10 [[a c] d]]` with a BIG axis `f_tth = (2, 9)` (kind-2 route: `kLab = 2`,
    `vLab = f_tth.v = 9`).
  * `witS10BF` — the FIELD-axis route: `f_tth = (0, 2^62 + 5)` (kind 0), chain-root label
    `(kLab, vLab) = (3, 64·3 + 1)` (the design's `(3, 64·id + 1)`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ChipHX9

namespace Nock.NockVMROM.Thm54
namespace VclL.Handle
namespace ChipHX9

open Nock Nock.Reified
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH Nock.NockVMROM.Thm54.VclL.Handle.ChipHX

/-- `s0B`: one-hot `123`; `f = (1,5)`, `f_h = (0,0)`, `f_t = (2,7)` (`kb(f_t)` col `55`), `s = (1,11)`,
`e = (1,13)`, `xId = 3`. -/
def witListS0B : List (ℕ × ℚ) :=
  [(123, 1), (25, 1), (26, 11), (27, 1), (28, 5), (29, 1), (30, 13), (35, 0), (36, 0),
   (37, 2), (38, 7), (55, 1), (126, 3)]

def witS0B : Env ℚ := ⟨fun i => (witListS0B.lookup i).getD 0, fun _ => 0, fun _ => 0, fun _ => 0⟩

/-- `s10B`, big axis: `f = (1,5)`, `f_h = (0,10)`, `f_t = (1,6)`, `f_th = (1,7)`, `f_tt = (1,8)`,
`f_tth = (2,9)` (`kb` col `58`), `f_ttt = (1,10)`, `s = (1,11)`, `e = (1,13)`, `sf1 = (1,14)`,
`sf2 = (1,15)`, `kLab = 2`, `vLab = 9`, `xId = 3`. -/
def witListS10B : List (ℕ × ℚ) :=
  [(124, 1), (25, 1), (26, 11), (27, 1), (28, 5), (29, 1), (30, 13), (31, 1), (32, 14), (33, 1),
   (34, 15), (35, 0), (36, 10), (37, 1), (38, 6), (39, 1), (40, 7), (41, 1), (42, 8), (43, 2),
   (44, 9), (58, 1), (45, 1), (46, 10), (126, 3), (127, 2), (128, 9)]

def witS10B : Env ℚ := ⟨fun i => (witListS10B.lookup i).getD 0, fun _ => 0, fun _ => 0, fun _ => 0⟩

/-- `s10B`, field axis `2^62 + 5` (kind 0): `kLab = 3`, `vLab = 64·3 + 1 = 193`. -/
def witListS10BF : List (ℕ × ℚ) :=
  [(124, 1), (25, 1), (26, 11), (27, 1), (28, 5), (29, 1), (30, 13), (31, 1), (32, 14), (33, 1),
   (34, 15), (35, 0), (36, 10), (37, 1), (38, 6), (39, 1), (40, 7), (41, 1), (42, 8), (43, 0),
   (44, 4611686018427387909), (45, 1), (46, 10), (126, 3), (127, 3), (128, 193)]

def witS10BF : Env ℚ := ⟨fun i => (witListS10BF.lookup i).getD 0, fun _ => 0, fun _ => 0, fun _ => 0⟩

/-- **Non-vacuity of `s0B`** (A0 17c): the row satisfies every twin base gate, is one-hot at `s0B`, and
reads a kind-2 (big) axis. -/
theorem witS0B_ok :
    BaseHoldsX9 witS0B ∧ OneHotAt9 witS0B sS0B ∧ kcV witS0B xFt = 0 ∧ kbV witS0B xFt = 1 := by
  refine ⟨by unfold BaseHoldsX9; decide +kernel, by unfold OneHotAt9; decide +kernel,
    by decide +kernel, by decide +kernel⟩

/-- **Non-vacuity of `s10B`, big axis** (A0 17c). -/
theorem witS10B_ok :
    BaseHoldsX9 witS10B ∧ OneHotAt9 witS10B sS10B ∧ kbV witS10B xFtth = 1 ∧
      tr witS10B kLabX = 2 ∧ tr witS10B vLabX = tr witS10B xFtth.v := by
  refine ⟨by unfold BaseHoldsX9; decide +kernel, by unfold OneHotAt9; decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- **Non-vacuity of `s10B`, field axis** (A0 17c): the kind-3 chain-root label `(3, 64·xId + 1)`. -/
theorem witS10BF_ok :
    BaseHoldsX9 witS10BF ∧ OneHotAt9 witS10BF sS10B ∧ kcV witS10BF xFtth = 0 ∧
      kbV witS10BF xFtth = 0 ∧ tr witS10BF kLabX = 3 ∧ tr witS10BF vLabX = 64 * tr witS10BF xIdX + 1 := by
  refine ⟨by unfold BaseHoldsX9; decide +kernel, by unfold OneHotAt9; decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

end ChipHX9
end VclL.Handle
end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9.witS0B_ok
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9.witS10B_ok
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9.witS10BF_ok
