/-
  Nock/RedTeam/Batch1890Thm54TowerC2cBase.lean

  **Base gates, endpoint equalities and the IO vestige at the
  tower honest fill.**

  * `base15_of_cells` (`TowerKeptHolds.base`): the 15 `finalBaseTransitionGates n` hold at honest base cells.
  * `eq22_of_cells` (`TowerKeptHolds.eq`): the 22 endpoint equalities hold against banks `x 20..41` that
    are the one-hots of the first / last row states; `pubCFT_bank`: `pubCFT` reads `x` there and on `6..8`.
  * `honest_core81`, `honest_accInit`, `honest_accTerminal`: core 81, ep2 accInit / accTerminal in `𝕂′`,
    joined to the placement lemmas (`tower_ext_zero`, `tower_extNext_zero`, `tower_pub2_zero`).
  * Negative controls (each discriminates): two-hot selectors break `selectorOneHot`; a bank mismatch breaks
    the endpoint equality; `acc_after = 1` breaks `accTerminal`.
  UNCONFIRMED: the generator -> `TowerRowVals` map that supplies the cells; C2a/b/d.
-/
import Nock.NockVMROM.Thm54.VclL.Compute.TowerC2cBase
import Nock.RedTeam.Batch1889Thm54TowerHonestPlace

set_option autoImplicit false

namespace Nock.RedTeam.Batch1890

open Nock Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeBaseGates Nock.NockVMROM.Thm54.OptimizedComputeFinal
open Nock.NockVMROM.Thm54.Unhosted309 Nock.NockVMROM.Thm54.VclL.Compute.TowerD
open Nock.Reified Nock.NockVMROM.Thm54.CoordinateCompiler

/-- A concrete `ℚ` environment with a TWO-hot selector (columns `0`, `1`), first mask on. -/
def ctlE : Env ℚ where
  trace := fun j => if j = 0 ∨ j = 1 ∨ j = 11 then 1 else 0
  traceNext := fun _ => 0
  chal := fun _ => 0
  pub := fun j => if j = 21 then 1 else 0

/-- **NC (base)**: a two-hot selector violates `selectorOneHot`. -/
theorem selectorOneHot_twoHot : (selectorOneHot : CoeffExpr ℚ).eval ctlE ≠ 0 := by
  simp [selectorOneHot, selectorSum, CoeffExpr.sumList, bv, CoeffExpr.eval, ctlE, List.range, List.range.loop]

/-- **NC (eq)**: state `0` in the first row against a bank that names state `1` breaks the check. -/
theorem eqCheck_mismatch : (endpointEqualityCheck (isFirstVar : CoeffExpr ℚ) 20 0).eval ctlE ≠ 0 := by
  simp [endpointEqualityCheck, isFirstVar, bv, CoeffExpr.eval, ctlE]

/-- The accTerminal body over `ℚ`: isLast on, `acc_after = 1`, request public `0`. -/
def ctlT : CorrectedFinalTypedEnv ℚ ℚ where
  baseTrace := fun j => if (j : ℕ) = 12 then 1 else 0
  baseTraceNext := fun _ => 0
  extTrace := fun r => if (r : ℕ) = 60 then 1 else 0
  extTraceNext := fun _ => 0
  chal := fun _ => 0
  extensionPublic := fun _ => 0
  scalarPublic := fun _ => 0
  certBase := fun _ => 0
  certExt := fun _ => 0
  expCol := 0

/-- The width-309 wrapper of `ctlT` (walk columns `0`). -/
def ctlT309 : Env309 ℚ ℚ where
  base := ctlT
  walk := fun _ => 0
  walkNext := fun _ => 0

/-- **NC (accTerminal)**: with `acc_after = 1` at the last row the terminal gate is `1 ≠ 0`, so the
zero `acc_after` fill is load-bearing. -/
theorem accTerminal_nonzero_control :
    ((lowerLeaf finalAccTerminal).eval ctlT309 : ℚ) ≠ 0 := by
  rw [lowerLeaf_accTerminal]
  simp [WTyped.eval, CorrectedFinalTypedExpr.eval, ctlT309, ctlT]

end Nock.RedTeam.Batch1890

#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.base15_of_cells
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.eq22_of_cells
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.honestBaseCells_of_src
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.honest_core81
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.honest_accInit
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.honest_accTerminal
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.tower_pub2_zero
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.pubCFT_bank
#print axioms Nock.RedTeam.Batch1890.selectorOneHot_twoHot
#print axioms Nock.RedTeam.Batch1890.eqCheck_mismatch
#print axioms Nock.RedTeam.Batch1890.accTerminal_nonzero_control
