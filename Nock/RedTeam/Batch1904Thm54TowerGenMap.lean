/-
  Nock/RedTeam/Batch1904Thm54TowerGenMap.lean

  **Generator → honest tower row; C2a / C2c hypotheses.**

  * `genRowVals` (the map), `honestOverlay`, `honestEx` (`Classical.choose` from `computeAIR_iff_Vcomp`).
  * `gen_vcomp_wf`: `V_comp` (re-keyed to `(a,b,c)`) and `WF` at every generated BFS row from `SeedGood`
    and the named honestBad condition `rlc5Holds a b c`.
  * `genRow_baseCells`, `genRow_eq_hyps`, `genRow_banks`: C1b's `HonestBaseCells` / `eq22_of_cells` side
    conditions.
  * Negative control `dead_roles_differ`: the source env's roles 54/55 and challenge 0 are NOT the tower
    env's in general (so `AgreeOffT`'s exclusions are load-bearing, and the free generator is needed).
-/
import Nock.NockVMROM.Thm54.VclL.Compute.TowerGenMap
import Nock.RedTeam.Batch1903Thm54TowerGenTable
import Nock.NockVMROM.Thm54.CensusExtraClosure
import Nock.NockVMROM.Thm54.ForestExponentWindow
import Nock.NockVMROM.Thm54.P8Core.SVCompute.QueueTwins
import Nock.NockVMROM.Thm54.P8Core.SVWalk.ExpAlign

set_option autoImplicit false

namespace Nock.RedTeam.Batch1904

open Nock Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD

/-- A zero typed env over `ℚ`. -/
def T0 : CorrectedFinalTypedEnv ℚ ℚ where
  baseTrace := fun _ => 0
  baseTraceNext := fun _ => 0
  extTrace := fun _ => 0
  extTraceNext := fun _ => 0
  chal := fun _ => 0
  extensionPublic := fun _ => 0
  scalarPublic := fun _ => 0

/-- **NC**: filling the dead read set with `α* = 1`, `ln_prev = 2` changes exactly those slots. -/
theorem dead_roles_differ :
    (honestSrcEnv T0 1 2 3).chal 0 ≠ T0.chal 0 ∧ (honestSrcEnv T0 1 2 3).extTrace 54 ≠ T0.extTrace 54 ∧
      (honestSrcEnv T0 1 2 3).extTrace 55 ≠ T0.extTrace 55 := by
  simp [honestSrcEnv, T0]

end Nock.RedTeam.Batch1904

#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.honestEx_air
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.genRowVals_vestige
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.genRowVals_imZero
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.agreeOffT_honestSrc
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.honest_rowMatch
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.renderNode_inputs
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.gen_vcomp_wf
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.genRow_baseCells
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.genRow_eq_hyps
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.genRow_banks
#print axioms Nock.RedTeam.Batch1904.dead_roles_differ
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.genRow_walkFields
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.genRow_walkNextFields
