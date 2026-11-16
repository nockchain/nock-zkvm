/-
  Nock/RedTeam/Batch382Thm54WalkHypsOfDeployed.lean

  **`TracesWalkHyps` from deployed walk gates.**

  `tracesWalkHyps_of_deployed` is **not** inhabited.  Reconstruction
  (`Walk.reconTree` / `reconForest`) consumes `BFSValid` / `Sf` on the
  **opcode-derived** fanouts `foC` / `foM` (`fanoutComp` / `fanoutMem`
  of `computeStateOf` / `memoryStateOf`).  Deployed walk gates
  (`Walk.lean::WalkSat`) constrain the walk-column fanout `fo`, not
  those opcode fanouts.

  Topology conjuncts (`computeTopology`, `memoryTopology`,
  `axisStructural`, `rootBoundary`, `structuralChecks`) stay open
  for the same reason.
-/
import Nock.NockVMROM.Thm54.ExecOfTraces
import Nock.NockVMROM.Thm54.DeployedAcceptance
import Nock.Walk
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch382

open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54
open Nock.Walk

/-- Remaining walk-tiling facts `reconTree` / `reconForest` consume.
These are **not** fields of `WalkSat`. -/
def walkTilingObligations : List String :=
  ["sfCompute", "validCompute", "sfMemory", "validMemory"]

theorem walkTilingObligations_length : walkTilingObligations.length = 4 := by
  decide

#check TracesWalkHyps
#check WalkSat
#check foC
#check foM

end Nock.RedTeam.Batch382

#print axioms Nock.RedTeam.Batch382.walkTilingObligations_length
