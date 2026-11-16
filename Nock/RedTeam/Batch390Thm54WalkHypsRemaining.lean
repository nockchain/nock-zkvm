/-
  Nock/RedTeam/Batch390Thm54WalkHypsRemaining.lean

  **Topology five stay open.**

  `TracesWalkHyps` (`ExecOfTraces.lean::TracesWalkHyps`) is still a
  hypothesis of `strategyOfTraces`.  Deployed walk gates ⇒ `WalkSat`
  ⇒ `ForestVecBFT` ⇒ `BFSValidF` is not discharged.
-/
import Nock.NockVMROM.Thm54.ExecOfTraces
import Nock.RedTeam.Batch388Thm54OpenConjunctsTransfer

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch390

def topologyStillOpen : List String :=
  ["computeTopology", "memoryTopology", "axisStructural",
    "rootBoundary", "structuralChecks"]

theorem topologyStillOpen_length : topologyStillOpen.length = 5 := by decide

theorem topology_subset_open :
    topologyStillOpen.Sublist Nock.RedTeam.Batch388.openConjuncts := by
  decide

end Nock.RedTeam.Batch390

#print axioms Nock.RedTeam.Batch390.topologyStillOpen_length
