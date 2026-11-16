/-
  Nock/RedTeam/Batch494Thm54TopologyAxisRecord.lean

  Record.**

  Open conjuncts before: 7 (`Batch448.openConjunctsAfterVer`).
  Residual-circularity diagnosis retracted.
  `hFcommit` / whole-table `VecBFT` land at the compute chip; `hseed` and
  the prefix `α`-event discharge from the priced walk-root event.
  Exact failing statement: `Batch490.computeTopology_of_deployed` still
  needs `γ ∉ prefixBadGammas` (unpriced; priced `γ` is root/claim only).
  Memory `hFcommit_memory` lands (`hpole`); forest VecBFT blocked by
  `seedW` / `forestPrefixBadGammas`.  No new `nockCompiles_zmod` hyp.

  Price `prefixBadGammas` (or prove it ⊆ a priced
  event) and the memory seed / `forestPrefixBadGammas`.  Then topology
  7→5 and axis 5→3 resume.
-/
import Nock.RedTeam.Batch490Thm54TopologyAssembly
import Nock.RedTeam.Batch490Thm54TopologyAssemblyStop
import Nock.RedTeam.Batch448Thm54VerTransfer
import Nock.RedTeam.Batch491Thm54WrongChildLink
import Nock.RedTeam.Batch492Thm54AxisLookupStop

set_option autoImplicit false

namespace Nock.RedTeam.Batch494

def openBefore : List String :=
  Nock.RedTeam.Batch448.openConjunctsAfterVer

def openAfter : List String :=
  Nock.RedTeam.Batch490.openConjunctsAfterAssembly

theorem open_unmoved : openBefore = openAfter := rfl

theorem open_length : openAfter.length = 7 :=
  Nock.RedTeam.Batch490.openConjunctsAfterAssembly_length

/-- What remains for topology, axis, and dropping `TracesBindsHyps`. -/
def remainingForNextLane : List String :=
  ["WalkPrefix.prefixBadGammas",
    "MemoryWalkDeployed.seedW",
    "WalkPrefix.forestPrefixBadGammas",
    "axisStructural", "rootBoundary", "structuralChecks",
    "TracesBindsHyps (H1.4 joins)"]

theorem remainingForNextLane_length : remainingForNextLane.length = 7 := by
  decide

/-- Batches entered / not. -/
def batchStatus : List (String × String) :=
  [("Batch489", "landed: foOf = foW + tracesWalkHyps_of_failureEvent"),
    ("Batch490", "STOP: computeTopology_of_deployed needs prefixBadGammas"),
    ("Batch491", "landed: fo5/fo3 rejected at the chips"),
    ("Batch492", "STOP: deployed_axis_lookup_correct needs MemoryExactTopology"),
    ("Batch493", "not entered (5 → 3 needs 492)")]

theorem batchStatus_length : batchStatus.length = 5 := by
  decide

end Nock.RedTeam.Batch494

#print axioms Nock.RedTeam.Batch494.open_unmoved
#print axioms Nock.RedTeam.Batch494.open_length
