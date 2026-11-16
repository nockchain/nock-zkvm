/-
  Nock/RedTeam/Batch492Thm54AxisLookupStop.lean

  **`:1401` axis conclusion
  is not a theorem of the chips + priced events.**

  `AxisBridge.axis_lookups_valid_endToEnd` wants a reconstructed memory
  forest (`MemoryExactTopology` of `execOfTraces`) plus root-accumulator
  zeros (`deployed_root_accumulators_zero`).  Compute topology still
  carries `γ ∉ prefixBadGammas` (`Batch490.computeTopology_of_deployed`);
  the memory twin is blocked by prover-committed `seedW` and unpriced
  `forestPrefixBadGammas`.  Do not weaken `mem_first_counts` /
  `mem_first_indicator`.

  The paper's argument is `:1413-1427` (indicator pairs each add/remove
  on one path; counts sum the path's bits).
-/
import Nock.RedTeam.Batch490Thm54TopologyAssembly
import Nock.RedTeam.Batch448Thm54VerTransfer

set_option autoImplicit false

namespace Nock.RedTeam.Batch492

/-- What `deployed_axis_lookup_correct` still needs. -/
def remainingForAxis : List String :=
  ["WalkPrefix.prefixBadGammas (compute ComputeExactTopology)",
    "MemoryWalkDeployed.seedW (prover-committed public role 1)",
    "WalkPrefix.forestPrefixBadGammas (memory ForestVecBFT)",
    "MemoryExactTopology of execOfTraces"]

theorem remainingForAxis_length : remainingForAxis.length = 4 := by
  decide

def openAfterAxisStop : List String :=
  Nock.RedTeam.Batch448.openConjunctsAfterVer

theorem openAfterAxisStop_length : openAfterAxisStop.length = 7 :=
  Nock.RedTeam.Batch448.openConjunctsAfterVer_length

theorem axis_names_still_open :
    "mem_first_counts" ∈ openAfterAxisStop ∧
      "mem_first_indicator" ∈ openAfterAxisStop := by
  decide

end Nock.RedTeam.Batch492

#print axioms Nock.RedTeam.Batch492.remainingForAxis_length
#print axioms Nock.RedTeam.Batch492.openAfterAxisStop_length
