/-
  Nock/RedTeam/Batch484Thm54WalkQueueConsequences.lean

  Deployed consequences.**

  Compute: `WalkQueueDeployed.deployed_bfsValid` (no α condition) and
  `deployed_tiling` outside `computeTilingEvent`.  Both halves of `TracesWalkHyps` at the
  family remapping (`tracesWalkHyps_of_chips`).  Extra hyp `hchar :
  MemStateTagChar F` on the memory WalkSat (one-hot); compiler `hp : 25 ≤ p`
  implies it.  No new `nockCompiles_zmod` hypothesis.

  Closing
  those names without that proof would be a ledger lie.  Not a new gate
  and not an `AcceptedContent` meaning change — assembly remaining.

  Slot 7 / roles 34–36 untouched.
-/
import Nock.NockVMROM.Thm54.WalkQueueDeployed
import Nock.NockVMROM.Thm54.MemoryWalkDeployed
import Nock.RedTeam.Batch448Thm54VerTransfer
import Nock.RedTeam.Batch483Thm54MemoryQueueWitness

set_option autoImplicit false

namespace Nock.RedTeam.Batch484

open Nock.Walk
open Nock.NockVMROM.Thm54.WalkQueueDeployed
open Nock.NockVMROM.Thm54.MemoryWalkDeployed

/-- Compute queue-validity is now a theorem, not a residual hyp. -/
def computeValidClosed : String := "validCompute"

/-- Compute tiling is priced, then derived outside the event. -/
def computeSfClosed : String := "sfCompute"

/-- Memory queue-validity is now a theorem (`BFSValidF`). -/
def memoryValidClosed : String := "validMemory"

/-- Memory forest tiling is priced, then derived outside the event. -/
def memorySfClosed : String := "sfMemory"

theorem compute_hyps_named :
    computeValidClosed = "validCompute" ∧
      computeSfClosed = "sfCompute" :=
  ⟨rfl, rfl⟩

theorem memory_hyps_named :
    memoryValidClosed = "validMemory" ∧
      memorySfClosed = "sfMemory" :=
  ⟨rfl, rfl⟩

/-- Both `TracesWalkHyps` halves are theorems at the family remapping. -/
def tracesWalkHypsDerived : List String :=
  ["sfCompute", "validCompute", "sfMemory", "validMemory"]

theorem tracesWalkHypsDerived_length : tracesWalkHypsDerived.length = 4 := by
  decide

/-- Ledger after this batch: topology names still open until
`ComputeExactTopology` / `MemoryExactTopology` of `execOfTraces` is
assembled. -/
def openAfterWalkHyps : List String :=
  ["mem_first_counts", "mem_first_indicator",
    "computeTopology", "memoryTopology", "axisStructural",
    "rootBoundary", "structuralChecks"]

theorem openAfterWalkHyps_eq_afterVer :
    openAfterWalkHyps = Nock.RedTeam.Batch448.openConjunctsAfterVer := by
  decide

/-- `openConjunctsAfterVer` stays 7 until both topology conjuncts close. -/
theorem afterVer_unmoved : Nock.RedTeam.Batch448.openConjunctsAfterVer.length = 7 :=
  Nock.RedTeam.Batch448.openConjunctsAfterVer_length

/-- Memory WalkSat twin exists (same shape as `Batch459.deployed_walkSat`). -/
def memoryWalkSatLanded : String := "MemoryWalkDeployed.deployed_walkSat"

theorem memoryWalkSatLanded_name :
    memoryWalkSatLanded = "MemoryWalkDeployed.deployed_walkSat" :=
  rfl

end Nock.RedTeam.Batch484

#print axioms Nock.RedTeam.Batch484.compute_hyps_named
#print axioms Nock.RedTeam.Batch484.memory_hyps_named
#print axioms Nock.NockVMROM.Thm54.WalkQueueDeployed.deployed_bfsValid
#print axioms Nock.NockVMROM.Thm54.WalkQueueDeployed.deployed_tiling
#print axioms Nock.NockVMROM.Thm54.WalkQueueDeployed.deployed_bfsValid_memory
#print axioms Nock.NockVMROM.Thm54.WalkQueueDeployed.deployed_tiling_memory
#print axioms Nock.NockVMROM.Thm54.WalkQueueDeployed.tracesWalkHyps_of_chips
#print axioms Nock.NockVMROM.Thm54.MemoryWalkDeployed.deployed_walkSat
