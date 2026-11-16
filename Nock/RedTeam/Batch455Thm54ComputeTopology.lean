/-
  Nock/RedTeam/Batch455Thm54ComputeTopology.lean

  **Topology from the in-gate label.**

  Target: `DeployedAcceptanceAt ⇒ WalkSat (in-gate label) ⇒ VecBFT ⇒
  RawComputeTopologyBinding` via `label_rlc_is_decoded_label`,
  `Walk.lean::reconForest`, `::bfsForest_reconForest`,
  `::reconForest_ForestReconGoal`, and the `_of_label` variants.

  Landed: the gate-vanishing half  and the hostile label
  identity.  Not landed: packing those into a `WalkSat` value at the
  decoded `lblC` / `foC` of `ExecOfTraces`, then `VecBFT_reconstruct_of_label`
  / `reconForest_ForestReconGoal_of_label`.  `TracesWalkHyps`' compute
  half (`sfCompute` / `validCompute`) therefore stays a named hyp.

  `computeTopology` stays on `openConjuncts` (10 names, unchanged).

  **Do not retire the K-side compute topology RAP.**  Consumers:
  `VerifierGeneratedSegmentedTopologyChecks` (`ProductionRawVerifier`),
  `RawTopologyBindingResidual` (`RawTopologySoundness`),
  `walkFamily` / `topologyBinding` on the package, the K-side
  `FailureUnion` walk summand (`JointSoundness` / `SeedFibers`).
-/
import Nock.Walk
import Nock.NockVMROM.Thm54.RawTopologySoundness
import Nock.NockVMROM.Thm54.ExecOfTraces
import Nock.RedTeam.Batch398Thm54PublicConjuncts
import Nock.RedTeam.Batch454Thm54ComputeWalkSat
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch455

open Nock
open Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.RedTeam.Batch398
open Nock.RedTeam.Batch454

/-- Compute-half of `TracesWalkHyps` is still a named hyp. -/
def computeWalkHypsOpen : List String := ["sfCompute", "validCompute"]

theorem computeWalkHypsOpen_length : computeWalkHypsOpen.length = 2 := by decide

/-- `computeTopology` remains on the live open list. -/
theorem computeTopology_still_open :
    "computeTopology" ∈ openConjuncts := by
  decide

theorem openConjuncts_length_unmoved : openConjuncts.length = 10 :=
  openConjuncts_length

/-- What still depends on the K-side compute topology RAP.  Do not retire. -/
def ksideComputeTopologyConsumers : List String :=
  ["ProductionRawVerifier.VerifierGeneratedSegmentedTopologyChecks",
    "RawTopologySoundness.RawTopologyBindingResidual",
    "OptimizedFullStrictNockVMROMPackage.topologyBinding",
    "JointSoundness / SeedFibers walkBad*_of_label"]

theorem kside_consumers_length : ksideComputeTopologyConsumers.length = 4 := by
  decide

/-- `RawComputeTopologyBinding` is the local fanout + `childLinkComp`
    residual (`RawTopologySoundness.lean`).  The `_of_label` reconstruction
    theorems exist; they are not yet applied to `execOfTraces`. -/
def RAW_COMPUTE_TOPOLOGY : String :=
  "Nock.NockVMROM.Thm54.RawComputeTopologyBinding"

def RECON_FOREST_OF_LABEL : String :=
  "Nock.Walk.reconForest_ForestReconGoal_of_label"

def VEC_BFT_OF_LABEL : String :=
  "Nock.Walk.VecBFT_reconstruct_of_label"

/-- Pipeline names, in order.  Steps 0–1 landed.
    Steps 2–4 are the remaining assembly. -/
def topologyPipeline : List String :=
  ["0 label_rlc_is_decoded_label",
    "1 walk gates vanish from DeployedAcceptanceAt",
    "2 WalkSat at lblC / foC",
    "3 VecBFT_reconstruct_of_label",
    "4 reconForest_ForestReconGoal_of_label → RawComputeTopologyBinding"]

theorem topologyPipeline_length : topologyPipeline.length = 5 := by decide

end Nock.RedTeam.Batch455

#print axioms Nock.RedTeam.Batch455.computeTopology_still_open
#print axioms Nock.RedTeam.Batch455.kside_consumers_length
