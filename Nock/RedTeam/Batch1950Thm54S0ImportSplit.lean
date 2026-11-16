import Nock.NockVMROM.Thm54.StandaloneVerifierData
import Nock.NockVMROM.Thm54.P8Core.SVFrame.MemSoundnessFamily
import Nock.NockVMROM.Thm54.P8Core.SVFrame.JointSummands
import Nock.NockVMROM.Thm54.P8Core.SVFrame.StandaloneGeneric
import Nock.NockVMROM.Thm54.VclL.Chips.ChipV
import Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
import Nock.NockVMROM.Thm54.VclL.Events.Bound
import Nock.NockVMROM.Thm54.VclL.Compute.TowerLookup
import Nock.NockVMROM.Thm54.VclL.Compute.TowerCompFamilyT
import Nock.NockVMROM.Thm54.VclL.Compute.TowerHonestT
import Nock.NockVMROM.Thm54.VclL.Compute.TowerJointSizes
import Nock.NockVMROM.Thm54.VclL.Compute.TowerRowFactsAt
import Nock.RedTeam.Batch1882Thm54VclStandaloneNoHrow
import Nock.RedTeam.Batch1938Thm54VclCompletenessJoint
import Nock.RedTeam.Batch1947Thm54VclCompletenessFigure
import Nock.NockVMROM.Thm54.BelowDefs.CensusExtraClosure
import Nock.NockVMROM.Thm54.BelowDefs.GenericHonestCommitment
import Nock.NockVMROM.Thm54.BelowDefs.HonestCommitment
import Nock.NockVMROM.Thm54.BelowDefs.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.BelowDefs.P8Core.Batch458Thm54StrategyBindsStop
import Nock.NockVMROM.Thm54.BelowDefs.P8Core.Batch471Thm54ComputeTopologyPrefix
import Nock.NockVMROM.Thm54.BelowDefs.P8Core.Batch490Thm54TopologyAssembly
import Nock.NockVMROM.Thm54.BelowDefs.P8Core.DeployedComputeRows
import Nock.NockVMROM.Thm54.BelowDefs.P8Core.FamilyIOChainCompute
import Nock.NockVMROM.Thm54.BelowDefs.P8Core.FamilyIOChainRouteB
import Nock.NockVMROM.Thm54.BelowDefs.P8Core.OptimizedComputeHostileAccumulator
import Nock.NockVMROM.Thm54.BelowDefs.P8Core.OptimizedHostileIOAssembly
import Nock.NockVMROM.Thm54.BelowDefs.P8Core.OptimizedHostileTimestamps
import Nock.NockVMROM.Thm54.BelowDefs.P8Core.OptimizedMemoryHostileAccumulator
import Nock.NockVMROM.Thm54.BelowDefs.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.BelowDefs.P8Core.WalkQueueDeployed
import Nock.NockVMROM.Thm54.BelowDefs.P8Core.WrapFixesVcomp
import Nock.NockVMROM.Thm54.BelowDefs.TraceGen.GenFormRAxisLambda
import Nock.NockVMROM.Thm54.BelowDefs.TraceGen.GenGoodSeedExists
import Nock.NockVMROM.Thm54.BelowDefs.Unhosted309Events

/-!
Import-closure check for the standalone VCL verifier: a `run_cmd` confirms that the closure of this module excludes `OptimizedStrictFullPackageDefs` and `OptimizedStrictFullPackage`, and contains the positive-control modules. The final `#print axioms` lines list the axioms of the VCL standalone, completeness and tower soundness headline theorems.
-/

set_option autoImplicit false

namespace Nock.RedTeam.Batch1950

run_cmd do
  let env ← Lean.getEnv
  let mods := env.header.moduleNames
  let pinned : List Lean.Name :=
    [`Nock.NockVMROM.Thm54.OptimizedStrictFullPackageDefs, `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage]
  for p in pinned do
    if mods.contains p then Lean.throwError m!"S0 walk: pinned module {p} is in the closure"
  let positive : List Lean.Name := [`Nock.NockVMROM.Thm54.OptimizedStrictPackage,
    `Nock.NockVMROM.Thm54.StandaloneVerifierData, `Nock.NockVMROM.Thm54.VclL.Compute.TowerHonestT,
    `Nock.RedTeam.Batch1938Thm54VclCompletenessJoint, `Nock.NockVMROM.Thm54.BelowDefs.Unhosted309Events]
  for p in positive do
    unless mods.contains p do Lean.throwError m!"S0 walk positive control: {p} missing"
  Lean.logInfo m!"S0 walk: {mods.size} modules in the closure; pinned files absent; positive controls present"

end Nock.RedTeam.Batch1950

-- headline theorems
#print axioms Nock.RedTeam.Batch1882.vcl_standalone_164'
#print axioms Nock.RedTeam.Batch1938.vcl_completeness'
#print axioms Nock.RedTeam.Batch1947.vcl_completeness_figure
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.compSoundnessVCLT
