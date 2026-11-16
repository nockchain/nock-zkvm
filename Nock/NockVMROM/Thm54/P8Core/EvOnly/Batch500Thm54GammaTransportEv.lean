/-
  Nock/NockVMROM/Thm54/P8Core/EvOnly/Batch500Thm54GammaTransportEv.lean

  The originals are untouched.  Imports P8Core only; never the statement file.
-/
import Nock.NockVMROM.Thm54.P8Core.Batch500Thm54GammaTransport
import Nock.NockVMROM.Thm54.P8Core.PlacementABridge
import Nock.NockVMROM.Thm54.P8Core.EvOnly.OptimizedHostileTimestampsEv
import Nock.NockVMROM.Thm54.P8Core.EvOnly.Batch465Thm54DeployedRootLabelEqClaimEv
import Nock.NockVMROM.Thm54.P8Core.EvOnly.Batch489Thm54FoOfEqFoWEv
import Nock.NockVMROM.Thm54.P8Core.EvOnly.Batch490Thm54TopologyAssemblyEv
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace Nock.RedTeam.Batch500

open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.WalkPrefixGammaEvents
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.OptimizedMemoryRAP
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.MemoryWalkDeployed
open Nock.NockVMROM.Thm54.MemoryWalkLabel
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.WrapMemoryConjuncts
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.ComputeWalkRootEvents
open Nock.NockVMROM.Thm54.ComputeWalkLabel
open Nock.NockVMROM.Thm54.ComputeWalkSeed
open Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator
open Nock.Framework
open Nock.Framework.Reify
open MonolithicRAP
open Nock.RedTeam.Batch465
open Nock.RedTeam.Batch471
open Nock.RedTeam.Batch489
open Nock.RedTeam.Batch490
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Module
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

section DeployedVectors

variable {F : Type} [Field F] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc₀ : Fin P.computeChip.rap.w → F[X])
  (hsatC : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) (familyQc P c Qc₀))
include hsatC

end DeployedVectors

section PricedGamma

variable {F : Type} [Field F] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc₀ : Fin P.computeChip.rap.w → F[X])
  (Qm₀ : Fin P.memoryChip.rap.w → F[X])
  (hsatC : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) (familyQc P c Qc₀))
  (hsatM : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) (familyQm P c Qm₀))
  (hz : nprSeed c.1 ≠ 0)
  (hchar : MemStateTagChar F)
  (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
  (hbasis : FormRBasis P.optimized.basis)
  (hwidth : FormRWidth F)
include hsatC

include hsatM

/-- `c ∉ optimizedFailureEvent` discharges topology `hγ`. -/
theorem hγ_of_good_ev
    (hgood : c ∉ Nock.NockVMROM.Thm54.OptimizedFailureEventEv.optimizedFailureEventEv P Qc₀ Qm₀) :
    gamma c.1 ∉ prefixBadGammas (Vd P c Qc₀) (Cvd P c Qc₀ hsatC)
      (foC P Qc₀ c) (rows P) :=
  hγ_of_priced P c Qc₀ hsatC
    (Nock.NockVMROM.Thm54.PlacementA.good_components_of_Ev P Qc₀ Qm₀ c hgood).2.2.2.2.2.2.2.1

include hz hchar
include hax hbasis hwidth

/-- **`ComputeExactTopology` of `execOfTraces` from chips + priced events.**
    No extra `hγ`. -/
theorem computeTopology_of_deployed_of_good_ev
    (hacc : DeployedAcceptanceAt P c (familyQc P c Qc₀) (familyQm P c Qm₀))
    (hgood : c ∉ Nock.NockVMROM.Thm54.OptimizedFailureEventEv.optimizedFailureEventEv P Qc₀ Qm₀) :
    ComputeExactTopology (execOfTraces P Qc₀ Qm₀ c
      (tracesWalkHyps_of_deployed_ev P c Qc₀ Qm₀ hsatC hsatM hchar hax hbasis hwidth hacc hgood)) :=
  computeTopology_of_deployed_ev P c Qc₀ Qm₀ hsatC hsatM hz hchar hax hbasis hwidth hacc hgood
    (hγ_of_good_ev P c Qc₀ Qm₀ hsatC hsatM hgood)

end PricedGamma

end Nock.RedTeam.Batch500

