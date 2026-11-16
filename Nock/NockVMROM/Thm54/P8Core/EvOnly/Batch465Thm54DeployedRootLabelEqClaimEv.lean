/-
  Nock/NockVMROM/Thm54/P8Core/EvOnly/Batch465Thm54DeployedRootLabelEqClaimEv.lean

  The originals are untouched.  Imports P8Core only; never the statement file.
-/
import Nock.NockVMROM.Thm54.P8Core.Batch465Thm54DeployedRootLabelEqClaim
import Nock.NockVMROM.Thm54.P8Core.PlacementABridge
import Nock.NockVMROM.Thm54.P8Core.EvOnly.OptimizedHostileTimestampsEv
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch465

open scoped Polynomial
open Polynomial
open Nock
open Nock.Reified
open Nock.Walk
open Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ComputeWalkSeed
open Nock.NockVMROM.Thm54.ComputeWalkLabel
open Nock.NockVMROM.Thm54.ComputeWalkRootEvents
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.DeployedComputeRows
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.ComputePaperPacking
open Nock.NockVMROM.Thm54.StrategyOfTraces
open Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator
open Nock.RedTeam.Batch457
open Nock.RedTeam.Batch458
open Nock.RedTeam.Batch459
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.Framework
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTypedLowering
open Nock.NockVMROM.Thm54.OptimizedComputeTemplate
open Nock.NockVMROM.Thm54.OptimizedComputeFinal
open Nock.NockVMROM.Thm54.OptimizedComputeBaseGates
open Nock.NockVMROM.Thm54.OptimizedComputeGateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.Framework.Reify
open MonolithicRAP
open OptimizedHostileTimestamps
open Module

noncomputable section

section Congr

variable {K : Type} [Field K] [DecidableEq K]

end Congr

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc₀ : Fin P.computeChip.rap.w → F[X])

variable (hsat : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) (familyQc P c Qc₀))
  (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
  (hbasis : FormRBasis P.optimized.basis)
  (hwidth : FormRWidth F)
include hsat
include hax hbasis hwidth

/-- The same at the consumed event, plus the (now separately priced) `α`-root
polynomial event.  `hgood` gives the walk-root and tiling exclusions;
`hα` is the paper's degree-`h` root set, which the consumed union prices
only on a tiled table. -/
theorem deployed_root_label_eq_claim_of_good_ev
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (hgood : c ∉ Nock.NockVMROM.Thm54.OptimizedFailureEventEv.optimizedFailureEventEv P Qc₀ Qm)
    (hα : c.1 ∉ alphaRootEvent (P.computeSourceEnv Qc₀)
      (fun z => claimLabelVec z P.optimized.verifier.raw.claim)) :
    ChipRootBinding P c (familyQc P c Qc₀) :=
  deployed_root_label_eq_claim P c Qc₀ hsat hax hbasis hwidth
    (Nock.NockVMROM.Thm54.PlacementA.good_components_of_Ev P Qc₀ Qm c hgood).2.2.2.2.1 hα

end

end Nock.RedTeam.Batch465

