/-
  Nock/NockVMROM/Thm54/P8Core/EvOnly/Batch489Thm54FoOfEqFoWEv.lean

  The originals are untouched.  Imports P8Core only; never the statement file.
-/
import Nock.NockVMROM.Thm54.P8Core.Batch489Thm54FoOfEqFoW
import Nock.NockVMROM.Thm54.P8Core.PlacementABridge
import Nock.NockVMROM.Thm54.P8Core.EvOnly.OptimizedHostileTimestampsEv
import Nock.NockVMROM.Thm54.P8Core.EvOnly.Batch465Thm54DeployedRootLabelEqClaimEv
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.RedTeam.Batch489

open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.MemoryTable
open Nock.Framework
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.ComputeWalkRootEvents
open Nock.NockVMROM.Thm54.WalkTilingEvents
open Nock.NockVMROM.Thm54.WalkQueueDeployed
open Nock.NockVMROM.Thm54.MemoryWalkDeployed
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.WrapMemoryConjuncts
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.RedTeam.Batch459
open Nock.RedTeam.Batch465
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc₀ : Fin P.computeChip.rap.w → F[X])
  (Qm₀ : Fin P.memoryChip.rap.w → F[X])
variable (hsatC : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) (familyQc P c Qc₀))
variable (hsatM : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) (familyQm P c Qm₀))
variable (hchar : MemStateTagChar F)
variable (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
variable (hbasis : FormRBasis P.optimized.basis)
variable (hwidth : FormRWidth F)
include hsatC

omit hsatC

include hsatC hsatM hchar
include hax hbasis hwidth

/-- `c ∉ optimizedFailureEvent` discharges both tiling exclusions, hence
`TracesWalkHyps`.  Chip satisfaction and `MemStateTagChar` are the queue
theorems' existing hypotheses, not new walk hyps. -/
theorem tracesWalkHyps_of_failureEvent_ev
    (hgood : c ∉ Nock.NockVMROM.Thm54.OptimizedFailureEventEv.optimizedFailureEventEv P Qc₀ Qm₀) :
    TracesWalkHyps P Qc₀ Qm₀ c := by
  have hc := Nock.NockVMROM.Thm54.PlacementA.good_components_of_Ev P Qc₀ Qm₀ c hgood
  have htileC : c.1 ∉ P.computeTilingEventOf Qc₀ := hc.2.2.2.2.2.1
  have htileM : c.1 ∉ P.memoryTilingEventOf Qm₀ := hc.2.2.2.2.2.2.1
  have hC : c.1 ∉ WalkTilingEvents.computeTilingEvent
      (Batch459.foW P c (familyQc P c Qc₀) hsatC) (rows P) := by
    rwa [← computeTilingEventOf_eq_foW P c Qc₀ hsatC]
  have hM : c.1 ∉ WalkTilingEvents.memoryTilingEvent
      (MemoryWalkDeployed.foW P c (familyQm P c Qm₀))
      P.optimized.family.problem.cfg.kMem (memRows P) := by
    rwa [← memoryTilingEventOf_eq_foWmem P c Qm₀]
  exact tracesWalkHyps_of_chips P c Qc₀ Qm₀ hsatC hsatM hchar hax hbasis hwidth hC hM

/-- Same conclusion from `DeployedAcceptanceAt` at the family remapping. -/
theorem tracesWalkHyps_of_deployed_ev
    (hacc : DeployedAcceptanceAt P c (familyQc P c Qc₀) (familyQm P c Qm₀))
    (hgood : c ∉ Nock.NockVMROM.Thm54.OptimizedFailureEventEv.optimizedFailureEventEv P Qc₀ Qm₀) :
    TracesWalkHyps P Qc₀ Qm₀ c :=
  tracesWalkHyps_of_failureEvent_ev P c Qc₀ Qm₀ hacc.compute_satisfies
    hacc.memory_satisfies hchar hax hbasis hwidth hgood

end

end Nock.RedTeam.Batch489

