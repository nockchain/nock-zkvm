/-
  Nock/RedTeam/Batch489Thm54FoOfEqFoW.lean

  The `foOf = foW` bridge.**

  Compute half is `Batch465::foOf_eq_foW`
  (same one-hot: `fanoutComp` of the decoded state).  This batch adds the
  memory twin and discharges `TracesWalkHyps` from
  `c ∉ optimizedFailureEvent` (plus the chip satisfaction the queue
  theorems already take).  No new `nockCompiles_zmod` hyp.
-/
import Nock.NockVMROM.Thm54.WalkQueueDeployed
import Nock.NockVMROM.Thm54.WalkTilingEvents
import Nock.NockVMROM.Thm54.DeployedAcceptance
import Nock.RedTeam.Batch465Thm54DeployedRootLabelEqClaim
import Nock.RedTeam.Batch448Thm54VerTransfer
import Nock.NockVMROM.Thm54.P8Core.Batch489Thm54FoOfEqFoW
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

def openAfterBridge : List String :=
  Nock.RedTeam.Batch448.openConjunctsAfterVer

theorem openAfterBridge_length : openAfterBridge.length = 7 :=
  Nock.RedTeam.Batch448.openConjunctsAfterVer_length

end

end Nock.RedTeam.Batch489

#print axioms Nock.RedTeam.Batch489.Sf_foOf_eq_foW
#print axioms Nock.RedTeam.Batch489.foOfMem_eq_foWmem
#print axioms Nock.RedTeam.Batch489.tracesWalkHyps_of_failureEvent
