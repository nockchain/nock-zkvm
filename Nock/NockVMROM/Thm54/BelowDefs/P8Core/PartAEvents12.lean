/-
  Nock/NockVMROM/Thm54/BelowDefs/P8Core/PartAEvents12.lean

  The
  remaining declarations stay in `Nock/NockVMROM/Thm54/P8Core/PartAEvents12.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackageDefs` or the statement file, directly or transitively.
-/
import Nock.NockVMROM.Thm54.P8Core.PartATuple12
import Nock.NockVMROM.Thm54.P8Core.RepartitionedStaging

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Nock.NockVMROM.Thm54.PartA12

open scoped Polynomial BigOperators Classical
open Polynomial
open Nock
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedComputeCollisionBound
open Nock.NockVMROM.Thm54.OptimizedMemoryCollisionAccounting
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.RoundFibred

noncomputable section

section ConstStrategy

open RepartitionedStaging
open Nock.Reified
variable {n M : ℕ} {K F : Type} [Fintype K] [DecidableEq K] [Fintype F]

/-- **`StagedTraces` at the twelve-coin tuple** (design §5's shape, over any column type): each
column is a function only of the coins sampled strictly before its block. -/
def Staged12 {ι β : Type*} (colRound : ι → ℕ)
    (Q : OptimizedProductionChallengeTuple12 K F → ι → β) : Prop :=
  ∀ j c c', (∀ i : Fin 12, (repartitionedChronology.sampledAfter i : ℕ) < colRound j →
    landedVec12 c i = landedVec12 c' i) → Q c j = Q c' j

end ConstStrategy

end

end Nock.NockVMROM.Thm54.PartA12
