/-
  Nock/NockVMROM/Thm54/BelowDefs/P8Core/WalkQueueDeployed.lean

  The
  remaining declarations stay in `Nock/NockVMROM/Thm54/P8Core/WalkQueueDeployed.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackageDefs` or the statement file, directly or transitively.
-/
import Nock.NockVMROM.Thm54.BelowDefs.P8Core.Batch471Thm54ComputeTopologyPrefix
import Nock.NockVMROM.Thm54.WalkTilingEvents

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.WalkQueueDeployed

open scoped Classical
open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.ComputeTable
open Nock.Reified
open Nock.Framework
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ComputeWalkLabel
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.RedTeam.Batch471

noncomputable section

/-- Terminal-accepting coins on a non-tiling committed fanout column. -/
abbrev computeTilingEvent {K : Type} [Field K] [Fintype K] [DecidableEq K]
    (fo : ℕ → ℕ) (h : ℕ) : Finset (JointCoins K) :=
  WalkTilingEvents.computeTilingEvent fo h

theorem mem_computeTilingEvent_iff {K : Type} [Field K] [Fintype K] [DecidableEq K]
    (fo : ℕ → ℕ) (h : ℕ) (ω : JointCoins K) :
    ω ∈ computeTilingEvent fo h ↔
      alphaC ω ^ (1 + Sf fo h) = alphaC ω ^ h ∧ 1 + Sf fo h ≠ h :=
  WalkTilingEvents.mem_computeTilingEvent_iff fo h ω

end

end Nock.NockVMROM.Thm54.WalkQueueDeployed
