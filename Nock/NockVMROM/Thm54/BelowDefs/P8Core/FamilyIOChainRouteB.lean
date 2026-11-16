/-
  Nock/NockVMROM/Thm54/BelowDefs/P8Core/FamilyIOChainRouteB.lean

  The
  remaining declarations stay in `Nock/NockVMROM/Thm54/P8Core/FamilyIOChainRouteB.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackageDefs` or the statement file, directly or transitively.
-/
import Nock.NockVMROM.Thm54.OptimizedComputeCodec

namespace Nock.NockVMROM.Thm54.FamilyIOChain

open scoped Polynomial
open Polynomial
open Nock
open Nock.Reified
open Nock.Framework
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open StrictExtension
open Module
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}

section Carrier

omit [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
  [FiniteDimensional F K] in
/-- `Batch672.opCol_eq_stateIndex_iff`, restated here so the production module does not import
`Nock.RedTeam`. -/
theorem opCol_eq_stateIndex_iff' (st s : ComputeTable.State) :
    opCol st = (OptimizedComputeCodec.stateIndex s : ℕ) ↔ st = s := by
  cases st <;> cases s <;> decide

end Carrier

end

end Nock.NockVMROM.Thm54.FamilyIOChain
