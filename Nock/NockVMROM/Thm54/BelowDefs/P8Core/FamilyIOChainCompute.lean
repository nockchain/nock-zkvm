/-
  Nock/NockVMROM/Thm54/BelowDefs/P8Core/FamilyIOChainCompute.lean

  The
  remaining declarations stay in `Nock/NockVMROM/Thm54/P8Core/FamilyIOChainCompute.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackageDefs` or the statement file, directly or transitively.
-/
import Nock.NockVMROM.Thm54.OptimizedStrictPackage

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
open OptimizedStrictPackage
open OptimizedComputeBaseGates
open OptimizedComputeFinal
open OptimizedComputeCorrectedFinal
open OptimizedComputeGateBasis
open OptimizedComputeSubstitution
open OptimizedComputeSemanticRealization
open OptimizedComputeFiniteIOGates
open OptimizedComputeHostileAccumulator
open OptimizedHostileTimestamps
open Module
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (c : OptimizedProductionChallengeTuple K F)

/-- The timestamp base of the family chip: compute slot `0` **is** the coin `alphaM c.1`. -/
abbrev chipAlphaAt : K := alphaM c.1

end

end Nock.NockVMROM.Thm54.FamilyIOChain
