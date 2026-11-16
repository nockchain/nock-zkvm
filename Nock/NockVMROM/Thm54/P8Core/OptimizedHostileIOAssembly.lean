/-
  Nock/NockVMROM/Thm54/P8Core/OptimizedHostileIOAssembly.lean

  Relocated below the statement file: declarations of
  `Nock.NockVMROM.Thm54.OptimizedHostileIOAssembly`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/NockVMROM/Thm54/OptimizedHostileIOAssembly.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.P8Core.DeployedAcceptance
import Nock.NockVMROM.Thm54.P8Core.OptimizedComputeHostileAccumulator
import Nock.NockVMROM.Thm54.BelowDefs.P8Core.OptimizedHostileIOAssembly
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

namespace Nock.NockVMROM.Thm54

namespace OptimizedHostileIOAssembly

open Nock
open Nock.Reified
open Nock.Framework
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open OptimizedComputeSubstitution
open OptimizedComputeFiniteIOGates
open OptimizedComputeSameExecution
open OptimizedComputeSampledTrace
open OptimizedComputeCanonicalSatisfaction
open OptimizedMemoryGateBasis
open OptimizedMemoryCanonicalSatisfaction
open OptimizedMemorySemanticRealization
open StrictExtension
open OptimizedStrictFullPackage
open OptimizedComputeFinalTrace
open Module
open scoped Polynomial

noncomputable section

variable {F K : Type} [Field F]
  [Field K] [Algebra F K] [FiniteDimensional F K]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
variable (Qc : Fin P.computeChip.rap.w → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X])

theorem hostileRequests_eq_package :
    OptimizedComputeHostileAccumulator.hostileRequests P Qc = P.hostileRequests Qc := by
  unfold OptimizedComputeHostileAccumulator.hostileRequests
    OptimizedFullStrictNockVMROMPackage.hostileRequests
    OptimizedFullStrictNockVMROMPackage.computeBaseEnv
  rfl

end

end OptimizedHostileIOAssembly

end Nock.NockVMROM.Thm54
