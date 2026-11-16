/-
  Nock/NockVMROM/Thm54/P8Core/Batch521Thm54ReadRootImpliesVer.lean

  Relocated below the statement file: declarations of
  `Nock.RedTeam.Batch521Thm54ReadRootImpliesVer`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/RedTeam/Batch521Thm54ReadRootImpliesVer.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.P8Core.FamilyMemoryRows

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch521

open scoped Polynomial
open Polynomial
open Nock
open Nock.Reified
open Nock.Framework
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.OptimizedMemoryHostileAccumulator
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.MemoryPaperFactorization
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.StrategyOfTraces
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedMemoryRAP
open Nock.Framework.Reify
open Module
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

theorem readRootVerGate_eval (b : Basis (Fin 3) F K) (envF : Env F) :
    (readRootVerGate b).eval envF =
      envF.trace 2 * (coord b (1 : K) (0 : Fin 3) - envF.trace (6 + 3 * 39)) := by
  simp [readRootVerGate, CoeffExpr.eval, bcur, extCoord]

theorem gather_ver_coord0 (b : Basis (Fin 3) F K) (envF : Env F) :
    coord b ((gatherEnv b memoryCol0 envF).trace 39) (0 : Fin 3) =
      envF.trace (6 + 3 * 39) := by
  simpa [gatherEnv, memoryCol0] using
    coord_sum_smul b (fun j => envF.trace (6 + 3 * 39 + (j : ℕ))) (0 : Fin 3)

end Nock.RedTeam.Batch521
