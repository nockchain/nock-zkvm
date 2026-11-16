/-
  Nock/NockVMROM/Thm54/P8Core/Batch408Thm54SeedBoundaryGates.lean

  Relocated below the statement file: declarations of
  `Nock.RedTeam.Batch408Thm54SeedBoundaryGates`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/RedTeam/Batch408Thm54SeedBoundaryGates.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackageDefs
import Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch408

open Nock
open Nock.MemoryTable
open Nock.Reified
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.AxisBatching.MTree

section Generic

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

theorem rootMaskCountsGate_mem :
    rootMaskCountsGate (F := F) ∈ paperKGates (F := F) (K := K) := by
  simp [paperKGates, paperEndpointGates]

theorem rootMaskIndicatorGate_mem :
    rootMaskIndicatorGate (F := F) ∈ paperKGates (F := F) (K := K) := by
  simp [paperKGates, paperEndpointGates]

theorem rootMaskCountsGate_eval (eK : Env K) (eF : Env F) :
    (rootMaskCountsGate (F := F)).eval eK eF =
      algebraMap F K (eF.trace 153) * eK.trace 4 := by
  simp [rootMaskCountsGate, MixedExpr.eval, rootMask, bcur, CoeffExpr.eval,
    rootMaskCol]

theorem rootMaskIndicatorGate_eval (eK : Env K) (eF : Env F) :
    (rootMaskIndicatorGate (F := F)).eval eK eF =
      algebraMap F K (eF.trace 153) * eK.trace 3 := by
  simp [rootMaskIndicatorGate, rootMaskPwGate, MixedExpr.eval, rootMask, bcur, CoeffExpr.eval,
    rootMaskCol]

end Generic

end Nock.RedTeam.Batch408
