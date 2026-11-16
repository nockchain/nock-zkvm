/-
  Nock/NockVMROM/Thm54/P8Core/WrapMemoryConjuncts.lean

  Relocated below the statement file: declarations of
  `Nock.NockVMROM.Thm54.WrapMemoryConjuncts`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/NockVMROM/Thm54/WrapMemoryConjuncts.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.P8Core.FamilyMemoryRows
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

namespace Nock.NockVMROM.Thm54.WrapMemoryConjuncts

open scoped Polynomial Classical
open Polynomial
open Nock
open Nock.MemoryTable
open Nock.Reified
open Nock.Framework
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.StrategyOfTraces
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.OptimizedMemoryRAP
open Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction
open Nock.NockVMROM.Thm54.MemoryPaperFactorization
open Nock.NockVMROM.Thm54.OptimizedMemoryHostileAccumulator
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.Framework.Thm54
open MonolithicRAP
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
variable {K : Type} [Field K]
variable {F : Type} [Field F] [Algebra F K]

noncomputable section

variable [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- Reindex a constant-chip memory trace at the family width. -/
def familyQm
    (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin P.memoryChip.rap.w → F[X]) :
    Fin (P.memoryChipAt c).rap.w → F[X] :=
  fun j => Qm (Fin.cast (memoryChipAt_width P c) j)

end

end Nock.NockVMROM.Thm54.WrapMemoryConjuncts
