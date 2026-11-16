/-
  Nock/NockVMROM/Thm54/P8Core/Batch884Thm54Part2aFamIOInstance.lean

  Relocated below the statement file: declarations of
  `Nock.RedTeam.Batch884Thm54Part2aFamIOInstance`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/RedTeam/Batch884Thm54Part2aFamIOInstance.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.P8Core.FamilyIOChainRouteB
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 2000

namespace Nock.RedTeam.Batch884

open scoped Polynomial
open Polynomial
open Nock
open Nock.Reified
open Nock.Framework
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.FamilyIOChain

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- `WrapMemoryConjuncts.familyQm`, restated below that module. -/
def famQm (c : OptimizedProductionChallengeTuple K F) (Qm : Fin P.memoryChip.rap.w → F[X]) :
    Fin (P.memoryChipAt c).rap.w → F[X] :=
  fun j => Qm (Fin.cast (memoryChipAt_width P c) j)

variable (Qc : Fin P.computeChip.rap.w → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X])

def famIOEventOf : Finset (OptimizedProductionChallengeTuple K F) :=
  Finset.univ.filter fun c =>
    c.2.1 ∈ FiniteIO.IOFailureEvent (hostileRecordsAt P c (famQm P c Qm) (familyQc P c Qc))

/-- What the twins consume: outside the event, `FamilyIOGood` at the reindexed traces. -/
theorem familyIOGood_of_not_mem (c : OptimizedProductionChallengeTuple K F)
    (h : c ∉ famIOEventOf P Qc Qm) :
    FamilyIOGood P c (familyQc P c Qc) (famQm P c Qm) := by
  simpa [famIOEventOf, FamilyIOGood] using h

end

end Nock.RedTeam.Batch884
