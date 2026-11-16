/-
  Nock/NockVMROM/Thm54/P8Core/DeployedAcceptance.lean

  Relocated below the statement file: declarations of
  `Nock.NockVMROM.Thm54.DeployedAcceptance`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/NockVMROM/Thm54/DeployedAcceptance.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackageDefs
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

namespace Nock.NockVMROM.Thm54

open scoped Polynomial
open Polynomial
open Nock.Framework
open OptimizedStrictPackage
open OptimizedStrictFullPackage
open OptimizedComputeCorrectedFinal
open OptimizedComputeFinal
set_option autoImplicit false
set_option linter.unusedSectionVars false
variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}

/-- Acceptance at the chip *family*.  No pin fields — the chips read `c`.
Traces are indexed by the family RAP's own `w` (see module docstring).
Public equality checks are already gates (`finalEndpointEqualityChecks_mem_allGates`).

**** the capstone's `OptimizedProductionAcceptanceAt Qc Qm c`
is now exactly this predicate at `familyQc c Qc` / `familyQm c Qm`
(`deployedAcceptanceAt_iff_acceptance`, both directions field-by-field with no rewriting).  A
literal `abbrev` alias in the other orientation (at `honestQc`/`honestQm`) times out in the kernel
(the `Fin` eta through the two width casts), so the alias is this `iff`. -/
structure DeployedAcceptanceAt
    (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (c : OptimizedProductionChallengeTuple K F)
    (Qc : Fin (P.computeChipAt c).rap.w → F[X])
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X]) : Prop where
  compute_satisfies :
    RAP.SatisfiesWithPreprocessing (P.computeChipAt c) Qc
  memory_satisfies :
    RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm

end Nock.NockVMROM.Thm54
