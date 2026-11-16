/-
  Nock/NockVMROM/Thm54/P8Core/Batch453Thm54SeedWiring.lean

  Relocated below the statement file: declarations of
  `Nock.RedTeam.Batch453Thm54SeedWiring`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/RedTeam/Batch453Thm54SeedWiring.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.P8Core.FamilyComputeRows
import Nock.NockVMROM.Thm54.TraceGen.GenRootState
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch453

open scoped Polynomial
open Polynomial
open Nock
open Nock.Reified
open Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ComputeWalkSeed
open Nock.NockVMROM.Thm54.ComputeWalkLabel
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTypedLowering
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.Framework
open Module
open MonolithicRAP
open OptimizedComputeHostileAccumulator

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- Family publics `3..5` are the 𝔽-coordinates of `seedOfClaim`. -/
theorem family_seed_slots
    (c : OptimizedProductionChallengeTuple K F) (k : Fin 3) :
    P.familyComputePublic c (3 + (k : ℕ)) =
      coord P.optimized.basis
        (seedOfClaim P.optimized.verifier.raw.claim c) k :=
  computePublicOfTuple_seed_coord P.optimized.basis
    P.optimized.verifier.raw.claim P.optimized.computePublic c k

end

end Nock.RedTeam.Batch453
