/-
  Nock/NockVMROM/Thm54/FamilyComputeRows.lean

  `rowEnvAt` gathers `Qc` with `computeChalValOfTuple` (mentions `Qc`).
  `deployed_row_vcomp_at` needs `hz : nprSeed c.1 ≠ 0`, not the package `z`.
  Old statements remain corollaries at `honestTuple`.

  Paper: the paper (`V_comp`), `:1697` (`Lem:equiv_compute`),
  `:1893-1895` (SV).
-/
import Nock.NockVMROM.Thm54.DeployedComputeRows
import Nock.NockVMROM.Thm54.DeployedChipFamily
import Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
import Nock.NockVMROM.Thm54.CoordinateBasis
import Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
import Nock.NockVMROM.Thm54.OptimizedMemoryRAP
import Nock.NockVMROM.Thm54.P8Core.FamilyComputeRows
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

namespace Nock.NockVMROM.Thm54.FamilyComputeRows

open scoped Polynomial
open Polynomial
open Nock
open Nock.Reified
open Nock.ComputeTable
open Nock.Framework
open Nock.Framework.Reify
open OptimizedStrictPackage
open OptimizedStrictFullPackage
open OptimizedComputeHostileAccumulator
open OptimizedHostileTimestamps
open OptimizedComputeBaseGates
open OptimizedComputeFinal
open OptimizedComputeGateBasis
open OptimizedComputeSubstitution
open OptimizedComputeSemanticRealization
open OptimizedComputeCorrectedFinal
open ComputePaperPacking
open DeployedComputeRows
open DeployedChipFamily
open CoordinateBasis
open CoordinateCompiler
open Module
open MonolithicRAP
open OptimizedMemoryGateBasis
open OptimizedMemoryRAP

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

variable (c : OptimizedProductionChallengeTuple K F)
  (Qc : Fin (P.computeChipAt c).rap.w → F[X])
  (hsat : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) Qc)
include hsat

variable (hz : nprSeed c.1 ≠ 0)
include hz

/-- Named; not used as a substitute for
the family theorem. -/
theorem deployed_row_vcomp_honest_corollary
    (Qc₀ : Fin P.computeChip.rap.w → F[X])
    (hsat₀ : RAP.SatisfiesWithPreprocessing P.computeChip Qc₀)
    (hz0 : P.optimized.family.problem.cfg.challenges.z ≠ 0)
    (i : Fin (rows P)) :
    VcompAt (rowEnv P Qc₀ i) :=
  deployed_row_vcomp P Qc₀ hsat₀ hz0 i

end

end Nock.NockVMROM.Thm54.FamilyComputeRows

#print axioms Nock.NockVMROM.Thm54.FamilyComputeRows.rowEnvAt_chal9_lambda
#print axioms Nock.NockVMROM.Thm54.FamilyComputeRows.rowEnvAt_chal
