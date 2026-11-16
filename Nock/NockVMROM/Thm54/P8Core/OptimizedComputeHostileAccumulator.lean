/-
  Nock/NockVMROM/Thm54/P8Core/OptimizedComputeHostileAccumulator.lean

  Relocated below the statement file: declarations of
  `Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/NockVMROM/Thm54/OptimizedComputeHostileAccumulator.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackageDefs
import Nock.NockVMROM.Thm54.BelowDefs.P8Core.OptimizedComputeHostileAccumulator
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

namespace Nock.NockVMROM.Thm54

namespace OptimizedComputeHostileAccumulator

open Nock
open Nock.Reified
open Nock.Framework
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open OptimizedComputeBaseGates
open OptimizedComputeFinal
open OptimizedComputeCorrectedFinal
open OptimizedComputeGateBasis
open OptimizedComputeSubstitution
open OptimizedComputeFiniteIOGates
open OptimizedComputeSemanticRealization
open StrictExtension
open OptimizedStrictFullPackage
open OptimizedComputeFinalTrace
open Module
open scoped Polynomial

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

section Deployed

variable [Fintype K] [DecidableEq K] [CharP K (ringChar K)] {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- The gathered typed environment of `Qc` at row `i`. -/
abbrev rowEnv (Qc : Fin P.computeChip.rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.compRows) : CorrectedFinalTypedEnv F K :=
  gatherCorrectedFinalTypedEnv P.optimized.basis
    (envOfTrace Qc P.optimized.orbit.ω (P.optimized.computeNodes i)
      P.optimized.computeChallenge P.optimized.computePublic)

abbrev rows : ℕ := P.optimized.family.problem.cfg.compRows

abbrev firstRow : Fin (rows P) := ⟨0, P.optimized.family.problem.cfg.compRows_pos⟩

abbrev lastRow : Fin (rows P) :=
  ⟨rows P - 1, Nat.sub_lt P.optimized.family.problem.cfg.compRows_pos (by omega)⟩

variable (Qc : Fin P.computeChip.rap.w → F[X])
  (hsat : RAP.SatisfiesWithPreprocessing P.computeChip Qc)
include hsat

/-- **The request list read off the trace**: every row's emitted records, in row order. -/
def hostileRequests : List (Fin 10 → K) :=
  (List.ofFn fun i : Fin (rows P) => rowRequests (rowEnv P Qc i)).flatten

end Deployed

end

end OptimizedComputeHostileAccumulator

end Nock.NockVMROM.Thm54
