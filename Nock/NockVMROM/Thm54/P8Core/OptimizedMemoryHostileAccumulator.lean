/-
  Nock/NockVMROM/Thm54/P8Core/OptimizedMemoryHostileAccumulator.lean

  Relocated below the statement file: declarations of
  `Nock.NockVMROM.Thm54.OptimizedMemoryHostileAccumulator`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/NockVMROM/Thm54/OptimizedMemoryHostileAccumulator.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.P8Core.DeployedAcceptance
import Nock.NockVMROM.Thm54.P8Core.OptimizedComputeHostileAccumulator
import Nock.NockVMROM.Thm54.BelowDefs.P8Core.OptimizedMemoryHostileAccumulator
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

namespace Nock.NockVMROM.Thm54

namespace OptimizedMemoryHostileAccumulator

open Nock
open Nock.Reified
open Nock.Framework
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open OptimizedMemoryGateBasis
open OptimizedMemoryRAP
open OptimizedMemoryCanonicalSatisfaction
open StrictExtension
open OptimizedStrictFullPackage
open OptimizedComputeFinalTrace
open Module
open scoped Polynomial

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

theorem intermediateInit_mem (b : Basis (Fin 3) F K) :
    intermediateInit (F := F) ∈ mixedTransitionGates (K := K) b := by
  simp [mixedTransitionGates, paperKGates, paperEndpointGates]

theorem intermediateTerminal_mem (b : Basis (Fin 3) F K) :
    intermediateTerminal (F := F) ∈ mixedTransitionGates (K := K) b := by
  simp [mixedTransitionGates, paperKGates, paperEndpointGates]

theorem chainMixed_mem (b : Basis (Fin 3) F K) :
    chainMixed (F := F) ∈ mixedTransitionGates (K := K) b := by
  simp [mixedTransitionGates, paperKGates, paperKGatesCore, intermediateChain]

section Deployed

variable [Fintype K] [DecidableEq K] [CharP K (ringChar K)] {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- The source chip the consumed memory chip pads. -/
abbrev sourceOf : FixedPreprocessingRAP F :=
  namedSourceMemoryRAP P.optimized.family.problem.cfg.memRows_pos P.optimized.memoryNodes
    P.optimized.basis P.optimized.memoryChallenge P.optimized.memoryPublic P.optimized.orbit
    P.optimized.family.problem.cfg.kMem

abbrev rows : ℕ := P.optimized.family.problem.cfg.memRows

abbrev firstRow : Fin (rows P) := ⟨0, P.optimized.family.problem.cfg.memRows_pos⟩

abbrev lastRow : Fin (rows P) :=
  ⟨rows P - 1, Nat.sub_lt P.optimized.family.problem.cfg.memRows_pos (by omega)⟩

variable (Qm : Fin P.memoryChip.rap.w → F[X])
  (hsat : RAP.SatisfiesWithPreprocessing P.memoryChip Qm)
include hsat

omit hsat in
/-- **The two chips read the same `requests`.** -/
theorem compute_requests_eq_memory_requests :
    (∑ k : Fin 3, P.optimized.computePublic (6 + (k : ℕ)) • P.optimized.basis k) =
      ∑ k : Fin 3, P.optimized.memoryPublic (12 + (k : ℕ)) • P.optimized.basis k := by
  have hc : (∑ k : Fin 3, P.optimized.computePublic (6 + (k : ℕ)) • P.optimized.basis k) =
      P.optimized.sampled.witness10.terminal := by
    rw [eq_iff_coords_eq P.optimized.basis]
    intro k
    rw [coord_sum_smul]
    exact P.optimized.computeRequestsPins k
  have hm := P.optimized.memoryRealization.coordinate_pins.requests
  rw [hc, ← hm]

end Deployed

end

end OptimizedMemoryHostileAccumulator

end Nock.NockVMROM.Thm54
