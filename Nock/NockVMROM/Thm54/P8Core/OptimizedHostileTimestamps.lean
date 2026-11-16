/-
  Nock/NockVMROM/Thm54/P8Core/OptimizedHostileTimestamps.lean

  Relocated below the statement file: declarations of
  `Nock.NockVMROM.Thm54.OptimizedHostileTimestamps`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/NockVMROM/Thm54/OptimizedHostileTimestamps.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.P8Core.OptimizedHostileIOAssembly
import Nock.NockVMROM.Thm54.BelowDefs.P8Core.OptimizedHostileTimestamps
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

namespace Nock.NockVMROM.Thm54

namespace FiniteIO

open Polynomial
open scoped BigOperators
variable {K : Type*} [Field K] {m : ℕ} [Fintype K] [DecidableEq K] {p : ℕ} [CharP K p]

end FiniteIO

namespace OptimizedHostileTimestamps

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
open OptimizedComputeHostileAccumulator
open OptimizedMemoryGateBasis
open StrictExtension
open OptimizedStrictFullPackage
open OptimizedComputeFinalTrace
open ConcreteStrictPackage
open TemplateRawJointSoundness
open Module
open scoped Polynomial

noncomputable section

variable {F K : Type} [Field F]
  [Field K] [Algebra F K] [FiniteDimensional F K]

section Arity

variable [DecidableEq K]

end Arity

section Assembly

open OptimizedHostileIOAssembly
variable [Fintype K] [DecidableEq K] [CharP K (ringChar K)] {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (Qc : Fin P.computeChip.rap.w → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X])

section Acceptance

variable [Fintype F] [DecidableEq F]
variable (c : OptimizedStrictPackage.OptimizedProductionChallengeTuple K F)

/-- `optimizedFailureEvent` lifts
`ProductionP8Containment.FailureUnion`, whose first summand is
`zeroSeedFailureEvent` (`ω ∈ _ ↔ nprSeed ω = 0`), priced in `p8Work` as the leading `1`
(`ProductionP8Containment.workload`).  the paper. -/
theorem nprSeed_ne_of_good (hgood : c ∉ P.optimizedFailureEvent Qc Qm) :
    nprSeed c.1 ≠ 0 := by
  have hp8 := (P.optimizedFailureEvent_good_components Qc Qm c hgood).1
  intro hz
  refine hp8 ?_
  simp [ProductionP8Containment.FailureUnion, mem_zeroSeedFailureEvent_iff, hz]

end Acceptance

end Assembly

end

end OptimizedHostileTimestamps

end Nock.NockVMROM.Thm54
