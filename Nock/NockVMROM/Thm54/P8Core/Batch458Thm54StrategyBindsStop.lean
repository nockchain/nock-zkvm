/-
  Nock/NockVMROM/Thm54/P8Core/Batch458Thm54StrategyBindsStop.lean

  Relocated below the statement file: declarations of
  `Nock.RedTeam.Batch458Thm54StrategyBindsStop`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/RedTeam/Batch458Thm54StrategyBindsStop.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.P8Core.FamilyComputeRows
import Nock.NockVMROM.Thm54.BelowDefs.P8Core.Batch458Thm54StrategyBindsStop
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch458

open scoped Polynomial
open Polynomial
open Nock
open Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ComputeWalkSeed
open Nock.NockVMROM.Thm54.ComputeWalkLabel
open Nock.NockVMROM.Thm54.DeployedComputeRows
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.StrategyOfTraces
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.ComputePaperPacking
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness
open Nock.NockVMROM.Thm54.OptimizedComputeTemplate
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.Framework
open MonolithicRAP
open OptimizedComputeHostileAccumulator
open Module

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
variable (c : OptimizedProductionChallengeTuple K F)
  (Qc : Fin (P.computeChipAt c).rap.w → F[X])

/-- Stated at the committed family trace; not proved (see the STOPs). -/
def ChipRootBinding : Prop :=
  ∃ st0 : State,
    OneHotSelector (rowEnvAt P c Qc (firstRow P)).toSourceEnv st0 ∧
      bindFP (nprSeed c.1) P.optimized.verifier.raw.claim.subject
          (decodePub (rowEnvAt P c Qc (firstRow P)) st0).s ∧
        bindFP (nprSeed c.1) P.optimized.verifier.raw.claim.formula
          (decodePub (rowEnvAt P c Qc (firstRow P)) st0).f ∧
        bindFP (nprSeed c.1) P.optimized.verifier.raw.claim.result
          (decodePub (rowEnvAt P c Qc (firstRow P)) st0).e

end

end Nock.RedTeam.Batch458
