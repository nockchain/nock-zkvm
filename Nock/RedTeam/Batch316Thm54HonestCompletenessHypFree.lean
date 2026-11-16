/-
  Nock/RedTeam/Batch316Thm54HonestCompletenessHypFree.lean

  The capstone constructor
  `optimizedFullStrictNockVMROM_of_package` stays hyp-free — no
  `MemoryCompletenessHyps` binder.  Completeness hyps are derived inside the
  package (`memoryCompletenessHyps` from `pairedRecordLayout` +
  `hdenAll_of_interPoleHitGood`).

  Paper at source: the paper.
-/
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

namespace Nock.RedTeam.Batch316

open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace

/-- The capstone constructor takes no completeness hyp.  Form R SAT
    fragments (`FormRAxisBound` / `FormRBasis` / `FormRWidth`) are the
    leftover-certificate discharge, not `FormRCover` and not a
    `nockCompiles_zmod` binder. -/
theorem capstone_of_package_is_hyp_free
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F) :
    OptimizedFullStrictThm54Statement P :=
  optimizedFullStrictNockVMROM_of_package P hax hbasis hwidth

/-- Realization surface is a field projection.  Form R SAT fragments
    discharge the leftover certificate; no completeness binder. -/
theorem realization_surface_is_field
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb : ℕ} (P : OptimizedStrictNockVMROMPackage F K hOrb)
    (hax : FormRAxisBound P.sampled P.basis)
    (hbasis : FormRBasis P.basis)
    (hwidth : FormRWidth F) :
    OptimizedComputeRealizationAt P.sampled P.computeObligations P.computeNodes P.basis
        P.computeChallenge P.computePublic P.orbit ∧
      OptimizedMemoryRealizationAt P.sampled P.memoryProduction P.memoryNodes P.basis
        P.memoryChallenge P.memoryPublic P.orbit :=
  P.realization_surface_is_optimized hax hbasis hwidth

end Nock.RedTeam.Batch316

#print axioms Nock.RedTeam.Batch316.capstone_of_package_is_hyp_free
#print axioms Nock.RedTeam.Batch316.realization_surface_is_field
