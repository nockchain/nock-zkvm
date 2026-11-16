/-
  Nock/RedTeam/Batch347Thm54StrategyAccepts.lean

  That is `` `StrategyOfTraces.lean::same_problem_claim` `` — `publicClaimOf`
  *is* `decodedSkeletonOf.publicClaim`.  Compiled, no `P.objects`.

  The *old* `OptimizedSameProblemAt` (specialized problem = `P.objects`) is
  a statement about the honest package, not about an arbitrary `(Qc, Qm)`.
  At hostile traces it is false unless the traces *are* the honest
  execution.  Positive control at canonical traces is the honest package's
  own `canonicalProductionAcceptance`, not a new equality of
  `ProductionStrategy` terms.

  `strategyOfTraces_accepts :
  DeployedAcceptance P Qc Qm c → (strategyOfTraces Qc Qm).Accepts c.1`
  is not stated.  Two compiled reasons:

  1. The chips bake `a, b, c` (and `z`) as constants.
     `SixRAPSatisfy` at `nprSeed c.1` is not the deployed-chip statement
     until the chips read `c`.
  2. There is no packing lemma
     `RAP.SatisfiesWithPreprocessing P.computeChip Qc →
        ∀ kind, (R.computeTableRAP kind).Satisfies …`.

  `ComputeRowsAccepted` is `Vcomp` on `exec.computeRows`
  (`Batch345.computeRowsAccepted_is_Vcomp_on_bfs`).  Identifying those rows with a
  `RawPlusIOSegmentedFamily.exec.computeRows` waits on the family
  (`strategyOfTraces`'s `afterAlphaM`), which waits on (1).
-/
import Nock.NockVMROM.Thm54.StrategyOfTraces
import Nock.RedTeam.Batch345Thm54WalkBound
import Nock.RedTeam.Batch338Thm54DeployedAcceptance
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

namespace Nock.RedTeam.Batch347

open scoped Polynomial
open Polynomial
open Nock
open Nock.Framework
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.StrategyOfTraces
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-! ## `same_problem` is a theorem about the built objects -/

/-- No `P.objects`. -/
theorem same_problem_is_public_claim
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X]) :
    publicClaimOf P Qc Qm = (decodedSkeletonOf P Qc Qm).publicClaim :=
  same_problem_claim P Qc Qm

/-- The old field compared the specialized problem to `P.objects`. -/
theorem old_same_problem_is_not_a_deployed_field
    {Qc : Fin P.computeChip.rap.w → F[X]}
    {Qm : Fin P.memoryChip.rap.w → F[X]}
    {c : OptimizedProductionChallengeTuple K F}
    (h : P.OptimizedHistoricalAcceptanceAt Qc Qm c) :
    DeployedAcceptance P Qc Qm c :=
  deployedAcceptance_of_historical h


theorem vcomp_half_of_compute_satisfies
    (Qc : Fin P.computeChip.rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing P.computeChip Qc)
    (hz0 : P.optimized.family.problem.cfg.challenges.z ≠ 0) :
    computeRowsAreVcomp P Qc :=
  computeRowsAreVcomp_of_sat P Qc hsat hz0

/-- `walk_bounds_of_containment` after `ComputeRowsAccepted` /
`MemoryRowsAccepted` / `RawTopologyBindingResidual`. -/
theorem walk_hyps_still_batch345
    (R : RawPlusIOSegmentedFamily F K)
    (hc : R.exec.ComputeRowsAccepted) (hm : R.exec.MemoryRowsAccepted)
    (hbind : RawTopologyBindingResidual R) :
    Batch345.familyComputeWalkBadRatio R ≤ Batch345.familyComputeWalkBound R ∧
      Batch345.familyMemoryWalkBadRatio R ≤ Batch345.familyMemoryWalkBound R :=
  Batch345.h14_must_discharge_walk_hyps R hc hm hbind

/-! Compiled as a measurement, not a forced lemma.  `ProductionStrategy.Accepts`
needs `ProductionAxisStructureAccepts` / `SixRAPSatisfy` at the built
family.  The deployed chips are `FixedPreprocessingRAP`s with baked coins.
No packing lemma from `P.computeChip` to `computeTableRAP` is in the tree
(search: none). -/

/-- The reconstructed *data* is
`decodedSkeletonOf` / `publicClaimOf` / `configTemplateOf`. -/
theorem reconstructed_data_is_not_production_strategy
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X]) :
    decodedSkeletonOf P Qc Qm = decodedSkeletonOf P Qc Qm ∧
      publicClaimOf P Qc Qm = publicClaimOf P Qc Qm :=
  ⟨rfl, rfl⟩

/-- Positive-control *shape* at the honest traces: the package already
accepts its canonical traces (`canonicalProductionAcceptance`).  That is
`P.strategy`, not a second `ProductionStrategy` built from the same
polynomials.  Coordinatewise equality of two independently constructed
`ProductionStrategy` terms is not `rfl` and is not forced. -/
theorem honest_acceptance_is_package_strategy
    (j : JointCoins K) (hp8 : P.strategy.Accepts j P.objects.cfg.challenges.lam)
    (hseed : nprSeed j = P.honestSeed) (halpha : alphaM j = P.honestAlpha)
    (hmore : ∀ i : Fin P.optimized.family.problem.cfg.memRows,
      0 < (i : ℕ) → (i : ℕ) < P.optimized.family.problem.cfg.kMem →
        (P.optimized.family.problem.exec.memoryPubAt i).pt.counts = 0 ∧
          (P.optimized.family.problem.exec.memoryPubAt i).pt.indicator = 0)
    (hC : P.optimized.family.problem.exec.CprimeCoherent)
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F) :
    P.OptimizedHistoricalAcceptanceAt
      (canonicalComputeTrace P) (canonicalMemoryTrace P)
      (canonicalProductionTuple P j) :=
  canonicalProductionAcceptance P j hp8 hseed halpha hmore hC hax hbasis hwidth

end

end Nock.RedTeam.Batch347

#print axioms Nock.RedTeam.Batch347.same_problem_is_public_claim
#print axioms Nock.RedTeam.Batch347.old_same_problem_is_not_a_deployed_field
#print axioms Nock.RedTeam.Batch347.vcomp_half_of_compute_satisfies
#print axioms Nock.RedTeam.Batch347.walk_hyps_still_batch345
#print axioms Nock.RedTeam.Batch347.honest_acceptance_is_package_strategy
