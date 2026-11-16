import Nock.NockVMROM.Thm54.DistinctCensusFold2
import Nock.NockVMROM.Thm54.WalkTilingEvents
import Nock.RedTeam.Batch86Thm54DistinctCensusPhaseCorrect
import Nock.RedTeam.Batch82Thm54OptimizedAcceptance
import Nock.NockVMROM.Thm54.Walk37.PaperNames
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
# Collision-free selector fold at the consumed Theorem 5.4 package

Paper frame:

Consumed release declaration:
`OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package`.

The package result passes at its exact scope: one fixed `packageR`, the committed
`(alphaM,nprSeed)=(4,8)` fibre, and the canonical optimized traces.  The accepted
tuple is outside all four summands of the complete optimized failure event, and
the released `acceptance_to_target` field therefore has an inhabited antecedent.

There is one paper-provenance finding.  `challenge9`, `challenge11`, and
base-field `challenge36` are the Lean optimized compiler-fold namespace, not the
paper's compute-input vector `(alpha,z,a,b,c) ∈ K^5`.  In the current paper,
the paper describes formula decomposition and does not introduce a
selector challenge.  The paper's one-hot selector constraints are
the paper; its uniform compute inputs are the paper; and its
gate-combination discussion is the paper.
-/

set_option autoImplicit false

namespace Nock.RedTeam.Batch87

open scoped Classical Polynomial
open Module Polynomial
open Nock Nock.Noun Nock.Walk Nock.Framework Nock.Reified Nock.NockVM
open Nock.Framework.Reify
open Nock.ComputeTable Nock.MemoryTable
open Nock.NockVMROM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.NockVMROM.Thm54.EqualityOperandCensus
open Nock.NockVMROM.Thm54.DistinctCensusExecution
open Nock.NockVMROM.Thm54.DistinctCensusCommitment
open Nock.NockVMROM.Thm54.DistinctCensusHonestArrays
open Nock.NockVMROM.Thm54.DistinctCensusPhaseCorrect
open Nock.NockVMROM.Thm54.DistinctCensusFold2
open Nock.NockVMROM.Thm54.MultiRootHonestCommitment
open Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges
open Nock.NockVMROM.Thm54.MultiRootPhaseCorrect
open Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance
open Nock.NockVMROM.Thm54.OptimizedComputeCollisionBound
open Nock.NockVMROM.Thm54.OptimizedComputeCanonicalSatisfaction
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.BuildablePackage
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace

noncomputable section

local instance prime97b87 : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic
local instance char97b87 : CharP K97cubic 97 := inferInstance
local instance : CharP K97cubic (ringChar K97cubic) := ringChar.charP K97cubic

variable (hfirstD :
  (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.counts = 0 ∧
    (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.indicator = 0)
variable (haxR : FormRAxisBound (packageR hfirstD).optimized.sampled (packageR hfirstD).optimized.basis)
variable (hbasisR : FormRBasis (packageR hfirstD).optimized.basis)
variable (hwidthR : FormRWidth F97)
include hfirstD
variable (hrootAt : ∀ a g : K97cubic,
  (packageR hfirstD).strategy.RootAxisBoundaryAt
    (nprSeed (coinQ a g)) seedH_ne (alphaM (coinQ a g)))
include hrootAt
variable (hrootAtQ : ∀ a g : K97cubic,
  (packageQ hfirstD).strategy.RootAxisBoundaryAt
    (nprSeed (coinQ a g)) seedH_ne (alphaM (coinQ a g)))
include hrootAtQ
variable (hmoreM : BuildableAxisWitness.LaterSeedZeros
    Nock.NockVMROM.Thm54.MultiRootServedFixture.multiRootExecution)
include hmoreM
variable (haxP : FormRAxisBound (packageP hmoreM).optimized.sampled
    (packageP hmoreM).optimized.basis)
variable (hbasisP : FormRBasis (packageP hmoreM).optimized.basis)
variable (hwidthP : FormRWidth F97)
variable (hrootAtP : ∀ a g : K97cubic,
  (packageP hmoreM).strategy.RootAxisBoundaryAt
    (nprSeed (coinN a g)) MultiRootHonestArrays.seedM_ne (alphaM (coinN a g)))
include hrootAtP

/-! ## A. -/

theorem released_aliases_and_control_unchanged :
    @«Thm:NockVMROM» =
        @OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package ∧
      @«Thm:NockVMROM:forest-control» = @Nock.NockVM.V_NockVMROM_forest :=
  Nock.RedTeam.Batch86.released_aliases_and_control_unchanged hfirstD hrootAtQ

/-- Exact fourteen-field eta receipt for the statement consumed at `(packageR hfirstD)`. -/
theorem statementR_fourteen_field_eta
    (haxR : FormRAxisBound (packageR hfirstD).optimized.sampled (packageR hfirstD).optimized.basis)
    (hbasisR : FormRBasis (packageR hfirstD).optimized.basis)
    (hwidthR : FormRWidth F97) :
    (statementR hfirstD haxR hbasisR hwidthR) =
      { structural := (statementR hfirstD haxR hbasisR hwidthR).structural
        optimized_chips := (statementR hfirstD haxR hbasisR hwidthR).optimized_chips
        shared_io := (statementR hfirstD haxR hbasisR hwidthR).shared_io
        perfect_completeness := (statementR hfirstD haxR hbasisR hwidthR).perfect_completeness
        containment := (statementR hfirstD haxR hbasisR hwidthR).containment
        walk_bounds := (statementR hfirstD haxR hbasisR hwidthR).walk_bounds
        p8_fixed_field_soundness := (statementR hfirstD haxR hbasisR hwidthR).p8_fixed_field_soundness
        p8_fixed_field_bits := (statementR hfirstD haxR hbasisR hwidthR).p8_fixed_field_bits
        acceptance_to_target := (statementR hfirstD haxR hbasisR hwidthR).acceptance_to_target
        complete_false_acceptance_bound := (statementR hfirstD haxR hbasisR hwidthR).complete_false_acceptance_bound
        complete_false_acceptance_bits := (statementR hfirstD haxR hbasisR hwidthR).complete_false_acceptance_bits
        staged_false_acceptance_bound := (statementR hfirstD haxR hbasisR hwidthR).staged_false_acceptance_bound
        exact_resources := (statementR hfirstD haxR hbasisR hwidthR).exact_resources
        row_budgets := (statementR hfirstD haxR hbasisR hwidthR).row_budgets
        shared_forest_axis := (statementR hfirstD haxR hbasisR hwidthR).shared_forest_axis } := by
  cases (statementR hfirstD haxR hbasisR hwidthR)
  rfl

theorem released_hzero_boundary_is_load_bearing :
    (∀ (I : Inputs (distinctCensusExecution hfirstD))
      (_R : CommitmentResidual (distinctCensusExecution hfirstD)),
      I.computeChallenges = default →
        (2 ≤ (distinctCensusExecution hfirstD).cfg.compRows →
          (distinctCensusExecution hfirstD).cfg.compRows ≤ orderOf I.computeWalkAlpha) →
        (2 ≤ (distinctCensusExecution hfirstD).cfg.memRows →
          (distinctCensusExecution hfirstD).cfg.memRows ≤ orderOf I.memoryWalkAlpha) →
        GeneratedField.ClaimGenerated K97cubic _R.verifier.raw.claim _R.Λ →
        Nonempty (OptimizedFullStrictNockVMROMPackage F97 K97cubic I.hOrb)) ∧
      (inputsR hfirstD).computeChallenges = default :=
  released_hzero_still_required hfirstD hrootAt hrootAtQ

/-! ## B. `With` is a selector-only mixed assignment, not a full generalization -/

theorem selector_only_mixed_assignment :
    fold2Challenges = (default :
      FinalComputeChallengeTuple K97cubic) ∧
      ExactFinalChallengeCoordinatesWith (inputsR hfirstD).basis
        (sampledAssignment (distinctCensusExecution hfirstD) (inputsR hfirstD))
        (inputsR hfirstD).computeChallenges
        (computeChallenge (distinctCensusExecution hfirstD) (inputsR hfirstD)) ∧
      ExactFinalChallengeCoordinates (inputsR hfirstD).basis
        (sampledAssignment (distinctCensusExecution hfirstD) (inputsR hfirstD))
        (computeChallenge (distinctCensusExecution hfirstD) (inputsR hfirstD)) ∧
      (inputsR hfirstD).computeChallenges = (default : FinalComputeChallengeTuple K97cubic) := by
  refine ⟨rfl, computeChallenge_pins (distinctCensusExecution hfirstD) (inputsR hfirstD),
    computeChallenge_historical_pins_of_zero_cubic (distinctCensusExecution hfirstD) (inputsR hfirstD),
    rfl⟩

def nonzeroCubicChallenges : FinalComputeChallengeTuple K97cubic := default

def nonzeroCubicInputs : Inputs (distinctCensusExecution hfirstD) :=
  (inputsD hfirstD).withComputeChallenges nonzeroCubicChallenges

/-- Negative control: `ExactFinalChallengeCoordinatesWith` itself accepts a nonzero cubic fold,
but that input cannot discharge `buildFullPackageWith`'s `challenge9 = 0` side condition. -/
theorem parameterized_pin_is_stronger_than_the_With_constructor_scope :
    ExactFinalChallengeCoordinatesWith (nonzeroCubicInputs hfirstD).basis
        (sampledAssignment (distinctCensusExecution hfirstD) (nonzeroCubicInputs hfirstD))
        (nonzeroCubicInputs hfirstD).computeChallenges
        (computeChallenge (distinctCensusExecution hfirstD) (nonzeroCubicInputs hfirstD)) :=
  computeChallenge_pins (distinctCensusExecution hfirstD) (nonzeroCubicInputs hfirstD)

theorem fold2_reuses_the_Batch86_scalar_and_polynomial :
    (∀ j : Fin 11,
        ((packageR hfirstD).computeScalarEnv (computeTraceR hfirstD)).trace (j : ℕ) -
            ((packageR hfirstD).computeScalarEnv (computeTraceR hfirstD)).pub (31 + (j : ℕ)) =
          ((packageQ hfirstD).computeScalarEnv (computeTraceQ hfirstD)).trace (j : ℕ) -
            ((packageQ hfirstD).computeScalarEnv (computeTraceQ hfirstD)).pub (31 + (j : ℕ))) ∧
      (2 : F97) ∉ finalSelectorBadChallenges
        ((packageQ hfirstD).computeScalarEnv (computeTraceQ hfirstD)) ∧
      (2 : F97) ∉ finalSelectorBadChallenges
        ((packageR hfirstD).computeScalarEnv (computeTraceR hfirstD)) ∧
      canonicalComputeChallengeTuple (packageR hfirstD) ∉
        extensionFinalComputeCollisionEvent ((packageR hfirstD).computeSourceEnv (computeTraceR hfirstD))
          ((packageR hfirstD).computeWalkEnv (computeTraceR hfirstD)) := by
  refine ⟨?_, Nock.RedTeam.Batch86.two_is_not_packageQ_selector_bad hfirstD hrootAtQ,
    two_is_not_packageR_selector_bad hfirstD, packageR_compute_outside_failure hfirstD⟩
  intro j
  rw [packageR_selector31_error_value hfirstD,
    Nock.RedTeam.Batch86.packageQ_selector31_error_value hfirstD hrootAtQ]

/-! ## C. Quantifier order, fibre, and census threading -/

theorem one_package_and_exact_committed_fibre :
    (∃ P : OptimizedFullStrictNockVMROMPackage F97 K97cubic 5,
      P = (packageR hfirstD) ∧ ∀ a g : K97cubic, P.strategy.Accepts (coinQ a g) cfgD.challenges.lam) ∧
      (∀ ω : JointCoins K97cubic,
        ω ∈ Finset.univ.image
            (fun pair : K97cubic × K97cubic => coinQ pair.1 pair.2) ↔
          nprSeed ω = seedD ∧ alphaM ω = alphaD) :=
  ⟨⟨(packageR hfirstD), rfl, packageR_accepts hfirstD hrootAt hrootAtQ⟩,
    Nock.RedTeam.Batch86.coinQ_image_iff_committed_fibre hfirstD hrootAtQ⟩

/-- The consumed package census is the committed twenty-four-occurrence census and contains
the genuinely unequal `([7 9],[8 10])` pair. -/
theorem packageR_census_is_threaded_and_distinct :
    (packageR hfirstD).optimized.census = censusD ∧
      (packageR hfirstD).optimized.census.census.count = 24 ∧
      ∃ i : Fin (packageR hfirstD).optimized.census.census.count,
        (packageR hfirstD).optimized.census.census.pair i = (operandLeft, operandRight) ∧
          ((packageR hfirstD).optimized.census.census.pair i).1 ≠
            ((packageR hfirstD).optimized.census.census.pair i).2 := by
  refine ⟨packageR_census hfirstD, ?_,
    packageR_consumed_census_has_genuine_distinct_pair hfirstD hrootAt hrootAtQ⟩
  exact (Nock.RedTeam.Batch84.consumed_census_is_not_the_released_fixture_census
    hfirstD hmoreM hrootAtP).1

/-! ## D. Complete consumed event and informative connective -/




/-! ## E. Exact four-field tail: same names as packageP, different census evidence -/

def FourResidualFields
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb) : Prop :=
  (∀ lmb : K, |jointProbability (FalseAcceptanceSet P.strategy P.q P.optimized.Λ lmb)| ≤
      (workload P.strategy P.optimized.Λ
          (fixedTopologyWorkload P.strategy) (fixedAxisWorkload P.strategy) : ℝ) /
        (Fintype.card K : ℝ)) ∧
  (∀ (lmb : K) (b : ℕ),
    workload P.strategy P.optimized.Λ
        (fixedTopologyWorkload P.strategy) (fixedAxisWorkload P.strategy) * 2 ^ b ≤
        Fintype.card K →
      |jointProbability (FalseAcceptanceSet P.strategy P.q P.optimized.Λ lmb)| ≤ 1 / 2 ^ b) ∧
  (∀ (Qc : Fin P.computeChip.rap.w → F[X])
      (Qm : Fin P.memoryChip.rap.w → F[X]),
    ((P.OptimizedFalseAcceptanceSet Qc Qm).card : ℚ) /
        Fintype.card (OptimizedProductionChallengeTuple K F) ≤
      optimizedProductionFailureProbabilityBound (Fintype.card K) (Fintype.card F)
        (OptimizedFailureEventEv.workloadEv P P.optimized.Λ +
          OptimizedHostileTimestamps.timestampCollisionBound
            (3 * P.optimized.family.problem.cfg.compRows) +
            pricedWalkWork P.optimized.family.problem.cfg.compRows
              P.optimized.family.problem.cfg.memRows)
        (P.hostileIOWork + P.hostileInterWork)
        P.optimized.family.problem.cfg.compRows P.optimized.family.problem.cfg.memRows) ∧
  (∀ (Qc : Fin P.computeChip.rap.w → F[X])
      (Qm : Fin P.memoryChip.rap.w → F[X]) (b : ℕ),
    optimizedProductionFailureProbabilityBound (Fintype.card K) (Fintype.card F)
        (OptimizedFailureEventEv.workloadEv P P.optimized.Λ +
          OptimizedHostileTimestamps.timestampCollisionBound
            (3 * P.optimized.family.problem.cfg.compRows) +
            pricedWalkWork P.optimized.family.problem.cfg.compRows
              P.optimized.family.problem.cfg.memRows)
        (P.hostileIOWork + P.hostileInterWork)
        P.optimized.family.problem.cfg.compRows P.optimized.family.problem.cfg.memRows *
        2 ^ b ≤ 1 →
      ((P.OptimizedFalseAcceptanceSet Qc Qm).card : ℚ) /
        Fintype.card (OptimizedProductionChallengeTuple K F) ≤ 1 / 2 ^ b)

theorem packageR_and_packageP_have_the_same_four_field_tail
    (haxR : FormRAxisBound (packageR hfirstD).optimized.sampled (packageR hfirstD).optimized.basis)
    (hbasisR : FormRBasis (packageR hfirstD).optimized.basis)
    (hwidthR : FormRWidth F97)
    (haxP : FormRAxisBound (packageP hmoreM).optimized.sampled (packageP hmoreM).optimized.basis)
    (hbasisP : FormRBasis (packageP hmoreM).optimized.basis)
    (hwidthP : FormRWidth F97) :
    FourResidualFields (packageR hfirstD) ∧ FourResidualFields (packageP hmoreM) :=
  ⟨⟨(statementR hfirstD haxR hbasisR hwidthR).p8_fixed_field_soundness, (statementR hfirstD haxR hbasisR hwidthR).p8_fixed_field_bits,
      (packageR hfirstD).optimizedFalseAcceptance_probability_le_legacy haxR hbasisR hwidthR,
      (packageR hfirstD).optimizedFalseAcceptance_probability_le_two_pow_neg_legacy haxR hbasisR hwidthR⟩,
    ⟨(statementP hmoreM haxP hbasisP hwidthP).p8_fixed_field_soundness, (statementP hmoreM haxP hbasisP hwidthP).p8_fixed_field_bits,
      (packageP hmoreM).optimizedFalseAcceptance_probability_le_legacy haxP hbasisP hwidthP,
      (packageP hmoreM).optimizedFalseAcceptance_probability_le_two_pow_neg_legacy haxP hbasisP hwidthP⟩⟩

/-- Same `9+1+4` field split does not mean same fixture evidence: P's census consists only of
self-pairs, whereas R's consumed census has a genuinely distinct pair. -/
theorem same_field_split_but_different_census_evidence :
    (9 + 1 + 4 = 14) ∧
      (∀ i : Fin (packageP hmoreM).optimized.census.census.count,
        ((packageP hmoreM).optimized.census.census.pair i).1 =
          ((packageP hmoreM).optimized.census.census.pair i).2) ∧
      (∃ i : Fin (packageR hfirstD).optimized.census.census.count,
        (packageR hfirstD).optimized.census.census.pair i = (operandLeft, operandRight) ∧
          ((packageR hfirstD).optimized.census.census.pair i).1 ≠
            ((packageR hfirstD).optimized.census.census.pair i).2) := by
  refine ⟨by norm_num, ?_,
    packageR_consumed_census_has_genuine_distinct_pair hfirstD hrootAt hrootAtQ⟩
  exact Nock.RedTeam.Batch82.censusM_every_pair_is_self hmoreM hrootAtP


#print axioms released_aliases_and_control_unchanged
#print axioms statementR_fourteen_field_eta
#print axioms released_hzero_boundary_is_load_bearing
#print axioms selector_only_mixed_assignment
#print axioms parameterized_pin_is_stronger_than_the_With_constructor_scope
#print axioms fold2_reuses_the_Batch86_scalar_and_polynomial
#print axioms one_package_and_exact_committed_fibre
#print axioms packageR_census_is_threaded_and_distinct
#print axioms FourResidualFields
#print axioms packageR_and_packageP_have_the_same_four_field_tail
#print axioms same_field_split_but_different_census_evidence

#print axioms Nock.NockVMROM.Thm54.BuildablePackage.buildFullPackage
#print axioms Nock.NockVMROM.Thm54.BuildablePackage.buildFullPackageWith
#print axioms Nock.NockVMROM.Thm54.DistinctCensusFold2.packageR
#print axioms Nock.NockVMROM.Thm54.DistinctCensusFold2.statementR
#print axioms Nock.NockVMROM.Thm54.DistinctCensusFold2.packageR_accepts

#print axioms «Thm:IO_result»
#print axioms «Thm:Walk_IOP»
#print axioms «Corr:forest»
#print axioms «Thm:deterministic_Trace»
#print axioms «Lem:NPR_decomp»
#print axioms «Thm:Noun_Validation»
#print axioms «Thm:comp_38»
#print axioms «Thm:mem_38»
#print axioms «Thm:NockVMROM»
#print axioms «Lem:equiv_compute»
#print axioms «Lem:equiv_mem»
#print axioms
  Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package
#print axioms Nock.NockVM.V_NockVMROM_forest

end
end Nock.RedTeam.Batch87
